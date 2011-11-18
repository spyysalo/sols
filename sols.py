#!/usr/bin/env python

# soft-matching ontology lookup service

# author: Sampo Pyysalo <sampo pyysalo gmail com>

from __future__ import with_statement

import sys
import re
import os
from itertools import chain

from readobo import parse_obo, Term
from sdistance import tsuruoka_norm
try:
    import simstring
except ImportError:
    print >> sys.stderr, """Error: failed 'import simstring'.
This software cannot work without this library. 
Please make sure that you have simstring and its
python bindings set up correctly from 

    http://www.chokkan.org/software/simstring/
"""
    sys.exit(1)

# directory in which to store simstring DBs for lookup.
DB_BASE_DIRECTORY = 'simstring_dbs'

# file from which to read known lexical variants.
LEXICAL_VARIANT_FILE = 'lexical-variants.txt'

# similarity measures supported by simstring
SIMILARITY_MEASURE = {
    'exact'   : simstring.exact,
    'dice'    : simstring.dice,
    'cosine'  : simstring.cosine,
    'jaccard' : simstring.jaccard,
    'overlap' : simstring.overlap,
}

# the string used to mark "is-a" connections
ISA_STRING = "is_a"
# same for bridge links
BRIDGE_STRING = "is_a" # same for compatibility

options = None

search_targets = {}

bridge_mapping = {}

# known types for search targets
SEARCH_TARGET_CRITERIA = set([
    "STOP-BEFORE", 
    "STOP-AT",
    "REMOVE",
])

def argparser():
    import argparse

    ap=argparse.ArgumentParser(description="Perform soft string matching lookups against OBO ontologies. Reads query strings from STDIN.")
    ap.add_argument("-s", "--similarity", metavar="SIM", default="cosine", help="Simstring similarity measure. SIM should be one of: "+", ".join(SIMILARITY_MEASURE.keys()))
    ap.add_argument("-t", "--threshold", metavar="TH", default='0.95', help="Soft string match threshold, 0 < TH <= 1")
    ap.add_argument("-st", "--simstring-threshold", metavar="TH", default='0.7', help="Simstring threshold, 0 < TH <= 1")
    ap.add_argument("-a", "--all-hits", default=False, action="store_true", help="Output all hits in each ontology, not only the best")
    ap.add_argument("-k", "--keep-case", default=False, action="store_true", help="Preserve case when populating string DBs (ignored by default)")
    ap.add_argument("-ci", "--case-insensitive", default=False, action="store_true", help="Case-insensitive processing (lowercases everything)")    
    ap.add_argument("-nm", "--no-multiple-inheritance", default=False, action="store_true", help="Exclude paths involving multiple inheritance.")
    ap.add_argument("-np", "--no-part-of", default=False, action="store_true", help="Never consider paths involving part-of relations.")
    ap.add_argument("-nc", "--no-case-normalization", default=False, action="store_true", help="Skip heuristic case normalization of ontology terms.")
    ap.add_argument("-nv", "--no-lexical-variants", default=False, action="store_true", help="Skip adding lexical variants as synonyms to ontology terms.")
    ap.add_argument("-pi", "--print-index", default=False, action="store_true", help="Print string index after constructing it.")
    ap.add_argument("-T", "--targets", metavar="FILE", default="targets.txt", help="File defining \"target\" terms at which to stop traversal")
    ap.add_argument("-m", "--minimal", default=False, action="store_true", help="Minimal output format")
    ap.add_argument("-M", "--more-minimal", default=False, action="store_true", help="More minimal output format")
    ap.add_argument("-b", "--bridge", metavar="FILE", default=None, help="\"Bridge\" mapping between ontologies to apply.")
    ap.add_argument("files", metavar="OBO-FILE", nargs="+", help="Source ontologies.")
    return ap

def read_bridge(filename):
    # the "bridge" format is just a subset of the full OBO format;
    # read in normally

    try:
        with open(filename) as f:
            all_terms, term_by_id = parse_obo(f, include_nameless=True)
    except Exception, e:
        print >> sys.stderr, "Warning: failed to read \"bridge\" %s: %s" % (filename, e)
        print >> sys.stderr, "         Mappings will not be applied."
        return {}

    # process into a id-to-id multimap
    mapping = {}
    for sid in term_by_id:
        if sid not in mapping:
            mapping[sid] = []
        for tid, tname in term_by_id[sid].is_a:
            mapping[sid].append(tid)

    return mapping

def read_ontologies(filenames):
    global options

    ontology_by_name = {}

    for fn in filenames:
        # The way to get ontology names from .obo is a bit flaky, so use
        # the given file basename to identify the ontologies.
        bn = os.path.basename(fn)
        bn = bn.replace(".obo","")
        
        assert bn not in ontology_by_name, "Error: ontology '%s' appears multiple times!"

        try:
            with open(fn) as f:
                try:
                    all_terms, term_by_id = parse_obo(f)
                    ontology_by_name[bn] = (all_terms, term_by_id) 
                except Exception, e:
                    print >> sys.stderr, "ERROR: failed to parse %s: %s" % (fn, e)
                    print >> sys.stderr, """
########################################
#
# Warning: could not parse ontology
#     %s.
# Matches will not be performed against
# this ontology.
#
########################################""" % bn
        except IOError, e:
            print >> sys.stderr, "Error: failed to read %s: %s" % (fn, e)
            return None

    # normalize case by default; use ID prefix as heuristic for when
    # this is necessary
    if not options.no_case_normalization:
        for n in ontology_by_name:
            all_terms, term_by_id = ontology_by_name[n]
            for t in all_terms:
                # normalization currently limited to a few ontologies
                # with known nonstandard capitalization practices.
                # (FMA systematically capitalizes initial letter; WBbt
                # has a mix of capitalization conventions; SAO
                # capitalizes all words.)
                if t.obo_idspace() in ("FMA", "WBbt"):
                    t.case_normalize_initial()
                elif t.obo_idspace() == "SAO":
                    t.case_normalize_all_words()

    return resolve_references(ontology_by_name)

def resolve_mapping(mapping, ontology_by_name):
    # assume that term_by_id maps have already been combined by
    # resolve_references so that is't enough to just pick an
    # arbirtrary one (sorry, this is exceedingly ugly)
    term_by_id = ontology_by_name[ontology_by_name.keys()[0]][1]

    resolved_mapping = {}
    for sid in mapping:
        resolved = []
        for tid in mapping[sid]:
            if tid not in term_by_id:
                print >> sys.stderr, "Warning: ID %s not defined, discarding from mapping" % tid
            else:
                resolved.append(term_by_id[tid])
        if resolved != []:
            resolved_mapping[sid] = resolved

    return resolved_mapping

def resolve_references(ontology_by_name):
    # separated reference resolution (such as is_a ID list into parent
    # and child object references) from initial read to allow
    # cross-ontology refs (e.g. VAO into CARO) to resolve.

    # combine ID maps
    combined_term_by_id = {}
    for bn in ontology_by_name:
        all_terms, term_by_id = ontology_by_name[bn]
        for tid in term_by_id:
            #assert tid not in combined_term_by_id, "ERROR: id '%s' defined multiple times" % tid
            if tid in combined_term_by_id:
                # multiple defs. Redefinitions happen; no good principled solutions yet, I'm afraid.
                print >> sys.stderr, "Warning: id '%s' defined multiple times, arbitrarily picking one definition." % tid
                pass
            else:
                combined_term_by_id[tid] = term_by_id[tid]

    # use the combined for all 
    for bn in ontology_by_name:
        ontology_by_name[bn] = (ontology_by_name[bn][0], combined_term_by_id)

    # resolve references
    for bn in ontology_by_name:
        all_terms, term_by_id = ontology_by_name[bn]
        for t in all_terms:
            t.resolve_references(term_by_id)

    return ontology_by_name

def find_head(np):
    # Simple algorithm for heuristically identifying the likely head of
    # the given noun phrase. Largely follows the method of Cohen et al.,
    # BioNLP'11. Returns strings before, head, after, where
    # before+head+after == np and head is the heuristically guessed head
    # word.
    initial_np = np

    # clean up and store and initial or terminal space
    start_space, end_space = "", ""
    m = re.match(r'^(\s+)(.*\s*)$', np)
    if m:
        start_space, np = m.groups()
    m = re.match(r'(.*?)(\s+)$', np)
    if m:
        np, end_space = m.groups()
    
    # start by splitting by first preposition occurring after
    # non-empty string, if any (not a "complete" list)
    m = re.match(r'^(.+?)( +(?:of|in|by|as|on|at|to|via|for|with|that|than|from|into|upon|after|while|during|within|through|between|whereas|whether) .*)$', np)
    if m:
        np, post_after = m.groups()
    else:
        np, post_after = np, ""

    # remove highly likely initial determiner followed by candidate
    # word, if any
    m = re.match(r'^((?:a|the)\s+)(\S.*)$', np)
    if m:
        pre_before, np = m.groups()
    else:
        pre_before, np = "", np

    # then, pick last "word" in the (likely) head NP, where "word" is
    # defined as space-separated non-space sequence containing at
    # least one alphabetic character, or the last non-space if not
    # found (or just the whole thing as a final fallback).
    m = re.match(r'^(.*\s|.*?)(\S*[a-zA-Z]\S*)(.*)$', np)
    if m:
        before, head, after = m.groups()
    else:
        m = re.match(r'^(.* )(\S+)(.*)$', np)
        if m:
            before, head, after = m.groups()
        else:
            before, head, after = "", np, ""

    # combine back possible omitted bits
    before = start_space + pre_before + before
    after  = after + post_after + end_space

    # sanity check
    assert before+head+after == initial_np, "INTERNAL ERROR: '%s' + '%s' + '%s' != '%s'" % (before, head, after, initial_np)

    return before, head, after

def add_lexical_variants(ontology_by_name):
    global LEXICAL_VARIANT_FILE

    variants = {}

    try:
        with open(LEXICAL_VARIANT_FILE, 'rt') as f:
            for l in f:
                l = l.strip()
                # expect three TAB-separated fields: original token,
                # variant type, and variant token
                orig, vartype, var = l.split('\t')
                if orig not in variants:
                    variants[orig] = []
                variants[orig].append((var, vartype))
    except Exception, e:
        print >> sys.stderr, "Error reading %s: %s\nNot adding lexical variant synonyms." % (LEXICAL_VARIANT_FILE, e)
        return False

    # for each ontology, add synonym variants for strings that are not
    # already included in that ontology.
    for all_terms, dummy in ontology_by_name.values():
        known_strings = {}
        for t in all_terms:
            known_strings[t.name] = True
            for s in t.synonyms:
                known_strings[s[0]] = True

        for t in all_terms:
            known_synonyms = t.synonyms[:]

            for orig, syntype in chain([(t.name,"")], known_synonyms):
                # just generate variants for the head
                before, head, after = find_head(orig)
                if head not in variants:
                    #print >> sys.stderr, "No variants for '%s'" % head
                    continue
                for var, vartype in variants[head]:
                    s = before+var+after
                    if s in known_strings:
                        #print >> sys.stderr, "Known variant, skip: '%s'" % s
                        continue
                    # OK to add
                    #print >> sys.stderr, "Adding variant '%s' -%s-> '%s'" % (before+head+after, vartype, s)
                    if syntype == "":
                        t.synonyms.append((s, vartype))
                    else:
                        t.synonyms.append((s, syntype+"_"+vartype))

    return True

def index_ontologies(ontology_by_name):
    global options

    idx = {}

    if options.keep_case:
        # index as-is
        for all_terms, dummy in ontology_by_name.values():
            for t in all_terms:
                # I wish I had 2.5 and defaultdict ...
                if t.name not in idx:
                    idx[t.name] = []
                idx[t.name].append(t)
                for s in t.synonyms:
                    if s[0] not in idx:
                        idx[s[0]] = []
                    idx[s[0]].append(t)
    else:
        # index lowercase (sorry dup, wanted if out of inner loop)
        for all_terms, dummy in ontology_by_name.values():
            for t in all_terms:
                lc = t.name.lower()
                if lc not in idx:
                    idx[lc] = []
                idx[lc].append(t)
                for s in t.synonyms:
                    lc = s[0].lower()
                    if lc not in idx:
                        idx[lc] = []
                    idx[lc].append(t)

    return idx

def build_simstring_db(strs, name):
    """
    Given a collection of strings and a DB name, builds a simstring
    database for the strings. Returns the name under which the DB is
    stored, which is based on but not identical to the given name.
    """

    try:
        # include pid to assure that there are no clashes.
        dbfn = os.path.join(DB_BASE_DIRECTORY, name+"."+str(os.getpid())+".db")
        db = simstring.writer(dbfn)
        for s in strs:
            db.insert(s)
        db.close()
    except:
        print >> sys.stderr, "Error building simstring DB"
        raise

    return dbfn

def open_simstring_db(dbname):
    try:
        db = simstring.reader(dbname)
    except:
        print >> sys.stderr, "Error opening simstring DBs for reading"
        raise        
    return db

def delete_simstring_db(dbname):
    # Some caution should be exercised with this one
    import glob
    
    # remove the "base" DB
    os.remove(dbname)
    # remove the "sub" DBs
    for fn in glob.glob(dbname+'.*.cdb'):
        os.remove(fn)

    return True

def _paths_via(link, node, traversed, traversed_part_of=False, ignore_targets=False):
    # implementation for root_paths(), don't invoke directly
    # unless you're sure what you're doing.
    global search_targets

    # targets may be ignored in cases to force a transition,
    # e.g. for bridge-mapping
    if node.tid in search_targets and not ignore_targets:
        assert search_targets[node.tid][1] in SEARCH_TARGET_CRITERIA, "INTERNAL ERROR"
        if search_targets[node.tid][1] == "STOP-BEFORE":
            # explicit instruction not to traverse to this node; don't
            # take the link but instead give a single empty path.
            return [[]]
        elif search_targets[node.tid][1] == "REMOVE":
            # instruction to remove the whole path as irrelevant.
            # exception: don't remove if a "part-of" connection was
            # traversed to allow classifications such as "X part-of
            # organism" even if "organism" is not of interest as a
            # classification.
            if not traversed_part_of:
                return []
        else:
            # no need to stop yet
            assert search_targets[node.tid][1] == "STOP-AT"
            pass

    # OK to traverse, take link to node
    paths = [[link]+path for path in _root_paths(node, traversed, traversed_part_of)]
    return paths

def _root_paths(node, traversed=None, traversed_part_of=False):
    # implementation for root_paths(), don't invoke directly
    # unless you're sure what you're doing.
    global search_targets, bridge_mapping, options

    if traversed is None:
        traversed = {}

    if node.tid in traversed:
        # way too noisy
        #print >> sys.stderr, "Warning: arrived multiple times at %s, breaking traversal" % str(node)
        return []
    traversed[node.tid] = True

    # apply mappings (if any) before checking if we've hit a target to
    # make sure that mappings are honored
    if node.tid in bridge_mapping:
        #print >> sys.stderr, "Mapping via bridge from %s to %s" % (str(node), ",".join([str(n) for n in bridge_mapping[node.tid]]))
        all_paths = []
        for nextn in bridge_mapping[node.tid]:
            for path in _paths_via(BRIDGE_STRING, nextn, traversed, 
                                   traversed_part_of, ignore_targets=True):
                all_paths.append([node]+path)
        return all_paths

    if node.tid in search_targets:
        if search_targets[node.tid][1] in ("STOP-BEFORE", "STOP-AT"):
            # explicit instruction to stop once reaching here (if not
            # earlier); result is single path consisting of the node only.
            return [[node]]
        else:
            assert search_targets[node.tid][1] == "REMOVE", "INTERNAL ERROR"
            # instruction to remove the whole path as irrelevant
            # exception: treat as "STOP-AT" if traversed part-of (see 
            # detailed comment in _paths_via)
            if not traversed_part_of:
                return []
            else:
                return [[node]]

    elif node.parents != []:
        # has is-a parents; prioritize searching these.
        if len(node.parents) > 1 and options.no_multiple_inheritance:
            print >> sys.stderr, "Note: multiple inheritance at %s, cutting search (option -nm)" % str(node)
            return []

        all_paths = []
        for nextn in node.parents:
            for path in _paths_via(ISA_STRING, nextn, traversed, traversed_part_of):
                all_paths.append([node]+path)
        return all_paths

    elif node.objects != []:
        # no is-a parents but has part-of parents; traverse as a backup unless ruled out.
        if options.no_part_of:
            print >> sys.stderr, "Note: only part-of relations at %s, cutting search (option -np)" % str(node)
            return []
        if len(node.objects) > 1 and options.no_multiple_inheritance:
            print >> sys.stderr, "Note: multiple part-of relations at %s, cutting search (option -nm)" % str(node)
            return []

        all_paths = []
        for link, nextn in node.objects:
            for path in _paths_via(link, nextn, traversed, traversed_part_of=True):
                all_paths.append([node]+path)
        return all_paths

    else:
        # nowhere to go (root?), result is single path consisting of
        # this node only.
        return [[node]]

def unique_paths(paths):
    seen = {}
    unique = []
    for p in paths:
        tp = tuple(p)
        if tp not in seen:
            unique.append(p)
            seen[tp] = True
        else:
            print >> sys.stderr, "Note: eliminating duplicate path %s" % str(p)
    return unique

def matching_string(node, s):
    # given a node and a string matching it, returns (MATCH, MATCHTYPE)
    # where MATCH is the matching string among those defined for the
    # node (name and synonyms) and MATCHTYPE is either "name" if the
    # name matches and a string representing the synonym type
    # otherwise. Returns (None, None) if matching fails.
    # Assume case-insensitive matches are acceptable.

    if s.lower() == node.name.lower():
        return (node.name, "name")
    else:
        candidates = []
        for synstr, syntype in node.synonyms:
            if s.lower() == synstr.lower():
                if syntype is not None and syntype != "":
                    candidates.append((synstr, "synonym_%s" % syntype.lower().replace(" ","_")))
                else:
                    candidates.append((synstr, "synonym"))

        if len(candidates) == 0:
            return (None, None)

        # prefer exact synonyms to others, and simple synonyms
        # to remaining
        exacts = [(ss,st) for ss, st in candidates if "exact" in st]
        if len(exacts) != 0:
            return exacts[0]
        plains = [(ss,st) for ss, st in candidates if st == "synonym"]
        if len(plains) != 0:
            return plains[0]

        if len(candidates) > 1:
            print >> sys.stderr, "Note: matching_string: can't decide between %s synonyms, picking one arbitrarily." % ",".join([st for ss,st in candidates])
        return candidates[0]
    
def root_paths(node, querystr=None):
    # returns a list representing path(s) from the given node to
    # ontology root (or the "nearest" intervening target).  
    # Returns a list of paths, each a list containing alternating Term
    # objects and strings, where the strings represent connections
    # between the terms.

    path_start = []

    # in case the path is not for a query string matching the name but
    # a synonym, start off the path with a "fake" Term representing
    # the synonym.
    if querystr is not None:
        match_str, match_type = matching_string(node, querystr)
        if match_str is None:
            print >> sys.stderr, "Warning: root_path: failed to determine how %s matched %s" % (querystr, node)
        elif match_type == "name":
            # straight match, OK as is
            pass
        else:
            # synonym match, make intermediate
            path_start.append(Term(node.tid, match_str, [], []))
            path_start.append(match_type)

    all_paths = []
    for p in _root_paths(node):
        all_paths.append(path_start[:] + p)

    # remove dups. These can arise e.g. through multiple inheritance
    # prior to a STOP-BEFORE target
    all_paths = unique_paths(all_paths)

    return all_paths

def _wrap_path_strings(path):
    # helper; wrap the strings in the path to make them more visually obvious
    if len(path) == 0:
        return path

    wrapped = []
    # note: leaving first and last string untouched; this is used for
    # info, not links (sorry, this is a bit clumsy)
    for n in path[:-1]:
        if isinstance(n, str):
            wrapped.append("-%s-" % n)
        else:
            wrapped.append(n)
    wrapped.append(path[-1])
    return wrapped

def minimize_path(path):
    # given a path of alternating Term objects and strings defining
    # their links (e.g. "is_a"), returns a minimized path that aims to
    # characterize the relevant top-level classification.

    # first, if there's a first synonym link, strip that and keep it
    # separately
    if len(path) >= 3 and "synonym" in path[1]:
        synstr = path[1]
        path   = path[2:]
    else:
        synstr = None

    # next, take out any pair of sequential "is_a" links in the chain
    while len(path) >= 3:
        compressed = False
        for i in range(1, len(path)-1):
            if path[i-1] == ISA_STRING and path[i+1] == ISA_STRING:
                path = path[:i-1]+path[i+1:]
                compressed = True
                break
        if not compressed:
            break

    # next, take out any pair of sequential identical "part_of" links
    # (assumed to be transitive)
    while len(path) >= 3:
        compressed = False
        for i in range(1, len(path)-1):
            if isinstance(path[i-1],str) and "part_of" in path[i-1] and path[i-1]==path[i+1]:
                path = path[:i-1]+path[i+1:]
                compressed = True
                break
        if not compressed:
            break

    # if there was a synonym, attach it to the start of the path
    if synstr is not None:
        path = [synstr] + path

    return path

def minimize_path_more(path):
    # like minimize_path, but does a more aggressive job

    # first, if there's a first synonym link, strip that and keep it
    # separately
    if len(path) >= 3 and "synonym" in path[1]:
        synstr = path[1]
        path   = path[2:]
    else:
        synstr = None

    # next, take out any "is_a" links in the chain (taken as
    # implied in minimal output)
    while len(path) >= 3:
        compressed = False
        for i in range(1, len(path), 2):
            if path[i] == ISA_STRING:
                path = path[:i-1]+path[i+1:]
                compressed = True
                break
        if not compressed:
            break

    # next, take out any pair of sequential identical "part_of" links
    # (assumed to be transitive)
    while len(path) >= 3:
        compressed = False
        for i in range(1, len(path)-1):
            if isinstance(path[i-1],str) and "part_of" in path[i-1] and path[i-1]==path[i+1]:
                path = path[:i-1]+path[i+1:]
                compressed = True
                break
        if not compressed:
            break

    # finally, if there's more than one node remaining, take out
    # the first (understood as implied)
    if len(path) > 1:
        path = path[1:]

    # if there was a synonym, attach it to the end of the path
    # (sorry, this is a bit messy)
    if synstr is not None:
        path.append("["+synstr+"]")

    return path

def stringify_path(path):
    return "\t".join(str(n) for n in _wrap_path_strings(path))

def read_targets(fn):
    # Read in "targets" types which to stop the ontology traversal and
    # return the identified concept. The read format is three-column
    # and tab-separated, with the first being the stopping criterion,
    # the second an OBO ID, and the third an OBO name.

    # Returns a dict indexed by OBO IDs and having the (name,
    # criterion) pairs as values.

    try:
        targets = {}

        with open(fn) as f:
            for l in f:
                l = l.strip()

                # anything followed by a '#' is ignored as a comment
                l = re.sub(r'\#.*', '', l)

                if l.strip() == '':
                    continue

                # non-empty, non-comment lines must have three
                # tab-separated fields
                fields = l.split('\t')
                if len(fields) != 3:
                    print >> sys.stderr, "Warning: error parsing line in %s, ignoring: %s" % (fn, l)
                    continue
                criterion, tid, name = fields

                if criterion not in SEARCH_TARGET_CRITERIA:
                    print >> sys.stderr, "Warning: unrecognized target criterion in %s, ignoring: %s" % (fn, l)
                    continue

                if tid in targets:
                    print >> sys.stderr, "Warning: %s appears multiple times in %s, ignoring all but first" % (tid, fn)
                else:
                    targets[tid] = (name, criterion)

        return targets

    except IOError:
        print >> sys.stderr, "Warning: error reading in \"targets\" from %s. Output likely to contain extraneous terms." % fn
        return {}

def main(argv=None):
    global options

    global options
    arg = argparser().parse_args(argv[1:])
    options = arg

    # check arguments
    try:
        assert arg.similarity in SIMILARITY_MEASURE
        arg.threshold = float(arg.threshold)
        arg.simstring_threshold = float(arg.simstring_threshold)
        assert arg.threshold > 0.0 and arg.threshold <= 1.0
        assert arg.simstring_threshold > 0.0 and arg.simstring_threshold <= 1.0
    except:
        print >> sys.stderr, "Argument error, exiting."
        argparser().print_help()
        return 1

    if arg.threshold < arg.simstring_threshold:
        print >> sys.stderr, """Warning: threshold (%f) lower than simstring threshold (%f).
Some matches meeting threshold will likely be missed because they 
will not be recovered from the simstring DB.
Suggest lowering simstring threshold.""" % (arg.threshold, arg.simstring_threshold)

    if arg.case_insensitive and arg.keep_case:
        print >> sys.stderr, "Error: -k and -ci arguments are not compatible."
        return 1

    # read in the "target" types, if any
    global search_targets
    search_targets = read_targets(arg.targets)

    # read in "bridge" mapping, if any
    global bridge_mapping
    if arg.bridge:
        bridge_mapping = read_bridge(arg.bridge)

    # read in the ontologies specified on command-line
    print >> sys.stderr, "Reading ontologies ...",
    ontology_by_name = read_ontologies(arg.files)
    if ontology_by_name is None:
        print >> sys.stderr, "Error reading ontologies, exiting."
        return 1
    print >> sys.stderr, "done."

    # add lexical variants as synonyms of ontology terms
    if not arg.no_lexical_variants:
        print >> sys.stderr, "Adding term lexical variants as synonyms ...",
        add_lexical_variants(ontology_by_name)
        print >> sys.stderr, "done."

    # resolve the bridge mapping IDs into objects
    bridge_mapping = resolve_mapping(bridge_mapping, ontology_by_name)

    # create indices mapping for each name or synonym in each ontology
    # and lowercased versions of these to the set of matching nodes
    print >> sys.stderr, "Creating string indices ...",
    string_idx = index_ontologies(ontology_by_name)
    print >> sys.stderr, "done."

    # output string index keys if requested
    if arg.print_index:
        for s in string_idx:
            print s

    # build simstring DBs for approximate string matching and
    # open for reading
    print >> sys.stderr, "Building simstring DBs ...",
    sdbname   = build_simstring_db(string_idx, "strings")
    string_db = open_simstring_db(sdbname)
    print >> sys.stderr, "done."

    # set up DB matching according to command-line parameters
    string_db.measure = SIMILARITY_MEASURE[options.similarity]
    string_db.threshold = options.simstring_threshold

    # keep some stats
    total_query_count, total_string_count, total_node_count = 0, 0, 0
    
    print >> sys.stderr, "Ready."

    # main loop: read string, look up, return results.
    for l in sys.stdin:
        query = l.strip()
        total_query_count += 1

        if options.keep_case:
            resp  = string_db.retrieve(query)
        else:
            resp  = string_db.retrieve(query.lower())

        new_string_count = len(resp)
        total_string_count += new_string_count

        # collect the unique set of ontology nodes that have a
        # matching name or synonym and "scores" for the string matches
        # for cases where the score crosses the user-set threshold.
        # For each returned node, store the highest-scoring response
        # retrieving it.
        nodes = set()
        score = {}
        response = {}
        for r in resp:
            for n in string_idx[r]:
                match_str, match_type = matching_string(n, r)
                if match_str is None:
                    # shouldn't happen, but just as a fallback ...
                    match_str = r

                if options.case_insensitive:
                    rscore = tsuruoka_norm(match_str.lower(), query.lower())
                else:
                    rscore = tsuruoka_norm(match_str, query)

                if rscore < arg.threshold:
                    # too low agreement, skip
                    continue
                if n not in nodes or rscore > score[n]:
                    response[n] = match_str
                    nodes.add(n)
                    score[n] = rscore

        # sort by score
        snodes = []
        for n in nodes:
            snodes.append((score[n], n))
        snodes.sort(lambda a,b: cmp(b,a))
        nodes = [sn[1] for sn in snodes]

        if not options.all_hits:
            # Only keep top-scoring hits from each ontology. Note that
            # this may still preserve multiple hits with equal score
            # from a single ontology.
            filtered_nodes = []
            otop = {}
            for n in nodes:
                o = n.obo_idspace()
                if o in otop and otop[o] > score[n]:
                    # way too much noise, maybe under -vv
                    #print >> sys.stderr, "Note: ignoring hit with score %f (%s) as there was already a %s hit with score %f" % (s, n, o, otop[o])
                    pass
                else:
                    filtered_nodes.append(n)
                    otop[o] = score[n]
            nodes = filtered_nodes

        # find and store (node, path) pairs, eliminating duplicate
        # paths arising from a single ontology in the process. (dups
        # arise in particular for minimized paths.)
        seen_paths = {}
        node_paths = []
        for n in nodes:
            paths = root_paths(n, response[n])

            if options.more_minimal:
                paths = [minimize_path_more(p) for p in paths]
            elif options.minimal:
                paths = [minimize_path(p) for p in paths]

            # take uniques per ontology, using the node ID "idspace"
            # part to identify ontologies. Per-ontology uniqueing to
            # avoid overload from cases like "spine" being the synonym
            # of 19 types in TGMA, most of which end up at the same
            # few top-level nodes.
            o = n.obo_idspace()
            for p in paths:
                tp = tuple(p)
                if (o,tp) not in seen_paths:
                    seen_paths[(o,tp)] = True
                    node_paths.append((n,p))
                else:
                    #print >> sys.stderr, "Note: eliminating duplicate path %s" % str(p)
                    pass

        # finally, output.
        for n, p in node_paths:
            print "%s\t%f\t%s" % (response[n], score[n], stringify_path(p))

        # some nodes may have been judged irrelevant; redo set
        unique_relevant_nodes = []
        for n, p in node_paths:
            if n not in unique_relevant_nodes:
                unique_relevant_nodes.append(n)
        nodes = unique_relevant_nodes

        total_node_count += len(nodes)

        print "\tMatched %d strings and retrieved %d matches for query: %s" % (new_string_count, len(nodes), l),

    print >> sys.stderr, "Cleaning up ...",

    # remove DBs
    string_db.close()
    delete_simstring_db(sdbname)

    print >> sys.stderr, "done."

    print >> sys.stderr, "Received %d queries, found %d matched strings, returned %d responses." % (total_query_count, total_string_count, total_node_count)

    return 0

if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except Exception, e:
        print >> sys.stderr, """
########################################
#
# WARNING: died unexpectedly. There may
# be leftover data in the directory
#     %s
# that needs to be cleaned up manually.
# Sorry about that.
#
########################################""" % DB_BASE_DIRECTORY
        raise
