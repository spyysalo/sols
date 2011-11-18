#!/usr/bin/env python

'''
Various string distance measures.

Author:     Pontus Stenetorp    <pontus stenetorp se>
Version:    2011-08-09
'''

from string import digits

DIGITS = set(digits)
TSURUOKA_2004_INS_CHEAP = set((' ', '-', ))

def _tsuruoka_ins(c):
    if c in TSURUOKA_2004_INS_CHEAP:
        return 10
    else:
        return 100

def _tsuruoka_del(c):
    return _tsuruoka_ins(c)

def _tsuruoka_repl(c, d):
    if ((c in DIGITS and d in DIGITS) or
            (c == '-' and d == ' ') or
            (c == ' ' and d == '-') or
            (c.upper() == d) or
            (c.lower() == d)):
        return 10
    else:
        return 50

def tsuruoka(a, b):
    # Special case for empties
    if len(a) == 0 or len(b) == 0:
        return 100*max(len(a),len(b))

    # Initialise the first column
    prev_min_col = [0]
    for b_c in b:
        prev_min_col.append(prev_min_col[-1] + _tsuruoka_ins(b_c))
    curr_min_col = prev_min_col

    for a_c in a:
        curr_min_col = [prev_min_col[0] + _tsuruoka_del(a_c)]

        for b_i, b_c in enumerate(b):
            if b_c == a_c:
                curr_min_col.append(prev_min_col[b_i])
            else:
                curr_min_col.append(min(
                    prev_min_col[b_i + 1] + _tsuruoka_del(a_c),
                    curr_min_col[-1] + _tsuruoka_ins(b_c),
                    prev_min_col[b_i] + _tsuruoka_repl(a_c, b_c)
                        ))
        
        prev_min_col = curr_min_col

    return curr_min_col[-1]

def tsuruoka_norm(a, b):
    return 1 - (tsuruoka(a,b) / (max(len(a),len(b)) * 100.))

def levenstein(a, b):
    # Special case for empties
    if len(a) == 0 or len(b) == 0:
        return max(len(a),len(b))

    # Initialise the first column
    prev_min_col = [0]
    for b_c in b:
        prev_min_col.append(prev_min_col[-1] + 1)
    curr_min_col = prev_min_col

    for a_c in a:
        curr_min_col = [prev_min_col[0] + 1]

        for b_i, b_c in enumerate(b):
            if b_c == a_c:
                curr_min_col.append(prev_min_col[b_i])
            else:
                curr_min_col.append(min(
                    prev_min_col[b_i + 1] + 1,
                    curr_min_col[-1] + 1,
                    prev_min_col[b_i] + 1
                        ))
        
        prev_min_col = curr_min_col

    return curr_min_col[-1]

if __name__ == '__main__':
    for a, b in (('kitten', 'sitting'), ('Saturday', 'Sunday'), ('Caps', 'caps'), ('', 'bar'), ('dog', 'dog')):
        print a, b, levenstein(a,b)
        print a, b, tsuruoka(a,b)
        print a, b, tsuruoka_norm(a,b)
