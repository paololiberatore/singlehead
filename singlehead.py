#!/usr/bin/env python3
#
# single-head equivalence:
# is the given formula equivalent to a single-head formula,
# one where each variable occurs in the head of at most one clause?

import itertools
import sys


# print up to a certain level of nesting

maxlevel = 2
def printinfo(level, *s):
    if level <= maxlevel:
        if level > 1:
            print(' ' * (8 * (level - 1) - 1), end = '')
        for e in s:
            if e == '\\nonl':
                break;
            print(e, end = '')
        else:
            print()


# make a formula from a collection of lists

def clause(s):
    if isinstance(s, list):
        return frozenset([frozenset(s)])
    elif '=' in s:
        h = s.split('=')
        return clause(h[0] + '->' + h[1]) | clause(h[1] + '->' + h[0])
    else:
        all = frozenset()
        body = set()
        sign = '-'
        for c in s:
            if c == '>':
                sign = ''
            elif c == '-':
                pass
            elif sign == '-':
                body |= {sign + c}
            else:
                all |= {frozenset(body | {sign + c})}
        return all

def formula(*l):
    return set().union(*{clause(x) for x in l})


# from clause to string

def clausetostring(clause, pretty = True):
    if pretty:
        return ''.join({l[1:] for l in clause if l[0] == '-'}) + '->' + \
               ''.join({l for l in clause if l[0] != '-'})
    else:
        return '(' + ' '.join(clause) + ')'


# from formula to string

def formulatostring(formula, label = None, pretty = True):
    s = label + ' ' if label else ''
    s += ' '.join(clausetostring(c, pretty) for c in formula)
    return s


# print a formula

def formulaprint(formula, label = None, pretty = True):
    print(formulatostring(formula, label, pretty))


# size of a formula, as total occurrencies of variables

def formulasize(a):
    return sum([len(x) for x in a])


# check whether a clause is a tautology

def tautology(c):
    for l in c:
        if '-' + l in c:
            return True
    return False


# remove tautologies from a formula

def detautologize(s):
    return {c for c in s if not tautology(c)}


# resolve two clauses; emptyset if they don't resolve or resolve to a tautology

def resolve(a, b):
    for x in a:
        for y in b:
            if x == '-' + y or '-' + x == y:
                r = a.difference([x]).union(b.difference([y]))
                return set() if tautology(r) else set({r})
    return set()


# minimal (not containing others) clauses of a formula

def minimal(s, e = set()):
   r = set()
   for c in s:
       for d in s | e:
           if d < c:
               break
       else:
           r |= {c}
   return r


# resolution closure, minimized

def close(s):
    r = set()
    n = s.copy()
    while n != r:
        r = n.copy()
        for a in r:
           for b in r:
               n |= resolve(a, b)
        n = minimal(n)
    return n


# check equivalence

def equivalent(s, r):
    return minimal(close(detautologize(s))) == minimal(close(detautologize(r)))


# check whether a formula is single-head

def issinglehead(e):
    h = [h for c in e for h in c if h[0] != '-']
    return len(h) == len(set(h))


# head and body

def head(c):
    return next((l for l in c if l[0] != '-'))

def heads(f):
    return {head(c) for c in f}

def body(c):
    return {l[1:] for l in c if l[0] == '-'}

def bodies(f):
    return {frozenset(body(c)) for c in f}


# rcn and ucl

def rcnucl(b, f):
    heads = set()
    usable = set()
    prev = None
    while heads != prev:
        prev = heads.copy()
        for c in f:
            if body(c) <= b | heads:
                 usable |= {c}
                 heads |= {head(c)}
    return heads,minimal(usable)


# single-head selection by body minimality

def shmin(f):
    s = set()
    d = set()

    for c in f:
        h = head(c)
        b = body(c)

        # only one clause for each head

        print(clausetostring(c), end = ' | ')
        if h in d:
            print('[head already in shmin]')
            continue
        d |= {h}

        # minimize according to <F

        a = None
        r,u = rcnucl(b, f)
        while a != b and b - r:
            a = b
            for e in b - r:
                nb = (b | r) - {e,h}
                nr,nu = rcnucl(nb, u)
                if h in nr:
                    print(''.join(nb), end = ' ')
                    b = nb
                    r = nr
                    u = nu
                    break
        print(end = '| ')

        # minimize according to set containment

        a = None
        while a != b and b & r:
            a = b
            for e in b & r:
                nb = b - {e}
                nr,nu = rcnucl(nb, u)
                if h in nr:
                    print(''.join(nb), end = ' ')
                    b = nb
                    r = nr
                    u = nu
                    break
        print(end = '| ')

        n = frozenset([h]) | frozenset(['-' + l for l in b])
        print(clausetostring(n))
        s |= {n}
    return s


# analyze a formula

Check='Check'
def analyze(d, result, *s):
    print('##', d, '##')
    print('formula:', ' '.join(s))
    f = formula(*s)

    if result == Check:
        printinfo(1, formulatostring(f, 'clausal:'))
        f = detautologize(f)
        f = minimal(f)
        printinfo(1, formulatostring(f, 'simplified:'))
        printinfo(1, 'single head:', issinglehead(f))
        print()
        return

    shm = shmin(f)
    printinfo(1, formulatostring(shm, 'shmin:'))
    res = equivalent(shm, f)
    print('shmin equivalent:', res)
    print('expected result:', result)
    if (result == None):
        pass
    elif (res == False and result == True):
        print('TEST INCONCLUSIVE')
    elif (res != result):
        print('TEST FAILED')
    else:
        print('TEST PASSED')
    print()


# do not analyze a formula

def donotanalyze(d, result, *s):
    pass


# commandline arguments

if len(sys.argv) <= 1 or sys.argv[1] == '-h':
    if len(sys.argv) <= 1:
        print('no argument')
    print('usage:')
    print('\tsinglehead.py [-t] testfile.py')
    print('\tsinglehead.py -f clause clause...' )
    print('\t\tclause: ab->c, ab=c, abc (= a or b or c)')
elif sys.argv[1] == '-f':
    analyze('cmdline formula', None, *sys.argv[2:])
elif sys.argv[1] == '-t':
    exec(open(sys.argv[2]).read())
else:
    exec(open(sys.argv[1]).read())

