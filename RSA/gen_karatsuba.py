#!/usr/bin/env python3
"""Codifica p*q = N (p,q impares de NB bits) en CNF usando Karatsuba recursivo.
Uso: python3 gen_karatsuba.py [NB] [LEAF] [salida.cnf]
Var 1 = TRUE (unidad). Vars 2..NB+1 = bits de p (LSB primero), NB+2..2NB+1 = bits de q.
Ahorro de variables:
  * productos parciales sin variable AND (se expanden dentro de las clausulas)
  * restas de Karatsuba por complemento bit a bit + offset constante (sin restadores)
  * simplificacion de constantes; bits de salida fijados a N sin variable de suma
"""
import sys
sys.setrecursionlimit(100000)
NB   = int(sys.argv[1]) if len(sys.argv) > 1 else 1024
LEAF = int(sys.argv[2]) if len(sys.argv) > 2 else 16
OUT  = sys.argv[3] if len(sys.argv) > 3 else 'rsa2048_karatsuba.cnf'
N = int(open('N.txt').read().strip())

tmp = open(OUT + '.tmp', 'w', buffering=1 << 24)
nv = 1; ncl = 0
T = 1; F = -1

def new():
    global nv; nv += 1; return nv

# literal: int, o ('a',x,y) = x AND y, o ('n',x,y) = NOT(x AND y)
def neg(l):
    if isinstance(l, tuple): return ('n' if l[0] == 'a' else 'a', l[1], l[2])
    return -l

def cl(*lits):
    global ncl
    base = set(); ands = []
    for l in lits:
        if isinstance(l, tuple):
            if l[0] == 'a': ands.append(l)
            else: base.add(-l[1]); base.add(-l[2])
        else:
            if l == T: return
            if l == F: continue
            base.add(l)
    clauses = [base]
    for (_, x, y) in ands:
        clauses = [c | {x} for c in clauses] + [c | {y} for c in clauses]
    for c in clauses:
        if T in c: continue
        c.discard(F)
        if any(-v in c for v in c): continue
        tmp.write(' '.join(map(str, c)) + ' 0\n'); ncl += 1

def AND(a, b):
    if a == F or b == F: return F
    if a == T: return b
    if b == T: return a
    if a == b: return a
    if a == neg(b): return F
    z = new(); cl(neg(a), neg(b), z); cl(a, -z); cl(b, -z); return z
def OR(a, b): return neg(AND(neg(a), neg(b)))
def XOR(a, b):
    if a == F: return b
    if b == F: return a
    if a == T: return neg(b)
    if b == T: return neg(a)
    if a == b: return F
    if a == neg(b): return T
    z = new(); na, nb = neg(a), neg(b)
    cl(na, nb, -z); cl(a, b, -z); cl(a, nb, z); cl(na, b, z); return z
def XOR_fixed(a, b, bit):
    if bit: cl(a, b); cl(neg(a), neg(b))
    else:   cl(a, neg(b)); cl(neg(a), b)
def FA(a, b, c):
    for x, y, z in ((a, b, c), (b, c, a), (c, a, b)):
        if z == F: return XOR(x, y), AND(x, y)
        if z == T: return neg(XOR(x, y)), OR(x, y)
    s = new(); co = new()
    na, nb, nc = neg(a), neg(b), neg(c)
    cl(na, nb, nc, s); cl(na, b, c, s); cl(a, nb, c, s); cl(a, b, nc, s)
    cl(a, b, c, -s); cl(a, nb, nc, -s); cl(na, b, nc, -s); cl(na, nb, c, -s)
    cl(na, nb, co); cl(na, nc, co); cl(nb, nc, co)
    cl(a, b, -co); cl(a, c, -co); cl(b, c, -co)
    return s, co
def FA_fixed(a, b, c, bit):
    for x, y, z in ((a, b, c), (b, c, a), (c, a, b)):
        if z == F: XOR_fixed(x, y, bit); return AND(x, y)
        if z == T: XOR_fixed(x, y, 1 - bit); return OR(x, y)
    co = new(); na, nb, nc = neg(a), neg(b), neg(c)
    if bit: cl(a, b, c); cl(a, nb, nc); cl(na, b, nc); cl(na, nb, c)
    else:   cl(na, nb, nc); cl(na, b, c); cl(a, nb, c); cl(a, b, nc)
    cl(na, nb, co); cl(na, nc, co); cl(nb, nc, co)
    cl(a, b, -co); cl(a, c, -co); cl(b, c, -co)
    return co

K_CNT = int(sys.argv[4]) if len(sys.argv) > 4 else 7
from itertools import product as iproduct
def COUNTER(lits, fixed_bit=None):
    """k entradas (vars puras) -> (s0,s1,s2) con s0+2s1+4s2 = suma. si fixed_bit se da, s0 se fija."""
    k = len(lits); assert 4 <= k <= 7
    s1 = new(); s2 = new()
    s0 = None if fixed_bit is not None else new()
    for bits in iproduct((0, 1), repeat=k):
        c = sum(bits)
        prem = [(-l if b else l) for l, b in zip(lits, bits)]  # "si entradas = bits"
        if fixed_bit is not None:
            if (c & 1) != fixed_bit: cl(*prem); continue
        else:
            cl(*prem, s0 if c & 1 else -s0)
        cl(*prem, s1 if c & 2 else -s1)
        cl(*prem, s2 if c & 4 else -s2)
    return s0, s1, s2

def compress(cols, target=None):
    """cols[j]: literales de peso 2^j. Si target es None devuelve vector binario
    equivalente a la suma; si no, fuerza suma == target (target >= 0)."""
    cols = [list(c) for c in cols] + [[]]
    out = []
    j = 0
    while j < len(cols):
        col = cols[j]
        col = [l for l in col if l != F]
        ones = sum(1 for l in col if l == T)
        col = [l for l in col if l != T]
        # constantes T: emparejarlas (2 unos = un acarreo)
        while ones >= 2:
            ones -= 2
            if j + 1 >= len(cols): cols.append([])
            cols[j + 1].append(T)
        if ones: col.append(T)
        # 1) literales AND (tuplas) se absorben con FA de 3
        plain = [l for l in col if not isinstance(l, tuple)]
        ands  = [l for l in col if isinstance(l, tuple)]
        while len(ands) >= 3:
            s_, c_ = FA(ands.pop(), ands.pop(), ands.pop()); plain.append(s_)
            if c_ != F:
                if j + 1 >= len(cols): cols.append([])
                cols[j + 1].append(c_)
        col = ands + plain
        # 2) contadores k:3 sobre variables puras
        def ready():
            return [l for l in col if not isinstance(l, tuple)]
        lim = 1 if target is None else 3
        while len(col) >= lim + K_CNT - 1 and len(ready()) >= K_CNT:
            r = ready()[:K_CNT]
            for l in r: col.remove(l)
            s0, s1, s2 = COUNTER(r)
            col.append(s0)
            if j + 1 >= len(cols): cols.append([])
            cols[j + 1].append(s1)
            if j + 2 >= len(cols): cols.append([])
            cols[j + 2].append(s2)
        if target is None:
            while len(col) > 1:
                if len(col) >= 3: s, c = FA(col.pop(), col.pop(), col.pop())
                else:             s, c = HA2(col.pop(), col.pop())
                col.append(s)
                if c != F:
                    if j + 1 >= len(cols): cols.append([])
                    cols[j + 1].append(c)
            out.append(col[0] if col else F)
        else:
            bit = (target >> j) & 1
            while len(col) > 3:
                s, c = FA(col.pop(), col.pop(), col.pop())
                col.append(s)
                if c != F:
                    if j + 1 >= len(cols): cols.append([])
                    cols[j + 1].append(c)
            if len(col) == 3:   c = FA_fixed(col[0], col[1], col[2], bit)
            elif len(col) == 2: XOR_fixed(col[0], col[1], bit); c = AND(col[0], col[1])
            elif len(col) == 1: cl(col[0] if bit else neg(col[0])); c = F
            else:
                assert bit == 0, "UNSAT trivial (bit constante distinto)"; c = F
            if c != F:
                if j + 1 >= len(cols): cols.append([])
                cols[j + 1].append(c)
        j += 1
    if target is not None:
        assert (target >> j) == 0, "UNSAT trivial (target demasiado grande)"
        return None
    while out and out[-1] == F: out.pop()
    return out

def HA2(a, b): return XOR(a, b), AND(a, b)

# numero = (vec, off): valor = sum vec[i]*2^i + off
def negate(num):
    vec, off = num
    return ([neg(l) for l in vec], -off - ((1 << len(vec)) - 1))
def shift(num, k):
    vec, off = num
    return ([F] * k + vec, off << k)
def add_nums(nums, target=None):
    W = max(len(v) for v, _ in nums) + len(nums).bit_length() + 2
    cols = [[] for _ in range(W)]
    off = 0
    for vec, o in nums:
        off += o
        for i, l in enumerate(vec): cols[i].append(l)
    if target is None:
        return (compress(cols), off)
    compress(cols, target - off)
    return None

def schoolbook(a, b):
    cols = [[] for _ in range(len(a) + len(b))]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            cols[i + j].append(AND_lit(x, y))
    return cols
def AND_lit(x, y):
    if x == F or y == F: return F
    if x == T: return y
    if y == T: return x
    if x == y: return x
    return ('a', x, y)

def mult(a, b, target=None):
    """a, b: vectores de literales. Devuelve numero (vec, 0) o fija a target."""
    n = max(len(a), len(b))
    if n <= LEAF or min(len(a), len(b)) <= 2:
        cols = schoolbook(a, b)
        if target is None: return (compress(cols), 0)
        compress(cols, target); return None
    h = n // 2
    a0, a1 = a[:h], a[h:]
    b0, b1 = b[:h], b[h:]
    z0 = mult(a0, b0)
    z2 = mult(a1, b1)
    sa, _ = add_nums([(a0, 0), (a1, 0)])
    sb, _ = add_nums([(b0, 0), (b1, 0)])
    z1 = mult(sa, sb)
    parts = [z0, shift(z2, 2 * h), shift(z1, h), shift(negate(z0), h), shift(negate(z2), h)]
    return add_nums(parts, target)

p = [new() for _ in range(NB)]
q = [new() for _ in range(NB)]
cl(T)
cl(p[0]); cl(q[0]); cl(p[-1]); cl(q[-1])
P = [T] + p[1:-1] + [T]
Q = [T] + q[1:-1] + [T]
mult(P, Q, target=N)
tmp.close()
with open(OUT, 'w') as f:
    f.write(f'c p*q = N con Karatsuba (NB={NB}, LEAF={LEAF}). var 1 = TRUE\n')
    f.write(f'c vars 2..{NB+1} = bits de p (LSB primero), {NB+2}..{2*NB+1} = bits de q\n')
    f.write(f'p cnf {nv} {ncl}\n')
    with open(OUT + '.tmp') as t:
        for chunk in iter(lambda: t.read(1 << 24), ''): f.write(chunk)
import os; os.remove(OUT + '.tmp')
print(f'NB={NB} LEAF={LEAF} vars={nv} clauses={ncl}')
