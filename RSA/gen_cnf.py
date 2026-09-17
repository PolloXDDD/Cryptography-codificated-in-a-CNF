import sys
N = int(open('N.txt').read().strip())
NB = 1024  # bits por factor (RSA-2048 balanceado)
nbits = N.bit_length()
assert nbits <= 2*NB
out = open('rsa2048_factor.cnf.tmp','w', buffering=1<<24)
nv = 0
def new():
    global nv; nv += 1; return nv
def cl(*lits): out.write(' '.join(map(str,lits))+' 0\n')
p = [new() for _ in range(NB)]
q = [new() for _ in range(NB)]
ncl = 0
def AND(a,b):
    global ncl
    z=new(); cl(-a,-b,z); cl(a,-z); cl(b,-z); ncl+=3; return z
def HA(a,b):
    global ncl
    s=new(); c=new()
    cl(-a,-b,-s); cl(a,b,-s); cl(a,-b,s); cl(-a,b,s)
    cl(-a,-b,c); cl(a,-c); cl(b,-c); ncl+=7; return s,c
def FA(a,b,c):
    global ncl
    s=new(); co=new()
    for x in (a,-a):
        for y in (b,-b):
            for z in (c,-c):
                par = (x>0)+(y>0)+(z>0)
                # si x,y,z verdaderos con paridad par -> s = paridad
                cl(-x,-y,-z, s if par%2==1 else -s)
    cl(-a,-b,co); cl(-a,-c,co); cl(-b,-c,co)
    cl(a,b,-co); cl(a,c,-co); cl(b,c,-co)
    ncl+=14; return s,co
# restricciones triviales: factores impares y de 1024 bits exactos
cl(p[0]); cl(q[0]); cl(p[NB-1]); cl(q[NB-1]); ncl+=4
cols = [[] for _ in range(2*NB+2)]
for j in range(2*NB-1):
    # productos parciales de la columna j
    for a in range(max(0,j-NB+1), min(j,NB-1)+1):
        cols[j].append(AND(p[a], q[j-a]))
    col = cols[j]
    while len(col) > 1:
        if len(col) >= 3:
            s,c = FA(col.pop(),col.pop(),col.pop())
        else:
            s,c = HA(col.pop(),col.pop())
        col.append(s); cols[j+1].append(c)
    bit = (N>>j)&1
    cl(col[0] if bit else -col[0]); ncl+=1
for j in range(2*NB-1, 2*NB+2):
    for v in cols[j]:
        bit = (N>>j)&1
        cl(v if bit else -v); ncl+=1
out.close()
with open('rsa2048_factor.cnf','w') as f:
    f.write('c Factorizacion de N (RSA-2048) como SAT: p*q=N, p,q impares de 1024 bits\n')
    f.write('c vars 1..1024 = bits de p (LSB primero), 1025..2048 = bits de q\n')
    f.write(f'p cnf {nv} {ncl}\n')
    with open('rsa2048_factor.cnf.tmp') as t:
        for chunk in iter(lambda: t.read(1<<24), ''): f.write(chunk)
import os; os.remove('rsa2048_factor.cnf.tmp')
print('vars',nv,'clauses',ncl)
