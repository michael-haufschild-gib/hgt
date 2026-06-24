#!/usr/bin/env python3
"""
chip-firing/sandpiles x tensegrity, method=revisualise (seed 736294618170950574).
Sandpile group K(G) = coker(reduced Laplacian) = nonunit invariant factors of SNF.
Compute K(G) structure across graph families; hunt a clean invariant-factor LAW.
Wheel graph = instrument check (known: |K(W_n)| = Lucas-ish / spanning trees).

Goal per user bar: a NOVEL structural conjecture (a law), not a number.
"""
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form

def laplacian(n, edges):
    L=[[0]*n for _ in range(n)]
    for (a,b) in edges:
        L[a][a]+=1; L[b][b]+=1; L[a][b]-=1; L[b][a]-=1
    return L

def sandpile_invariants(n, edges):
    L=laplacian(n,edges)
    # reduced: delete last row/col
    R=Matrix([[L[i][j] for j in range(n-1)] for i in range(n-1)])
    S=smith_normal_form(R, domain=ZZ)
    diag=[abs(S[i,i]) for i in range(n-1)]
    inv=[d for d in diag if d!=1]      # nontrivial invariant factors
    order=1
    for d in diag: order*=d
    return inv, order

def cycle_edges(verts):
    m=len(verts); return [(verts[i],verts[(i+1)%m]) for i in range(m)]

def prism(n):
    V=2*n; E=cycle_edges(list(range(n)))+cycle_edges(list(range(n,2*n)))
    E+=[(i,i+n) for i in range(n)]; return V,E
def antiprism(n):
    V=2*n; E=cycle_edges(list(range(n)))+cycle_edges(list(range(n,2*n)))
    E+=[(i,i+n) for i in range(n)]+[(i,n+((i+1)%n)) for i in range(n)]; return V,E
def mobius_ladder(n):
    V=2*n; E=cycle_edges(list(range(2*n)))+[(i,i+n) for i in range(n)]; return V,E
def wheel(n):
    V=n+1; hub=n; E=cycle_edges(list(range(n)))+[(i,hub) for i in range(n)]; return V,E

fams={'wheel(CHK)':wheel,'prism':prism,'antiprism':antiprism,'mobius':mobius_ladder}
for name,f in fams.items():
    print(f'=== {name} ===')
    for n in range(3,11):
        V,E=f(n)
        inv,order=sandpile_invariants(V,E)
        print(f'  n={n:>2}: |K|={order:>8}  invariant-factors={inv}')
    print()
print('Look for: a clean formula for the invariant-factor structure as a function of n,')
print('especially the 2-rank / cyclic-vs-noncyclic pattern (parity of n etc.).')
