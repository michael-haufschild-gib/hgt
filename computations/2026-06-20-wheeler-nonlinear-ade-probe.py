# Nonlinear ADE probe (Wheeler 2nd pipeline). Tests P(x,f,...,f^(w))=0 of jet-degree<=d (the Hölder test).
# Low order WORKS: separates tan (DA-nonlinear, caught at d=2) from logΓ/ψ (HT, resist). CONFOUND: at (2,2)+
# monomial-correlation ill-conditioning gives false-0 for HT (contradicts Hölder) — fixable by orthogonalization.
import mpmath as mp
from itertools import product
mp.mp.dps=40
xs=[mp.mpf(3)/10+mp.mpf(i)*mp.mpf(4)/(10*49) for i in range(50)]
def jets_poly(fn,w): return [[mp.diff(fn,x,j) for j in range(w+1)] for x in xs]
def jets_lg(w): return [[mp.loggamma(x)]+[mp.polygamma(j-1,x) for j in range(1,w+1)] for x in xs]
def jets_psi(w): return [[mp.polygamma(j,x) for j in range(w+1)] for x in xs]
def exps(w,d): return [t for t in product(range(d+1),repeat=w+1) if sum(t)<=d]
def smin_smax(jets,w,d,px=1):
    E=exps(w,d); rows=[]
    for x_i,J in zip(xs,jets):
        row=[]
        for p in range(px+1):
            for e in E:
                v=x_i**p
                for j in range(w+1): v*=J[j]**e[j]
                row.append(v)
        rows.append(row)
    nc=len(rows[0]); M=mp.matrix(len(xs),nc)
    for r in range(len(xs)):
        for c in range(nc): M[r,c]=rows[r][c]
    for c in range(nc):
        nrm=mp.sqrt(sum(M[r,c]**2 for r in range(M.rows)))
        if nrm!=0:
            for r in range(M.rows): M[r,c]=M[r,c]/nrm
    ev=mp.eigsy(M.T*M,eigvals_only=True); evl=[ev[i] for i in range(nc)]
    return mp.sqrt(max(mp.mpf(0),min(evl))/max(evl))
funcs={"e^x":jets_poly(lambda x:mp.e**x,2),"tan":jets_poly(lambda x:mp.tan(x),2),
       "logGam":jets_lg(2),"psi":jets_psi(2)}
for name,J in funcs.items():
    print(name,[f"{float(smin_smax(J,w,d)):.1e}" for w,d in [(1,1),(1,2),(2,1),(2,2)]])
