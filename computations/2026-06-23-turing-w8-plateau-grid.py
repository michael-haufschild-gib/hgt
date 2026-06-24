import mpmath as mp
# plateau(n,d) := precision-converged best-fit residual of an order-(n-1) algebraic ODE
# over C(s) (jets G,G',...,G^{(n-1)}), basis s^a * prod jets^exponents, total jet-deg<=D, a<=A.
# For Gamma (HT) we expect a POSITIVE plateau at every (n,d): does it shrink fast (soft) or stay (rigid)?
seed_pts=[(1.5+2.0*(((i*9301+49297)%233280)/233280.0),
          -3+6*(((i*4096+150889)%714025)/714025.0)) for i in range(130)]

def jets_gamma(s, n):
    G=mp.gamma(s); psi=mp.digamma(s)
    out=[G]
    if n>=2: out.append(G*psi)
    if n>=3:
        psi1=mp.polygamma(1,s); out.append(G*(psi**2+psi1))
    return out

def monomials(jvals, svals, A, D, npts):
    n=len(jvals[0])   # number of jets (G,G',...), NOT number of points
    cols=[]
    # exponent tuples on the n jets with total<=D
    def tuples(n,D):
        if n==1:
            for e in range(D+1): yield (e,)
        else:
            for e in range(D+1):
                for rest in tuples(n-1,D-e): yield (e,)+rest
    for a in range(A+1):
        for ex in tuples(n,D):
            col=[ (svals[k]**a)*mp.fprod([jvals[k][t]**ex[t] for t in range(n)]) for k in range(npts)]
            cols.append(col)
    return cols

def plateau(n,D,A,dps_list):
    res={}
    for dps in dps_list:
        mp.mp.dps=dps
        pts=[mp.mpc(re,im) for (re,im) in seed_pts]
        jv=[jets_gamma(s,n) for s in pts]
        cols=monomials(jv, pts, A, D, len(pts))
        ncol=len(cols)
        for c in range(ncol):
            nrm=mp.sqrt(sum(abs(cols[c][k])**2 for k in range(len(pts))))
            if nrm!=0: cols[c]=[x/nrm for x in cols[c]]
        Mf=mp.matrix([[cols[c][k] for c in range(ncol)] for k in range(90)])
        U,S,V=mp.svd(Mf)
        res[dps]=(ncol, S[ncol-1])
    return res

for (n,D,A) in [(1,3,2),(1,5,2),(2,3,2)]:
    r=plateau(n,D,A,[30,45])
    n30=r[30][0]; s30=r[30][1]; s45=r[45][1]
    frozen = abs(mp.mpf(s45)/mp.mpf(s30) - 1) < mp.mpf(10)**(-3) if s30!=0 else False
    print(f"n={n} D={D} ncol={n30}: sigma_min dps30={mp.nstr(s30,4)}  dps45={mp.nstr(s45,4)}  FROZEN(real plateau)={frozen}")
print("rigid HT: plateau stays the same order across (n,D); soft: drops fast as basis grows.")
