import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
L=imp("hgtlib_L","hgtlib_L.py")
mp.mp.dps=60
name=sys.argv[1] if len(sys.argv)>1 else 'chi4'
q,a,chi=L.CHARS[name]
# find zeros of xi_chi(1/2+it) by sign change of real part, t in (0,TMAX)
def Z(t): return mp.re(L.xi_chi(name, mp.mpf('0.5')+1j*mp.mpf(t)))
gs=[]; tprev=mp.mpf('0.2'); vprev=Z(tprev); t=tprev
while t<60 and len(gs)<25:
    t+=mp.mpf('0.1'); v=Z(t)
    if vprev==0 or v*vprev<0:
        g=mp.findroot(Z,(t-0.1+t)/2); 
        if not gs or abs(g-gs[-1])>1e-3: gs.append(g)
    vprev=v
gs=[g for g in gs if g>0.05]
T=L.T_moments_L(name, 6)
print(f"{name}: q={q} parity a={a}; found {len(gs)} zeros, gamma_1={mp.nstr(gs[0],10)}")
for k in [1,2,3]:
    Te=T[k]; Ttr=2*mp.fsum((1/(g*g))**k for g in gs)
    print(f"  k={k}: T_k(exact)={mp.nstr(Te,15)}  T_k({len(gs)}zeros)={mp.nstr(Ttr,15)}  reldiff={mp.nstr(abs(Te-Ttr)/abs(Te),3)}")
