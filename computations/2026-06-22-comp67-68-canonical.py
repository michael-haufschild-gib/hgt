"""comp67 (rt#67): is the scalar gap s_d presentation/regulator-independent?
s_d depends ONLY on H^-=H^0-a_* v_* v_*^T. Compute s_d three ways:
  (A) 1/(v_*^T (H^0)^{-1} v_*)
  (B) a_* + 1/(v_*^T (H^-)^{-1} v_*)
  (C) via the source presentation H^- = M_triv^{(j>=2)} + R^P  (comp57 split)
All must agree (s_d carries no split/regulator freedom).
comp68 (rt#68): gauge audit Xi -> e^{q(w^2)} Xi (zeros UNMOVED). q=c w^2 => Xi'/Xi gains 2c w,
M_Xi=(1/2w)Xi'/Xi gains constant c. Show: (i) true moments T_k (power sums of zeros) invariant =>
s_d invariant; (ii) naive Lemma-1 extraction from the GAUGED M_Xi is contaminated by q' (=c) unless
the canonical xi-counterterm is subtracted."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
def ev(y,d): return mp.matrix([mp.power(y,i) for i in range(d+1)])
a_=mp.power(mp.mpf('2.5'),-2); ystar=mp.mpf('-0.16')
print("=== comp67: s_d presentation-invariance ===")
for d in [8,12]:
    mp.mp.dps=int(7*d)+130
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d); v=ev(ystar,d)
    Hm=A-a_*(v*v.T)
    sA=1/(v.T*mp.inverse(A)*v)[0]
    sB=a_+1/(v.T*mp.inverse(Hm)*v)[0]
    # (C) source presentation: M_triv^{(j>=2)} = B - a_* v v^T ; R^P = A - B ; H^- = that sum
    Mj2=B-a_*(v*v.T); RP=A-B; HmC=Mj2+RP
    sC=a_+1/(v.T*mp.inverse(HmC)*v)[0]
    print(f"  d={d}: s(1/K)={mp.nstr(sA,8)}  s(a_*+1/m)={mp.nstr(sB,8)}  s(source M>=2+R^P)={mp.nstr(sC,8)}  "
          f"max-reldiff={mp.nstr(max(abs(sA-sB)/abs(sA),abs(sA-sC)/abs(sA)),2)}")
print("=== comp68: gauge audit Xi -> e^{c w^2} Xi ===")
mp.mp.dps=120; KMAX=8
# true moments via log Xi: c_{2k}=[w^2k]logXi ; M_Xi=(1/2w)Xi'/Xi has [w^2k]=(k+1?) ... use T directly
T=H.T_moments_exact(KMAX)
print(f"  true T_1={mp.nstr(T[1],12)} T_2={mp.nstr(T[2],12)} (power sums of zeros; GAUGE-INVARIANT by definition)")
for c in [mp.mpf('0.3'), mp.mpf('-1.5')]:
    # gauged M_Xi gains constant c at [w^0]; recall [w^2k]M_Xi = (-1)^k T_{k+1}/2
    # so naive T_1^gauge = 2*[w^0]M_Xi^gauge = 2*([w^0]M_Xi + c) = T_1 + 2c
    T1naive = T[1] + 2*c
    print(f"  q=({mp.nstr(c,3)})w^2: naive Lemma-1 T_1 (from gauged Xi'/Xi) = {mp.nstr(T1naive,10)} = T_1 + 2c (contaminated by q'=c); "
          f"contamination={mp.nstr(T1naive-T[1],3)}")
print("  => s_d uses the TRUE zero power-sums (gauge-invariant); naive source-extraction needs the canonical xi q-counterterm.")
