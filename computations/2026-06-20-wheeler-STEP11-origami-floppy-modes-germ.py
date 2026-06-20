"""
STEP 11 — WILD metaphor experiment (no predictable outcome).
Metaphor: origami mechanism rigidity. RIGID pattern = ONE fold mode (one exact relation +
a spectral GAP). FLOPPY / bifurcating pattern = MULTIPLE competing modes (clustered low modes).
Transfer to HT germ: the recurrence matrix's BOTTOM singular-value spectrum.
 - DA germ (rigid?): sigma_min ~ 0 (exact relation), big GAP to sigma_2.
 - HT germ (floppy/multi-mode?): are the lowest few singular values CLUSTERED (many near-
   recurrences of similar quality) or is sigma_min isolated with a gap?
Outcome unknown. mpmath-native, dps=40. Report bottom-3 singular values + gap ratios.
"""
import mpmath as mp
mp.mp.dps=40

def bottom_svs(seq, r=3, d=1, m=3):
    N=len(seq); rows=[]
    for k in range(1,N-r):
        rows.append([((mp.mpf(k)**e)*seq[k+i]) for i in range(r+1) for e in range(d+1)])
    A=mp.matrix(rows)
    for j in range(A.cols):
        nrm=mp.sqrt(sum(A[i,j]**2 for i in range(A.rows)))
        if nrm!=0:
            for i in range(A.rows): A[i,j]=A[i,j]/nrm
    ev=mp.eigsy(A.T*A, eigvals_only=True)   # ascending
    svs=[mp.sqrt(abs(ev[i])) for i in range(len(ev))]
    return svs[:m]

K=24
germs={
 "DA 1/(1-z) c_k=1":        [mp.mpf(1) for k in range(1,K)],
 "DA exp c_k=1/k!":         [mp.mpf(1)/mp.factorial(k) for k in range(1,K)],
 "DA Fib-like c_k=phi^k":   [ (mp.phi**k) for k in range(1,K)],
 "HT logGamma germ z(k)/k": [mp.zeta(k)/k for k in range(2,K+1)],
 "HT zeta(k)":              [mp.zeta(k) for k in range(2,K+1)],
 "HT Stieltjes gamma_n":    [mp.stieltjes(n) for n in range(K)],
}
print("="*82)
print(" STEP11 WILD: origami rigid(single-mode+gap) vs floppy(clustered modes) — HT germ spectrum")
print("="*82)
print(f"\n {'germ':26s}  sigma_1      sigma_2      sigma_3     gap s2/s1   gap s3/s2")
for n,seq in germs.items():
    s=bottom_svs(seq)
    g21 = s[1]/s[0] if s[0]>0 else mp.inf
    g32 = s[2]/s[1] if s[1]>0 else mp.inf
    print(f" {n:26s} {mp.nstr(s[0],3):12s} {mp.nstr(s[1],3):12s} {mp.nstr(s[2],3):12s} {mp.nstr(g21,4):10s} {mp.nstr(g32,4):8s}")
print("\n interpret: big gap s2/s1 = RIGID single-mode (DA-like); small/clustered low svs =")
print(" FLOPPY multi-mode. Does HT show a distinct mode-structure vs DA?")
