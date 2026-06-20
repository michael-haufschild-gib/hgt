"""
STEP 8 (HT continuum germ) + STEP 9 method=12 "find an invariant".
Question: as the EXPANSION POINT x0 moves (the 'motion'), what is INVARIANT about the HT
signature of a germ?  Candidates: (a) binary saturates/floors; (b) saturation-residual
magnitude; (c) the order-saturation RATE resid(r+1)/resid(r).
Probe: precision-saturation residual (mpmath-native, dps 30 vs 55) of Taylor germs at several x0.
DA control = 1/(2-x) (rational, holonomic) translated; HT = log Gamma translated.
"""
import mpmath as mp

def resid_mp(seq, r=2, d=1):
    N=len(seq); rows=[]
    for k in range(1,N-r):
        row=[((mp.mpf(k)**e)*seq[k+i]) for i in range(r+1) for e in range(d+1)]
        rows.append(row)
    A=mp.matrix(rows)
    for j in range(A.cols):
        nrm=mp.sqrt(sum(A[i,j]**2 for i in range(A.rows)))
        if nrm!=0:
            for i in range(A.rows): A[i,j]=A[i,j]/nrm
    ev=mp.eigsy(A.T*A, eigvals_only=True); return mp.sqrt(abs(ev[0]))

def germ(f, x0, K=18):
    return mp.taylor(f, x0, K+2)[2:K+1]   # drop c0,c1; keep c2..cK

def scan(f, x0):
    out={}
    for dps in (30,55):
        mp.mp.dps=dps
        out[dps]=resid_mp(germ(f,x0))
    sat = out[30]/out[55]   # ~1 => saturates(HT); >>1 => drops(DA)
    return out[30], out[55], sat

print("="*80)
print(" STEP8+9(method12): invariant of HT germ under EXPANSION-POINT translation")
print("="*80)
print(f"\n {'function / x0':28s} resid(dps30)  resid(dps55)  ratio   class")
for name,f in [("DA 1/(2-x)", lambda x: 1/(2-x)), ("HT logGamma", mp.loggamma)]:
    for x0 in [mp.mpf('0.3'), mp.mpf('0.8'), mp.mpf('1.6'), mp.mpf('2.7')]:
        try:
            a,b,sat = scan(f,x0)
            cls = "HT(saturates)" if sat<10 else "DA(drops)"
            print(f" {name+' @'+mp.nstr(x0,2):28s} {mp.nstr(a,4):12s} {mp.nstr(b,4):12s} {mp.nstr(sat,3):6s} {cls}")
        except Exception as e:
            print(f" {name+' @'+mp.nstr(x0,2):28s} error {e}")
print("\n method-12 read: INVARIANT under x0 = the binary saturates/floors class? Does the")
print(" magnitude vary with x0 (singularity proximity) while the HT/DA class stays fixed?")
