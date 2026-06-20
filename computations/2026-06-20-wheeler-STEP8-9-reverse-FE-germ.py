"""
STEP 8 (HT germ, local vs non-local) + STEP 9 method=3 "reverse it".
Forward: local recurrence on germ zeta(k), k>=2 -> HT (saturates).
Reverse (the FE inverts the index k -> 1-k): test the reflected sequence zeta(1-k) = values at
NEGATIVE integers (Bernoulli/rational side), and the even subsequence zeta(2k). Does the non-local
REVERSAL (functional equation) change the HT/DA classification of the LOCAL recurrence probe?
Validated mpmath-native precision-saturation (dps 25 vs 50). ratio~1 => HT(saturates), >>1 => DA(floors).
"""
import mpmath as mp
def resid(seq, r=2, d=1):
    N=len(seq); rows=[]
    for k in range(1,N-r):
        rows.append([((mp.mpf(k)**e)*seq[k+i]) for i in range(r+1) for e in range(d+1)])
    A=mp.matrix(rows)
    for j in range(A.cols):
        nrm=mp.sqrt(sum(A[i,j]**2 for i in range(A.rows)))
        if nrm!=0:
            for i in range(A.rows): A[i,j]=A[i,j]/nrm
    return mp.sqrt(abs(mp.eigsy(A.T*A, eigvals_only=True)[0]))

def scan(builder, K=20):
    out={}
    for dps in (25,50):
        mp.mp.dps=dps
        out[dps]=resid(builder(K))
    return out[25], out[50], (out[25]/out[50] if out[50]>0 else mp.inf)

seqs = {
 "FORWARD germ zeta(k), k>=2 (HT)":        lambda K: [mp.zeta(k) for k in range(2,K+1)],
 "REVERSED zeta(1-k)=neg-int (Bernoulli)": lambda K: [mp.zeta(1-k) for k in range(2,K+1)],
 "even subseq zeta(2k)":                   lambda K: [mp.zeta(2*k) for k in range(1,K+1)],
 "Bernoulli B_2k":                         lambda K: [mp.bernoulli(2*k) for k in range(1,K+1)],
 "control 1/k! (DA)":                      lambda K: [mp.mpf(1)/mp.factorial(k) for k in range(1,K+1)],
}
print("="*78)
print(" STEP8+9(method3 'reverse'): does the FE index-reversal change HT/DA of the local probe?")
print("="*78)
print(f"\n {'sequence':40s} resid(25)   resid(50)   ratio   class")
for name,b in seqs.items():
    try:
        a,c,rt = scan(b)
        cls = "HT(saturates)" if rt<10 else "DA(floors)"
        print(f" {name:40s} {mp.nstr(a,3):10s} {mp.nstr(c,3):10s} {mp.nstr(rt,3):6s} {cls}")
    except Exception as e:
        print(f" {name:40s} error {e}")
print("\n reverse-read: does reflecting k->1-k (the functional equation, a NON-LOCAL reversal)")
print(" move a sequence between HT and DA, or is HT-ness reversal-invariant?")
