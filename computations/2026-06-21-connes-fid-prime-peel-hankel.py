import mpmath as mp
mp.mp.dps = 50
# Free-cumulant Hankel H_m = [ b_{i+j} ], i,j=0..m-1, with b_n a moment-like sequence at s=2n+3 (>=3, avoids zeta(1)).
def seq_raw(n):     s=2*n+3; return mp.zeta(s)
def seq_peel(peeled, scaleprime):
    def f(n):
        s=2*n+3
        v=mp.zeta(s)-mp.mpf(1)              # remove rank-one all-ones bulk (the m=1 term)
        for p in peeled: v-=mp.power(p,-s)  # peel earlier primes
        return v*mp.power(scaleprime, s)    # rescale by next prime
    return f
bases={
 "raw zeta(2n+3)":            seq_raw,
 "peel{} scale2":             seq_peel([], 2),
 "peel{2} scale3":            seq_peel([2], 3),
 "peel{2,3} scale5":          seq_peel([2,3], 5),
 "peel{2,3,5} scale7":        seq_peel([2,3,5], 7),
 "peel{2,3,5,7} scale11":     seq_peel([2,3,5,7], 11),
}
MAXSIZE=18
def first_neg_minor(f):
    b=[f(n) for n in range(0, 2*MAXSIZE)]
    last_det=None; cond=None
    for m in range(1, MAXSIZE+1):
        H=mp.matrix(m,m)
        for i in range(m):
            for j in range(m): H[i,j]=b[i+j]
        d=mp.det(H)
        if d<=0: return m, d
        last_det=d
    return None, last_det   # stayed PSD through MAXSIZE
print(f"Free-cumulant Hankel positivity (Sylvester leading minors), dps={mp.mp.dps}, to size {MAXSIZE}:")
print(f"  {'basis':<24} {'first non-PSD size':<20} {'last leading-det':<16}")
for name,f in bases.items():
    sz,d=first_neg_minor(f)
    tag = f"size {sz}" if sz else f"PSD through {MAXSIZE}"
    print(f"  {name:<24} {tag:<20} {mp.nstr(d,4)}")
print()
print("reading: if raw stays PSD at high dps to large size, R41's 'sign loss at size 8' was NUMERICAL")
print("(double precision), not a real positivity failure; prime-peeled bases recondition the same cone.")
