# Effective modulus Q' = Q / gcd(U, Q) of each window of the rounded log 2, weighted by window length.
import math, json
from valuations import smooth_upto

def windows(S, X):
    sm = smooth_upto(S, X)
    pp = sorted(set(p**a for p in S for a in range(1, 80) if p**a <= X))
    bps = sorted(set(sm) | set(pp))
    R, Q = 0, 1
    out = []
    j = 0
    for i, k1 in enumerate(bps):
        k2 = bps[i+1] if i + 1 < len(bps) else X + 1
        Qn = 1
        for p in S:
            a = 0
            while p**(a+1) <= k1: a += 1
            Qn *= p**a
        R = R * (Qn // Q) % Qn; Q = Qn
        while j + 1 < len(sm) and sm[j+1] <= k1: j += 1
        sigma = sm[j]
        R = (2*R + Q//sigma) % Q
        U = (R + Q//sigma) % Q
        g = math.gcd(U, Q)
        out.append((k1, k2 - k1, Q, Q // g))
        U = U * pow(2, k2 - k1 - 1, Q) % Q
        R = (U - Q//sigma) % Q
    return out

if __name__ == "__main__":
    res = {}
    for S, X in [((3,), 10**15), ((3, 5), 10**15), ((5, 7), 10**15), ((3, 5, 7), 10**12), ((3, 7, 11), 10**12), ((5, 7, 11), 10**12)]:
        w = windows(S, X)
        tot = sum(L for _, L, _, _ in w)
        # length-weighted fraction of positions in windows with effective modulus Q' < Q^eta
        stats = {}
        for eta in (0.25, 0.5, 0.75, 1.0):
            bad = sum(L for _, L, Q, Qe in w if Q > 1 and math.log(Qe) < eta * math.log(Q) - 1e-9)
            stats[eta] = bad / tot
        trivial = [(k1, L, Q) for k1, L, Q, Qe in w if Qe == 1 and Q > 1]
        late = [(k1, L, Q, Qe) for k1, L, Q, Qe in w if k1 > X // 100]
        res[str(S)] = dict(windows=len(w), frac_below=stats, n_trivial=len(trivial),
                           trivial=trivial[:10], late=late[-8:])
        print(S, len(w), {k: round(v, 4) for k, v in stats.items()}, "trivial:", len(trivial), trivial[:5], flush=True)
        print("   late windows (k1, L, Q, Q'):", late[-5:], flush=True)
    json.dump(res, open("eff_modulus.json", "w"), indent=1, default=str)
