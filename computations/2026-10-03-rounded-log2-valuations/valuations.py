# Rounded log 2:  x_S = sum_k 1/(s(k) 2^k),  s(k) = largest S-smooth integer <= k.
# State 2^n x mod 1 = R_n / Q_n + tail, Q_n = lcm{s(k): k <= n} = prod p^{floor log_p n}.
# On a window where Q and sigma = s(k) are constant: R_{k+1} = 2 R_k + Q/sigma (mod Q),
# so U = R + Q/sigma satisfies U_{k} = 2^{k-k1} U_{k1}.  Record v_p(U mod Q) per window.
import sys, math, json
from itertools import product

def smooth_upto(S, X):
    out = [1]
    for p in S:
        new = []
        for m in out:
            v = m
            while v <= X:
                new.append(v); v *= p
        out = new
    return sorted(set(out))

def vp(n, p):
    if n == 0: return 10**9
    c = 0
    while n % p == 0: n //= p; c += 1
    return c

def run(S, X):
    sm = smooth_upto(S, X)            # breakpoints of s(k)
    pp = sorted(set(p**a for p in S for a in range(1, 64) if p**a <= X))
    bps = sorted(set(sm) | set(pp))   # s(k) and Q change only at these k
    R, Q = 0, 1
    rows = []
    for i, k1 in enumerate(bps):
        k2 = bps[i+1] if i + 1 < len(bps) else X + 1
        # new modulus and sigma at k1
        Qn = 1
        for p in S:
            a = int(math.floor(math.log(k1, p) + 1e-12))
            while p**(a+1) <= k1: a += 1
            while p**a > k1: a -= 1
            Qn *= p**a
        R = R * (Qn // Q) % Qn; Q = Qn
        sigma = max(m for m in sm if m <= k1)
        # include term k = k1, then run the window k1 < k < k2 in closed form
        R = (2*R + Q//sigma) % Q   # state after including k1 (R_{k1} := 2 R_{k1-1} + Q/s(k1))
        U = (R + Q//sigma) % Q
        L = k2 - k1 - 1
        rows.append((k1, k2 - k1, Q, [vp(U, p) if U else -1 for p in S],
                     [ (Q.bit_length()) ]))
        # advance to k2 - 1: U <- 2^L U
        U = U * pow(2, L, Q) % Q
        R = (U - Q//sigma) % Q
    return rows

if __name__ == "__main__":
    res = {}
    for S, X in [((3,), 10**12), ((3, 5), 10**12), ((3, 5, 7), 10**10), ((5, 7), 10**12), ((3, 7, 11), 10**10)]:
        rows = run(S, X)
        exps = [r[3] for r in rows]
        Qexp = [[vp(r[2], p) for p in S] for r in rows]
        maxrel = max(max((e/q if q else 0) for e, q in zip(ex, qe)) for ex, qe in zip(exps, Qexp))
        bad = [(r[0], r[1], ex, qe) for r, ex, qe in zip(rows, exps, Qexp) if any(e >= 2 for e in ex)]
        res[str(S)] = dict(windows=len(rows), max_val=max(max(e) for e in exps),
                           max_rel=maxrel, n_val_ge2=len(bad), first_bad=bad[:12])
        print(S, res[str(S)]["windows"], res[str(S)]["max_val"], round(maxrel, 3), len(bad), bad[:6], flush=True)
    json.dump(res, open("valuations.json", "w"), indent=1)
