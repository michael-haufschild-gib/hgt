# EDQ exact-gcd heads: cost of separating the polynomial

Status: completed finite diagnostic; numerical guidance only. No result is a
Lean premise, and no asymptotic estimate or RH proof follows from this test.

The predeclared head/tail budget survives all eight cases. Separately charging
the polynomial and corrected head exceeds the same budget for the raw sources
at M=64 and M=128. Thus the earlier corrected-head theorem should not be used
as evidence that its two pieces have a cheap separate absolute-value budget.
These finite failures do not refute any subpower asymptotic estimate.

## Frozen question and actual sources

[Protocol](PROTOCOL.md) was written before execution. This diagnostic reuses
the full-source intervals from the
[complete gcd-group experiment](../edq-gcd-gram-variation-2026-09-07/REPORT.md),
retaining their infinite tails instead of recomputing or truncating them.

For M=64,128,256,512, use either a(d)=mu(d), X=M, or the exact taper
`a(d)=mu(d)*log(M/max(X,d))/log(4)`, X=M/4. Put

```
f_d(k) = a(d)*(k mod d)/d,        w(k) = 1/[k(k+1)],
C_r = sum_(gcd(d,e)=r) sum_(k>=1) f_d(k)*f_e(k)*w(k),
H_r = sum_(gcd(d,e)=r) sum_(1<=k<=X) f_d(k)*f_e(k)*w(k),
T_r = C_r-H_r,
K_r = sum_(gcd(d,e)=r) a(d)*a(e)/(d*e),
P_r = K_r*sum_(1<=k<=X) k/(k+1).
```

D is the actual full diagonal from the previous experiment. The fixed tests
were A: `sum |H_r| + sum |T_r| <= 4D`, and B:
`sum |P_r| + sum |H_r-P_r| + sum |T_r| <= 4D`.
No threshold or scale was changed after observing results. Every group's
head, harmonic coefficient, polynomial, corrected head, tail interval and
complete interval appears in [results.json](results.json).

## Results

| M | Source | A / D interval | A | B / D interval | B |
|---:|:---|:---|:---|:---|:---|
| 64 | raw | [2.330877, 2.355351] | Pass | [7.849413, 7.873887] | Fail |
| 64 | averaged | [1.089432, 1.124429] | Pass | [2.689256, 2.724253] | Pass |
| 128 | raw | [1.930228, 1.949774] | Pass | [4.920854, 4.940401] | Fail |
| 128 | averaged | [1.732207, 1.758516] | Pass | [3.595035, 3.621345] | Pass |
| 256 | raw | [1.698434, 1.714650] | Pass | [3.904535, 3.920751] | Pass |
| 256 | averaged | [1.913486, 1.934353] | Pass | [3.282046, 3.302913] | Pass |
| 512 | raw | [1.575490, 1.589326] | Pass | [3.688107, 3.701942] | Pass |
| 512 | averaged | [1.704080, 1.718590] | Pass | [2.638721, 2.653231] | Pass |

For raw M=64 the absolute head mass is 4.169010, whereas the separately
charged polynomial and corrected head have masses 6.260743 and 9.180997.
The later-tail mass is only in [0.592281,0.642274]. This locates a concrete
loss inside the head decomposition; it does not establish where cancellation
must occur at arbitrary cutoffs. The tapered cases do not fail either test.

## Method and validation

Finite divisor inversion computes the head groups from multiples-channel
squares. If `E_q^head=sum_(k<=X)(sum_(q|d)f_d(k))^2*w(k)` and
`J_q=sum_(q|d)a(d)/d`, then
`H_r=sum_l mu(l)*E_(rl)^head` and `K_r=sum_l mu(l)*J_(rl)^2`.
The residue matrix uses the actual coordinate k; no block offsets are lost.

Subtracting H_r from the archived interval for C_r gives the interval for
T_r. Absolute values use their exact interval extrema. The inherited total
analytic infinite-tail allowance is at most 0.05; the original report gives
its allocation and series-remainder bounds. Floating-point sensitivity is
separate: this run uses long double and a 1e-7 classification margin, not
certified interval arithmetic.

Independent controls passed:

- Direct gcd-masked Gram versus divisor inversion, every group at M=64:
  maximum discrepancy 2.17e-19.
- Full initial residue source versus `F(k)=k*sum_d a(d)/d-1`, for every
  k through X in all eight cases: maximum discrepancy 4.93e-17.
- Sum of head groups versus direct squared-source energy: 6.51e-19.
- Sum of harmonic groups versus the square of the harmonic sum: 3.13e-21.

RunPod execution used eight Python workers and one thread per native pool,
Python 3.8.10, NumPy 1.24.4, and a 63-bit long-double mantissa. Measured
experiment wall time was 0.03812 seconds under a 60-second limit. Numerical
analysis also ran on RunPod. Inputs and downloaded outputs were hash-checked.
Source, protocol, original full-source data, logs and analysis are archived
here; [SHA256SUMS](SHA256SUMS) records their hashes.

## Mathematical consequence and open estimate

This diagnostic supports retaining each head as a signed object when trying
a direct bound. It supplies no proof that the head/tail budget stays small.
For raw sources the complete signed head is already
`sum_(k<=M)(k*H(M)-1)^2/[k(k+1)]`; small samples cannot replace a uniform or
cofinal bound for that expression and its later tail.

The separate paper attempt through
[Bettin--Conrey formula (13)](https://msp.org/ant/2013/7-1/ant-v7-n1-p08-p.pdf)
cancels the universal constants in the normalized Gram, but the elementary
pairwise cotangent estimate still permits an O(N log N) budget on a balanced
dyadic square. The needed improvement concerns the signed arithmetic
aggregate. No estimate for that aggregate was proved in this work, and no
new Lean representation or conditional receiver was added. The EDQ cofinal
subpower ceiling remains open; the frontier map was not edited.
