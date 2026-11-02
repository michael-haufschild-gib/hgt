# Compact-profile tail uncertainty at growing overlap

- **ID:** compact-profile-tail-uncertainty-at-growing-overlap
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Σ1d; quantitative continuation of the positive conductor floor.
- **Statement:** Every nonzero real compact `C²` profile on `[0,1]` admits `a,b>0` with `∫_(t>c)|φ̂(2πt)|²dt ≥ a exp(-bc)` for every `c≥1`.

The qualitative positive-tail theorem is formalized. It supplies no decay
rate. A quantitative uncertainty bound would control the conductor floor
while overlap grows. Candidate sources are the compact Fourier entire
extension and finite-band concentration leakage; the corpus has prolate
leakage and barrier estimates, whose hypotheses and applicability remain
to be checked.

## Extrapolation route

`HTGeometry.PolynomialExtrapolationRemez.abs_eval_le_extrapolate` controls
extrapolation from `[-2c,-c]` to zero by `(4 exp(1))^d` for degree `d`.
The prolate barrier estimates instead require an eigenfunction and specified
spectral parameters; they do not by themselves bound arbitrary profiles.

Choose a nonzero real or imaginary Fourier component at one fixed frequency.
Approximate its translate on an interval of length `2c` by its degree-`d`
Taylor polynomial, with `d=⌈Dc⌉`. Compact support bounds every frequency
derivative by `∫|φ|`; the factorial remainder can beat the extrapolation
factor when `D` is large. This would force an exponentially large-in-`-c`
Fourier value somewhere in the tail interval. The first frequency-derivative
bound would spread that value over an interval and give the required `L²`
tail lower bound. The uniform Taylor estimate and its quantitative assembly
remain to be verified.

Available inputs include the global complex exponential factorial remainder
`RHTower.norm_complex_exp_sub_sum_le_factorial_tail` and the compact-support
Fourier derivative formula `RHTower.iteratedDeriv_fourier_compactSupport`.
The latter makes the derivative bound an explicit moment estimate.

The weighted high-conductor proof has bounded-overlap cost
`O_φ(K⁴(1+log K))`. A cutoff with
`log Q ≳ K⁴(1+log K)` therefore controls the high block. If the proposed
tail lower bound holds, then `K≤(log log N)^β`, `β<1/4`, makes both this
cutoff and the inverse floor subpolynomial in `log N`. Existing quantitative
quasimode residuals may then control the low block. No growing-overlap
coercivity theorem or quantitative uncertainty bound is claimed.
