# EDQ: linear cutoff from signed Fourier modes

- **Stage:** 3-formalized
- **Date:** 2026-09-06
- **Lean modules:** `RHTower/ArithmeticLogarithmicFourierTail.lean`, `RHTower/ArithmeticRemainderLinearCutoff.lean`
- **Target:** literal normalized arithmetic remainder; no assumed zero equation
- **RH chain:** Euler deletion → retained remainder → uniform tail orientation and exceptional-head comparison → exclusion of off-line zeros → RH
- **RH status:** unproved; this target confines the exceptional head but does not orient the unit value at high zeros.

## Proved theorem LNC

For `0<Re(s)<=1`, `t=Im(s)>=1`, and integer `N>=1` with `t<=N`, Lean proves

`Im(normalizedWeightedRemainder(s,N))<0`.

This strengthens the existing superlinear bound `t^3<=N^2`. It is weaker than the frozen R conjecture `t<2*pi*N`; R is not changed or claimed. No numerical input is used.

## Source ancestry and dependency-closed paper argument

The actual Bernoulli kernel has the absolutely convergent expansion

`b(x)=-1/12 + sum_(k in Z, k!=0) exp(2*pi*i*k*x)/(4*pi^2*k^2)`.

The corpus already proves this Fourier identity (`BernoulliFourierBridge`) and both signs of the weighted first-derivative test (`VanDerCorputWeighted`, `VanDerCorputWeightedAnti`). These are the starting source facts.

At positive integer N, let `u=conjugate(s)` and multiply the Bernoulli tail by `N^(u+1)`. The mean is exactly `-1/[12(u+1)]`. Each nonzero Fourier mode is an integral with real decreasing amplitude `x^(-Re(s)-2)` and phase `2*pi*k*x+t*log x`. When `|t|<=N` and x>=N, the derivative has absolute value at least five, since `2*pi>6`. Its sign and monotonicity are fixed. The existing weighted first-derivative tests therefore bound each mode by `4*N^(-Re(s)-2)/5`, uniformly in its integer frequency and upper endpoint. Conjugation handles negative frequencies. Absolute integrability passes the bound to the half-line.

The Fourier coefficients are nonnegative real numbers and have total mass exactly `1/12` (evaluate the existing series at zero). Thus the complete centered tail has the uniform norm bound

`|N^(u+1)*tail(N,u) + 1/[12(u+1)]| <= 1/(15*N)`.

Every exchange of infinite sum, integral, conjugation, and normalization is justified in Lean. This is an estimate for the literal source, with its power weight retained.

For t>=5 and `0<Re(s)<=1`, the mean's negative imaginary margin is

`t/[12*((Re(s)+1)^2+t^2)] > 1/(15*t) >= 1/(15*N)`.

For `1<=t<=5`, reuse the already proved quartic disk bound. Its numerator is at most

`(t^2+25/2)*(t^2+4)=t^4+(33/2)*t^2+50 <= (143/2)*t^3 < 96*t^3`.

The denominator condition is at least `96*t*N^2 >= 96*t^3`. Hence the quartic phase theorem covers this remaining compact height range. Combining the two analytic bounds proves LNC.

## Formal audit

- [x] Check both signed logarithmic Fourier modes with actual power amplitude.
- [x] Prove Fourier coefficient mass and justified whole-tail sum/integral transfer.
- [x] Prove the scaled source disk and the two height comparisons.
- [x] Scratch-check, targeted leaf audits, and umbrella wiring. Only the 27 new declarations were axiom-audited; all use `propext`, `Classical.choice`, and `Quot.sound`. Lint status is recorded below.

The independent exceptional-head comparison and unconditional RH remain open. Continue that work on the [active source-comparison card](../1-in-progress/edq-logarithmic-cotangent-orientation.md).

This is a classical weighted Fourier/nonstationary-phase proof, not a novelty claim or a new independent route label. No sign is assigned to individual Bernoulli cells. The finite cotangent identity remains exact, but the present proof controls its arithmetic source by retaining the power weights in each signed-frequency estimate.


## Exact Lean results

All declarations below use namespace `RHTower.DeletionMixedRefinement`.

| Declaration | Proved scope |
| --- | --- |
| `hasSum_bernoulliModeWeight` | Exact positive Fourier coefficient mass `1/12` |
| `norm_integral_Ioi_logarithmicFourierMode_le_abs` | Both signed complete logarithmic Fourier tails with actual power amplitude |
| `hasSum_integral_bernoulliFourierTerm` | Justified infinite source sum–integral interchange |
| `norm_centeredBernoulliTail_le_linear` | Centered-tail bound for `Re(s)>-1`, every real anchor `a>0`, `abs(Im(s))<=a` |
| `norm_normalizedWeightedRemainder_scaled_sub_mean_le_linear` | Actual normalized remainder disk `1/(15N)`, `Re(s)>0`, `s!=1`, `abs(Im(s))<=N` |
| `normalizedWeightedRemainder_im_neg_of_linear_bound` | Strict phase if additionally `4*normSq(s+1)<5*Im(s)*N` |
| `normalizedWeightedRemainder_im_neg_of_height_le_cutoff` | Frozen LNC: `0<Re(s)<=1`, `1<=Im(s)<=N` |

Both new modules passed `lake env lean` scratch checks and targeted final `lake build --old` audits. The final cutoff build refreshed its directly required `ArithmeticRemainderPhaseCutoff` prerequisite. No full or umbrella build ran, and no old declaration received an axiom audit. The new code has 24 theorems and 3 definitions. No computed data or numerical certificate appears in the proof.

`python3 scripts/formal_tools.py lint` passed with existing large-file warnings. The corpus index was refreshed once. Owned scratch sources were removed after validation; audit logs remain under `/tmp/edq_linear_*`.
