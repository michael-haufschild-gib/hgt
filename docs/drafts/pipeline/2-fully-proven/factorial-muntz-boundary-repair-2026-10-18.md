# Canonical boundary repair of the actual factorial Müntz completion

- **Stage:** dependency-closed paper proof; Lean verification in progress.
- **Date:** 2026-10-18.
- **Route:** BiScaleUncertainty WL/RW.
- **Parent:** [actual factorial ramp diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Positive survivor:** exact negative-end coefficient, uniqueness of the exponential correction restoring polar integrability, and its exact nonzero zeta-zero readout.
- **Scope:** the literal existing factorial Müntz seed and completion. No substitute source, assumed Weil lower bound, external novelty claim, or numerical experiment.

## Exact statements

Put `N=n+1`, `epsilon=sourceFactorialCollar N>0`, and let `A_n(t)` be the existing `factorialMuntzSum n t`. The actual completion is

```
F_n(x) = exp(x/2) * A_n(exp x) / sqrt(N).
c_N = 1/(2*sqrt(N)) > 0.
K_N = 25/(32*N*epsilon*sqrt(N)).
F_(n,c)(x) = F_n(x) + 1_(x<=0) * c * exp(x/2).
```

For every `t>0` and every real `x`,

```
|A_n(t)+1/2| <= 25*t/(32*N*epsilon),
|exp(-x/2)*F_n(x)+c_N| <= K_N*exp(x).
```

Consequently `exp(-x/2)*F_n(x) -> -c_N` at negative infinity. The full real-line polar-integrability classification is

```
Integrable (exp(-x/2)*F_(n,c)(x))  <->  c=c_N.
```

The positive weighted source `exp(x/2)*F_(n,c)(x)` is integrable for every real `c`. Thus the canonical correction has both weighted moments integrable, while the uncorrected completion fails the negative one.

For every complex `s` with `Re(s)>0`, the corrected readout is integrable and

```
integral exp((s-1/2)*x)*F_(n,c)(x) dx
  = mellin(A_n)(s)/sqrt(N) + c/s.
```

At any zeta zero `rho` in that half-plane it equals `c/rho`; at the canonical coefficient it is nonzero. Uniqueness concerns this one-parameter exponential correction family, not arbitrary corrections.

## Dependency-closed paper proof

For `y>=0`, set `m=floor(y)`, `r=y-m`, and

```
R(y) = sum_(k>=1) max(y-k,0),
delta(y) = r*(1-r)/2.
```

Only the first `m` summands can be nonzero. Summing that finite arithmetic progression, including the zero final summand when `y` is an integer, gives

```
R(y) = m*y - m*(m+1)/2 = (y^2-y)/2 + delta(y),
0 <= delta(y) <= 1/8.
```

For positive `epsilon,a,t`, the literal clamp has the positive-part identity

```
clampedRamp epsilon (k*t/a)
  = t/(a*epsilon) *
      (max(a*(1+epsilon)/t-k,0) - max(a/t-k,0)).
```

Both sums have finite support. Substituting the exact formula for `R` yields

```
S(epsilon,a,t) := sum_(k>=1) clampedRamp epsilon (k*t/a)
 = a*(1+epsilon/2)/t - 1/2
   + t/(a*epsilon)*(delta(a*(1+epsilon)/t)-delta(a/t)).
```

The final term has absolute value at most `t/(8*a*epsilon)`. The actual seed gives

```
A_n(t) = S(epsilon,4*N,t) - 4*S(epsilon,2*N,t) + 4*S(epsilon,N,t).
```

Its reciprocal-scale coefficient vanishes, since `4*N-4*(2*N)+4*N=0`. Its constant coefficient is `(-1/2)*(1-4+4)=-1/2`. The sum of the three error bounds is `25*t/(32*N*epsilon)`. Inserting `t=exp(x)` and dividing by `sqrt(N)>0` proves the completion bound and its negative-end limit.

On `x<=0`, the canonical negative weighted source is `exp(-x/2)*F_n(x)+c_N`; the bound by `K_N*exp(x)` proves integrability there. On the positive half-line, the existing literal identity `factorialMuntzCompletion_eq_ramp` identifies the source with the continuous compactly supported factorial ramp. These two facts prove integrability on the full line. The value at zero is included in the negative indicator and does not affect the integral.

For general `c`, subtract the canonical negative weighted source. The difference is exactly the constant `c-c_N` on `(-infinity,0]` and zero elsewhere. This function is integrable exactly when `c=c_N`, because that half-line has infinite Lebesgue measure. This proves necessity and sufficiency, and excludes `c=0` since `c_N>0`.

For `Re(s)>0`, the existing completion readout is integrable and equals `mellin(A_n)(s)/sqrt(N)`. Multiplication of the added correction by the readout kernel gives `c*exp(s*x)` on `x<=0`, whose integral is `c/s`. Addition proves the exact corrected formula and integrability. At `s=1`, taking real parts proves positive weighted integrability. At a right-half-plane zeta zero, the existing theorem `factorialMuntzSum_mellin_zero` removes the Mellin term. Such a zero is nonzero because its real part is positive; hence `c_N/rho` is nonzero.

## Lean and verification status

The implementation comprises `ClampedRampLatticeSum.lean`, `FactorialMuntzBoundaryPole.lean`, and `FactorialMuntzBoundaryRepair.lean` in `formal/GaloisForLFunctions/BiScaleUncertainty/`. All three leaves passed, together with both necessary tail/readout dependency checks. All three new modules are wired into the area umbrella. The implementation contains 18 public theorems and five public definitions. The full 24-declaration axiom audit is running; it enumerates every new public declaration and the repaired existing theorem, not a sample.

The first repair check found an unavailable bundled ramp name and several elaboration mismatches. The revised proof uses the existing underlying ramp and its continuity/compact-support properties directly. It explicitly types the real indicator before casting to complex values, exposes pointwise function subtraction, uses the constant-integrability equivalence as a term, and fixes the integrable-indicator and real-projection applications. A mathlib-only probe of the analytic fixes passed, followed by the full repair leaf. No mathematical statement changed. Only tactic-style warnings remain in the passed new-leaf logs.

Existing Müntz seed/completion/tail sources remain unchanged; the tail dependency passed. The readout dependency check exposed one rewrite failure in `factorialRamp_zeta_readout`: its integrability facts used the expanded exponential while the goal used the private `readoutKernel` definition. Two explicit type annotations align those facts with the goal; no statement or other proof changed. The narrow dependency repair passed and is included in the final axiom audit, giving 24 audited declarations: 23 new declarations plus this repaired existing theorem. Required dependency objects are pinned in an owned temporary cache to avoid the concurrent global rebuild. The manifest records fallback provenance and older transitive objects; this is not a fresh whole-tree build.

## Remaining boundary

This closes the claim that the unmodified L2 completion already supplies a source with both polar moments integrable and vanishing zeta-zero readouts. The canonical exponential repair restores the moments but leaves the explicit nonzero readout `c_N/rho`.

No full-Weil-domain membership or full-Weil positivity is proved for the repaired source. Its indicator correction has a jump at zero. The bound `K_N` depends on `epsilon^-1` and supplies no uniform-in-`N` Weil control. The coupled diagonal margin, all-source RW positivity, and RH remain open.

## Concrete follow-up from existing Lean source

The additional corpus query `rational Mellin readout inverse s Weil form zero sum rho one minus rho first Li coefficient` completed with partial reranking results in `/tmp/bsu-muntz-rational-weil-search-20261018.json`. All 20 candidate-lemma and 20 source-argument statements were inspected. Semantic coverage was unmeasured, refresh incomplete, and reranking hit its local runtime deadline. No exhaustive-search claim follows.

Direct source inspection identified these existing ingredients; they are not new results of this card and were not added as implementation dependencies:

- `RHTower/ArchimedeanGenusZeroSum.lean`, `tsum_inv_zero_mul_one_sub_zero`: the multiplicity-expanded sum `sum_q 1/(rho_q*(1-rho_q))` equals `poleSharpConstant = 2 + gamma - log(4*pi)`.
- `RHTower/LiCoefficientXi.lean`, `summable_xiLiPairedTerm`: absolute summability of the paired Li terms.
- `RHTower/LiFirstCoefficientsNonneg.lean`, `re_xiLiPaired_nonneg_of_le_68`: unconditional nonnegativity of the first 68 paired Li coefficients.
- `RHTower/SuzukiCorFourSix.lean`, `suzukiEntireFourier_liTestFun_term` and `suzukiLiWeilForm_eq_xiLiPaired`: a literal half-line test family and its zero-side Li identity.

The candidate next bridge is to connect the corrected source's exact readouts to an admissible full-Weil form with the correct normalization and multiplicities, then control passage back to the compact ramp. The existing `ExpDecayTest` in `RHTower/WeilConeXiDivisibleBlindTest.lean` explicitly requires `ContDiff` of order two. Therefore `riemannHypothesis_iff_decayClass_weilPositive` cannot be applied directly to this discontinuous correction. An identity for a zero series alone does not discharge that domain or truncation obligation. No further identity for the corrected source's full-Weil form is claimed here.
