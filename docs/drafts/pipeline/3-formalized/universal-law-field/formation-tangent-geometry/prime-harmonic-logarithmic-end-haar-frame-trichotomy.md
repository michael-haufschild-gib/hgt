# Prime-harmonic logarithmic-end Haar-frame trichotomy

- **ID:** ULF-FTG-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [PRE-DIVISOR] [NOT RH] [LEAN-PROVED]`

## Big-picture law

Completion is tested by its moving tangent at infinity, not by subtracting a fixed divergent
scalar.  Literal Euler half-densities, Poisson scale histories, prime-harmonic density, and theta
translation have one common end tangent.  Horizontal grade is its scaling dimension:

\[
 a>0:\text{ collapse},\qquad a=0:\text{ finite nonzero Haar tangent},\qquad
 a<0:\text{ local explosion}.
\]

Thus the critical line is the unique grade with a nondegenerate two-sided formation tangent.  This
is an unconditional source theorem.  It becomes an RH theorem only after proving that the actual
Xi completion, before its divisor is supplied, must land continuously in this tangent geometry.

## Corpus audit before conjecture

- `FieldOneFiniteStageThetaEulerSourceIdentification` and
  `FieldOneFiniteStageThetaCoreEulerIdentification` give the exact finite-stage Euler coefficients.
- `FieldOneFiniteStageThetaSourceNormalization` and `FieldOneFiniteStageSelfDualHaar` give the
  literal theta/Poisson half-density carrier and its forced Haar normalization.
- `PoissonScaleHistoryFrame` proves that clock `t` has one translated log-aperture mother
  `F(x+log t)`, with unsquared external amplitude untouched.
- `XiThetaLogTranslationSeam` proves theta square-atoms translate by `2 log m`; taking the logarithmic
  tangent of this translation end sends the prime coordinate to `log log p`, up to an additive
  normalization.
- `MertensSecondPrimeRecipSum` and `MertensConstantIdentification` prove
  `sum_{p<=x} 1/p = log log x + B + r(x)` with `r(x) -> 0`.
- `SoninSemilocalMetricLog` identifies the nonsummable central mode as the principal `1/p` energy.
- `HedenmalmThetaPrincipalClassTrichotomy` forbids fixed subtraction of that class.
- `DeningerMeyerHalfDensityGaussianXiEvaluationCriterion` proves that canonical source-to-Xi
  continuous descent in the existing half-density norm is equivalent to RH; it cannot be imported
  as a premise here.

Corpus searches included `Mertens reciprocal prime cumulative error`, `loglog prime translate
frame`, `PrimeClockCriticalProfile`, `theta translation square integer atoms 2 log`, and
`canonical source to global Xi continuous extension iff RH`.

## Arithmetic tangent theorem

Write

\[
 A(x)=\sum_{p\le x}\frac1p=\log\log x+B+r(x),\qquad r(x)\longrightarrow0.
\]

For `L` large, `X_L=exp(exp L)`, grade `a in R`, and `y>=0`, define the locally finite end measure

\[
 \mu_{a,L}=\sum_{p>X_L}p^{-1-a}\,
   \delta_{\log\log p-L}.
\]

Then:

1. **Neutral Haar tangent.** For every `y>=0`,

   \[
   \mu_{0,L}([0,y])-y
    =r(X_{L+y})-r(X_L).
   \]

   Consequently

   \[
   \epsilon_L:=\sup_{y\ge0}|\mu_{0,L}([0,y])-y|
      \le 2\sup_{x\ge X_L}|r(x)|\longrightarrow0.
   \]

   In particular `mu_{0,L}` converges to Lebesgue/Haar measure on the whole future half-line with
   uniform cumulative-discrepancy control, not only vaguely on compact intervals.

2. **Positive collapse.** If `a>0`,

   \[
   \mu_{a,L}([0,\infty))=\sum_{p>X_L}p^{-1-a}\longrightarrow0.
   \]

3. **Negative local explosion.** If `a<0`, put `b=-a`.  For every fixed `delta>0`,

   \[
   \mu_{a,L}([0,\delta])
      \ge X_L^b\mu_{0,L}([0,\delta])\longrightarrow\infty.
   \]

### Proof

The first identity is the difference of Mertens' formula at `X_{L+y}` and `X_L`; the main terms
differ by exactly `y`.  Convergence of `r` gives the uniform tail supremum.  For `a>0`, the prime
sum is bounded by the tail of `sum n^{-1-a}`.  For `a<0`, every prime in the displayed interval
satisfies `p^b>=X_L^b`, while the neutral interval mass tends to `delta`.  QED.

## Operator-valued lift

Let `0 != h in W^{1,1}(R) cap L^2(R)`, let `T_y h(x)=h(x-y)`, and retain the literal principal
Euler amplitude and phase by

\[
 u_{p,a,L,\tau}=p^{-(1+a)/2}e^{-i\tau\log p}T_{\log\log p-L}h.
\]

For finite prime support this defines the coefficient-faithful synthesis map

\[
 S_{a,L,\tau}c=\sum_pc_pu_{p,a,L,\tau}.
\]

Its quadratic frame form is

\[
 Q_{a,L}(f)=\sum_{p>X_L}|\langle f,u_{p,a,L,\tau}\rangle|^2
 =\int_0^\infty |\langle f,T_yh\rangle|^2\,d\mu_{a,L}(y).
\]

The phase cancels only after polarization; it is not discarded by the synthesis map.  Define the
continuous Haar frame operator by

\[
 \langle A_Hf,f\rangle=\int_0^\infty|\langle f,T_yh\rangle|^2dy.
\]

At neutral grade the positive frame operators `A_{0,L}=S_{0,L,tau}S_{0,L,tau}^*` exist and

\[
 \boxed{\|A_{0,L}-A_H\|_{op}
   \le 2\epsilon_L\|h\|_1\|h'\|_1\longrightarrow0.}
\]

Moreover `A_H` is nonzero.  If `a>0`, `A_{a,L}` tends to zero in trace norm.  If `a<0`, already
the operator obtained from clocks in any fixed end interval `[0,delta]` has norm tending to
infinity.

### Proof

For `g_f(y)=<f,T_yh>`, Young's inequality gives

\[
 \|g_f\|_2\le\|h\|_1\|f\|_2,\qquad
 \|g_f'\|_2\le\|h'\|_1\|f\|_2.
\]

Hence `q_f=|g_f|^2` is absolutely continuous, tends to zero at infinity, and

\[
 \|q_f'\|_1\le2\|h\|_1\|h'\|_1\|f\|_2^2.
\]

Stieltjes integration by parts against the cumulative discrepancy from the arithmetic theorem
gives the boxed quadratic-form bound, uniformly for `||f||_2=1`; polarization/Riesz representation
gives operator-norm convergence.  Translation continuity and `h!=0` make
`<h,T_yh>` nonzero on a small interval, so `A_H!=0` and the negative-grade local mass lower bound
forces operator-norm explosion.  For positive grade, the sum of rank-one trace norms is at most
`||h||_2^2 sum_{p>X_L}p^{-1-a}`, which tends to zero.  QED.

For the corpus Poisson mother `F(x)=2e^x exp(-e^x)`,

\[
 \|F\|_1=2,\qquad \|F'\|_1=4/e,
\]

so the neutral bound is `(16/e) epsilon_L ||f||_2^2`.

## Full Euler formation

At prime-power depth `m`, literal Euler/Poisson formation has unsquared amplitude

\[
 \frac{p^{-m(1+a)/2}}m
\]

and translated clock coordinate `log(m log p)-L`.  At `a=0`, every `m>=2` contribution is
trace-class and its tail tends to zero because

\[
 \sum_p\sum_{m\ge2}\frac{p^{-m}}{m^2}<\infty.
\]

Therefore the full prime-power formation has exactly the same nonzero Haar tangent as its
principal `m=1` layer; higher Euler modes form the vanishing residual completion boundary.  This
is the precise valid replacement for fixed principal-shell subtraction.

## Functional-equation consequence and limitation

The functional equation exchanges grades `a` and `-a`.  The two orientations possess finite,
nonzero end tangents simultaneously if and only if `a=0`.  This is an exact source-side selection
law.

It is **not** an RH proof.  Functional equation swaps the two Xi fibres but does not prove that
either completed Xi evaluation factors through this tangent norm.  Ordinary Hilbert graph closure
is maximally saturated (`ArithmeticFormationCompletionBoundaryFusion`), while the known canonical
source-to-Xi continuous descent is RH-equivalent.  The remaining noncircular theorem must derive a
cofinal transition map from finite literal theta transports into this tangent completion and prove,
independently of the divisor, that actual Xi completion factors through it.

## Route-independent prediction

For any Euler formation whose principal local coefficient energies satisfy

\[
 \sum_{p\le x}|\lambda(p)|^2/p=\kappa\log\log x+C+o(1),
\]

the same proof predicts tangent `kappa dy` at neutral grade, collapse for positive grade, and local
explosion for negative grade when a corresponding lower interval law holds.  The corpus theorem
`tendsto_dirichletCharacterPrimeRecipEnergy_sub_logLog` confirms the prediction for primitive
Dirichlet characters, with only finitely many conductor primes removed.  This is evidence that the
tangent is a formation law rather than a zeta-specific receiver.

## External collision audit

Related parent theories exist: irregular frames of translates, operator-valued measures, Gabor
operator-norm limits, and Connes--Consani semilocal scaling/Poisson geometry.  Mertens' reciprocal
prime theorem is classical.  Searches found no exact result combining the reciprocal-prime
`log log p` end tangent, grade trichotomy, literal Euler amplitudes, and operator-norm Haar-frame
lift.  Relevant comparisons:

- Balazs--Heineken, *An operator based approach to irregular frames of translates*,
  <https://arxiv.org/abs/1401.4955>.
- Han--Larson--Liu--Liu, *Operator-Valued Measures, Dilations, and the Theory of Frames*,
  <https://arxiv.org/abs/1110.5833>.
- Poria, *Behavior of Gabor frame operators on Wiener amalgam spaces*,
  <https://arxiv.org/abs/1507.04549>.
- Connes--Consani, *The Scaling Hamiltonian*, <https://arxiv.org/abs/1910.14368>.
- Villarino, *Mertens' Proof of Mertens' Theorem*, <https://arxiv.org/abs/math/0504289>.

This is an internal collision audit, not a publication-level priority claim.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.TranslationFrameHaarDiscrepancy`, `GaloisForLFunctions.HTGeometry.TranslationFrameOperators`, `GaloisForLFunctions.HTGeometry.PrimeHarmonicEndHaarFrame`, `GaloisForLFunctions.HTGeometry.PrimeHarmonicEulerFormationTangent`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.TranslationFrameHaarDiscrepancy` (window analysis, Stieltjes
comparison), `GaloisForLFunctions.HTGeometry.TranslationFrameOperators` (Bessel/frame operators, Haar frame,
translate-system comparison), `GaloisForLFunctions.HTGeometry.PrimeHarmonicEndHaarFrame` (end measures, energy
laws, grades, operator lift), `GaloisForLFunctions.HTGeometry.PrimeHarmonicEulerFormationTangent` (Mertens and
Dirichlet energy laws, end-tangent selection, full Euler formation, Poisson mother, capstone).  Corpus inputs:
`RHTower.tendsto_primeRecipSum_floor_sub_logLog` (Mertens), `RHTower.tendsto_dirichletCharacterPrimeRecipEnergy_sub_logLog`,
`HTGeometry.lintegral_enorm_sq_le_of_convolution_bound` (Young), `HTGeometry.translateL2`, corpus trace-norm calculus.
The card is formalized for an arbitrary coefficient `λ` with energy law `∑_{p≤x}|λ(p)|²/p = κ log log x + C + o(1)`
(`HasPrimeEnergyLaw`), specialized to `λ ≡ 1, κ = 1` (Mertens) and to Dirichlet characters.

| Claim | Lean declaration |
|-|-|
| `X_L = exp(exp L)`, end primes, clocks `log log p - L ≥ 0`, literal amplitudes `λ(p)p^{-(1+a)/2}e^{-iτ log p}` | `endClock`, `IsEndPrime`, `endPrimeClock`, `endPrimeClock_nonneg`, `endPrimeCoeff`, `norm_endPrimeCoeff_sq` |
| `μ_{a,L} = ∑_{p>X_L} p^{-1-a} δ_{log log p - L}` (phase-free) | `primeEndMeasure`, `primeEndMeasure_apply`, `translateSystemMeasure_endPrimeCoeff` |
| `A(x) = ∑_{p≤x} 1/p = log log x + B + r(x)`, `r → 0` | `primeEnergySum`, `energyRemainder`, `HasPrimeEnergyLaw`, `hasPrimeEnergyLaw_one`, `HasPrimeEnergyLaw.tendsto_remainder` |
| 1. `μ_{0,L}([0,y]) - y = r(X_{L+y}) - r(X_L)` | `primeEndMeasure_zero_Icc` (window identity), `primeEndMeasure_zero_Icc_real`, `primeEndMeasure_zero_Icc_sub` |
| 1. `ε_L := sup_{y≥0}∣μ_{0,L}[0,y] - y∣ ≤ 2 sup_{x≥X_L}∣r(x)∣ → 0` (uniform discrepancy on the whole half-line) | `neutralDiscrepancy`, `energyTailSup`, `abs_primeEndMeasure_zero_Icc_sub_le`, `neutralDiscrepancy_le`, `tendsto_energyTailSup`, `tendsto_neutralDiscrepancy` |
| 2. `a > 0`: `μ_{a,L}[0,∞) → 0` | `tendsto_primeEndMeasure_univ_of_pos` (quantitative: `primeEndMeasure_univ_le`, via the tilt relation `setLIntegral_primeEndMeasure`, `gradeTilt`) |
| 3. `a < 0`: `μ_{a,L}[0,δ] ≥ X_L^b μ_{0,L}[0,δ] → ∞` | `primeEndMeasure_Icc_ge`, `tendsto_primeEndMeasure_Icc_of_neg` |
| `0 ≠ h ∈ W^{1,1} ∩ L²`, `T_y h = h(·-y)` | `SobolevTranslateWindow`, `SobolevTranslateWindow.toL2`, `translateRight`, `coeFn_translateRight` |
| `u_{p,a,L,τ} = p^{-(1+a)/2}e^{-iτ log p} T_{log log p - L} h` | `SobolevTranslateWindow.endFrame`, `SobolevTranslateWindow.endFrame_of_isEndPrime`, `translateSystem` |
| coefficient-faithful synthesis `S c = ∑ c_p u_p` on finite supports | `besselAnalysis`, `besselSynthesis_single`, `besselSynthesis_finsetSum` |
| `Q_{a,L}(f) = ∑∣⟨f,u_p⟩∣² = ∫_0^∞∣⟨f,T_y h⟩∣² dμ_{a,L}`, phase cancels | `SobolevTranslateWindow.setLIntegral_corrSq_primeEndMeasure`, `norm_inner_translateSystem_sq`, `setLIntegral_Ici_translateSystemMeasure` |
| `⟨A_H f,f⟩ = ∫_0^∞∣⟨f,T_y h⟩∣² dy` | `SobolevTranslateWindow.haarAnalysis`, `SobolevTranslateWindow.haarFrameOp`, `SobolevTranslateWindow.re_inner_haarFrameOp_self`, `SobolevTranslateWindow.haarFrameOp_isPositive` |
| `A_{0,L} = S S*` exists (positive, Bessel) | `SobolevTranslateWindow.isBesselFamily_endFrame_zero`, `SobolevTranslateWindow.neutralEndFrameOp`, `besselFrameOp`, `besselFrameOp_isPositive`, `inner_besselFrameOp_self` |
| Young: `‖g_f‖₂ ≤ ‖h‖₁‖f‖₂`, `‖g_f'‖₂ ≤ ‖h'‖₁‖f‖₂` | `SobolevTranslateWindow.lintegral_translateCorrelation_sq_le`, `SobolevTranslateWindow.lintegral_derivCorrelation_sq_le`, `SobolevTranslateWindow.translateCorrelation_sub_eq_integral` |
| `q_f = ∣g_f∣²` absolutely continuous, `→ 0`, `‖q_f'‖₁ ≤ 2‖h‖₁‖h'‖₁‖f‖₂²` | `normSq_sub_eq_integral_of_primitive`, `SobolevTranslateWindow.corrSq_sub_eq_integral`, `SobolevTranslateWindow.tendsto_corrSq_atTop`, `SobolevTranslateWindow.integral_norm_corrSqDeriv_le` |
| Stieltjes integration by parts against the discrepancy; polarization/Riesz | `setIntegral_Icc_eq_of_primitive`, `abs_setIntegral_Ici_sub_le`, `SobolevTranslateWindow.translateSystem_comparison`, `norm_le_of_abs_re_inner_self_le` |
| **boxed** `‖A_{0,L} - A_H‖ ≤ 2ε_L‖h‖₁‖h'‖₁ → 0` | `SobolevTranslateWindow.norm_neutralEndFrameOp_sub_le`, `SobolevTranslateWindow.norm_besselFrameOp_translateSystem_sub_le`, `SobolevTranslateWindow.tendsto_neutralEndFrameOp` |
| `A_H ≠ 0` (translation continuity, `h ≠ 0`) | `SobolevTranslateWindow.exists_corrSq_self_ge`, `SobolevTranslateWindow.re_inner_haarFrameOp_window_pos`, `SobolevTranslateWindow.haarFrameOp_ne_zero` |
| `a > 0`: `A_{a,L} → 0` in trace norm (`≤ ‖h‖₂² ∑_{p>X_L} p^{-1-a}`) | `SobolevTranslateWindow.hasSum_norm_endFrame_sq`, `SobolevTranslateWindow.positiveEndFrameOp`, `SobolevTranslateWindow.positiveEndFrameOp_traceClass`, `SobolevTranslateWindow.tendsto_traceNorm_positiveEndFrameOp`, `traceNorm_besselFrameOp_le`, `traceNorm_tsum_rankOne_le` |
| `a < 0`: clocks in any fixed `[0,δ]` give operator norm `→ ∞` | `endWindow`, `SobolevTranslateWindow.endWindowFrameOp`, `SobolevTranslateWindow.exists_window_norm_ge`, `SobolevTranslateWindow.tendsto_norm_endWindowFrameOp` |
| Poisson mother `F = 2e^x exp(-e^x)`: `‖F‖₁ = 2`, `‖F'‖₁ = 4/e`, neutral bound `(16/e)ε_L` | `poissonMotherWindow`, `poissonMotherDeriv`, `integral_poissonLogScaleMother`, `integral_norm_poissonMotherWindow`, `integral_abs_poissonMotherDeriv`, `poissonMother_neutral_bound`, `poissonMotherWindow_toL2_ne_zero` |
| Full Euler formation: depth-`m` amplitudes `p^{-m/2}/m`, clocks `log(m log p) - L`; `∑_p∑_{m≥2}p^{-m}/m² < ∞`; every `m ≥ 2` term trace class, tail `→ 0`; same nonzero Haar tangent | `IsEndPrimePower`, `higherEulerCoeff`, `higherEulerClock`, `summable_eulerResidualWeight`, `tendsto_eulerResidualMass`, `SobolevTranslateWindow.fullEulerFrame`, `SobolevTranslateWindow.fullEulerFrameOp_eq`, `SobolevTranslateWindow.eulerResidualFrameOp_traceClass`, `SobolevTranslateWindow.tendsto_traceNorm_eulerResidualFrameOp`, `SobolevTranslateWindow.tendsto_fullEulerFrameOp`, `besselFrameOp_sumElim` |
| Functional-equation consequence: `a` and `-a` both have finite nonzero end tangents iff `a = 0` | `HasFiniteNonzeroEndTangent`, `hasFiniteNonzeroEndTangent_iff`, `hasFiniteNonzeroEndTangent_both_iff`, `tendsto_primeEndMeasure_zero_Icc` |
| Route-independent prediction: tangent `κ dy`, collapse, explosion under the energy law; Dirichlet characters | all of the above for general `coef, κ`; `hasPrimeEnergyLaw_dirichletCharacter`, `tendsto_logLog_floor_sub`, `SobolevTranslateWindow.tendsto_dirichletEndFrameOp` |
| Trichotomy capstone | `SobolevTranslateWindow.primeHarmonicHaarFrameTrichotomy` |

The card's "Functional-equation consequence and limitation" section explicitly disclaims an RH proof and the
"cofinal transition map" programme; neither is claimed.  The external collision audit carries no Lean obligation.

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
