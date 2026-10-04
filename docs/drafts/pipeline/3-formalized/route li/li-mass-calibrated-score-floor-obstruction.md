# Literal-mass calibrated score floor: paper obstruction and strict envelope

- **ID:** LI-CURRENT-CALIBRATED-FLOOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [actual-current scaling route](../1-in-progress/li-actual-current-small-mass-sinc-scaling.md)
- **Statement:** A Gaussian–Hermite source matches literal actual raw mass and complete fixed first-atom polynomial score floor while its normalized cumulant determinant is negative. The actual first-atom floor satisfies a strict global Gaussian score envelope.

## Candidate before hard proof work

Let `P=−He_4+He_6−2He_8+He_10`, in the probabilists' Gaussian convention. Use spatial scale `s=1/6` and density

`ρ_τ(x)=6φ(6x)(1+τP(6x))`.

For sufficiently small positive `τ`, uniform analytic bounds are `ρ_τ≥(9/10)ρ_0` and `−(logρ_τ)''≥30`. Polynomial mass correction is zero, so `∫_ℝρ_τ=1`. Fix amplitude **literally** `A=thetaCuspRawEvenMoment 0`. Existing `XiCentralDiscBound.norm_XiC_zero_ge` and exact zero-order raw-moment identity give `A≥9/20`.

On `x≥0`, evenness yields score defect `d_τ=1−16xρ_τ'/ρ_τ−303x²≥1+177x²`. It would suffice to prove

`πψ_1(x)²(x−1)² ≤ [243/(100√(2π))]exp(−18x²)(1+177x²)`.

Independent exact audit proves the stronger inequality with multiplier `c=110843/111104<1` on its right. Thus `Aρ_τd_τ≥c^(−1)πψ_1²(x−1)²`; integrating retained polynomial squares reproduces the prescribed floor with strict surplus at every degree, at actual raw mass. Normalized determinant is `(1/6)^18 τ²(−196+324τ+16τ²)<0` for small positive `τ`.

## Audited exact inequality proof

First-atom formula is `ψ_1²=4(πe^(2x)−3/2)exp(5x/2−πe^(2x))`.

For `x≥1/3`, drop `−3/2`, prove `πe^(2x)−18x²−(9/2)x≥0`, and use `(x−1)²/(1+177x²)≤2/93`. The remaining scalar inequality is `800π²√(2π)≤22599`, obtainable from rational bounds on π and its square root.

For `0≤x≤1/3`, monotonicity of `(y−3/2)e^(−y)` for `y≥π` gives a floor ratio bounded by

`D exp(18x²+(5/2)x)(1−x)²/(1+177x²)`,

where `D=4π(π−3/2)e^(−π)√(2π)/(243/100)`. Proposed bounds are `D≤15/16` and `exp(18x²+(5/2)x)≤1+3x+177x²`. The latter follows from `e^u≤1+u+(7/4)u²` on `0≤u≤17/6`, provided exact `e^(17/6)<35/2`. Polynomial multiplication then gives ratio at most `16/15`: drop negative cubic remainder and use `1/15−x+(84/5)x²>0`.

For the exponent inequality on `[0,3/4]`, fourth Taylor lower bound with `π≥157/50` has positive Bernstein coefficients `[157/50,2779/800,2167/800,4117/3200,1991/6400]`. On the tail, fifth-order certificates give value `≥32627/64000>1/2` and slope `≥−111373/32000>−7/2` at `3/4`; fourth-order certificate gives second derivative `≥30791/1600>18`. Hence the lower bound is `9(h−7/36)²+23/144>0` for `h=x−3/4≥0`.

Exact exponential certificates use `T_n(a)=Σ_(k≤n)a^k/k!`: `T_8(17/6)+(17/6)^9/[9!(1−17/60)]<69/4<35/2`, and `T_9(157/50)>23`. The tail is geometric since successive omitted ratios are at most `17/60`. Rational π bounds and `√(2π)≤251/100` prove both scalar inequalities. These are exact finite algebraic certificates, not numerical experiments or sampled checks.

Strong surplus follows on the small interval from `q=1/15−x+(84/5)x²=(84/5)(x−5/168)²+29/560` and `1+177x²≤62/3`: ratio is at most `(15/16)(16/15−87/34720)=110843/111104`. The large-interval rational bound is smaller than this same constant. Root independently checked the square completion and multiplier arithmetic before accepting the stronger statement.

Uniform perturbation control: bounded-below polynomial `P` ensures `1+τP≥9/10` for small positive `τ`. Since its leading term is `y^10`, a bound `1+τP(y)≥a(1+τ|y|^10)` holds uniformly for some `a>0`. Polynomial derivative bounds imply the absolute log correction is bounded by `C(τ+τ^(1/5)+τ²)→0`, splitting at `|y|=τ^(−1/10)`. Choose it at most `1/6`; base Gaussian curvature becomes at least `5/6`, and scaling six gives `30`. Intersect this analytic interval with `0<τ<1/2` for the negative determinant. All integrations converge by polynomial-Gaussian decay; Wick correction at degree zero is zero.

## Status and limits

Calibrated countermodel is paper-proved. It matches literal raw mass plus score/floor data; actual theta lattice, modular/Euler source membership, Xi growth order and full prescribed source moment sequence remain unmatched. It refutes this subset of proposed input constraints, not RH or the actual theta response. Analytic construction is not Lean-closed. No actual-source route is retired.

## No-go closure under way

- **Killing mechanism:** literal mass plus every polynomial score floor is compatible with a negative normalized cumulant determinant.
- **Strongest positive survivor:** actual first-atom floor lies strictly below the explicit Gaussian score envelope with factor `110843/111104`, yielding uniform calibrated surplus `111104/110843`. Complete polynomial-square source decomposition/PosDef and [this stronger exact envelope](../3-formalized/prime-arch-theta-gaussian-score-floor-envelope.md) are formalized.
- **New insight:** mass calibration does not rescue the score-floor producer. Full theta membership or another independent invariant must enter.
- **Status:** independent hostile paper audit passed; determinant/scaling algebra and exact source envelope are Lean-closed. Both envelope leaves passed named builds, final exact checks and all 13 public axiom audits. Full analytic family remains paper-only. No world-novelty or new RH criterion claim.

## Plan

1. Hostile paper audit of every constant and uniform perturbation bound — complete.
2. Formalize exact stronger source envelope and its scalar certificates — complete; retain analytic family as explicitly paper-only until its full Lean closure.
3. Return to actual source membership and the Volterra pointwise sign burden; do not treat a generic countermodel as literal-source falsification.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.RHTower.PrimeArchGaussianHermiteDensity`, `GaloisForLFunctions.RHTower.PrimeArchThetaGaussianHermiteCountermodel`, `GaloisForLFunctions.RHTower.PrimeArchHermiteMomentBoundary`, `GaloisForLFunctions.RHTower.PrimeArchThetaGaussianScoreFloorEnvelope`, `GaloisForLFunctions.RHTower.PrimeArchThetaGaussianScoreEnvelopeCertificates`, `GaloisForLFunctions.RHTower.PrimeArchThetaPolynomialScoreGap`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.RHTower`):
`GaloisForLFunctions.RHTower.PrimeArchGaussianHermiteDensity` (new), `GaloisForLFunctions.RHTower.PrimeArchThetaGaussianHermiteCountermodel` (new),
`GaloisForLFunctions.RHTower.PrimeArchHermiteMomentBoundary`, `GaloisForLFunctions.RHTower.PrimeArchThetaGaussianScoreFloorEnvelope`,
`GaloisForLFunctions.RHTower.PrimeArchThetaGaussianScoreEnvelopeCertificates`, `GaloisForLFunctions.RHTower.PrimeArchThetaPolynomialScoreGap`.

| Claim | Declaration |
|-|-|
| `P=−He₄+He₆−2He₈+He₁₀` (probabilists') | `hermiteBoundaryPoly_eq_hermite` |
| `∫y^{2k}φ=(2k−1)!!`, model moments `6^{-2j}(m_j+τc_j)` | `integral_even_pow_mul_stdGaussianDensity`, `integral_even_pow_mul_gaussianHermiteDensity` |
| `∫ρ_τ=1` (zero mass correction) | `integral_gaussianHermiteDensity`, `hermiteBoundaryWickCorrection_exact` |
| `ρ_τ≥(9/10)ρ_0`, `−(log ρ_τ)''≥30` for small `τ>0` | `nine_tenths_mul_le_gaussianHermiteDensity`, `thirty_le_neg_deriv_deriv_log_gaussianHermiteDensity` |
| Uniform perturbation control | `exists_hermiteBoundaryPoly_lower`, `small_perturbation_dominates`, `gaussianHermiteThreshold_pos` |
| `A=thetaCuspRawEvenMoment 0 ≥ 9/20` | `nine_div_twenty_le_thetaCuspRawEvenMoment_zero` |
| Literal raw mass `R^τ_0=A` | `gaussianHermiteRawMoment_zero` |
| Score defect `d_τ≥1+177x²` on `x≥0` | `thirty_mul_le_neg_gaussianHermiteDensityDeriv`, `one_add_mul_le_gaussianHermiteDefectDensity` |
| Envelope `πψ₁²(x−1)²≤c·[243/(100√2π)]e^{−18x²}(1+177x²)`, `c=110843/111104` | `thetaCuspFirstAtom_gaussianScoreEnvelope` |
| `Aρ_τd_τ≥c^{-1}πψ₁²(x−1)²` | `firstAtom_le_calibrated_gaussianHermiteDefect` |
| Score-gap form = defect integral (integration by parts) | `gaussianHermiteFiniteScoreGap_eq_integral`, `integral_even_pow_mul_gaussianHermiteDefectDensity`, `integral_pow_mul_gaussianHermiteDensityDeriv` |
| Prescribed floor at every degree with uniform surplus `111104/110843`, strict for `P≠0` | `gaussianHermiteFiniteScoreGap_ge_firstAtomSquare`, `gaussianHermitePolynomialScoreGap_ge_firstAtomSquare`, `firstAtomSquare_lt_gaussianHermitePolynomialScoreGap` |
| Normalized determinant `(1/6)^18τ²(−196+324τ+16τ²)<0` | `primeArchHankelDetOfEvenMoments_gaussianHermite`, `primeArchHankelDetOfEvenMoments_gaussianHermite_neg` (same map on actual moments: `primeArchHankelDetOfEvenMoments_actual`) |
| Packaged countermodel | `exists_gaussianHermite_calibrated_countermodel` |

## Log

- 2026-09-30 — Candidate recorded before hard work; uses existing certified center lower bound and exact raw source normalization. Independent audit requested.
- 2026-09-30 — Independent hostile audit closed all constants, full perturbation control and prescribed floor at literal raw mass. Stronger uniform surplus returned through paper audit; root checked its rational square completion. Moved to stage two; exact positive-envelope formalization assigned. Actual RH source route remains in progress.
- 2026-09-30 — Exact first-atom envelope and nine scalar certificates formalized in two named leaves. Final direct checks are warning-free; all 13 public declarations use only foundational axioms. Countermodel card remains stage two because its analytic family is paper-only.
- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
