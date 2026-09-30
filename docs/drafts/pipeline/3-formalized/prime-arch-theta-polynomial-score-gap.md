# Actual theta source: polynomial score-gap coercivity

- **ID:** PA-THETA-SCORE-GRAM
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); significance unverified
- **Objective:** retain the strongest positive source law exposed by the failed scalar-score-to-cumulant sign mechanism.

## Exact statement and normalization

Use the raw moments `R_j=thetaCuspRawEvenMoment j=2∫_(x>0) x^(2j) Φ(x) dx`. No continuous-source calibration factor is inserted. Set `D_j=(32j+17)R_j−303R_(j+1)`.

For a finite real polynomial `P(y)=Σ_i a_i y^i`,

`Σ_i Σ_j a_i a_j D_(i+j)`
`=2π Σ_(n≥1) ∫_(x>0) P(x²)² [1+32xW_n(x)−303x²] ψ_n(x)² dx`
`≥2π ∫_(x>0) P(x²)²(x−1)²ψ_1(x)² dx`.

For `P≠0` the final integral is strictly positive. Every finite Hankel matrix of raw score defects is therefore positive definite. This is a source score-defect matrix, not the cumulant matrix or reciprocal moment matrix required by an RH producer.

Here actual `q_n(x)=π(ne^x)²`, `ψ_n(x)=2√(q_n−3/2) n exp(5x/4) exp(−q_n/2)`, and `W_n=q_n−5/4−q_n/(q_n−3/2)`. Measure is `volume.restrict (Ioi 0)`. Atom zero contributes zero.

## Dependency-closed paper proof

1. Existing exact atom Ward identity gives `∫x^(2j+1)W_nψ_n²=((2j+1)/2)∫x^(2j)ψ_n²`. Thus its score defect is exactly `(32j+17)` times the atom's `j`th raw moment minus `303` times its next moment, after multiplying by `2π`.
2. Expand the finite square `P(x²)²` inside the integral. All polynomially weighted amplitude and superpotential terms are integrable. Linearity gives the signed finite quadratic form exactly. Do not sum scalar inequalities with signed `a_i a_j`.
3. Each atom has pointwise defect at least `(x−1)²`. Multiplying by the nonnegative polynomial square preserves this inequality. Every atom quadratic form is nonnegative.
4. Scalar raw atom moments are absolutely summable, so finite linear combinations of their score defects are summable. Exchange finite sums with the atom sum, then retain atom one to obtain the stated full-source lower bound.
5. A nonzero real polynomial has finitely many roots. Choose `x>2` with `P(x²)≠0`; actual `ψ_1(x)>0`. Continuity supplies an interval of positive measure with strictly positive integrand. Its integral is positive.

## Verified dependencies

- Raw normalization: `PrimeArchThetaCumulantMinor.lean:151`.
- Atom normalization and exact complete sum: `PrimeArchThetaBornWittenGroundState.lean:237,245`.
- Pointwise defect and exact atom integral: `PrimeArchThetaScoreMomentDefect.lean:16,35`; scalar full-source first-atom square bound at 185. Root checked the pointwise and exact integral declarations and raw normalization.
- Existing third cumulant product kernel has positive and negative open chambers on positive support: `PrimeArchThetaThirdCumulantProductKernel.lean:25,293`. The all-order recursion in `PrimeArchThetaAllOrderCumulant.lean:92` has no demonstrated positivity-preserving transfer.
- Prior corpus searches were partial; pending/stale compiler coverage supplies no fresh validation. Matrix extension was not identified among inspected declarations; no worldwide novelty claim.

## Obstruction and surviving arithmetic burden

The Gaussian–Hermite model still refutes the generic implication from all polynomial score-gap positivity to cumulant Hankel positivity. Strong log-concavity followed by scaling `s²≤1/38` gives its own score `W≥(19/2)x` and defect `≥1+x²≥(x−1)²`. Its transformed determinant remains `s^18 t²(−196+324t+16t²)<0` for sufficiently small positive `t`; determinant and scaling algebra already exist in `PrimeArchHermiteMomentBoundary.lean:161,169,178`. The strengthened analytic density argument remains paper-level.

The stronger paper audit now matches the actual fixed `ψ_1²` lower floor after an uncalibrated amplitude change. For spatial scale `s=1/10` and sufficiently small perturbation, curvature is at least `50`; its score defect is at least `1+497x²`. The ratio `ψ_1²/ρ` tends to zero at infinity, so a finite amplitude enforces the complete prescribed polynomial floor. One amplitude works uniformly for every perturbation in a small positive interval, giving countermodels with one common freely chosen raw mass. Normalized cumulants cancel amplitude and retain the negative determinant. These analytic assertions remain paper-level; `t<1/1000` alone does not establish density positivity/curvature.

[Literal actual `R_0` calibration now closes on paper](../2-fully-proven/li-mass-calibrated-score-floor-obstruction.md): scale `s=1/6`, certified `R_0≥9/20`, and exact global Gaussian score envelope give the prescribed floor with uniform strict surplus while the cumulant determinant stays negative. Analytic construction remains paper-only; [strongest positive envelope is formalized](prime-arch-theta-gaussian-score-floor-envelope.md), including factor `110843/111104`. Theta atom lattice, full actual moment sequence and exact source membership remain unmatched. Calibrated mass plus standalone floor coercivity is insufficient; no actual-source route is retired and no RH conclusion follows.

The complete actual pointwise slack is now formalized in `PrimeArchThetaFullScoreSlack.lean`: `E=(1−303x²)k−16xk'−πψ_1²(x−1)²` is continuous and retains the entire strictly positive second-atom score for every `x≥0`. Every atom after the first has strictly positive defect, including at `x=1`. All 14 public declarations passed final exact checks and foundational axiom audits. Generic compact/tail floor stability and complete packet compatibility are [formalized](theta-derivative-packet-full-score-floor.md): same parameter interval retains every strict nonzero polynomial floor and all original dark-divisor properties. Separate growth-order clause follows on paper from the exact transform; critical-strip/Euler membership remains absent.

## Log

- 2026-09-29 — Independent read-only audit supplied the exact raw normalization and complete polynomial-square proof. Positive survivor recorded before formal implementation; Lean pending.
- 2026-09-29 — `PrimeArchThetaPolynomialScoreGap.lean` closes the exact complete atom identity, fixed first-atom lower floor, strict positivity for every nonzero polynomial/vector and positive definiteness of every finite raw score-gap Hankel matrix. Named `lake build --old GaloisForLFunctions.RHTower.PrimeArchThetaPolynomialScoreGap` passed (leaf 3.6 seconds); final exact `lake env lean GaloisForLFunctions/RHTower/PrimeArchThetaPolynomialScoreGap.lean` passed with empty output. Nine capstone axiom checks returned only `propext`, `Classical.choice`, `Quot.sound`. Evidence in `/tmp/hgt-theta-polynomial-gap.9GACuD/{build,direct,axioms}.log`.
- 2026-09-29 — Root spot-checked raw defect definition, complete `2π` atom sum, strict polynomial-square integral and finite matrix PosDef proof; wired the leaf in `RHTower.lean`. Whole-tree lint still has unrelated reachability failures; targeted proof validation does not claim a clean global gate. The generic analytic Hermite strengthening remains explicitly paper-level and no actual-source route is retired.
