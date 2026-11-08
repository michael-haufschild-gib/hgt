# Frankenstein routes of review-0811 §2.3: assemblies, bridges, conjectures

- **ID:** FR-0811
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per route; CONJECTURE loop
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.3 (F1–F25)
- **Statement:** assemble each Frankenstein route as one Lean theorem; build the missing bridges;
  conjecture on what the assembly exposes.

Lean modules go into the owning programme folders.
Order: F22, F21, F18, F15, F2, then the rest.

## F22 — curve-proof template over ℤ

**Parts in the corpus.** `RH ⇔ ZAL ∧ AAL` (`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`);
weak recurrence ⇒ AAL; curve data with zeros `ρ_{i,k}` periodic in height (`CurveDatum.zetaZero`,
`curveConfig_periodic`); vertical recurrence of periodic and exponential-polynomial configurations
(`verticallyRecurrent_of_periodic`, `verticallyRecurrent_of_expPoly`); RH for odd hyperelliptic
curves (`riemannHypothesis_oddHyperelliptic`, `hyperellipticDatum_unitary`); JAS shell criterion.

**Missing bridge.** The matching curve step ↔ ℤ step was a reading [D]: ZAL and AAL were defined
only for ζ. Bridge: define both laws on every `ZeroConfig` and evaluate them on curves and on ζ.

**Results (Lean, `ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawsOfAZeroConfiguration`).**
- For every configuration: pure ⇔ ZAL ∧ AAL (the FE of the configuration gives the left side).
- AAL ⇔ zero transport: every right zero has, for every `ε` and `T`, a zero of real part
  `> Re ρ − ε` at height `|Im| > T`. This is exactly the zero-level conclusion of weak recurrence;
  AAL carries no more and no less.
- Vertical recurrence ⇒ AAL. Curves (periodic, Kronecker rank one) and zero sets of exponential
  polynomials (finite rank) satisfy AAL unconditionally.
- For a curve datum in the strip: AAL holds; ZAL ⇔ pure ⇔ unitary. Odd hyperelliptic curves: all
  three hold.
- ζ: the configuration laws are `AsymptoticAbscissaLaw` and `ZerosApproachLine`.
- The configuration FE does not give B13: for every `½ < Re ρ < 1` the two-point configuration
  `{ρ, 1 − ρ̄}` approaches the line, is reflection-symmetric, and violates AAL at `h = 0`.

**Correction of the [D] matching.** In the coordinates where both laws are stated (the `s`-plane),
the curve proof's split is the opposite of the reading `Stepanov ↔ ZAL, power sums ↔ AAL`: AAL is
supplied for free by the Frobenius (periodicity of the zeros in height), and ZAL is the whole
content, proved by Stepanov plus power sums plus FE. Over ℤ, AAL is the trace of the missing
Frobenius periodicity; weak recurrence is its function-level shadow, and AAL equals its zero-level
shadow. The JAS shell criterion reads the same proof in the Frobenius-eigenvalue coordinate:
ZAL ↔ finite rank (free on curves), shell-sum growth ↔ Stepanov's count, Turán ↔ power sums.

## Log
- 2026-11-08 — created; F22 started.
