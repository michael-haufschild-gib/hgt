# Quasi-RH is a tail law

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0911/fable.md`, §11.6.
- **Module:** `ZeroConfigurationGeometry/AbscissaLaws/QuasiRHIsATailLaw.lean`.

## Statements

Writing Θ for the global zero abscissa and Θ∞ for the asymptotic abscissa:

- `quasiRH_of_not_asymptoticAbscissaLaw`: ¬AAL ⇒ Θ < 1.
- `quasiRH_or_asymptoticAbscissaLaw`: Θ < 1 ∨ AAL.
- `quasiRH_iff_zetaAsymptoticAbscissa_lt_one`: Θ < 1 ⇔ Θ∞ < 1.
- `not_quasiRH_iff_abscissas_eq_one`: ¬(Θ < 1) ⇔ Θ = 1 ∧ Θ∞ = 1 ∧ AAL.

## Proof

The bilateral spectral-gap theorem gives, under ¬AAL, a top abscissa β < 1
with no zeros to its right. Hence Θ ≤ β < 1. This proves the dichotomy.
Since Θ∞ ≤ Θ, quasi-RH implies Θ∞ < 1. Conversely, in the AAL branch,
Θ = Θ∞; the other branch already gives quasi-RH. The failure statement
then follows from Θ ≤ 1.

These are assemblies of existing spectral-gap and abscissa results; no claim
of new analytic input or proof of quasi-RH.

## Verification

Direct `lake --old env lean` check exited 0. All four transitive axiom reports:
`propext`, `Classical.choice`, `Quot.sound`. Imported by `ZeroConfigurationGeometry.lean`.
