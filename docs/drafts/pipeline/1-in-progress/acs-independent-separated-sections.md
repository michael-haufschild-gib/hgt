# Independent separated sections for ACS

- **ID:** acs-independent-separated-sections
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Route ACS; `RHTower/SeparatedBumpWeilPositivity.lean`, `ArithmeticCastelnuovoSeveri/ArithmeticSectionSpace.lean`.
- **Statement:** For every fixed separation `s > 0` and `0 < κ < 2`, sufficiently narrow independent real C² profiles supported in intervals of width `δ`, with centres separated by `s` and span at most `κ log(1/δ)`, satisfy `W(f,f) ≥ ∫ f²`. Their whole linear section space has source Riemann–Roch and ampleness.

## Goal

Remove the common-profile restriction from separated-bump positivity. Allow arbitrary prime lags and independent local shapes, producing a linear section space for the original Weil pairing. This does not give full-source coverage: the span remains below the pole scale.

## Gates

- [x] 0 → 1: source-defined statement and explicit analytic mechanism.
- [ ] Dependency-closed proof checked in Lean.
- [ ] Exact-file Lean check and transitive axiom audit; umbrella import.

## Proof mechanism under formalization

Write `f(u) = Σᵢ Gᵢ(u-xᵢ)` and `Eᵢ = ∫ Gᵢ²`. Disjoint supports give `∫ f² = Σᵢ Eᵢ`.

1. For `δ < t < s-δ`, the support misses its translate, so the translation-square integral is `2∫ f²`. The existing Lévy-window integral gives gain `exp(-s/2) log((s-δ)/δ)`.
2. Each mixed correlation is bounded by `(Eᵢ+Eⱼ)/2` and vanishes outside its alignment window. Symmetry converts the prime pair-kernel sum into a weighted row sum. Existing arithmetic node estimates bound those rows without exact-divisibility assumptions.
3. Each profile has `L1² ≤ δ Eᵢ`. After extracting centre exponentials, the two pole moments cost at most `2 exp(δ/2) exp(D/2) δ N Σᵢ Eᵢ`.
4. The existing asymptotic coefficient estimate, used with constant term `gammaBracket(0)-1`, leaves one full unit of square mass when `D ≤ κ log(1/δ)`, `κ < 2`.
5. Apply the existing source L²-cone construction to the linear carrier of all these independent profiles.

## Status

Lean implementation: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/IndependentSeparatedSections.lean`.
Main declarations: `SeparatedSections.le_weil_sectionSum`,
`SeparatedSections.exists_integral_sq_le_weil_sectionSum`, and
`SeparatedSections.exists_separatedSections_effectivity`.

Exact-file checking and axiom audits are pending. No proof claimed until those pass.
Full-source ACS effectivity remains open.
