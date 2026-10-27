# Independent separated sections for ACS

- **ID:** acs-independent-separated-sections
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route ACS; `RHTower/SeparatedBumpWeilPositivity.lean`, `ArithmeticCastelnuovoSeveri/ArithmeticSectionSpace.lean`.
- **Statement:** For every fixed separation `s > 0` and `0 < κ < 2`, sufficiently narrow independent real C² profiles supported in intervals of width `δ`, with centres separated by `s` and span at most `κ log(1/δ)`, satisfy `W(f,f) ≥ ∫ f²`. Their whole linear section space has source Riemann–Roch and ampleness.

## Goal

Remove the common-profile restriction from separated-bump positivity. Allow arbitrary prime lags and independent local shapes, producing a linear section space for the original Weil pairing. The earlier common-profile theorem alone does not control cross terms between distinct local shapes. This does not give full-source coverage: the span remains below the pole scale.

## Gates

- [x] 0 → 1: source-defined statement and explicit analytic mechanism.
- [x] Dependency-closed proof checked in Lean.
- [x] Exact-file Lean check and transitive axiom audit; umbrella import.

## Proof

Write `f(u) = Σᵢ Gᵢ(u-xᵢ)` and `Eᵢ = ∫ Gᵢ²`. Disjoint supports give `∫ f² = Σᵢ Eᵢ`.

1. For `δ < t < s-δ`, the support misses its translate, so the translation-square integral is `2∫ f²`. The existing Lévy-window integral gives gain `exp(-s/2) log((s-δ)/δ)`.
2. Each mixed correlation is bounded by `(Eᵢ+Eⱼ)/2` and vanishes outside its alignment window. Symmetry converts the prime pair-kernel sum into a weighted row sum. The source estimate `SeparatedBump.sum_pairKernel_le` bounds each row by
   `R = N·6δ(D+1)exp(D/2) + 8(2+2M/s) + 8N exp(-M/4)`, without exact-divisibility assumptions. Thus the entire prime contribution is at most `R Σᵢ Eᵢ`.
3. Each profile has `L1² ≤ δ Eᵢ`. After extracting centre exponentials, the two pole moments cost at most `2 exp(δ/2) exp(D/2) δ N Σᵢ Eᵢ`.
4. Put `L=log(1/δ)`, `c=exp(-s/2)` and `M=scL/64`. Packing gives `N≤2+κL/s`. The pole and long-distance prime losses tend to zero for `κ<2`, while the near-distance prime loss is `16+cL/4`. The Lévy gain is at least `c(L+log(s/2))`. The source lemmas `SeparatedBump.exists_margin` and `SeparatedBump.coefficient_nonneg`, used with constant term `gammaBracket(0)-1`, therefore leave one full unit of square mass for sufficiently small positive `δ`.
5. Apply the existing source L²-cone construction to the linear carrier of all these independent profiles.

## Status

Lean implementation: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/IndependentSeparatedSections.lean`.
Main declarations: `SeparatedSections.le_weil_sectionSum`,
`SeparatedSections.exists_integral_sq_le_weil_sectionSum`, and
`SeparatedSections.exists_separatedSections_effectivity`.

Verified from `formal/`:

```sh
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/IndependentSeparatedSections.lean
```

Exit 0, no warnings. All three declarations above have transitive axioms exactly
`[propext, Classical.choice, Quot.sound]`. Module imported by `ArithmeticCastelnuovoSeveri.lean`;
umbrella not compiled. Card moved directly from in-progress to formalized.

Full-source ACS effectivity remains open. The theorem supplies RR, ampleness, and Hodge index
on these whole linear carriers, not on unrestricted compactly supported tests.
