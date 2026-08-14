# Card 2: tame symbols at the finite places (2026-08-14)

`formal/GaloisForLFunctions/HTGeometry/MilnorKTameDedekind.lean` — compiles clean, axioms
`propext, Classical.choice, Quot.sound`, wired into `HTGeometry.lean`.

For `R` a Dedekind domain with fraction field `K` and `v : IsDedekindDomain.HeightOneSpectrum R`:
- `tameDataAtPlace K v := tameDataOfValuation (v.valuation K)` — works because
  `v.valuation K : Valuation K ℤᵐ⁰` and `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`.
- **`tameHomAtPlace K v : MilnorKDeg K 2 →+ Additive (ResidueField (v.valuation K).valuationSubring)ˣ`**
- `finite_valuation_ne_one` — `{v | v.valuation K a ≠ 1}` is finite, via
  `IsDedekindDomain.HeightOneSpectrum.Support.finite` applied to `a` and `a⁻¹`
  (`Support R k = {v | 1 < v.valuation K k}`) and `Valuation.one_lt_val_iff`.
- **`finite_tame_ne_one`**, **`finite_tameHomAtPlace_ne_zero`** — a fixed pair of units, and its
  symbol class, has trivial tame symbol at all but finitely many places.

STATUS OF CARD 2's CHAIN — everything is unconditional except one classical statement:
`hNF : every degree-two Milnor class of a number field is torsion`.
Tame symbols see only torsion (finite residue fields) and have finite support; the residual content
is precisely that the TAME KERNEL is torsion = Garland's finiteness / Borel `rank K_2(O_K) = 0`.
Repeated literature checks (through July 2026) find no elementary proof; Tate's Euclidean argument
covers only `ℚ`, Bass–Tate's `(ℤ/2)^{r_1}` result is for `n ≥ 3`, Moore's theorem reduces to the
wild kernel whose finiteness is again Tate.  A proposed elementary mechanism — "Steinberg relations
among S-units span `Λ²(O_S^×) ⊗ ℚ`" — is FALSE: number fields with unit rank ≥ 2 and no exceptional
units have no such relations at all, so the vanishing must come from symbols involving non-units,
which is exactly what the Euclidean algorithm supplies for `ℚ` and what fails in general.

Not yet built (would need identifying `ResidueField (v.valuation K).valuationSubring ≅ R ⧸ v.asIdeal`):
finiteness of the residue field for a number field, hence an explicit common annihilator putting
`n • {a,b}` in the tame kernel.
