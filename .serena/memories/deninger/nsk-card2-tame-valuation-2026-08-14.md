# Card 2: `TameData` is now constructed from a real valuation (2026-08-14)

`formal/GaloisForLFunctions/HTGeometry/MilnorKTameValuation.lean` — compiles clean, axioms
`propext, Classical.choice, Quot.sound`, wired into `HTGeometry.lean`.

Given `v : Valuation K (WithZero (Multiplicative ℤ))` on a field:
- `tame_v_ne_zero`, `tameUnzero`, `coe_tameUnzero`;
- **`tameValHom : Kˣ →* Multiplicative ℤ`** — the INVERSE of the multiplicative value, so that
  maximal-ideal elements get positive additive valuation (this normalization is forced by the
  `TameData` clauses);
- `tameValHom_mem_ker_iff` (`ker ↔ v a = 1`), `tameValHom_pos_iff` (`↔ v a < 1`),
  `tameValHom_neg_iff` (`↔ 1 < v a`), `tameValHom_congr`;
- `tame_mem_valuationSubring`, `tame_inv_mem_valuationSubring`, `tameUnit`, `tameUnit_one`,
  `tameUnit_mul`, **`tameResHom`**, `tameResHom_val`;
- `tame_mem_maximalIdeal` (value `< 1` ⇒ nonunit), `tame_residue_eq_zero`;
- `tameResHom_neg_one`, **`tame_oneSub_of_pos`**, **`tame_oneSub_of_zero`**,
  **`tame_oneSub_of_neg`**;
- **`tameDataOfValuation : TameData K (IsLocalRing.ResidueField v.valuationSubring)`**;
- **`tameHomOfValuation : MilnorKDeg K 2 →+ Additive (ResidueField v.valuationSubring)ˣ`**.

Mathlib names used: `Valuation.ne_zero_iff`, `WithZero.unzero/coe_unzero/coe_inj/coe_lt_one/one_lt_coe`,
`Valuation.mem_valuationSubring_iff`, `Valuation.map_one_sub_of_lt`,
`Valuation.map_add_of_distinct_val`, `Valuation.map_sub`, `Valuation.map_inv`,
`Valuation.map_neg`, `Valuation.one_lt_val_iff`, `IsLocalRing.mem_maximalIdeal`,
`IsLocalRing.residue`, `Ideal.Quotient.eq_zero_iff_mem`.  Note `map_neg`/`map_sub`/`map_one` are
ambiguous with the `Valuation` namespace open — qualify with `_root_.`.

NEXT: apply `tameDataOfValuation` to `IsDedekindDomain.HeightOneSpectrum.valuation` of a number
field (its value group is already `ℤₘ₀`), and prove that a fixed pair `{a,b}` is a unit pair at all
but finitely many places (`tame_eq_one_of_mem_ker`), giving unconditionally: some nonzero multiple
of every `{a,b}` lies in the tame kernel.

RESIDUAL DEEP INPUT (unchanged): the tame kernel of a number field is torsion — Garland /
Quillen+Borel.
