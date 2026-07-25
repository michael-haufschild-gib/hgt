import GaloisForLFunctions.HTGeometry.GeneralKoszulComplex

/-!
# Degree-2 Koszul homology module structure of the 4-cycle

Opening the higher-`Tor` (`i ≥ 2`) arc of Hochster's formula, this file gives the module structure of
the `4`-cycle `Tor₂` class in the general vertex-Koszul homology (over a field `F`), mirroring the
degree-1 hollow-simplex embedding.  Over a field the homology is an `F`-vector space, so the nonzero
`C₄` class (`srC4KoszulTor_ne_zero`) is torsion-free and spans a free rank-one `F`:

- `srC4KoszulTorClass` — the `C₄` degree-2 homology class.
- `srC4KoszulTor_smul_ne_zero` — `r · [C₄] ≠ 0` for `r ≠ 0` (torsion-free over `F`).
- `srC4KoszulTorEquiv` — `F ≃ₗ[F] F·[C₄]`, the free rank-one `F`-line the class spans in `Tor₂`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The degree-2 (second Koszul homology) class of the `4`-cycle `C₄` over a field `F`. -/
noncomputable def srC4KoszulTorClass (F : Type*) [Field F] (facets : Finset (Finset α)) (a b c d : α)
    (hac : a ≠ c) (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd : b ≠ d) (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    koszulTor (p := 1) (srVertexX F facets) :=
  Submodule.Quotient.mk ⟨srC4KoszulCycle facets a b c d,
    srC4KoszulCycle_mem_koszulCycles facets hac hac_nf hbd hbd_nf⟩

variable (F : Type*) [Field F] (facets : Finset (Finset α)) {a b c d : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (had : a ≠ d) (hac : a ≠ c) (hbd : b ≠ d)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d})

include hab hbc hcd had ha hb hc hd hab_f hbc_f hcd_f had_f

/-- The `C₄` degree-2 homology class is nonzero. -/
theorem srC4KoszulTorClass_ne_zero :
    srC4KoszulTorClass F facets a b c d hac hac_nf hbd hbd_nf ≠ 0 :=
  srC4KoszulTor_ne_zero facets hab hbc hcd had hac hbd ha hb hc hd hab_f hbc_f hcd_f had_f
    hac_nf hbd_nf

/-- **Torsion-free.**  Over a field, a nonzero scalar multiple of the `C₄` `Tor₂` class is nonzero. -/
theorem srC4KoszulTor_smul_ne_zero {r : F} (hr : r ≠ 0) :
    r • srC4KoszulTorClass F facets a b c d hac hac_nf hbd hbd_nf ≠ 0 := by
  rw [Ne, smul_eq_zero, not_or]
  exact ⟨hr, srC4KoszulTorClass_ne_zero F facets hab hbc hcd had hac hbd ha hb hc hd hab_f hbc_f
    hcd_f had_f hac_nf hbd_nf⟩

/-- **Degree-2 embedding.**  The `C₄` `Tor₂` class spans a free rank-one `F`-module inside the second
Koszul homology: `F ≃ₗ[F] F·[C₄]`. -/
noncomputable def srC4KoszulTorEquiv :
    F ≃ₗ[F] ↥(LinearMap.range (LinearMap.toSpanSingleton F (koszulTor (p := 1) (srVertexX F facets))
      (srC4KoszulTorClass F facets a b c d hac hac_nf hbd hbd_nf))) :=
  LinearEquiv.ofInjective _ (by
    intro r r' h
    simp only [LinearMap.toSpanSingleton_apply] at h
    rcases smul_eq_zero.mp (show (r - r') • srC4KoszulTorClass F facets a b c d hac hac_nf hbd hbd_nf
        = 0 from by rw [sub_smul, h, sub_self]) with hr0 | hbase
    · exact sub_eq_zero.mp hr0
    · exact absurd hbase (srC4KoszulTorClass_ne_zero F facets hab hbc hcd had hac hbd ha hb hc hd
        hab_f hbc_f hcd_f had_f hac_nf hbd_nf))

end GaloisForLFunctions.HTGeometry
