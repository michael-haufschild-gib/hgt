/-
# The polarization weld: a compatible complex structure pins the negative index into pairs

This links the polarization surface (`OmegaComplexStructure` — a real-linear `J` with `J² = -1`
preserving a symmetric form `Q`, the algebraic face of the weld `J`) to the negative index that
decides definiteness (`SeamSpectralFlow`'s `KreinNonneg`, the real face here).

The lever is `Q_apply_span_self_of_isSymm`: on the forced `J`-plane `span{x, J x}`, a symmetric
preserved form is `Q(a·x + b·J x, a·x + b·J x) = (a² + b²)·Q(x,x)` — a scalar multiple of the
Euclidean form.  So the sign of `Q` on the whole plane is the sign of `Q(x,x)`: **one negative
direction `x` forces the entire two-plane `span{x, J x}` to be negative-definite.**

Consequently a `J`-polarized indefinite form cannot carry an *odd* sliver of negativity: negativity
comes welded in `J`-pairs.  In the seam picture this is the functional equation's conjugate-pairing
of off-line zeros, read as a constraint imposed by the polarization `J` rather than propagated: a
single off-line direction drags in its `J`-partner, so the negative index is `0` or `≥ 2`, never `1`.
No carrier is built; the polarization is a *given* compatible structure and the pairing is what it
forces on the negative cone.
-/
import GaloisForLFunctions.RHTower.OmegaComplexStructure
import GaloisForLFunctions.RHTower.SeamSpectralFlow

open GaloisForLFunctions GaloisForLFunctions.RHTower

namespace RHTower

/-- `Set.range ![x, y] = {x, y}` — the two-element range as a pair. -/
theorem range_pair_eq {V : Type*} (x y : V) : Set.range ![x, y] = {x, y} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- **The forced `J`-plane of a negative direction is negative-definite.**  For a symmetric
preserved form `Q` and its polarization `J`, if `Q(x,x) < 0` then every nonzero vector of the
two-plane `span{x, J x}` has `Q(y,y) < 0`: on that plane `Q = (a² + b²)·Q(x,x)`, so the sign is
constant.  A single negative direction drags its `J`-partner into a whole negative-definite plane. -/
theorem polarized_negDef_plane {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    (hQ : Q.IsSymm) {x : V} (hx : Q x x < 0) :
    ∀ y ∈ Submodule.span ℝ ({x, P.complex.J x} : Set V), y ≠ 0 → Q y y < 0 := by
  intro y hy hy0
  rw [Submodule.mem_span_pair] at hy
  obtain ⟨a, b, rfl⟩ := hy
  rw [P.Q_apply_span_self_of_isSymm hQ]
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    rw [not_or, not_ne_iff, not_ne_iff] at h
    exact hy0 (by rw [h.1, h.2]; simp)
  have hpos : 0 < a * a + b * b := by
    rcases hab with ha | hb
    · nlinarith [mul_self_pos.mpr ha, mul_self_nonneg b]
    · nlinarith [mul_self_pos.mpr hb, mul_self_nonneg a]
  exact mul_neg_of_pos_of_neg hpos hx

/-- The forced `J`-plane has real dimension `2` (`x` and `J x` are independent). -/
theorem polarized_negDef_plane_finrank {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    {x : V} (hx : x ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ ({x, P.complex.J x} : Set V)) = 2 := by
  have hli : LinearIndependent ℝ ![x, P.complex.J x] := P.complex.linearIndependent_pair hx
  have hc := finrank_span_eq_card hli
  rw [range_pair_eq] at hc
  simpa using hc

/-- **Polarization pins negativity in pairs: a negative direction forces a 2-dimensional
negative-definite subspace.**  Hence for a `J`-polarized symmetric form the negative index is `0`
or `≥ 2` — never an odd sliver.  This is the functional equation's conjugate-pairing of off-line
zeros, imposed by the polarization `J` as a constraint on the negative cone. -/
theorem polarized_exists_two_dim_negDef {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    (hQ : Q.IsSymm) {x : V} (hx : Q x x < 0) :
    ∃ W : Submodule ℝ V, Module.finrank ℝ W = 2 ∧ ∀ y ∈ W, y ≠ 0 → Q y y < 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  exact ⟨Submodule.span ℝ ({x, P.complex.J x} : Set V),
    polarized_negDef_plane_finrank P hx0, polarized_negDef_plane P hQ hx⟩

/-- **A `J`-invariant subspace has even real dimension** — the parity lever.  If `J w ∈ W` for every
`w ∈ W`, then `J` restricts to a complex structure on `W` (`J'² = -1`), so `W` is even-dimensional
(`OmegaComplexStructure.finrank_even`).  The negative cone the polarization builds is filled by such
`J`-invariant blocks; each carries an even chunk of negative index. -/
theorem Jinvariant_subspace_finrank_even {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (C : OmegaComplexStructure V) {W : Submodule ℝ V}
    (hW : ∀ w ∈ W, C.J w ∈ W) :
    Even (Module.finrank ℝ W) := by
  let J' : W →ₗ[ℝ] W := LinearMap.restrict C.J hW
  have hsq : J'.comp J' = -LinearMap.id := by
    ext w
    have h : C.J (C.J (w : V)) = -(w : V) := C.apply_sq w
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq,
      Submodule.coe_neg, J', LinearMap.coe_restrict_apply]
    exact h
  exact (OmegaComplexStructure.mk J' hsq).finrank_even

/-- The forced `J`-plane `span{x, J x}` is `J`-invariant: `J` sends its generators back into it
(`J·x = J x`, `J·(J x) = -x`).  So it is one of the even-dimensional `J`-blocks of the negative
cone — consistent with its dimension `2`. -/
theorem polarized_plane_Jinvariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) (x : V) :
    ∀ w ∈ Submodule.span ℝ ({x, C.J x} : Set V), C.J w ∈
      Submodule.span ℝ ({x, C.J x} : Set V) := by
  intro w hw
  rw [Submodule.mem_span_pair] at hw
  obtain ⟨a, b, rfl⟩ := hw
  rw [Submodule.mem_span_pair]
  refine ⟨-b, a, ?_⟩
  rw [map_add, map_smul, map_smul, C.apply_sq]
  module

end RHTower
