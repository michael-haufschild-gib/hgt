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

/-! ### Structural lemmas toward the signature decomposition (Sylvester for `J`-forms) -/

/-- A nondegenerate symmetric form on a nonzero space has a non-isotropic vector: were `Q(x,x) = 0`
for all `x`, symmetry (`char ≠ 2`) forces `Q = 0`, contradicting nondegeneracy. -/
theorem exists_self_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (hQ : Q.IsSymm) (hnd : Q.Nondegenerate)
    {v0 : V} (hv0 : v0 ≠ 0) :
    ∃ x, Q x x ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hzero : ∀ x y, Q x y = 0 := by
    intro x y
    have hxy := h (x + y)
    have hexp : Q (x + y) (x + y) = Q x x + Q x y + Q y x + Q y y := by
      simp only [map_add, LinearMap.add_apply]; ring
    rw [hexp, h x, h y] at hxy
    have hsymm : Q y x = Q x y := hQ.eq y x
    rw [hsymm] at hxy
    linarith
  exact hv0 (hnd.1 v0 (fun w => hzero v0 w))

/-- **The orthogonal complement of a `J`-invariant subspace is `J`-invariant.**  `J` is
`Q`-skew-adjoint (`Q x (J y) = -Q (J x) y`), so if `v ⊥ U` and `U` is `J`-invariant then
`Q u (J v) = -Q (J u) v = 0` for every `u ∈ U` (as `J u ∈ U`), i.e. `J v ⊥ U`. -/
theorem orthogonal_Jinvariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    {U : Submodule ℝ V} (hU : ∀ u ∈ U, P.complex.J u ∈ U) :
    ∀ v ∈ Q.orthogonal U, P.complex.J v ∈ Q.orthogonal U := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro u hu
  rw [LinearMap.BilinForm.isOrtho_def] at *
  have key : Q u (P.complex.J v) = -Q (P.complex.J u) v := P.Q_right_J_eq_neg_Q_J_left u v
  rw [key, hv (P.complex.J u) (hU u hu), neg_zero]

/-- **The forced `J`-plane is nondegenerate when `Q(x,x) ≠ 0`.**  On `span{x, J x}`, `Q` is the
dot product times `Q(x,x)` (`Q_apply_span_pair_of_isSymm`), so its Gram is `Q(x,x)·I₂` —
nondegenerate exactly when `Q(x,x) ≠ 0`. -/
theorem plane_restrict_nondegenerate {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm)
    {x : V} (hxQ : Q x x ≠ 0) :
    (Q.restrict (Submodule.span ℝ ({x, P.complex.J x} : Set V))).Nondegenerate := by
  set W := Submodule.span ℝ ({x, P.complex.J x} : Set V) with hW
  have hxW : x ∈ W := Submodule.subset_span (by simp)
  have hJxW : P.complex.J x ∈ W := Submodule.subset_span (by simp)
  have key : ∀ v : ↥W, (∀ w : ↥W, Q (v : V) (w : V) = 0) → (v : V) = 0 := by
    intro v hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp v.2
    have hvx : Q (v : V) x = a * Q x x := by
      rw [← hab]; simpa using P.Q_apply_span_pair_of_isSymm hQ x a b 1 0
    have hvJx : Q (v : V) (P.complex.J x) = b * Q x x := by
      rw [← hab]; simpa using P.Q_apply_span_pair_of_isSymm hQ x a b 0 1
    have h1 : a * Q x x = 0 := by rw [← hvx]; exact hv ⟨x, hxW⟩
    have h2 : b * Q x x = 0 := by rw [← hvJx]; exact hv ⟨P.complex.J x, hJxW⟩
    have ha : a = 0 := (mul_eq_zero.mp h1).resolve_right hxQ
    have hb : b = 0 := (mul_eq_zero.mp h2).resolve_right hxQ
    rw [← hab, ha, hb]; simp
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · exact Subtype.ext (key v (fun w => by
      have := hv w; simpa [LinearMap.BilinForm.restrict_apply] using this))
  · refine Subtype.ext (key v (fun w => ?_))
    have := hv w
    rw [LinearMap.BilinForm.restrict_apply] at this
    rw [hQ.eq (v : V) (w : V)]
    exact this

/-- `J` restricted to a `J`-invariant subspace is again a complex structure (`J'² = -1`). -/
def omegaRestrict {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) {W : Submodule ℝ V} (hW : ∀ w ∈ W, C.J w ∈ W) :
    OmegaComplexStructure W where
  J := LinearMap.restrict C.J hW
  sq := by
    ext w
    have h : C.J (C.J (w : V)) = -(w : V) := C.apply_sq w
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq,
      Submodule.coe_neg, LinearMap.coe_restrict_apply]
    exact h

/-- The restricted `J` preserves the restricted form: `polarizedRestrict` transports the whole
polarization to a `J`-invariant subspace, so the decomposition recursion stays inside the class. -/
theorem polarizedRestrict_preserves {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    {W : Submodule ℝ V} (hW : ∀ w ∈ W, P.complex.J w ∈ W) :
    PreservesBilin (Q.restrict W) (omegaRestrict P.complex hW).J := by
  intro x y
  simp only [omegaRestrict, LinearMap.BilinForm.restrict_apply, LinearMap.coe_restrict_apply]
  exact P.preserves (x : V) (y : V)

/-- **The polarization restricts to any `J`-invariant subspace.**  The inductive object for the
signature decomposition: peel a `J`-plane, land in its orthogonal complement (again `J`-invariant),
carry the whole polarized structure along. -/
def polarizedRestrict {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    {W : Submodule ℝ V} (hW : ∀ w ∈ W, P.complex.J w ∈ W) :
    PolarizedOmegaComplexStructure W (Q.restrict W) where
  complex := omegaRestrict P.complex hW
  preserves := polarizedRestrict_preserves P hW

end RHTower
