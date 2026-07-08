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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

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

/-! ### The signature decomposition and the even negative index -/

/-- The positive twin of `polarized_negDef_plane`: a positive direction's `J`-plane is
positive-definite. -/
theorem polarized_posDef_plane {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    (hQ : Q.IsSymm) {x : V} (hx : 0 < Q x x) :
    ∀ y ∈ Submodule.span ℝ ({x, P.complex.J x} : Set V), y ≠ 0 → 0 < Q y y := by
  intro y hy hy0
  rw [Submodule.mem_span_pair] at hy
  obtain ⟨a, b, rfl⟩ := hy
  rw [P.Q_apply_span_self_of_isSymm hQ]
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; rw [not_or, not_ne_iff, not_ne_iff] at h; exact hy0 (by rw [h.1, h.2]; simp)
  have hpos : 0 < a * a + b * b := by
    rcases hab with ha | hb
    · nlinarith [mul_self_pos.mpr ha, mul_self_nonneg b]
    · nlinarith [mul_self_pos.mpr hb, mul_self_nonneg a]
  exact mul_pos hpos hx

/-- A sup of two `J`-invariant subspaces is `J`-invariant. -/
theorem sup_Jinvariant {V : Type*} [AddCommGroup V] [Module ℝ V] (C : OmegaComplexStructure V)
    {A B : Submodule ℝ V} (hA : ∀ w ∈ A, C.J w ∈ A) (hB : ∀ w ∈ B, C.J w ∈ B) :
    ∀ w ∈ A ⊔ B, C.J w ∈ A ⊔ B := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact Submodule.add_mem_sup (hA a ha) (hB b hb)

/-- `J`-invariance transfers to a subspace lifted from a `J`-invariant subspace. -/
theorem map_Jinvariant {V : Type*} [AddCommGroup V] [Module ℝ V] (C : OmegaComplexStructure V)
    {W : Submodule ℝ V} (hWJ : ∀ w ∈ W, C.J w ∈ W) {NW : Submodule ℝ W}
    (hNWJ : ∀ w ∈ NW, (omegaRestrict C hWJ).J w ∈ NW) :
    ∀ y ∈ Submodule.map W.subtype NW, C.J y ∈ Submodule.map W.subtype NW := by
  intro y hy
  obtain ⟨w, hwNW, rfl⟩ := Submodule.mem_map.mp hy
  exact Submodule.mem_map.mpr ⟨(omegaRestrict C hWJ).J w, hNWJ w hwNW, by
    simp [omegaRestrict, LinearMap.coe_restrict_apply]⟩

/-- Negative-definiteness transfers from a subspace of `W` (under `Q.restrict W`) to its lift. -/
theorem restrict_map_negDef {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} {W : Submodule ℝ V} {NW : Submodule ℝ W}
    (hNW : ∀ y ∈ NW, y ≠ 0 → (Q.restrict W) y y < 0) :
    ∀ y ∈ Submodule.map W.subtype NW, y ≠ 0 → Q y y < 0 := by
  intro y hy hy0
  obtain ⟨w, hwNW, rfl⟩ := Submodule.mem_map.mp hy
  have hw0 : w ≠ 0 := fun h => hy0 (by rw [h]; simp)
  have := hNW w hwNW hw0
  rwa [LinearMap.BilinForm.restrict_apply] at this

/-- Positive-definiteness transfers from a subspace of `W` (under `Q.restrict W`) to its lift. -/
theorem restrict_map_posDef {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} {W : Submodule ℝ V} {NW : Submodule ℝ W}
    (hNW : ∀ y ∈ NW, y ≠ 0 → 0 < (Q.restrict W) y y) :
    ∀ y ∈ Submodule.map W.subtype NW, y ≠ 0 → 0 < Q y y := by
  intro y hy hy0
  obtain ⟨w, hwNW, rfl⟩ := Submodule.mem_map.mp hy
  have hw0 : w ≠ 0 := fun h => hy0 (by rw [h]; simp)
  have := hNW w hwNW hw0
  rwa [LinearMap.BilinForm.restrict_apply] at this

/-- Negative-definiteness on an orthogonal sum: needs only symmetry and cross-orthogonality
(`Q a b = 0`), not disjointness — the two decompositions add. -/
theorem negDef_sup {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : LinearMap.BilinForm ℝ V}
    (hsymm : Q.IsSymm) {A B : Submodule ℝ V}
    (hA : ∀ y ∈ A, y ≠ 0 → Q y y < 0) (hB : ∀ y ∈ B, y ≠ 0 → Q y y < 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Q a b = 0) :
    ∀ y ∈ A ⊔ B, y ≠ 0 → Q y y < 0 := by
  intro y hy hy0
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  have hc : Q a b = 0 := hAB a ha b hb
  have hc' : Q b a = 0 := by rw [hsymm.eq b a]; exact hc
  have hexp : Q (a + b) (a + b) = Q a a + Q b b := by
    simp only [map_add, LinearMap.add_apply]; rw [hc, hc']; ring
  rw [hexp]
  rcases eq_or_ne a 0 with h | h
  · have hb0 : b ≠ 0 := by rintro rfl; simp [h] at hy0
    have : Q a a = 0 := by rw [h]; simp
    nlinarith [hB b hb hb0]
  · rcases eq_or_ne b 0 with h2 | h2
    · have : Q b b = 0 := by rw [h2]; simp
      nlinarith [hA a ha h]
    · nlinarith [hA a ha h, hB b hb h2]

/-- Positive-definiteness on an orthogonal sum (positive twin of `negDef_sup`). -/
theorem posDef_sup {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : LinearMap.BilinForm ℝ V}
    (hsymm : Q.IsSymm) {A B : Submodule ℝ V}
    (hA : ∀ y ∈ A, y ≠ 0 → 0 < Q y y) (hB : ∀ y ∈ B, y ≠ 0 → 0 < Q y y)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Q a b = 0) :
    ∀ y ∈ A ⊔ B, y ≠ 0 → 0 < Q y y := by
  intro y hy hy0
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  have hc : Q a b = 0 := hAB a ha b hb
  have hc' : Q b a = 0 := by rw [hsymm.eq b a]; exact hc
  have hexp : Q (a + b) (a + b) = Q a a + Q b b := by
    simp only [map_add, LinearMap.add_apply]; rw [hc, hc']; ring
  rw [hexp]
  rcases eq_or_ne a 0 with h | h
  · have hb0 : b ≠ 0 := by rintro rfl; simp [h] at hy0
    have : Q a a = 0 := by rw [h]; simp
    nlinarith [hB b hb hb0]
  · rcases eq_or_ne b 0 with h2 | h2
    · have : Q b b = 0 := by rw [h2]; simp
      nlinarith [hA a ha h]
    · nlinarith [hA a ha h, hB b hb h2]

/-- Complementarity assembly: if `plane ⊕ W` and `W = Nl ⊕ Pl`, then `(plane ⊔ Nl) ⊕ Pl`. -/
theorem isCompl_planeExtend {V : Type*} [AddCommGroup V] [Module ℝ V]
    {plane W Nl Pl : Submodule ℝ V}
    (hpw : IsCompl plane W) (hNsup : Nl ⊔ Pl = W) (hNinf : Nl ⊓ Pl = ⊥)
    (hNl : Nl ≤ W) (hPl : Pl ≤ W) : IsCompl (plane ⊔ Nl) Pl := by
  have h1 : (plane ⊔ Nl) ⊓ W = Nl := by
    rw [sup_comm plane Nl, sup_inf_assoc_of_le plane hNl,
        disjoint_iff.mp hpw.disjoint, sup_bot_eq]
  constructor
  · rw [disjoint_iff]
    calc (plane ⊔ Nl) ⊓ Pl = (plane ⊔ Nl) ⊓ (W ⊓ Pl) := by rw [inf_eq_right.mpr hPl]
      _ = ((plane ⊔ Nl) ⊓ W) ⊓ Pl := by rw [inf_assoc]
      _ = Nl ⊓ Pl := by rw [h1]
      _ = ⊥ := hNinf
  · rw [codisjoint_iff, sup_assoc, hNsup]
    exact codisjoint_iff.mp hpw.codisjoint

/-- Complementary subspaces of `W` lift to a sup equal to `W`. -/
theorem lift_sup {V : Type*} [AddCommGroup V] [Module ℝ V] {W : Submodule ℝ V}
    {NW PW : Submodule ℝ W} (h : IsCompl NW PW) :
    Submodule.map W.subtype NW ⊔ Submodule.map W.subtype PW = W := by
  rw [← Submodule.map_sup, h.codisjoint.eq_top, Submodule.map_subtype_top]

/-- Disjoint subspaces of `W` lift to disjoint subspaces (`W.subtype` injective). -/
theorem lift_inf {V : Type*} [AddCommGroup V] [Module ℝ V] {W : Submodule ℝ V}
    {NW PW : Submodule ℝ W} (h : IsCompl NW PW) :
    Submodule.map W.subtype NW ⊓ Submodule.map W.subtype PW = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzN, hzP⟩
  obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.mp hzN
  obtain ⟨p, hp, hpn⟩ := Submodule.mem_map.mp hzP
  have hnp : n = p := W.subtype_injective hpn.symm
  have : n ∈ NW ⊓ PW := ⟨hn, hnp ▸ hp⟩
  rw [h.disjoint.eq_bot] at this
  simp only [Submodule.mem_bot] at this
  simp [this]

/-- Every vector of the plane is `Q`-orthogonal to every vector of `Q.orthogonal plane`. -/
theorem plane_orthogonal_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} {plane : Submodule ℝ V} {m : V}
    (hm : m ∈ Q.orthogonal plane) : ∀ p ∈ plane, Q p m = 0 := by
  intro p hp
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm
  have := hm p hp
  rwa [LinearMap.BilinForm.isOrtho_def] at this

/-- **The signature decomposition — Sylvester's law of inertia for a `J`-form.**  A nondegenerate
symmetric form with a compatible polarization `J` splits into two `J`-invariant, `Q`-orthogonally
complementary subspaces: `Nneg` (negative-definite) and `Npos` (positive-definite).  Proof by
strong induction on `finrank`: peel a non-isotropic `J`-plane (`polarized_{neg,pos}Def_plane`),
land in its `J`-invariant orthogonal complement (`orthogonal_Jinvariant`, again nondegenerate),
recurse, and reassemble along the sign of the plane. -/
theorem polarized_signature_decomp : ∀ (n : ℕ) {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q),
    Q.IsSymm → Q.Nondegenerate → Module.finrank ℝ V = n →
    ∃ Nneg Npos : Submodule ℝ V,
      (∀ w ∈ Nneg, P.complex.J w ∈ Nneg) ∧ (∀ w ∈ Npos, P.complex.J w ∈ Npos) ∧
      (∀ y ∈ Nneg, y ≠ 0 → Q y y < 0) ∧ (∀ y ∈ Npos, y ≠ 0 → 0 < Q y y) ∧
      IsCompl Nneg Npos := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ _ Q P hsymm hnd hn
    by_cases hV : ∃ x : V, x ≠ 0
    · obtain ⟨v0, hv0⟩ := hV
      obtain ⟨x, hxQ⟩ := exists_self_ne_zero hsymm hnd hv0
      have hx0 : x ≠ 0 := by rintro rfl; simp at hxQ
      set plane := Submodule.span ℝ ({x, P.complex.J x} : Set V) with hplane
      have hpJ : ∀ w ∈ plane, P.complex.J w ∈ plane := polarized_plane_Jinvariant P.complex x
      have hpnd : (Q.restrict plane).Nondegenerate := plane_restrict_nondegenerate P hsymm hxQ
      have hrefl : Q.IsRefl := hsymm.isRefl
      have hcompl : IsCompl plane (Q.orthogonal plane) :=
        LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hpnd
      set W := Q.orthogonal plane with hWdef
      have hWJ : ∀ w ∈ W, P.complex.J w ∈ W := orthogonal_Jinvariant P hpJ
      have hpf : Module.finrank ℝ plane = 2 := polarized_negDef_plane_finrank P hx0
      have hfr : Module.finrank ℝ plane + Module.finrank ℝ W = Module.finrank ℝ V :=
        Submodule.finrank_add_eq_of_isCompl hcompl
      have hWlt : Module.finrank ℝ W < n := by rw [← hn]; omega
      have hWnd : (Q.restrict W).Nondegenerate := by
        rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hrefl,
            LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
        exact hcompl.symm
      have hsymmW : (Q.restrict W).IsSymm := ⟨fun v w => by
        simp only [LinearMap.BilinForm.restrict_apply]; exact hsymm.eq (v : V) (w : V)⟩
      obtain ⟨NnegW, NposW, hNnegWJ, hNposWJ, hNnegWneg, hNposWpos, hNWcompl⟩ :=
        IH _ hWlt (polarizedRestrict P hWJ) hsymmW hWnd rfl
      set Nl := Submodule.map W.subtype NnegW with hNldef
      set Pl := Submodule.map W.subtype NposW with hPldef
      have hNlW : Nl ≤ W := Submodule.map_subtype_le W NnegW
      have hPlW : Pl ≤ W := Submodule.map_subtype_le W NposW
      have hNlsup : Nl ⊔ Pl = W := lift_sup hNWcompl
      have hNlinf : Nl ⊓ Pl = ⊥ := lift_inf hNWcompl
      have hNlJ : ∀ y ∈ Nl, P.complex.J y ∈ Nl := map_Jinvariant P.complex hWJ hNnegWJ
      have hPlJ : ∀ y ∈ Pl, P.complex.J y ∈ Pl := map_Jinvariant P.complex hWJ hNposWJ
      have hNlneg : ∀ y ∈ Nl, y ≠ 0 → Q y y < 0 := restrict_map_negDef hNnegWneg
      have hPlpos : ∀ y ∈ Pl, y ≠ 0 → 0 < Q y y := restrict_map_posDef hNposWpos
      have horth : ∀ p ∈ plane, ∀ m ∈ W, Q p m = 0 := fun p hp m hm =>
        plane_orthogonal_zero hm p hp
      rcases lt_or_gt_of_ne hxQ with hneg | hpos
      · refine ⟨plane ⊔ Nl, Pl, sup_Jinvariant P.complex hpJ hNlJ, hPlJ, ?_, hPlpos, ?_⟩
        · exact negDef_sup hsymm (polarized_negDef_plane P hsymm hneg) hNlneg
            (fun p hp m hm => horth p hp m (hNlW hm))
        · exact isCompl_planeExtend hcompl hNlsup hNlinf hNlW hPlW
      · refine ⟨Nl, plane ⊔ Pl, hNlJ, sup_Jinvariant P.complex hpJ hPlJ, hNlneg, ?_, ?_⟩
        · exact posDef_sup hsymm (polarized_posDef_plane P hsymm hpos) hPlpos
            (fun p hp m hm => horth p hp m (hPlW hm))
        · have hsup : Pl ⊔ Nl = W := by rw [sup_comm]; exact hNlsup
          have hinf : Pl ⊓ Nl = ⊥ := by rw [inf_comm]; exact hNlinf
          exact (isCompl_planeExtend hcompl hsup hinf hPlW hNlW).symm
    · simp only [not_exists, not_ne_iff] at hV
      have htop : (⊤ : Submodule ℝ V) = ⊥ := by
        ext v; simp only [Submodule.mem_top, Submodule.mem_bot, true_iff]; exact hV v
      refine ⟨⊥, ⊥, fun w _ => by rw [Submodule.mem_bot]; exact hV _,
        fun w _ => by rw [Submodule.mem_bot]; exact hV _, ?_, ?_, ?_⟩
      · intro y hy hy0; rw [Submodule.mem_bot] at hy; exact absurd hy hy0
      · intro y hy hy0; rw [Submodule.mem_bot] at hy; exact absurd hy hy0
      · refine ⟨by simp, ?_⟩
        rw [codisjoint_iff, sup_idem]; exact htop.symm

/-- **The negative index of a `J`-polarized nondegenerate symmetric form is even.**  From the
signature decomposition, the negative part `Nneg` is `J`-invariant (hence even-dimensional,
`Jinvariant_subspace_finrank_even`), it is negative-definite, and it dominates every
negative-definite subspace (any such is disjoint from the positive-definite `Npos`, so its dimension
is at most `finrank Nneg`).  Thus the negative index — the off-line zero count `κ₋` of the seam
Krein form — is forced **even**: under a polarization, off-line negativity occurs only in
`J`-conjugate pairs.  This is the functional equation's conjugate-pairing of zeros, obtained as a
rigidity of the compatible complex structure, not propagated by any flow. -/
theorem polarized_negIndex_even {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    (hsymm : Q.IsSymm) (hnd : Q.Nondegenerate) :
    ∃ Nneg : Submodule ℝ V, Even (Module.finrank ℝ Nneg) ∧
      (∀ y ∈ Nneg, y ≠ 0 → Q y y < 0) ∧
      (∀ U : Submodule ℝ V, (∀ y ∈ U, y ≠ 0 → Q y y < 0) →
        Module.finrank ℝ U ≤ Module.finrank ℝ Nneg) := by
  obtain ⟨Nneg, Npos, hNnegJ, _, hNnegneg, hNpospos, hcompl⟩ :=
    polarized_signature_decomp (Module.finrank ℝ V) P hsymm hnd rfl
  refine ⟨Nneg, Jinvariant_subspace_finrank_even P.complex hNnegJ, hNnegneg, ?_⟩
  intro U hU
  have hdisj : U ⊓ Npos = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rcases eq_or_ne z 0 with h | h
    · rw [h]; exact Submodule.zero_mem _
    · exact absurd (hNpospos z hz.2 h) (not_lt.mpr (le_of_lt (hU z hz.1 h)))
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq U Npos
  rw [hdisj] at hkey
  simp only [finrank_bot, add_zero] at hkey
  have hle : Module.finrank ℝ ((U ⊔ Npos : Submodule ℝ V)) ≤ Module.finrank ℝ V :=
    Submodule.finrank_le _
  have hV : Module.finrank ℝ Nneg + Module.finrank ℝ Npos = Module.finrank ℝ V :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  omega

end RHTower
