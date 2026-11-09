import GaloisForLFunctions.HyperbolicArakelovTheory.TheOppositeAdelicDegreeConfiguration
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# An adelic carrier retaining every original degree

Let `K_p` be the image of `GL₂(ℤ_p)` in `PGL₂(ℚ_p)`. The finite vertices are
actual cosets `PGL₂(ℚ_p)/K_p`, with finite support away from the standard vertex.
The rational diagonal group embeds discretely in `SL₂(ℂ) × ∏'_p PGL₂(ℚ_p)`.
Conjugate it by the Weyl element at every finite place and identity at infinity.
On the quotient by this discrete subgroup, every original point

  `x_n = (z_n, (diag(n,1)K_p)_p)`

has a distinct class, for all positive integers `n`.

The arithmetic input is quadratic integrality: a projectively integral local
matrix satisfies `‖Mᵢⱼ‖² ≤ ‖det M‖`. A rational matrix satisfying these conditions
at every prime has integer quotients `Mᵢⱼ²/det M`. An orbit between opposite
degree points forces `(m/n)²` to be an integer; the inverse orbit forces its
reciprocal to be an integer. Hence `m=n`. Finite Weyl conjugation transfers
this rigidity to the original configuration using the ordinary adelic action.

This establishes the projective vertex carrier and orbit injectivity.
A global Green operator and its Robin diagonal are not constructed here.
-/

set_option autoImplicit false
noncomputable section
open Matrix Set
namespace GaloisForLFunctions.HyperbolicArakelovTheory.FullAdelic
open SurfaceOfSpecZ OppositeAdelic
local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩
abbrev LocalGL (p : {p : ℕ // p.Prime}) := GL (Fin 2) ℚ_[p.1]
abbrev LocalPGL (p : {p : ℕ // p.Prime}) := Matrix.ProjGenLinGroup (Fin 2) ℚ_[p.1]

def integralMap (p : {p : ℕ // p.Prime}) : GL (Fin 2) ℤ_[p.1] →* LocalGL p :=
  GeneralLinearGroup.map PadicInt.Coe.ringHom

/-- Integral basis changes inside the local projective group. -/
def integralPGL (p : {p : ℕ // p.Prime}) : Subgroup (LocalPGL p) :=
  (ProjGenLinGroup.mk.comp (integralMap p)).range

private theorem norm_det_le_one (p : {p : ℕ // p.Prime}) (g : LocalGL p)
    (hg : ∀ i j, ‖g i j‖ ≤ 1) : ‖g.val.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two]
  have h := Padic.nonarchimedean (g 0 0 * g 1 1) (-(g 0 1 * g 1 0))
  rw [← sub_eq_add_neg, norm_neg, norm_mul, norm_mul] at h
  exact h.trans (max_le
    (mul_le_one₀ (hg 0 0) (norm_nonneg _) (hg 1 1))
    (mul_le_one₀ (hg 0 1) (norm_nonneg _) (hg 1 0)))

theorem integralMap_det_norm (p : {p : ℕ // p.Prime}) (g : GL (Fin 2) ℤ_[p.1]) :
    ‖(integralMap p g).val.det‖ = 1 := by
  have h₁ := norm_det_le_one p (integralMap p g) (fun i j => (g i j).2)
  have h₂ := norm_det_le_one p (integralMap p g⁻¹) (fun i j => (g⁻¹ i j).2)
  have he : ‖(integralMap p g).val.det‖ * ‖(integralMap p g⁻¹).val.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← GeneralLinearGroup.coe_mul,
      ← map_mul, mul_inv_cancel, map_one]
    simp
  apply le_antisymm h₁
  calc
    1 = ‖(integralMap p g).val.det‖ * ‖(integralMap p g⁻¹).val.det‖ := he.symm
    _ ≤ ‖(integralMap p g).val.det‖ * 1 :=
      mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
    _ = _ := mul_one _

/-- Homothety of the standard integral lattice bounds every squared entry by the determinant. -/
theorem quadratic_entry_bound (p : {p : ℕ // p.Prime}) (g : LocalGL p)
    (hg : ProjGenLinGroup.mk g ∈ integralPGL p) (i j : Fin 2) :
    ‖g i j‖ ^ 2 ≤ ‖g.val.det‖ := by
  obtain ⟨h, hh⟩ := hg
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hh
  rw [← hu]
  have he : ((integralMap p h) * GeneralLinearGroup.scalar (Fin 2) u) i j =
      (integralMap p h) i j * u := by
    change ((integralMap p h).val * Matrix.scalar (Fin 2) u.val) i j = _
    simp only [Matrix.scalar_apply, Matrix.mul_diagonal]
  rw [he, norm_mul, mul_pow]
  have hd : ‖((integralMap p h) * GeneralLinearGroup.scalar (Fin 2) u).val.det‖ = ‖u.val‖ ^ 2 := by
    rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul, integralMap_det_norm]
    simp [GeneralLinearGroup.coe_scalar]
  rw [hd]
  have hi : ‖(integralMap p h) i j‖ ^ 2 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (h i j).2
  exact (mul_le_mul_of_nonneg_right hi (sq_nonneg ‖u.val‖)).trans_eq (one_mul _)

theorem normalized_entry_integral (p : {p : ℕ // p.Prime}) (g : LocalGL p)
    (hg : ProjGenLinGroup.mk g ∈ integralPGL p) (i j : Fin 2) :
    ‖(g i j) ^ 2 / g.val.det‖ ≤ 1 := by
  rw [norm_div, norm_pow]
  exact (div_le_one (norm_pos_iff.mpr g.det_ne_zero)).mpr (quadratic_entry_bound p g hg i j)

/-- Integral determinant-one matrices act through the projective integral stabilizer. -/
theorem integralSL_mem (p : {p : ℕ // p.Prime}) (g : LocalGroup p)
    (hg : g ∈ integralLocalGroup p) :
    SpecialLinearGroup.toPGL g ∈ integralPGL p := by
  let h : SpecialLinearGroup (Fin 2) ℤ_[p.1] :=
    ⟨fun i j => ⟨g i j, hg i j⟩, by
      apply PadicInt.ext
      have he := g.prop
      rw [Matrix.det_fin_two] at he
      simpa only [Matrix.det_fin_two, PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_one] using he⟩
  refine ⟨SpecialLinearGroup.toGL h, ?_⟩
  apply congrArg ProjGenLinGroup.mk
  apply GeneralLinearGroup.ext
  intro i j
  rfl

/-- Full local lattice-homothety vertex space, including both parity classes. -/
abbrev LocalVertex (p : {p : ℕ // p.Prime}) := LocalPGL p ⧸ integralPGL p

def baseVertex (p : {p : ℕ // p.Prime}) : LocalVertex p := QuotientGroup.mk 1

def localProj (p : {p : ℕ // p.Prime}) : RationalGroup →* LocalPGL p :=
  SpecialLinearGroup.toPGL.comp (localMap p)


/-- A matrix and its inverse with integral entries come from an integral invertible matrix. -/
theorem integralMap_range_iff (p : {p : ℕ // p.Prime}) (g : LocalGL p) :
    g ∈ (integralMap p).range ↔
      (∀ i j, ‖g i j‖ ≤ 1) ∧ (∀ i j, ‖g⁻¹ i j‖ ≤ 1) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => (h i j).2, ?_⟩
    intro i j
    rw [← map_inv]
    exact (h⁻¹ i j).2
  · rintro ⟨hg, hgi⟩
    let A : Matrix (Fin 2) (Fin 2) ℤ_[p.1] := fun i j => ⟨g i j, hg i j⟩
    let B : Matrix (Fin 2) (Fin 2) ℤ_[p.1] := fun i j => ⟨g⁻¹ i j, hgi i j⟩
    have hAB : A * B = 1 := by
      apply Matrix.ext
      intro i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      apply PadicInt.ext
      change g i 0 * g.inv 0 j + g i 1 * g.inv 1 j =
        (((1 : Matrix (Fin 2) (Fin 2) ℤ_[p.1]) i j) : ℚ_[p.1])
      have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[p.1] => M i j) g.val_inv
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, apply_ite,
        PadicInt.coe_one, PadicInt.coe_zero] using he
    have hBA : B * A = 1 := by
      apply Matrix.ext
      intro i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      apply PadicInt.ext
      change g.inv i 0 * g 0 j + g.inv i 1 * g 1 j =
        (((1 : Matrix (Fin 2) (Fin 2) ℤ_[p.1]) i j) : ℚ_[p.1])
      have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[p.1] => M i j) g.inv_val
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, apply_ite,
        PadicInt.coe_one, PadicInt.coe_zero] using he
    exact ⟨⟨A, B, hAB, hBA⟩, GeneralLinearGroup.ext fun _ _ => rfl⟩

abbrev RationalGL := GL (Fin 2) ℚ

def localGLMap (p : {p : ℕ // p.Prime}) : RationalGL →* LocalGL p :=
  GeneralLinearGroup.map (Rat.castHom ℚ_[p.1])

theorem localGLMap_apply (p : {p : ℕ // p.Prime}) (g : RationalGL) (i j : Fin 2) :
    localGLMap p g i j = ((g i j : ℚ) : ℚ_[p.1]) := rfl

theorem localProj_toGL (p : {p : ℕ // p.Prime}) (g : RationalGroup) :
    localProj p g = ProjGenLinGroup.mk (localGLMap p (SpecialLinearGroup.toGL g)) := by
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (localMap p g)) = _
  apply congrArg ProjGenLinGroup.mk
  apply GeneralLinearGroup.ext
  intro i j
  rfl

def principalVertex (g : RationalGL) (p : {p : ℕ // p.Prime}) : LocalVertex p :=
  QuotientGroup.mk (ProjGenLinGroup.mk (localGLMap p g))

theorem principalVertex_finite_support (g : RationalGL) :
    {p | principalVertex g p ≠ baseVertex p}.Finite := by
  have hf (h : RationalGL) : (⋃ i : Fin 2, ⋃ j : Fin 2,
      {p : {p : ℕ // p.Prime} | ¬‖((h i j : ℚ) : ℚ_[p.1])‖ ≤ 1}).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => finite_bad_places (h i j)
  apply ((hf g).union (hf g⁻¹)).subset
  intro p hp
  by_contra h
  have hb (i j : Fin 2) : ‖((g i j : ℚ) : ℚ_[p.1])‖ ≤ 1 := by
    by_contra hh
    exact h (Or.inl (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hh⟩⟩))
  have hbi (i j : Fin 2) : ‖((g⁻¹ i j : ℚ) : ℚ_[p.1])‖ ≤ 1 := by
    by_contra hh
    exact h (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hh⟩⟩))
  have hi : localGLMap p g ∈ (integralMap p).range :=
    (integralMap_range_iff p _).mpr ⟨hb, by
      intro i j
      rw [← map_inv]
      exact hbi i j⟩
  apply hp
  apply QuotientGroup.eq.mpr
  simpa only [mul_one] using (integralPGL p).inv_mem
    (show ProjGenLinGroup.mk (localGLMap p g) ∈ integralPGL p from
      by obtain ⟨a, ha⟩ := hi; exact ⟨a, congrArg ProjGenLinGroup.mk ha⟩)

/-- All local vertex types, with finite support relative to the standard lattices. -/
def FiniteVertices := {v : ∀ p : {p : ℕ // p.Prime}, LocalVertex p //
  {p | v p ≠ baseVertex p}.Finite}

instance : TopologicalSpace FiniteVertices := ⊥
instance : DiscreteTopology FiniteVertices := ⟨rfl⟩

def finiteBase : FiniteVertices := ⟨baseVertex, by simp⟩
def finitePoint (g : RationalGL) : FiniteVertices :=
  ⟨principalVertex g, principalVertex_finite_support g⟩

instance : MulAction RationalGroup FiniteVertices where
  smul g v := ⟨fun p => localProj p g • v.1 p, by
    apply (v.2.union (principalVertex_finite_support (SpecialLinearGroup.toGL g))).subset
    intro p hp
    by_contra h
    have hh : v.1 p = baseVertex p ∧
        principalVertex (SpecialLinearGroup.toGL g) p = baseVertex p := by
      simpa only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] using h
    apply hp
    change localProj p g • v.1 p = baseVertex p
    rw [hh.1]
    change (QuotientGroup.mk (localProj p g * 1) : LocalVertex p) = baseVertex p
    rw [mul_one, localProj_toGL]
    exact hh.2⟩
  one_smul v := by
    apply Subtype.ext
    funext p
    change localProj p 1 • v.1 p = v.1 p
    rw [map_one, one_smul]
  mul_smul g h v := by
    apply Subtype.ext
    funext p
    change localProj p (g * h) • v.1 p = localProj p g • (localProj p h • v.1 p)
    rw [map_mul, mul_smul]

/-- The finite determinant-one action agrees with multiplication on rational lattice bases. -/
theorem finite_smul_point (g : RationalGroup) (h : RationalGL) :
    g • finitePoint h = finitePoint (SpecialLinearGroup.toGL g * h) := by
  apply Subtype.ext
  funext p
  change (QuotientGroup.mk (localProj p g * ProjGenLinGroup.mk (localGLMap p h)) : LocalVertex p) =
    QuotientGroup.mk (ProjGenLinGroup.mk (localGLMap p (SpecialLinearGroup.toGL g * h)))
  simp only [map_mul, localProj_toGL]

/-- The lower diagonal basis represents the opposite finite degree orientation. -/
def lowerDegree (n : ℕ+) : RationalGL :=
  ⟨!![1, 0; 0, ((n : ℕ) : ℚ)], !![1, 0; 0, (((n : ℕ) : ℚ))⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, n.ne_zero],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, n.ne_zero]⟩

def transition (g : RationalGroup) (m n : ℕ+) : RationalGL :=
  (lowerDegree n)⁻¹ * SpecialLinearGroup.toGL g * lowerDegree m

theorem transition_det (g : RationalGroup) (m n : ℕ+) :
    (transition g m n).val.det = ((m : ℕ) : ℚ) / (n : ℕ) := by
  simp only [transition, GeneralLinearGroup.coe_mul, Matrix.det_mul]
  change (((lowerDegree n)⁻¹).val.det) * g.val.det * (lowerDegree m).val.det = _
  rw [g.prop]
  simp [lowerDegree, Matrix.det_fin_two, div_eq_mul_inv, mul_comm]

theorem transition_bottom (g : RationalGroup) (m n : ℕ+) :
    transition g m n 1 0 = g 1 0 / (n : ℕ) ∧
    transition g m n 1 1 = g 1 1 * (m : ℕ) / (n : ℕ) := by
  simp [transition, lowerDegree, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, div_eq_mul_inv,
    mul_comm, mul_left_comm]

theorem finite_orbit_transition (g : RationalGroup) (m n : ℕ+)
    (h : g • finitePoint (lowerDegree m) = finitePoint (lowerDegree n)) (p : {p : ℕ // p.Prime}) :
    ProjGenLinGroup.mk (localGLMap p (transition g m n)) ∈ integralPGL p := by
  rw [finite_smul_point] at h
  have he := congrArg (fun v : FiniteVertices => v.1 p) h
  have hh := QuotientGroup.eq.mp he.symm
  simpa only [principalVertex, transition, map_mul, map_inv, mul_assoc] using hh

/-- Local projective integrality produces an ordinary integer quadratic invariant. -/
theorem all_places_quadratic_integer (g : RationalGL)
    (hg : ∀ p, ProjGenLinGroup.mk (localGLMap p g) ∈ integralPGL p) (i j : Fin 2) :
    ∃ z : ℤ, (g i j) ^ 2 / g.val.det = z := by
  apply integer_of_all_local_norm_le_one
  intro p
  have h := normalized_entry_integral p (localGLMap p g) (hg p) i j
  simpa only [Matrix.det_fin_two, localGLMap_apply, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_mul] using h


private theorem complex_rat_norm_sq (q : ℚ) : ‖(q : ℂ)‖ ^ 2 = (q : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.ratCast_re, Complex.ratCast_im,
    mul_zero, add_zero, pow_two]

private theorem arch_degree_equation (g : RationalGroup) (m n : ℕ+)
    (he : h3Act (archMap g)
        (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)) =
      degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) :
    ((m : ℕ) : ℚ) / (n : ℕ) = (g 1 0) ^ 2 * ((m : ℕ) : ℚ) ^ 2 + (g 1 1) ^ 2 := by
  have hd : h3Denom (archMap g)
      (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)) =
      ((g 1 0 : ℚ) : ℝ) ^ 2 * ((m : ℕ) : ℝ) ^ 2 + ((g 1 1 : ℚ) : ℝ) ^ 2 := by
    simp only [h3Denom, degPoint, mul_zero, zero_add]
    change ‖((g 1 1 : ℚ) : ℂ)‖ ^ 2 + ‖((g 1 0 : ℚ) : ℂ)‖ ^ 2 *
      ((m : ℕ) : ℝ) ^ 2 = _
    rw [complex_rat_norm_sq, complex_rat_norm_sq, add_comm]
  have hD := h3Denom_pos (archMap g)
    (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos))
  have ht := congrArg H3.t he
  rw [h3Act_t] at ht
  change ((m : ℕ) : ℝ) / _ = ((n : ℕ) : ℝ) at ht
  have hmul := (div_eq_iff hD.ne').mp ht
  rw [hd] at hmul
  have hr : ((m : ℕ) : ℝ) / (n : ℕ) =
      ((g 1 0 : ℚ) : ℝ) ^ 2 * ((m : ℕ) : ℝ) ^ 2 + ((g 1 1 : ℚ) : ℝ) ^ 2 := by
    apply (div_eq_iff (show ((n : ℕ) : ℝ) ≠ 0 by exact_mod_cast n.ne_zero)).mpr
    simpa only [mul_comm] using hmul
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact hr

/-- An integral degree can move to another only with an integral squared degree ratio. -/
theorem orbit_square_ratio_integer (g : RationalGroup) (m n : ℕ+)
    (hf : g • finitePoint (lowerDegree m) = finitePoint (lowerDegree n))
    (ha : h3Act (archMap g)
        (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)) =
      degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) :
    ∃ z : ℤ, (((m : ℕ) : ℚ) / (n : ℕ)) ^ 2 = z := by
  have hloc := finite_orbit_transition g m n hf
  obtain ⟨C, hC⟩ := all_places_quadratic_integer (transition g m n) hloc 1 0
  obtain ⟨D, hD⟩ := all_places_quadratic_integer (transition g m n) hloc 1 1
  have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
  rw [transition_det, (transition_bottom g m n).1] at hC
  rw [transition_det, (transition_bottom g m n).2] at hD
  have hc : (g 1 0) ^ 2 / (((m : ℕ) : ℚ) * (n : ℕ)) = C := by
    calc
      _ = (g 1 0 / (n : ℕ)) ^ 2 / (((m : ℕ) : ℚ) / (n : ℕ)) := by
        field_simp [hm, hn]
      _ = _ := hC
  have hd : (g 1 1) ^ 2 * (m : ℕ) / (n : ℕ) = D := by
    calc
      _ = (g 1 1 * (m : ℕ) / (n : ℕ)) ^ 2 / (((m : ℕ) : ℚ) / (n : ℕ)) := by
        field_simp [hm, hn]
      _ = _ := hD
  have har := arch_degree_equation g m n ha
  refine ⟨C * ((m : ℕ) : ℤ) ^ 4 + D, ?_⟩
  calc
    (((m : ℕ) : ℚ) / (n : ℕ)) ^ 2 =
        ((g 1 0) ^ 2 * ((m : ℕ) : ℚ) ^ 2 + (g 1 1) ^ 2) *
          (((m : ℕ) : ℚ) / (n : ℕ)) := by rw [← har]; ring
    _ = ((g 1 0) ^ 2 / (((m : ℕ) : ℚ) * (n : ℕ))) * ((m : ℕ) : ℚ) ^ 4 +
        (g 1 1) ^ 2 * (m : ℕ) / (n : ℕ) := by field_simp [hm, hn]
    _ = _ := by rw [hc, hd]; push_cast; rfl

private theorem degree_le_of_square_ratio_integer (m n : ℕ+)
    (h : ∃ z : ℤ, (((m : ℕ) : ℚ) / (n : ℕ)) ^ 2 = z) : (n : ℕ) ≤ m := by
  obtain ⟨z, hz⟩ := h
  have hq : (0 : ℚ) < ((m : ℕ) : ℚ) / (n : ℕ) :=
    div_pos (by exact_mod_cast m.pos) (by exact_mod_cast n.pos)
  have hzpos : (0 : ℤ) < z := by
    have hs := sq_pos_of_pos hq
    rw [hz] at hs
    exact_mod_cast hs
  have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z from hzpos)
  have hsq : (1 : ℚ) ≤ (((m : ℕ) : ℚ) / (n : ℕ)) ^ 2 := by rwa [hz]
  have hratio : (1 : ℚ) ≤ ((m : ℕ) : ℚ) / (n : ℕ) := by
    simpa only [abs_of_pos hq] using
      (one_le_sq_iff_one_le_abs (((m : ℕ) : ℚ) / (n : ℕ))).mp hsq
  have hn : (0 : ℚ) < (n : ℕ) := by exact_mod_cast n.pos
  have hmn := (le_div_iff₀ hn).mp hratio
  simpa only [one_mul, Nat.cast_le] using hmn

/-- Opposite finite orientation separates every positive integer degree. -/
theorem opposite_degree_rigid (g : RationalGroup) (m n : ℕ+)
    (hf : g • finitePoint (lowerDegree m) = finitePoint (lowerDegree n))
    (ha : h3Act (archMap g)
        (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)) =
      degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) : m = n := by
  have hnm := degree_le_of_square_ratio_integer m n (orbit_square_ratio_integer g m n hf ha)
  have hfi : g⁻¹ • finitePoint (lowerDegree n) = finitePoint (lowerDegree m) := by
    rw [← hf, inv_smul_smul]
  have hai : h3Act (archMap g⁻¹)
        (degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) =
      degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos) := by
    rw [← ha, map_inv, ← h3Act_mul, inv_mul_cancel, h3Act_one]
  have hmn := degree_le_of_square_ratio_integer n m
    (orbit_square_ratio_integer g⁻¹ n m hfi hai)
  exact Subtype.ext (le_antisymm hmn hnm)



instance (p : {p : ℕ // p.Prime}) : TopologicalSpace (LocalPGL p) :=
  inferInstanceAs (TopologicalSpace (LocalGL p ⧸ Subgroup.center (LocalGL p)))

instance (p : {p : ℕ // p.Prime}) : IsTopologicalGroup (LocalPGL p) :=
  inferInstanceAs (IsTopologicalGroup (LocalGL p ⧸ Subgroup.center (LocalGL p)))

/-- The integral lattice stabilizer is open in the local projective group. -/
theorem integralPGL_isOpen (p : {p : ℕ // p.Prime}) : IsOpen (integralPGL p : Set (LocalPGL p)) := by
  have hball : IsOpen {x : ℚ_[p.1] | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
      IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p.1]) one_ne_zero
  have hc (i j : Fin 2) : Continuous (fun g : LocalGL p => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℚ_[p.1])))
  have hU : IsOpen {g : LocalGL p | ∀ i j, ‖g i j‖ ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i : Fin 2 =>
      isOpen_iInter_of_finite fun j : Fin 2 => hball.preimage (hc i j)
  have hr : IsOpen ((integralMap p).range : Set (LocalGL p)) := by
    have he : ((integralMap p).range : Set (LocalGL p)) =
        {g | ∀ i j, ‖g i j‖ ≤ 1} ∩ Inv.inv ⁻¹' {g | ∀ i j, ‖g i j‖ ≤ 1} := by
      ext g
      exact integralMap_range_iff p g
    rw [he]
    exact hU.inter (hU.preimage continuous_inv)
  have he : (integralPGL p : Set (LocalPGL p)) =
      ProjGenLinGroup.mk '' ((integralMap p).range : Set (LocalGL p)) := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨integralMap p h, ⟨h, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, rfl⟩
  rw [he]
  exact (show IsOpenMap (ProjGenLinGroup.mk : LocalGL p → LocalPGL p) from
    QuotientGroup.isOpenMap_coe) _ hr

open scoped RestrictedProduct
local instance : Fact (∀ p, IsOpen (integralPGL p : Set (LocalPGL p))) :=
  ⟨integralPGL_isOpen⟩

abbrev FiniteAdelicGroup := Πʳ p : {p : ℕ // p.Prime}, [LocalPGL p, integralPGL p]
abbrev AdelicGroup := SL2C × FiniteAdelicGroup

/-- The rational diagonal in the archimedean--projective adelic group. -/
def arithmeticEmbedding : RationalGroup →* AdelicGroup where
  toFun g := (archMap g, ⟨fun p => localProj p g, by
    rw [Filter.eventually_cofinite]
    change {p | localProj p g ∉ integralPGL p}.Finite
    apply (OppositeAdelic.principalVertex_finite_support g).subset
    intro p hp
    by_contra h
    have hi := (OppositeAdelic.principalVertex_eq_base_iff g p).mp (not_ne_iff.mp h)
    exact hp (integralSL_mem p (localMap p g) hi)⟩)
  map_one' := by
    apply Prod.ext
    · exact map_one archMap
    · apply RestrictedProduct.ext
      intro p
      exact map_one (localProj p)
  map_mul' g h := by
    apply Prod.ext
    · exact map_mul archMap g h
    · apply RestrictedProduct.ext
      intro p
      exact map_mul (localProj p) g h

theorem arithmeticEmbedding_injective : Function.Injective arithmeticEmbedding := by
  intro g h he
  apply Subtype.ext
  ext i j
  apply Rat.cast_injective (α := ℂ)
  exact congrArg (fun a : AdelicGroup => a.1.1 i j) he

def arithmeticGroup : Subgroup AdelicGroup := arithmeticEmbedding.range

private theorem integral_of_projective (p : {p : ℕ // p.Prime}) (g : LocalGroup p)
    (hg : SpecialLinearGroup.toPGL g ∈ integralPGL p) :
    g ∈ integralLocalGroup p := by
  intro i j
  have h := quadratic_entry_bound p (SpecialLinearGroup.toGL g) hg i j
  change ‖g i j‖ ^ 2 ≤ ‖g.val.det‖ at h
  rw [g.prop, norm_one] at h
  change ‖g i j‖ ≤ 1
  nlinarith only [h, norm_nonneg (g i j)]

/-- The diagonal group is discrete in `SL₂(ℂ) × Π'_p PGL₂(ℚ_p)`. -/
instance arithmeticGroup_discrete : DiscreteTopology arithmeticGroup := by
  apply discreteTopology_of_isOpen_singleton_one
  let U : Set AdelicGroup := {a | (∀ i j, ‖a.1.1 i j - (1 : SL2C).1 i j‖ < 1) ∧
    ∀ p, a.2 p ∈ integralPGL p}
  have hc (i j : Fin 2) : Continuous (fun a : AdelicGroup => a.1.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_fst))
  have hU : IsOpen U := by
    apply IsOpen.inter
    · have ho (i j : Fin 2) :
          IsOpen {a : AdelicGroup | ‖a.1.1 i j - (1 : SL2C).1 i j‖ < (1 : ℝ)} :=
        isOpen_lt ((hc i j).sub continuous_const).norm continuous_const
      have hh := isOpen_iInter_of_finite fun i : Fin 2 =>
        isOpen_iInter_of_finite fun j : Fin 2 => ho i j
      convert hh using 1
      ext a
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    · exact (RestrictedProduct.isOpen_forall_mem integralPGL_isOpen).preimage continuous_snd
  have he : (Subtype.val : arithmeticGroup → AdelicGroup) ⁻¹' U = {1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, hg⟩ := x.property
      have hn : (∀ i j, ‖(archMap g).1 i j - (1 : SL2C).1 i j‖ < 1) ∧
          ∀ p, localProj p g ∈ integralPGL p := by
        change (x : AdelicGroup) ∈ U at hx
        rw [← hg] at hx
        exact hx
      have hgone := OppositeAdelic.integral_near_identity_eq_one g
        (fun p => integral_of_projective p (localMap p g) (hn.2 p)) hn.1
      apply Subtype.ext
      exact hg.symm.trans (by rw [hgone, map_one]; rfl)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨by intro i j; simp, fun p => (integralPGL p).one_mem⟩
  rw [← he]
  exact hU.preimage continuous_subtype_val

/-- The finite integral Weyl conjugator, trivial at the archimedean place. -/
def finiteWeyl : AdelicGroup := (1, (arithmeticEmbedding weyl).2)

def conjugateEmbedding : RationalGroup →* AdelicGroup :=
  (MulAut.conj finiteWeyl⁻¹).toMonoidHom.comp arithmeticEmbedding

def conjugateArithmeticGroup : Subgroup AdelicGroup := conjugateEmbedding.range

theorem conjugateEmbedding_injective : Function.Injective conjugateEmbedding :=
  (MulAut.conj finiteWeyl⁻¹).injective.comp arithmeticEmbedding_injective

theorem conjugateEmbedding_arch (g : RationalGroup) : (conjugateEmbedding g).1 = archMap g := by
  change 1⁻¹ * archMap g * (1⁻¹)⁻¹ = archMap g
  simp

theorem conjugateEmbedding_finite (g : RationalGroup) (p : {p : ℕ // p.Prime}) :
    (conjugateEmbedding g).2 p = localProj p (weyl⁻¹ * g * weyl) := by
  change (localProj p weyl)⁻¹ * localProj p g * ((localProj p weyl)⁻¹)⁻¹ = _
  rw [inv_inv, map_mul, map_mul, map_inv]

private def undoConjugation (x : conjugateArithmeticGroup) : arithmeticGroup :=
  ⟨finiteWeyl * x.1 * finiteWeyl⁻¹, by
    obtain ⟨g, hg⟩ := x.property
    refine ⟨g, ?_⟩
    rw [← hg]
    change arithmeticEmbedding g = finiteWeyl *
      (finiteWeyl⁻¹ * arithmeticEmbedding g * (finiteWeyl⁻¹)⁻¹) * finiteWeyl⁻¹
    simp [mul_assoc]⟩

private theorem undoConjugation_continuous : Continuous undoConjugation := by
  apply Continuous.subtype_mk
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

private theorem undoConjugation_eq_one_iff (x : conjugateArithmeticGroup) :
    undoConjugation x = 1 ↔ x = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change finiteWeyl * x.1 * finiteWeyl⁻¹ = 1 at he
    have hh := congrArg (fun y : AdelicGroup => finiteWeyl⁻¹ * y * finiteWeyl) he
    change (x : AdelicGroup) = 1
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, mul_inv_cancel,
      one_mul] using hh
  · rintro rfl
    apply Subtype.ext
    simp [undoConjugation]

/-- The finite Weyl conjugate remains a discrete group in the full projective adelic product. -/
instance conjugateArithmeticGroup_discrete : DiscreteTopology conjugateArithmeticGroup := by
  apply discreteTopology_of_isOpen_singleton_one
  have h := (isOpen_discrete ({1} : Set arithmeticGroup)).preimage undoConjugation_continuous
  have he : undoConjugation ⁻¹' ({1} : Set arithmeticGroup) = {1} := by
    ext x
    exact undoConjugation_eq_one_iff x
  rwa [he] at h


instance : ContinuousConstSMul RationalGroup FiniteVertices :=
  ⟨fun _ => continuous_of_discreteTopology⟩

abbrev GlobalSpace := H3 × FiniteVertices
abbrev Carrier := Quotient (MulAction.orbitRel RationalGroup GlobalSpace)

def oppositeDegreePoint (n : ℕ+) : GlobalSpace :=
  (degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos), finitePoint (lowerDegree n))

def oppositeDegreeClass (n : ℕ+) : Carrier := Quotient.mk _ (oppositeDegreePoint n)

theorem oppositeDegreeClass_injective : Function.Injective oppositeDegreeClass := by
  intro m n h
  obtain ⟨g, hg⟩ := Quotient.exact h
  exact (opposite_degree_rigid g n m (congrArg Prod.snd hg) (congrArg Prod.fst hg)).symm

/-- The original degree basis `diag(n,1)` at the finite places. -/
def upperDegree (n : ℕ+) : RationalGL :=
  ⟨!![((n : ℕ) : ℚ), 0; 0, 1], !![(((n : ℕ) : ℚ))⁻¹, 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, n.ne_zero],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, n.ne_zero]⟩

theorem weyl_upperDegree (n : ℕ+) :
    SpecialLinearGroup.toGL weyl * upperDegree n = lowerDegree n * SpecialLinearGroup.toGL weyl := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upperDegree, lowerDegree, SpecialLinearGroup.toGL, weyl,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem finitePoint_mul_weyl (g : RationalGL) :
    finitePoint (g * SpecialLinearGroup.toGL weyl) = finitePoint g := by
  apply Subtype.ext
  funext p
  apply QuotientGroup.eq.mpr
  change (ProjGenLinGroup.mk (localGLMap p (g * SpecialLinearGroup.toGL weyl)))⁻¹ *
    ProjGenLinGroup.mk (localGLMap p g) ∈ integralPGL p
  rw [map_mul, map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [← localProj_toGL]
  exact (integralPGL p).inv_mem (integralSL_mem p (localMap p weyl) (weyl_integral p))

/-- Weyl reversal sends the original degree basis to its opposite, at every finite place. -/
theorem weyl_finite_upperDegree (n : ℕ+) :
    weyl • finitePoint (upperDegree n) = finitePoint (lowerDegree n) := by
  rw [finite_smul_point, weyl_upperDegree, finitePoint_mul_weyl]

/-- The restricted product acts on all finite homothety vertices. -/
instance : MulAction FiniteAdelicGroup FiniteVertices where
  smul a v := ⟨fun p => a p • v.1 p, by
    have hf : {p | a p ∉ integralPGL p}.Finite := by
      exact Filter.eventually_cofinite.mp a.property
    apply (v.2.union hf).subset
    intro p hp
    by_contra h
    have hh : v.1 p = baseVertex p ∧ a p ∈ integralPGL p := by
      simpa only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] using h
    apply hp
    change a p • v.1 p = baseVertex p
    rw [hh.1]
    apply QuotientGroup.eq.mpr
    simpa only [smul_eq_mul, mul_one] using (integralPGL p).inv_mem hh.2⟩
  one_smul v := by
    apply Subtype.ext
    funext p
    exact one_smul (LocalPGL p) (v.1 p)
  mul_smul a b v := by
    apply Subtype.ext
    funext p
    exact mul_smul (a p) (b p) (v.1 p)

/-- The action is the ordinary product action of the actual adelic group. -/
instance : MulAction AdelicGroup GlobalSpace where
  smul a x := (h3Act a.1 x.1, a.2 • x.2)
  one_smul x := by
    apply Prod.ext
    · exact h3Act_one x.1
    · exact one_smul FiniteAdelicGroup x.2
  mul_smul a b x := by
    apply Prod.ext
    · exact h3Act_mul a.1 b.1 x.1
    · exact mul_smul a.2 b.2 x.2

theorem conjugate_arithmetic_smul (g : RationalGroup) (x : GlobalSpace) :
    conjugateEmbedding g • x =
      (h3Act (archMap g) x.1, (weyl⁻¹ * g * weyl) • x.2) := by
  apply Prod.ext
  · exact congrArg (fun a : SL2C => h3Act a x.1) (conjugateEmbedding_arch g)
  · apply Subtype.ext
    funext p
    change (conjugateEmbedding g).2 p • x.2.1 p =
      localProj p (weyl⁻¹ * g * weyl) • x.2.1 p
    rw [conjugateEmbedding_finite]

/-- The quotient by the constructed discrete subgroup of the full adelic group. -/
abbrev ConjugateCarrier := Quotient (MulAction.orbitRel conjugateArithmeticGroup GlobalSpace)

/-- The original split-torus configuration at every positive integer degree. -/
def originalDegreePoint (n : ℕ+) : GlobalSpace :=
  (degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos), finitePoint (upperDegree n))

def originalDegreeClass (n : ℕ+) : ConjugateCarrier := Quotient.mk _ (originalDegreePoint n)

/-- Every original degree point survives distinctly on the discrete conjugate adelic carrier. -/
theorem originalDegreeClass_injective : Function.Injective originalDegreeClass := by
  intro m n h
  obtain ⟨γ, hγ⟩ := Quotient.exact h
  obtain ⟨g, hg⟩ := γ.property
  have he : conjugateEmbedding g • originalDegreePoint n = originalDegreePoint m := by
    change (γ : AdelicGroup) • originalDegreePoint n = originalDegreePoint m at hγ
    rwa [← hg] at hγ
  rw [conjugate_arithmetic_smul] at he
  have ha := congrArg Prod.fst he
  have hf : (weyl⁻¹ * g * weyl) • finitePoint (upperDegree n) =
      finitePoint (upperDegree m) := congrArg Prod.snd he
  have hfo := congrArg (fun v : FiniteVertices => weyl • v) hf
  rw [mul_smul, mul_smul, smul_inv_smul, weyl_finite_upperDegree,
    weyl_finite_upperDegree] at hfo
  exact (opposite_degree_rigid g n m hfo ha).symm


#print axioms quadratic_entry_bound
#print axioms integralPGL_isOpen
#print axioms all_places_quadratic_integer
#print axioms orbit_square_ratio_integer
#print axioms opposite_degree_rigid
#print axioms arithmeticEmbedding_injective
#print axioms arithmeticGroup_discrete
#print axioms conjugateEmbedding_injective
#print axioms conjugateArithmeticGroup_discrete
#print axioms conjugate_arithmetic_smul
#print axioms originalDegreeClass_injective

end GaloisForLFunctions.HyperbolicArakelovTheory.FullAdelic
