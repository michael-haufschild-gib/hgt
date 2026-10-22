import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Formality of a two-term connected cochain algebra

Let `A` be a nonnegatively graded algebra over a field with `A⁰ = k`, carrying a degree-one
differential with the graded Leibniz rule.  Connectivity forces the differential to vanish on
degree zero, so the degree-one cohomology is the space of degree-one cocycles, and the degree-zero
component is a `k`-valued augmentation.  Choosing a linear retraction onto the cocycles produces an
algebra map to the square-zero extension `k ⊕ Z¹`: it kills the differential, is the augmentation in
degree zero, is the identity on degree-one cocycles, and vanishes in degrees at least two.  Together
with the vanishing of the higher cohomology this is formality.

* `deningerAugmentation` : the degree-zero augmentation.
* `deningerDiff_gradeZero` : the differential vanishes on degree zero.
* `deningerFormalityHom` : the comparison map to the square-zero algebra.
* `deningerFormalityHom_cocycleOne`, `deningerFormalityHom_gradeGe_two` : it is a
  quasi-isomorphism.
-/

namespace RHTower

open DirectSum Finset

section GradedComponents

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
  (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

/-- The degree-`n` component of an element of a graded algebra. -/
noncomputable def deningerComp (n : ℕ) : R →ₗ[k] ↥(𝒜 n) :=
  (DirectSum.component k ℕ (fun i => ↥(𝒜 i)) n).comp
    (DirectSum.decomposeAlgEquiv 𝒜).toLinearMap

theorem deningerComp_apply (n : ℕ) (x : R) :
    (deningerComp 𝒜 n x : R) = (decompose 𝒜 x n : R) := rfl

theorem deningerComp_of_mem_same {n : ℕ} {x : R} (hx : x ∈ 𝒜 n) :
    (deningerComp 𝒜 n x : R) = x := by
  rw [deningerComp_apply]
  exact DirectSum.decompose_of_mem_same 𝒜 hx

theorem deningerComp_of_mem_ne {m n : ℕ} {x : R} (hx : x ∈ 𝒜 m) (hmn : m ≠ n) :
    (deningerComp 𝒜 n x : R) = 0 := by
  rw [deningerComp_apply]
  exact DirectSum.decompose_of_mem_ne 𝒜 hx hmn

/-- The graded product formula in degree zero. -/
theorem deningerComp_mul_zero (x y : R) :
    (deningerComp 𝒜 0 (x * y) : R)
      = (deningerComp 𝒜 0 x : R) * (deningerComp 𝒜 0 y : R) := by
  have h : ((decompose 𝒜 (x * y) 0 : R)) = ∑ ij ∈ antidiagonal (0 : ℕ),
      ((decompose 𝒜 x ij.1 : R) * (decompose 𝒜 y ij.2 : R)) := by
    rw [decompose_mul]
    exact DirectSum.coe_mul_apply_eq_sum_antidiagonal (A := 𝒜) (decompose 𝒜 x) (decompose 𝒜 y) 0
  rw [deningerComp_apply, h, show (antidiagonal (0 : ℕ)) = {(0, 0)} from by decide]
  simp [deningerComp_apply]

/-- The graded product formula in degree one. -/
theorem deningerComp_mul_one (x y : R) :
    (deningerComp 𝒜 1 (x * y) : R)
      = (deningerComp 𝒜 0 x : R) * (deningerComp 𝒜 1 y : R)
        + (deningerComp 𝒜 1 x : R) * (deningerComp 𝒜 0 y : R) := by
  have h : ((decompose 𝒜 (x * y) 1 : R)) = ∑ ij ∈ antidiagonal (1 : ℕ),
      ((decompose 𝒜 x ij.1 : R) * (decompose 𝒜 y ij.2 : R)) := by
    rw [decompose_mul]
    exact DirectSum.coe_mul_apply_eq_sum_antidiagonal (A := 𝒜) (decompose 𝒜 x) (decompose 𝒜 y) 1
  rw [deningerComp_apply, h, show (antidiagonal (1 : ℕ)) = {(0, 1), (1, 0)} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [deningerComp_apply]

end GradedComponents

section Augmentation

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] [Nontrivial R]
  (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]
  (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k R))

include h0

omit [Nontrivial R] [GradedAlgebra 𝒜] in
/-- Connectivity: the degree-zero component is a scalar. -/
theorem deningerGradeZero_mem_range {x : R} (hx : x ∈ 𝒜 0) :
    x ∈ LinearMap.range (Algebra.linearMap k R) := by
  rw [← h0]
  exact hx

/-- The degree-zero augmentation of a connected graded algebra. -/
noncomputable def deningerAugLinear : R →ₗ[k] k :=
  ((LinearEquiv.ofInjective (Algebra.linearMap k R)
      ((algebraMap k R).injective)).symm.toLinearMap).comp
    (((LinearEquiv.ofEq _ _ h0).toLinearMap).comp (deningerComp 𝒜 0))

theorem deningerAugLinear_spec (x : R) :
    algebraMap k R (deningerAugLinear 𝒜 h0 x) = (deningerComp 𝒜 0 x : R) := by
  set e := LinearEquiv.ofInjective (Algebra.linearMap k R) ((algebraMap k R).injective) with he
  set y : ↥(LinearMap.range (Algebra.linearMap k R)) :=
    (LinearEquiv.ofEq _ _ h0) (deningerComp 𝒜 0 x) with hy
  have hcoe : (y : R) = (deningerComp 𝒜 0 x : R) := rfl
  have h := e.apply_symm_apply y
  have hval : (e (e.symm y) : R) = (y : R) := by rw [h]
  have hcalc : algebraMap k R (e.symm y) = (e (e.symm y) : R) := rfl
  rw [deningerAugLinear]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← hy, hcalc, hval, hcoe]

theorem deningerAugLinear_algebraMap (c : k) :
    deningerAugLinear 𝒜 h0 (algebraMap k R c) = c := by
  have hmem : algebraMap k R c ∈ 𝒜 0 := by
    rw [h0]
    exact ⟨c, rfl⟩
  have h := deningerAugLinear_spec 𝒜 h0 (algebraMap k R c)
  rw [deningerComp_of_mem_same 𝒜 hmem] at h
  exact (algebraMap k R).injective h

/-- **The augmentation.**  On a connected graded algebra the degree-zero component is a
`k`-algebra map. -/
noncomputable def deningerAugmentation : R →ₐ[k] k where
  toFun := deningerAugLinear 𝒜 h0
  map_one' := by
    have h := deningerAugLinear_algebraMap 𝒜 h0 1
    rwa [map_one] at h
  map_mul' x y := by
    refine (algebraMap k R).injective ?_
    rw [map_mul (algebraMap k R), deningerAugLinear_spec, deningerAugLinear_spec,
      deningerAugLinear_spec]
    exact deningerComp_mul_zero 𝒜 x y
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' c := deningerAugLinear_algebraMap 𝒜 h0 c

theorem deningerAugmentation_spec (x : R) :
    algebraMap k R (deningerAugmentation 𝒜 h0 x) = (deningerComp 𝒜 0 x : R) :=
  deningerAugLinear_spec 𝒜 h0 x

/-- **The augmentation is onto in degree zero.** -/
theorem deningerAugmentation_gradeZero_surjective (c : k) :
    ∃ x ∈ 𝒜 0, deningerAugmentation 𝒜 h0 x = c :=
  ⟨algebraMap k R c, by rw [h0]; exact ⟨c, rfl⟩, deningerAugLinear_algebraMap 𝒜 h0 c⟩

/-- A degree-zero element of vanishing augmentation is zero. -/
theorem deningerGradeZero_eq_zero {x : R} (hx : x ∈ 𝒜 0)
    (hax : deningerAugmentation 𝒜 h0 x = 0) : x = 0 := by
  have h := deningerAugmentation_spec 𝒜 h0 x
  rw [hax, map_zero, deningerComp_of_mem_same 𝒜 hx] at h
  exact h.symm

end Augmentation

section Differential

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] [Nontrivial R]
  (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]
  (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k R))
  (d : R →ₗ[k] R)
  (hdeg : ∀ n : ℕ, ∀ x ∈ 𝒜 n, d x ∈ 𝒜 (n + 1))
  (hleib : ∀ (m n : ℕ) (x y : R), x ∈ 𝒜 m → y ∈ 𝒜 n →
    d (x * y) = d x * y + ((-1 : k) ^ m) • (x * d y))

include h0 hleib

omit [Nontrivial R] h0 in
/-- The differential of a unital graded algebra kills the unit. -/
theorem deningerDiff_one : d 1 = 0 := by
  have hone : (1 : R) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
  have h := hleib 0 0 1 1 hone hone
  simp only [one_mul, mul_one, pow_zero, one_smul] at h
  have h2 : d 1 + 0 = d 1 + d 1 := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

omit [Nontrivial R] in
/-- **Connectivity kills the differential in degree zero.** -/
theorem deningerDiff_gradeZero {x : R} (hx : x ∈ 𝒜 0) : d x = 0 := by
  obtain ⟨c, hc⟩ := deningerGradeZero_mem_range 𝒜 h0 hx
  have hcx : x = c • (1 : R) := by
    rw [← hc, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  rw [hcx, map_smul, deningerDiff_one 𝒜 d hleib, smul_zero]

/-- The degree-one cocycles. -/
def deningerCocycleOne : Submodule k R := (LinearMap.ker d) ⊓ 𝒜 1

omit [Nontrivial R] in
/-- **There are no coboundaries in degree one**, so the degree-one cohomology is the space of
degree-one cocycles. -/
theorem deningerCoboundaryOne_eq_bot : Submodule.map d (𝒜 0) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro _ ⟨x, hx, rfl⟩
  simp [deningerDiff_gradeZero 𝒜 h0 d hleib hx]

omit [Nontrivial R] in
/-- **Every degree-zero element is a cocycle**, so the degree-zero cohomology is all of degree
zero. -/
theorem deningerCocycleZero_eq : (LinearMap.ker d) ⊓ 𝒜 0 = 𝒜 0 := by
  refine le_antisymm inf_le_right ?_
  intro x hx
  exact ⟨deningerDiff_gradeZero 𝒜 h0 d hleib hx, hx⟩

/-- The comparison map to the square-zero extension, for a model `V` of the degree-one cohomology
and a chosen linear retraction onto the degree-one cocycles. -/
noncomputable def deningerFormalityMap {V : Type*} [AddCommGroup V] [Module k V]
    [Module kᵐᵒᵖ V] [IsCentralScalar k V] (φ : V ≃ₗ[k] ↥(deningerCocycleOne 𝒜 d))
    (p : R →ₗ[k] ↥(deningerCocycleOne 𝒜 d)) :
    R →ₐ[k] TrivSqZeroExt k V where
  toFun x := (deningerAugmentation 𝒜 h0 x, φ.symm (p ((deningerComp 𝒜 1 x : R))))
  map_one' := by
    have hone : (1 : R) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · have h1 : (deningerComp 𝒜 1 (1 : R) : R) = 0 :=
        deningerComp_of_mem_ne 𝒜 hone (by norm_num)
      simp [h1]
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · have hx0 : (deningerComp 𝒜 0 x : R) = algebraMap k R (deningerAugmentation 𝒜 h0 x) :=
        (deningerAugmentation_spec 𝒜 h0 x).symm
      have hy0 : (deningerComp 𝒜 0 y : R) = algebraMap k R (deningerAugmentation 𝒜 h0 y) :=
        (deningerAugmentation_spec 𝒜 h0 y).symm
      have hsplit : (deningerComp 𝒜 1 (x * y) : R)
          = (deningerAugmentation 𝒜 h0 x) • (deningerComp 𝒜 1 y : R)
            + (deningerAugmentation 𝒜 h0 y) • (deningerComp 𝒜 1 x : R) := by
        rw [deningerComp_mul_one, hx0, hy0, ← Algebra.smul_def, ← Algebra.commutes,
          ← Algebra.smul_def]
      show φ.symm (p ((deningerComp 𝒜 1 (x * y) : R))) = _
      rw [hsplit, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
      simp [TrivSqZeroExt.snd_mul]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [map_add]
  commutes' c := by
    have hmem : algebraMap k R c ∈ 𝒜 0 := by
      rw [h0]
      exact ⟨c, rfl⟩
    have h1 : (deningerComp 𝒜 1 (algebraMap k R c) : R) = 0 :=
      deningerComp_of_mem_ne 𝒜 hmem (by norm_num)
    refine TrivSqZeroExt.ext ?_ ?_
    · show deningerAugLinear 𝒜 h0 (algebraMap k R c) = _
      rw [deningerAugLinear_algebraMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
    · show φ.symm (p ((deningerComp 𝒜 1 (algebraMap k R c) : R))) = _
      rw [h1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      simp

omit hleib in
theorem deningerFormalityMap_apply {V : Type*} [AddCommGroup V] [Module k V]
    [Module kᵐᵒᵖ V] [IsCentralScalar k V] (φ : V ≃ₗ[k] ↥(deningerCocycleOne 𝒜 d))
    (p : R →ₗ[k] ↥(deningerCocycleOne 𝒜 d)) (x : R) :
    deningerFormalityMap 𝒜 h0 d φ p x
      = (deningerAugmentation 𝒜 h0 x, φ.symm (p ((deningerComp 𝒜 1 x : R)))) := rfl

include hdeg

omit [Nontrivial R] h0 hleib in
/-- The degree-zero component of a differential vanishes. -/
theorem deningerComp_zero_diff (x : R) : (deningerComp 𝒜 0 (d x) : R) = 0 := by
  classical
  have hx := DirectSum.sum_support_decompose 𝒜 x
  have hdx : d x = ∑ i ∈ (decompose 𝒜 x).support, d ((decompose 𝒜 x i : R)) := by
    conv_lhs => rw [← hx]
    exact map_sum d _ _
  rw [hdx, map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_eq_zero fun i _ => ?_
  exact deningerComp_of_mem_ne 𝒜 (hdeg i _ (decompose 𝒜 x i).2) (by omega)

omit [Nontrivial R] in
/-- The degree-one component of a differential vanishes: the degree-zero part is killed by the
differential and everything else lands in degree at least two. -/
theorem deningerComp_one_diff (x : R) : (deningerComp 𝒜 1 (d x) : R) = 0 := by
  classical
  have hx := DirectSum.sum_support_decompose 𝒜 x
  have hdx : d x = ∑ i ∈ (decompose 𝒜 x).support, d ((decompose 𝒜 x i : R)) := by
    conv_lhs => rw [← hx]
    exact map_sum d _ _
  rw [hdx, map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [deningerDiff_gradeZero 𝒜 h0 d hleib (decompose 𝒜 x 0).2]
    simp
  · exact deningerComp_of_mem_ne 𝒜 (hdeg i _ (decompose 𝒜 x i).2) (by omega)

variable {V : Type*} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

/-- **The comparison map kills the differential.**  The square-zero target has zero
differential, so this is the cochain map property. -/
theorem deningerFormalityMap_diff (φ : V ≃ₗ[k] ↥(deningerCocycleOne 𝒜 d))
    (p : R →ₗ[k] ↥(deningerCocycleOne 𝒜 d)) (x : R) :
    deningerFormalityMap 𝒜 h0 d φ p (d x) = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · have h := deningerAugmentation_spec 𝒜 h0 (d x)
    rw [deningerComp_zero_diff 𝒜 d hdeg] at h
    have h0' : deningerAugmentation 𝒜 h0 (d x) = 0 := by
      refine (algebraMap k R).injective ?_
      rw [h, map_zero]
    show deningerAugmentation 𝒜 h0 (d x) = (0 : TrivSqZeroExt k V).fst
    rw [h0']
    simp
  · show φ.symm (p ((deningerComp 𝒜 1 (d x) : R))) = (0 : TrivSqZeroExt k V).snd
    rw [deningerComp_one_diff 𝒜 h0 d hdeg hleib]
    simp

omit hdeg hleib in
/-- **In degree zero the comparison map is the augmentation.** -/
theorem deningerFormalityMap_gradeZero (φ : V ≃ₗ[k] ↥(deningerCocycleOne 𝒜 d))
    (p : R →ₗ[k] ↥(deningerCocycleOne 𝒜 d)) {x : R} (hx : x ∈ 𝒜 0) :
    deningerFormalityMap 𝒜 h0 d φ p x
      = TrivSqZeroExt.inl (deningerAugmentation 𝒜 h0 x) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show deningerAugmentation 𝒜 h0 x = _
    rw [TrivSqZeroExt.fst_inl]
  · show φ.symm (p ((deningerComp 𝒜 1 x : R))) = _
    rw [deningerComp_of_mem_ne 𝒜 hx (by norm_num), TrivSqZeroExt.snd_inl]
    simp

omit hdeg hleib in
/-- **On degree-one cocycles the comparison map is the identity.** -/
theorem deningerFormalityMap_cocycleOne (φ : V ≃ₗ[k] ↥(deningerCocycleOne 𝒜 d))
    (p : R →ₗ[k] ↥(deningerCocycleOne 𝒜 d))
    (hp : ∀ z : ↥(deningerCocycleOne 𝒜 d), p (z : R) = z) (v : V) :
    deningerFormalityMap 𝒜 h0 d φ p ((φ v : R)) = TrivSqZeroExt.inr v := by
  have hmem : ((φ v : R)) ∈ 𝒜 1 := (φ v).2.2
  refine TrivSqZeroExt.ext ?_ ?_
  · have h := deningerAugmentation_spec 𝒜 h0 ((φ v : R))
    rw [deningerComp_of_mem_ne 𝒜 hmem (by norm_num)] at h
    have h0' : deningerAugmentation 𝒜 h0 ((φ v : R)) = 0 := by
      refine (algebraMap k R).injective ?_
      rw [h, map_zero]
    show deningerAugmentation 𝒜 h0 ((φ v : R)) = _
    rw [h0', TrivSqZeroExt.fst_inr]
  · show φ.symm (p ((deningerComp 𝒜 1 ((φ v : R)) : R))) = _
    rw [deningerComp_of_mem_same 𝒜 hmem, hp, LinearEquiv.symm_apply_apply,
      TrivSqZeroExt.snd_inr]

omit hdeg hleib in
/-- **In degrees at least two the comparison map vanishes**, matching the vanishing of the higher
cohomology of the square-zero target. -/
theorem deningerFormalityMap_gradeGe_two (φ : V ≃ₗ[k] ↥(deningerCocycleOne 𝒜 d))
    (p : R →ₗ[k] ↥(deningerCocycleOne 𝒜 d)) {n : ℕ} (hn : 2 ≤ n) {x : R} (hx : x ∈ 𝒜 n) :
    deningerFormalityMap 𝒜 h0 d φ p x = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · have h := deningerAugmentation_spec 𝒜 h0 x
    rw [deningerComp_of_mem_ne 𝒜 hx (by omega)] at h
    have h0' : deningerAugmentation 𝒜 h0 x = 0 := by
      refine (algebraMap k R).injective ?_
      rw [h, map_zero]
    show deningerAugmentation 𝒜 h0 x = (0 : TrivSqZeroExt k V).fst
    rw [h0']
    simp
  · show φ.symm (p ((deningerComp 𝒜 1 x : R))) = (0 : TrivSqZeroExt k V).snd
    rw [deningerComp_of_mem_ne 𝒜 hx (by omega)]
    simp

omit [Nontrivial R] [GradedAlgebra 𝒜] hdeg h0 hleib in
/-- A linear retraction onto the degree-one cocycles exists. -/
theorem deningerCocycleRetraction_exists :
    ∃ p : R →ₗ[k] ↥(deningerCocycleOne 𝒜 d),
      ∀ z : ↥(deningerCocycleOne 𝒜 d), p (z : R) = z := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (deningerCocycleOne 𝒜 d)
  exact ⟨(deningerCocycleOne 𝒜 d).projectionOnto W hW,
    fun z => Submodule.projectionOnto_apply_left hW z⟩

/-- **Two-term formality.**  A connected nonnegatively graded cochain algebra whose cohomology is
concentrated in degrees zero and one admits an algebra map to the square-zero extension
`k ⊕ H¹[-1]` which kills the differential, is the augmentation in degree zero, is the identity on
degree-one cocycles, and vanishes in degrees at least two.  With the vanishing of the higher
cohomology of the source this is a quasi-isomorphism. -/
theorem deningerTwoTerm_formality (φ : V ≃ₗ[k] ↥(deningerCocycleOne 𝒜 d)) :
    ∃ f : R →ₐ[k] TrivSqZeroExt k V,
      (∀ x, f (d x) = 0)
      ∧ (∀ x ∈ 𝒜 0, f x = TrivSqZeroExt.inl (deningerAugmentation 𝒜 h0 x))
      ∧ (∀ v : V, f ((φ v : R)) = TrivSqZeroExt.inr v)
      ∧ (∀ n : ℕ, 2 ≤ n → ∀ x ∈ 𝒜 n, f x = 0) := by
  obtain ⟨p, hp⟩ := deningerCocycleRetraction_exists 𝒜 d
  refine ⟨deningerFormalityMap 𝒜 h0 d φ p, ?_, ?_, ?_, ?_⟩
  · exact fun x => deningerFormalityMap_diff 𝒜 h0 d hdeg hleib φ p x
  · exact fun x hx => deningerFormalityMap_gradeZero 𝒜 h0 d φ p hx
  · exact fun v => deningerFormalityMap_cocycleOne 𝒜 h0 d φ p hp v
  · exact fun n hn x hx => deningerFormalityMap_gradeGe_two 𝒜 h0 d φ p hn hx

omit hdeg h0 hleib [IsCentralScalar k V] in
/-- The target is square zero: the product of two positive-degree classes vanishes. -/
theorem deningerFormalityTarget_sq_zero (v w : V) :
    (TrivSqZeroExt.inr v : TrivSqZeroExt k V) * TrivSqZeroExt.inr w = 0 :=
  TrivSqZeroExt.inr_mul_inr k v w

end Differential

end RHTower
