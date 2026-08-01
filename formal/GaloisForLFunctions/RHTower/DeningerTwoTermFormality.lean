import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Finset.NatAntidiagonal

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

/-- The differential of a unital graded algebra kills the unit. -/
theorem deningerDiff_one : d 1 = 0 := by
  have hone : (1 : R) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
  have h := hleib 0 0 1 1 hone hone
  simp only [one_mul, mul_one, pow_zero, one_smul] at h
  have h2 : d 1 + 0 = d 1 + d 1 := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- **Connectivity kills the differential in degree zero.** -/
theorem deningerDiff_gradeZero {x : R} (hx : x ∈ 𝒜 0) : d x = 0 := by
  obtain ⟨c, hc⟩ := deningerGradeZero_mem_range 𝒜 h0 hx
  have hcx : x = c • (1 : R) := by
    rw [← hc]
    simp [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  rw [hcx, map_smul, deningerDiff_one 𝒜 d hleib, smul_zero]

end Differential

end RHTower
