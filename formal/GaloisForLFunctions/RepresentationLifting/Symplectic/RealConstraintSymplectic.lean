import GaloisForLFunctions.RHTower.SymplecticMultiplicity
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.Quadratic.FujikiDegreeRigidity
import Mathlib.Analysis.Matrix.PosDef

/-!
# Symplectic forms on real-defined constraint spaces

A complex kernel of real linear equations is closed under conjugation.
Pairing a vector with its conjugate makes the coordinate bilinear form
nondegenerate on that kernel. The standard split symplectic form therefore
restricts nondegenerately to its double. In particular this applies to
permutation-fixed zero-sum sectors, the fixed-space mechanism used in
Lemma 5.6 of Kurnosov–Ríos Ortiz, https://arxiv.org/abs/2611.01210.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace GaloisForLFunctions.RepresentationLifting
open Polynomial GaloisForLFunctions.HodgeTheoryWithoutVarieties
variable {J : Type*} {m : ℕ}

/-- Complex solutions of an arbitrary family of real linear equations. -/
def realConstraintKernel (A : Matrix J (Fin m) ℝ) : Submodule ℂ (Fin m → ℂ) where
  carrier := {v | ∀ j, ∑ i, (A j i : ℂ) * v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hv j, hw j, add_zero]
  smul_mem' := by
    intro c v hv j
    change (∑ i, (A j i : ℂ) * (c * v i)) = 0
    calc
      _ = c * ∑ i, (A j i : ℂ) * v i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [hv j, mul_zero]

/-- Reality of the equations makes the solution space stable under conjugation. -/
theorem realConstraintKernel_star (A : Matrix J (Fin m) ℝ) (v : realConstraintKernel A) :
    star v.val ∈ realConstraintKernel A := by
  intro j
  have hv : ∑ i, (A j i : ℂ) * v.val i = 0 := v.property j
  simpa [star_sum, mul_comm] using congrArg star hv

/-- The coordinate quadratic form along a line in the constrained space. -/
def realConstraintQuadraticLine (A : Matrix J (Fin m) ℝ)
    (x h : realConstraintKernel A) : ℂ[X] :=
  C (x.val ⬝ᵥ x.val) + C (2 * (x.val ⬝ᵥ h.val)) * X + C (h.val ⬝ᵥ h.val) * X ^ 2

/-- The affine Fujiki-power test has only the zero direction on every real-defined sector. -/
theorem realConstraintQuadratic_affine_power_iff (A : Matrix J (Fin m) ℝ)
    (h : realConstraintKernel A) (n : ℕ) :
    (∀ x, ((realConstraintQuadraticLine A x h) ^ (n + 2)).natDegree ≤ 1) ↔ h = 0 := by
  constructor
  · intro H
    let x : realConstraintKernel A := ⟨star h.val, realConstraintKernel_star A h⟩
    have hb := ((quadratic_power_affine_iff _ _ _ n).mp (H x)).1
    apply Subtype.ext
    exact dotProduct_star_self_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left two_ne_zero)
  · rintro rfl x
    simp [realConstraintQuadraticLine]

/-- Restriction of the existing standard symplectic form to two constrained copies. -/
def realConstraintSymplectic (A : Matrix J (Fin m) ℝ) :
    LinearMap.BilinForm ℂ (realConstraintKernel A × realConstraintKernel A) :=
  (RHTower.standardSymplectic m).comp
    (LinearMap.prodMap (realConstraintKernel A).subtype (realConstraintKernel A).subtype)
    (LinearMap.prodMap (realConstraintKernel A).subtype (realConstraintKernel A).subtype)

theorem realConstraintSymplectic_isAlt (A : Matrix J (Fin m) ℝ) :
    (realConstraintSymplectic A).IsAlt := by
  intro p
  change p.1.val ⬝ᵥ p.2.val - p.2.val ⬝ᵥ p.1.val = 0
  rw [dotProduct_comm, sub_self]

/-- Conjugate test vectors prove nondegeneracy without any rank condition on the equations. -/
theorem realConstraintSymplectic_nondegenerate (A : Matrix J (Fin m) ℝ) :
    (realConstraintSymplectic A).Nondegenerate := by
  refine (realConstraintSymplectic_isAlt A).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro p hp
  have hfirst : p.1.val = 0 := by
    let q : realConstraintKernel A := ⟨star p.1.val, realConstraintKernel_star A p.1⟩
    have h := hp (0, q)
    change p.1.val ⬝ᵥ star p.1.val - p.2.val ⬝ᵥ 0 = 0 at h
    rw [dotProduct_zero, sub_zero, dotProduct_comm] at h
    exact dotProduct_star_self_eq_zero.mp h
  have hsecond : p.2.val = 0 := by
    let q : realConstraintKernel A := ⟨star p.2.val, realConstraintKernel_star A p.2⟩
    have h := hp (q, 0)
    change p.1.val ⬝ᵥ 0 - p.2.val ⬝ᵥ star p.2.val = 0 at h
    rw [dotProduct_zero, zero_sub, neg_eq_zero, dotProduct_comm] at h
    exact dotProduct_star_self_eq_zero.mp h
  exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond)

/-- Equations for the common permutation-fixed part of the zero-sum representation. -/
def permutationMovingConstraints {κ : Type*} (σ : κ → Equiv.Perm (Fin m)) :
    Matrix (Unit ⊕ (κ × Fin m)) (Fin m) ℝ := by
  classical
  exact fun r j => match r with
    | .inl _ => 1
    | .inr (g, i) => (if j = σ g i then 1 else 0) - (if j = i then 1 else 0)

private theorem permutationMovingConstraints_row {κ : Type*}
    (σ : κ → Equiv.Perm (Fin m)) (v : Fin m → ℂ) (g : κ) (i : Fin m) :
    (∑ j, (permutationMovingConstraints σ (.inr (g, i)) j : ℂ) * v j) =
      v (σ g i) - v i := by
  classical
  have hc (j : Fin m) : (permutationMovingConstraints σ (.inr (g, i)) j : ℂ) =
      (if j = σ g i then (1 : ℂ) else 0) - (if j = i then 1 else 0) := by
    change (((if j = σ g i then (1 : ℝ) else 0) -
      (if j = i then 1 else 0) : ℝ) : ℂ) = _
    split_ifs <;> simp
  simp only [hc, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  simp

/-- The real constraint matrix cuts out exactly the fixed zero-sum vectors. -/
theorem mem_permutationMovingKernel_iff {κ : Type*} (σ : κ → Equiv.Perm (Fin m))
    (v : Fin m → ℂ) :
    v ∈ realConstraintKernel (permutationMovingConstraints σ) ↔
      (∑ i, v i = 0) ∧ ∀ g i, v (σ g i) = v i := by
  classical
  constructor
  · intro h
    constructor
    · simpa [permutationMovingConstraints] using h (.inl ())
    · intro g i
      exact sub_eq_zero.mp ((permutationMovingConstraints_row σ v g i).symm.trans
        (h (.inr (g, i))))
  · rintro ⟨hsum, hfix⟩ r
    rcases r with u | ⟨g, i⟩
    · simpa [permutationMovingConstraints] using hsum
    · exact (permutationMovingConstraints_row σ v g i).trans (sub_eq_zero.mpr (hfix g i))

/-- Every common fixed zero-sum sector carries the restricted nondegenerate symplectic form. -/
theorem permutationMoving_symplectic_nondegenerate {κ : Type*}
    (σ : κ → Equiv.Perm (Fin m)) :
    (realConstraintSymplectic (permutationMovingConstraints σ)).Nondegenerate :=
  realConstraintSymplectic_nondegenerate _

#print axioms realConstraintSymplectic_nondegenerate
#print axioms realConstraintQuadratic_affine_power_iff
#print axioms mem_permutationMovingKernel_iff
#print axioms permutationMoving_symplectic_nondegenerate
end GaloisForLFunctions.RepresentationLifting
