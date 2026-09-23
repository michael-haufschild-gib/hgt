import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem

/-!
# Thermal Krylov moments from finite Wightman transition values

For a finite Hamiltonian spectrum `energy`, a nonnegative transition intensity `intensity`, and
Liouvillian gaps `energy a - energy b`, this file records the exact value relation behind the even
thermal Krylov moments.  The even subsequence is the moment sequence of the nonnegative values
`(energy a - energy b)²`.  Consequently both its ordinary and shifted Hankel forms are
nonnegative.  Symmetry of the transition intensity separately forces every odd gap moment to
vanish.

The intended physics specialization is

`intensity a b = weight a b * ‖amplitude a b‖²`,

where `weight` is a nonnegative symmetric Wightman weight and `amplitude` is the matrix of a
self-adjoint observable.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

noncomputable section

/-- The nonnegative transition intensity attached to a Wightman weight and an observable matrix
element. -/
def wightmanTransitionIntensity {α : Type*}
    (weight : α → α → ℝ) (amplitude : α → α → ℂ) (a b : α) : ℝ :=
  weight a b * Complex.normSq (amplitude a b)

/-- Nonnegative Wightman weights give nonnegative transition intensities. -/
theorem wightmanTransitionIntensity_nonneg {α : Type*}
    (weight : α → α → ℝ) (amplitude : α → α → ℂ)
    (hweight : ∀ a b, 0 ≤ weight a b) (a b : α) :
    0 ≤ wightmanTransitionIntensity weight amplitude a b := by
  exact mul_nonneg (hweight a b) (Complex.normSq_nonneg _)

/-- A symmetric weight and a self-adjoint observable give a symmetric transition intensity. -/
theorem wightmanTransitionIntensity_symm {α : Type*}
    (weight : α → α → ℝ) (amplitude : α → α → ℂ)
    (hweight : ∀ a b, weight a b = weight b a)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    wightmanTransitionIntensity weight amplitude a b =
      wightmanTransitionIntensity weight amplitude b a := by
  rw [wightmanTransitionIntensity, wightmanTransitionIntensity, hweight a b,
    hHermitian a b]
  congr 1
  exact (Complex.normSq_conj (amplitude a b)).symm

/-- The `k`-th finite Liouvillian spectral moment of the transition values. -/
def thermalGapMoment {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (k : ℕ) : ℝ :=
  ∑ a, ∑ b, intensity a b * (energy a - energy b) ^ k

/-- The even Liouvillian moments, reindexed as a moment sequence. -/
def thermalEvenGapMoment {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (k : ℕ) : ℝ :=
  thermalGapMoment intensity energy (2 * k)

/-- Exact squared-gap spectral expansion of an even Liouvillian moment. -/
theorem thermalEvenGapMoment_eq {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (k : ℕ) :
    thermalEvenGapMoment intensity energy k =
      ∑ a, ∑ b, intensity a b * ((energy a - energy b) ^ (2 : ℕ)) ^ k := by
  simp only [thermalEvenGapMoment, thermalGapMoment]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← pow_mul]

/-- The moment functional is exactly evaluation on the finite squared-gap distribution. -/
theorem momentFunctional_thermalEvenGapMoment {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (p : Polynomial ℝ) :
    momentFunctional (thermalEvenGapMoment intensity energy) p =
      ∑ a, ∑ b, intensity a b * p.eval ((energy a - energy b) ^ (2 : ℕ)) := by
  rw [momentFunctional_eq_support_sum]
  simp_rw [thermalEvenGapMoment_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Nonnegative transition intensities make every ordinary Hankel square nonnegative. -/
theorem momentFunctional_thermalEvenGapMoment_sq_nonneg {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (p : Polynomial ℝ) :
    0 ≤ momentFunctional (thermalEvenGapMoment intensity energy) (p ^ (2 : ℕ)) := by
  rw [momentFunctional_thermalEvenGapMoment]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  rw [Polynomial.eval_pow]
  exact mul_nonneg (hintensity a b) (sq_nonneg _)

/-- Squared energy gaps also make every once-shifted Hankel square nonnegative. -/
theorem momentFunctional_X_mul_sq_thermalEvenGapMoment_nonneg {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (p : Polynomial ℝ) :
    0 ≤ momentFunctional (thermalEvenGapMoment intensity energy) (X * p ^ (2 : ℕ)) := by
  rw [momentFunctional_thermalEvenGapMoment]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow]
  exact mul_nonneg (hintensity a b)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The shifted Hankel quadratic form of the even thermal moments is nonnegative. -/
theorem shiftedHankelForm_thermalEvenGapMoment_nonneg {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * v j *
      thermalEvenGapMoment intensity energy ((i : ℕ) + (j : ℕ) + 1) := by
  rw [← momentFunctional_X_mul_sq_eq_shiftedHankel]
  exact momentFunctional_X_mul_sq_thermalEvenGapMoment_nonneg intensity energy hintensity _

/-- A symmetric transition intensity cancels every odd Liouvillian spectral moment. -/
theorem thermalGapMoment_odd_eq_zero {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hsymm : ∀ a b, intensity a b = intensity b a)
    {k : ℕ} (hk : Odd k) :
    thermalGapMoment intensity energy k = 0 := by
  have hneg : thermalGapMoment intensity energy k =
      -thermalGapMoment intensity energy k := by
    rw [thermalGapMoment]
    calc
      (∑ a, ∑ b, intensity a b * (energy a - energy b) ^ k) =
          ∑ a, ∑ b, intensity b a * (energy b - energy a) ^ k :=
        Finset.sum_comm
      _ = ∑ a, ∑ b, -(intensity a b * (energy a - energy b) ^ k) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [← hsymm a b]
        have hgap : (energy b - energy a) ^ k = -(energy a - energy b) ^ k := by
          rw [show energy b - energy a = -(energy a - energy b) by ring,
            neg_pow, hk.neg_one_pow]
          ring
        rw [hgap]
        ring
      _ = -(∑ a, ∑ b, intensity a b * (energy a - energy b) ^ k) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_neg_distrib]
  linarith

end

end HTGeometry
