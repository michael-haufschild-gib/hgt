import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount
import Mathlib.Analysis.Complex.Polynomial.GaussLucas

/-!
# Euler coefficient filters and real-root loss

Shi's anchored logarithmic-derivative argument (arXiv:2610.35783, §4)
localizes the roots of `s p + X p′`. At positive integer weight this is the
derivative of `X^s p` with a known zero power removed. Rolle's theorem then
controls the number of nonreal roots even for input polynomials with mixed
real and complex spectra. Iteration allows different weights at each step.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

/-- Multiply coefficient `j` by `s+j+1`. -/
def eulerFilter {K : Type*} [CommSemiring K] (s : ℕ) (p : K[X]) : K[X] :=
  C ((s : K)+1) * p + X * derivative p

theorem eulerFilter_coeff {K : Type*} [CommSemiring K] (s : ℕ) (p : K[X]) (j : ℕ) :
    (eulerFilter s p).coeff j = ((s : K)+1+j) * p.coeff j := by
  cases j with
  | zero => simp [eulerFilter]
  | succ j =>
    simp only [eulerFilter, coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, Nat.cast_succ]
    ring

private theorem filter_ne {K : Type*} [Field K] [CharZero K] (s : ℕ) {p : K[X]} (hp : p ≠ 0) :
    eulerFilter s p ≠ 0 := by
  intro h
  have ht := eulerFilter_coeff s p p.natDegree
  rw [h, coeff_zero] at ht
  have hs : (s : K)+1+p.natDegree ≠ 0 := by
    exact_mod_cast (show s+1+p.natDegree ≠ 0 by omega)
  exact mul_ne_zero hs (leadingCoeff_ne_zero.mpr hp) ht.symm

theorem eulerFilter_natDegree {K : Type*} [Field K] [CharZero K] (s : ℕ) (p : K[X]) :
    (eulerFilter s p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp, eulerFilter]
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr ?_) ?_
  · intro j hj
    rw [eulerFilter_coeff, coeff_eq_zero_of_natDegree_lt hj, mul_zero]
  · rw [eulerFilter_coeff]
    exact mul_ne_zero (by exact_mod_cast (show s+1+p.natDegree ≠ 0 by omega))
      (leadingCoeff_ne_zero.mpr hp)

/-- Clearing the zero of known multiplicity realizes a filter as an ordinary derivative. -/
theorem eulerFilter_derivative_lift {K : Type*} [CommSemiring K] (s : ℕ) (p : K[X]) :
    derivative (X^(s+1) * p) = X^s * eulerFilter s p := by
  rw [derivative_mul, derivative_X_pow_succ, pow_succ, eulerFilter]
  ring

/-- Integer-weight anchored Gauss–Lucas inclusion, valid for arbitrary complex input. -/
theorem eulerFilter_root_hull (s : ℕ) (p : ℂ[X]) :
    (eulerFilter s p).rootSet ℂ ⊆ convexHull ℝ (insert 0 (p.rootSet ℂ)) := by
  intro z hz
  by_cases hp : p = 0
  · simp [hp, eulerFilter] at hz
  have hprod : (X : ℂ[X])^(s+1) * p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hp
  have hdeg : 0 < ((X : ℂ[X])^(s+1) * p).degree := by
    rw [← natDegree_pos_iff_degree_pos, natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
    omega
  have hz' : z ∈ (derivative ((X : ℂ[X])^(s+1) * p)).rootSet ℂ := by
    rw [eulerFilter_derivative_lift, mem_rootSet, coe_aeval_eq_eval, eval_mul]
    rw [mem_rootSet, coe_aeval_eq_eval] at hz
    exact ⟨mul_ne_zero (pow_ne_zero _ X_ne_zero) (filter_ne s hp), by rw [hz.2, mul_zero]⟩
  refine convexHull_mono ?_ (rootSet_derivative_subset_convexHull_rootSet hdeg hz')
  intro w hw
  rw [mem_rootSet, coe_aeval_eq_eval, eval_mul, eval_pow, eval_X] at hw
  rcases mul_eq_zero.mp hw.2 with hw | hw
  · have hw0 : w = 0 := by by_contra hn; exact pow_ne_zero _ hn hw
    subst w
    exact Set.mem_insert 0 _
  · apply Set.mem_insert_of_mem
    rw [mem_rootSet, coe_aeval_eq_eval]
    exact ⟨hp, hw⟩

/-- Anchoring at zero accounts for the one real root normally lost by differentiation. -/
theorem eulerFilter_real_root_gain (s : ℕ) (p : ℝ[X]) :
    p.roots.card ≤ (eulerFilter s p).roots.card := by
  by_cases hp : p = 0
  · simp [hp]
  have h := card_roots_le_derivative ((X : ℝ[X])^(s+1) * p)
  rw [eulerFilter_derivative_lift, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hp),
    roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (filter_ne s hp)),
    roots_X_pow, roots_X_pow] at h
  simp only [Multiset.card_add, Multiset.card_nsmul, Multiset.card_singleton, mul_one] at h
  omega

/-- Exact degree preservation makes the real-root gain an upper bound for nonreal multiplicity. -/
theorem eulerFilter_nonreal_le (s : ℕ) (p : ℝ[X]) :
    nonrealRootCount (eulerFilter s p) ≤ nonrealRootCount p := by
  simp only [nonrealRootCount, eulerFilter_natDegree]
  exact Nat.sub_le_sub_left (eulerFilter_real_root_gain s p) _

/-- A word of anchored Euler operators, in its application order. -/
def eulerWord {K : Type*} [CommSemiring K] : List ℕ → K[X] → K[X]
  | [], p => p
  | s :: w, p => eulerWord w (eulerFilter s p)

theorem eulerWord_coeff {K : Type*} [CommSemiring K] (w : List ℕ) (p : K[X]) (j : ℕ) :
    (eulerWord w p).coeff j = (w.map (fun s : ℕ => (s : K)+1+j)).prod * p.coeff j := by
  induction w generalizing p with
  | nil => simp [eulerWord]
  | cons s w ih => rw [eulerWord, ih, eulerFilter_coeff]; simp; ring

theorem eulerWord_nonreal_le (w : List ℕ) (p : ℝ[X]) :
    nonrealRootCount (eulerWord w p) ≤ nonrealRootCount p := by
  induction w generalizing p with
  | nil => exact le_rfl
  | cons s w ih => exact (ih (eulerFilter s p)).trans (eulerFilter_nonreal_le s p)

/-- Mixing weights in any order keeps every zero in the original anchored convex hull. -/
theorem eulerWord_root_hull (w : List ℕ) (p : ℂ[X]) :
    (eulerWord w p).rootSet ℂ ⊆ convexHull ℝ (insert 0 (p.rootSet ℂ)) := by
  induction w generalizing p with
  | nil => exact (Set.subset_insert _ _).trans (subset_convexHull ℝ _)
  | cons s w ih =>
    apply (ih (eulerFilter s p)).trans
    apply convexHull_min _ (convex_convexHull ℝ _)
    exact Set.insert_subset ((subset_convexHull ℝ _) (Set.mem_insert _ _)) (eulerFilter_root_hull s p)

#print axioms eulerWord_nonreal_le
#print axioms eulerWord_root_hull
#print axioms eulerWord_coeff

end

end FiniteFreeProbability
