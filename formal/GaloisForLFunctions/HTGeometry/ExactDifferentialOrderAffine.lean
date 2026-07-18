import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.DifferentialOrder

/-!
# Exact differential order under affine reparametrization

The order-bounded differential-algebraicity predicate is invariant under translations and under
nonzero argument scalings.  Consequently its least order is unchanged by every invertible affine
change of the independent variable.  Unlike the older smooth scaling lemma, the result here uses
the unconditional iterated chain rule from `ArgumentScalingInvariance`.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- Translation preserves a differential equation without increasing its order. -/
theorem DifferentiallyAlgebraicOfOrder.comp_add_const {f : ℂ → ℂ} {n : ℕ}
    (hf : DifferentiallyAlgebraicOfOrder f n) (a : ℂ) :
    DifferentiallyAlgebraicOfOrder (fun z => f (z + a)) n := by
  obtain ⟨P, hP0, hPz⟩ := hf
  refine ⟨bind₁ (jetShiftSub n a) P, ?_, ?_⟩
  · intro h
    apply hP0
    have hback : bind₁ (jetShiftSub n (-a)) (bind₁ (jetShiftSub n a) P) = P := by
      rw [bind₁_bind₁]
      have hσ : (fun i => bind₁ (jetShiftSub n (-a)) (jetShiftSub n a i)) =
          (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
        funext i
        induction i using Fin.cases with
        | zero =>
          simp only [jetShiftSub, Fin.cases_zero, map_add, bind₁_X_right, bind₁_C_right]
          rw [map_neg]
          ring
        | succ j => simp only [jetShiftSub, Fin.cases_succ, bind₁_X_right]
      rw [hσ, bind₁_X_left]
      rfl
    rw [← hback, h, map_zero]
  · intro z
    rw [eval_bind₁]
    have hvec : (fun i => eval
          (Fin.cons z fun j : Fin (n + 1) =>
            iteratedDeriv (j : ℕ) (fun w => f (w + a)) z)
          (jetShiftSub n a i)) =
        Fin.cons (z + a) (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f (z + a)) := by
      funext i
      induction i using Fin.cases with
      | zero => simp [jetShiftSub]
      | succ j =>
        simp only [jetShiftSub, Fin.cases_succ, eval_X, Fin.cons_succ]
        exact congrFun (iteratedDeriv_comp_add_const (j : ℕ) f a) z
    rw [hvec]
    exact hPz (z + a)

/-- Translation is an equivalence at each fixed differential order. -/
theorem differentiallyAlgebraicOfOrder_comp_add_const_iff {f : ℂ → ℂ} {n : ℕ} (a : ℂ) :
    DifferentiallyAlgebraicOfOrder (fun z => f (z + a)) n ↔
      DifferentiallyAlgebraicOfOrder f n := by
  constructor
  · intro h
    have h2 := h.comp_add_const (-a)
    have hfun : (fun z => (fun w => f (w + a)) (z + -a)) = f := by
      funext z
      apply congrArg f
      ring
    rwa [hfun] at h2
  · exact fun h => h.comp_add_const a

/-- Nonzero argument scaling preserves a differential equation without increasing its order. -/
theorem DifferentiallyAlgebraicOfOrder.comp_const_mul_uncond {f : ℂ → ℂ} {n : ℕ}
    (hf : DifferentiallyAlgebraicOfOrder f n) {c : ℂ} (hc : c ≠ 0) :
    DifferentiallyAlgebraicOfOrder (fun z => f (c * z)) n := by
  obtain ⟨P, hP0, hPz⟩ := hf
  refine ⟨bind₁ (jetArgScaleSub n c) P, ?_, ?_⟩
  · intro h
    apply hP0
    have hback : bind₁ (jetArgScaleSub n c⁻¹) (bind₁ (jetArgScaleSub n c) P) = P := by
      rw [bind₁_bind₁]
      have hσ : (fun i => bind₁ (jetArgScaleSub n c⁻¹) (jetArgScaleSub n c i)) =
          (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
        funext i
        induction i using Fin.cases with
        | zero =>
          simp only [jetArgScaleSub, Fin.cases_zero, map_mul, bind₁_X_right, bind₁_C_right]
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
        | succ j =>
          simp only [jetArgScaleSub, Fin.cases_succ, map_mul, bind₁_X_right, bind₁_C_right]
          rw [← mul_assoc, ← map_mul, inv_inv, ← mul_pow, inv_mul_cancel₀ hc, one_pow,
            map_one, one_mul]
      rw [hσ, bind₁_X_left]
      rfl
    rw [← hback, h, map_zero]
  · intro z
    rw [eval_bind₁]
    have hvec : (fun i => eval
          (Fin.cons z fun j : Fin (n + 1) =>
            iteratedDeriv (j : ℕ) (fun w => f (c * w)) z)
          (jetArgScaleSub n c i)) =
        Fin.cons (c * z) (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f (c * z)) := by
      funext i
      induction i using Fin.cases with
      | zero =>
        simp only [jetArgScaleSub, Fin.cases_zero, eval_mul, eval_C, eval_X, Fin.cons_zero]
      | succ j =>
        simp only [jetArgScaleSub, Fin.cases_succ, eval_mul, eval_C, eval_X, Fin.cons_succ]
        rw [iteratedDeriv_comp_mul_left_uncond f c (j : ℕ) z, ← mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hc, one_pow, one_mul]
    rw [hvec]
    exact hPz (c * z)

/-- Nonzero argument scaling is an equivalence at each fixed differential order. -/
theorem differentiallyAlgebraicOfOrder_comp_const_mul_iff_uncond {f : ℂ → ℂ} {n : ℕ}
    {c : ℂ} (hc : c ≠ 0) :
    DifferentiallyAlgebraicOfOrder (fun z => f (c * z)) n ↔
      DifferentiallyAlgebraicOfOrder f n := by
  constructor
  · intro h
    have h2 := h.comp_const_mul_uncond (inv_ne_zero hc)
    have hfun : (fun z => (fun w => f (c * w)) (c⁻¹ * z)) = f := by
      funext z
      apply congrArg f
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rwa [hfun] at h2
  · exact fun h => h.comp_const_mul_uncond hc

/-- A function has exact differential order `n` when it has an equation of order at most `n`
and no equation of strictly smaller order. -/
def ExactDifferentialOrder (f : ℂ → ℂ) (n : ℕ) : Prop :=
  DifferentiallyAlgebraicOfOrder f n ∧
    ∀ m < n, ¬ DifferentiallyAlgebraicOfOrder f m

/-- Translation preserves exact differential order. -/
theorem exactDifferentialOrder_comp_add_const_iff {f : ℂ → ℂ} {n : ℕ} (b : ℂ) :
    ExactDifferentialOrder (fun z => f (z + b)) n ↔ ExactDifferentialOrder f n := by
  simp only [ExactDifferentialOrder, differentiallyAlgebraicOfOrder_comp_add_const_iff]

/-- Nonzero argument scaling preserves exact differential order, with no regularity hypothesis. -/
theorem exactDifferentialOrder_comp_const_mul_iff {f : ℂ → ℂ} {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) :
    ExactDifferentialOrder (fun z => f (a * z)) n ↔ ExactDifferentialOrder f n := by
  simp only [ExactDifferentialOrder,
    differentiallyAlgebraicOfOrder_comp_const_mul_iff_uncond ha]

/-- Exact differential order is invariant under every invertible affine precomposition. -/
theorem exactDifferentialOrder_affine_precomp {f : ℂ → ℂ} {n : ℕ} {a b : ℂ}
    (ha : a ≠ 0) :
    ExactDifferentialOrder (fun z => f (a * z + b)) n ↔ ExactDifferentialOrder f n := by
  calc
    ExactDifferentialOrder (fun z => f (a * z + b)) n ↔
        ExactDifferentialOrder (fun w => f (w + b)) n :=
      exactDifferentialOrder_comp_const_mul_iff (f := fun w => f (w + b)) ha
    _ ↔ ExactDifferentialOrder f n := exactDifferentialOrder_comp_add_const_iff b

end GaloisForLFunctions

end
