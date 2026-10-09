import GaloisForLFunctions.RHTower.PaperCirclePhaseMomentMajorant

/-! # Strict positivity and exact phase-cancellation cost

The nonzero constant Fourier coefficient prevents total cancellation. Every even
moment under the actual Gibbs law stays positive, and its loss relative to the
positive-coefficient moment is exactly an exponential of a nonnegative penalty.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Exact constant Fourier coefficient of the actual native phase polynomial. -/
theorem paperCirclePhasePolynomial_average (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    expU (paperCirclePhasePolynomial a M k t θ) =
      (paperCircleSubgridLaw a M k t 0 : ℂ) * Complex.exp ((θ 0 : ℂ) * Complex.I) := by
  classical
  unfold paperCirclePhasePolynomial Thermal.ply Law.Cx
  simp_rw [← mul_assoc, expU_sum, expU_lmul, expU_chi]
  rw [Finset.sum_eq_single (0 : Grid (paperCircleSubgridLevel M k))]
  · simp only [map_zero, ↓reduceIte, mul_one]
  · intro x _ hx
    have h : raise (paperCircleSubgrid_le M k) x ≠ 0 := by
      intro H
      apply hx
      apply raise_inj (paperCircleSubgrid_le M k)
      simpa only [map_zero] using H
    rw [if_neg h, mul_zero]
  · simp

theorem paperCirclePhasePolynomial_average_ne_zero (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    expU (paperCirclePhasePolynomial a M k t θ) ≠ 0 := by
  rw [paperCirclePhasePolynomial_average]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (paperCircleSubgridLaw_pos a M k t 0).ne')
    (Complex.exp_ne_zero _)

/-- Arbitrary coefficient phases cannot make the native polynomial vanish everywhere. -/
theorem paperCirclePhasePolynomial_exists_ne_zero (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    ∃ y : Grid M, paperCirclePhasePolynomial a M k t θ y ≠ 0 := by
  by_contra! H
  apply paperCirclePhasePolynomial_average_ne_zero a M k t θ
  rw [funext H]
  simp [expU]

/-- Every finite even moment is strictly positive, including after arbitrary phase cancellation. -/
theorem paperCirclePhaseMoment_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) :
    0 < paperCirclePhaseMoment a M k t θ N := by
  obtain ⟨y,hy⟩ := paperCirclePhasePolynomial_exists_ne_zero a M k t θ
  have H : 0 < paperCircleLocalizedLaw a M k t y *
      ‖paperCirclePhasePolynomial a M k t θ y‖ ^ (2 * N) :=
    mul_pos (Thermal.label_pos _ _) (pow_pos (norm_pos_iff.mpr hy) _)
  apply H.trans_le
  change _ ≤ ∑ x : Grid M, paperCircleLocalizedLaw a M k t x *
    ‖paperCirclePhasePolynomial a M k t θ x‖ ^ (2 * N)
  exact Finset.single_le_sum (f := fun x : Grid M => paperCircleLocalizedLaw a M k t x *
      ‖paperCirclePhasePolynomial a M k t θ x‖ ^ (2 * N))
    (fun x _ => mul_nonneg (Law.nonneg _ _) (pow_nonneg (norm_nonneg _) _))
    (Finset.mem_univ y)

/-- Exact logarithmic loss relative to the positive-coefficient native moment. -/
def paperCirclePhasePenalty (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) : ℝ :=
  -Real.log (paperCirclePhaseMoment a M k t θ N) - paperCirclePhaseMomentCost a M k t N

theorem paperCirclePhasePenalty_nonneg (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) :
    0 ≤ paperCirclePhasePenalty a M k t θ N := by
  have H := Real.log_le_log (paperCirclePhaseMoment_pos a M k t θ N)
    (paperCirclePhaseMoment_majorant a M k t θ N)
  unfold paperCirclePhasePenalty paperCirclePhaseMomentCost
  linarith

/-- Exponentiating the penalty recovers the exact surviving moment fraction. -/
theorem paperCirclePhasePenalty_exp (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) :
    Real.exp (-paperCirclePhasePenalty a M k t θ N) =
      paperCirclePhaseMoment a M k t θ N / paperCirclePhaseMoment a M k t (fun _ => 0) N := by
  unfold paperCirclePhasePenalty paperCirclePhaseMomentCost
  rw [show -(-Real.log (paperCirclePhaseMoment a M k t θ N) -
      -Real.log (paperCirclePhaseMoment a M k t (fun _ => 0) N)) =
        Real.log (paperCirclePhaseMoment a M k t θ N) -
          Real.log (paperCirclePhaseMoment a M k t (fun _ => 0) N) by ring,
    Real.exp_sub, Real.exp_log (paperCirclePhaseMoment_pos a M k t θ N),
    Real.exp_log (paperCirclePhaseMoment_zero_phase_pos a M k t N)]

theorem paperCirclePhasePenalty_zero_phase (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (N : ℕ) : paperCirclePhasePenalty a M k t (fun _ => 0) N = 0 := by
  simp only [paperCirclePhasePenalty, paperCirclePhaseMomentCost, sub_self]

theorem paperCirclePhasePenalty_zero_order (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    paperCirclePhasePenalty a M k t θ 0 = 0 := by
  simp only [paperCirclePhasePenalty, paperCirclePhaseMomentCost,
    paperCirclePhaseMoment_zero_order, Real.log_one, neg_zero, sub_self]

end
end RHTower
