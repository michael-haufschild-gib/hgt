import GaloisForLFunctions.RHTower.PaperCirclePhaseCancellation

/-! # Exact second-moment loss and phase rigidity

The native Gibbs majorant has an exact positive defect: a weighted sum of
squared distances between coefficient phases. Strict support makes every pair
visible, so equality holds precisely for one common phase.
-/

open scoped BigOperators NNReal ComplexConjugate
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- The exact positive interaction weight between two actual coarse frequencies. -/
def paperCirclePhasePairWeight (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x z : Grid (paperCircleSubgridLevel M k)) : ℝ :=
  paperCircleSubgridLaw a M k t x * paperCircleSubgridLaw a M k t z *
    Thermal.cred (paperCircleLocalizedForm a M k t) (raise (paperCircleSubgrid_le M k) (x-z))

theorem paperCirclePhasePairWeight_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x z : Grid (paperCircleSubgridLevel M k)) :
    0 < paperCirclePhasePairWeight a M k t x z :=
  mul_pos (mul_pos (paperCircleSubgridLaw_pos a M k t x)
    (paperCircleSubgridLaw_pos a M k t z))
    (div_pos (paperCircleLocalizedHeat_pos a M k t _) (Thermal.q_origin_pos _))

/-- The actual Gibbs second moment is an exact pairwise Fourier interaction. -/
theorem paperCirclePhaseMoment_one_eq_pair_sum (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    paperCirclePhaseMoment a M k t θ 1 =
      ∑ x, ∑ z, paperCirclePhasePairWeight a M k t x z *
        (Complex.exp ((θ x : ℂ) * Complex.I) *
          conj (Complex.exp ((θ z : ℂ) * Complex.I))).re := by
  let A := paperCircleLocalizedForm a M k t
  let p := paperCircleSubgridLaw a M k t
  let f := fun x => Complex.exp ((θ x : ℂ) * Complex.I)
  let r := raise (paperCircleSubgrid_le M k)
  have hc (x z : Grid (paperCircleSubgridLevel M k)) :
      (Thermal.label A).Ex (fun y =>
        ((f x * chi (r x) y) * conj (f z * chi (r z) y)).re) =
      Thermal.cred A (r (x-z)) * (f x * conj (f z)).re := by
    have he (y : Grid M) :
        (f x * chi (r x) y) * conj (f z * chi (r z) y) =
        (f x * conj (f z)) * chi (r (x-z)) y := by
      rw [map_sub r]
      simp only [sub_eq_add_neg, chi_add', chi_neg', map_mul]
      ring
    simp_rw [he]
    rw [← Law.re_Cx, Law.Cx_lmul, ← Thermal.cred_eq, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_comm]
  change (Thermal.label A).Ex (fun y => ‖p.Cx (fun x => f x * chi (r x) y)‖^2) = _
  simp_rw [Law.sq_norm_Cx, Law.Ex_swap (Thermal.label A) p, hc]
  unfold Law.Ex paperCirclePhasePairWeight
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  dsimp [p, A, r, f]
  ring

/-- Exact loss is half the weighted squared phase-distance energy. -/
theorem paperCirclePhaseMoment_defect (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    paperCirclePhaseMoment a M k t (fun _ => 0) 1 - paperCirclePhaseMoment a M k t θ 1 =
      (1/2 : ℝ) * ∑ x, ∑ z, paperCirclePhasePairWeight a M k t x z *
        ‖Complex.exp ((θ x : ℂ) * Complex.I) - Complex.exp ((θ z : ℂ) * Complex.I)‖^2 := by
  have hd (x z : Grid (paperCircleSubgridLevel M k)) :
      ‖Complex.exp ((θ x : ℂ) * Complex.I) - Complex.exp ((θ z : ℂ) * Complex.I)‖^2 =
      2 - 2 * (Complex.exp ((θ x : ℂ) * Complex.I) *
        conj (Complex.exp ((θ z : ℂ) * Complex.I))).re := by
    rw [Complex.sq_norm, Complex.normSq_sub]
    simp only [← Complex.sq_norm, Complex.norm_exp_ofReal_mul_I, one_pow]
    ring
  rw [paperCirclePhaseMoment_one_eq_pair_sum, paperCirclePhaseMoment_one_eq_pair_sum]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, map_one, mul_one,
    Complex.one_re]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [hd]
  ring

/-- Any one pair of disagreeing phases gives an explicit lower bound on moment loss. -/
theorem paperCirclePhaseMoment_pair_defect_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ)
    (x z : Grid (paperCircleSubgridLevel M k)) :
    (1/2 : ℝ) * paperCirclePhasePairWeight a M k t x z *
        ‖Complex.exp ((θ x : ℂ) * Complex.I) - Complex.exp ((θ z : ℂ) * Complex.I)‖^2 ≤
      paperCirclePhaseMoment a M k t (fun _ => 0) 1 - paperCirclePhaseMoment a M k t θ 1 := by
  classical
  let d := fun i j : Grid (paperCircleSubgridLevel M k) =>
    paperCirclePhasePairWeight a M k t i j *
      ‖Complex.exp ((θ i : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖^2
  have hd (i j) : 0 ≤ d i j :=
    mul_nonneg (paperCirclePhasePairWeight_pos a M k t i j).le (sq_nonneg _)
  have hi : d x z ≤ ∑ j, d x j :=
    Finset.single_le_sum (fun j _ => hd x j) (Finset.mem_univ z)
  have ho : (∑ j, d x j) ≤ ∑ i, ∑ j, d i j :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hd i j))
      (Finset.mem_univ x)
  rw [paperCirclePhaseMoment_defect, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hi.trans ho) (by positivity)

/-- Equality in the second-moment majorant is exactly a common coefficient phase. -/
theorem paperCirclePhaseMoment_one_eq_iff (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    paperCirclePhaseMoment a M k t θ 1 = paperCirclePhaseMoment a M k t (fun _ => 0) 1 ↔
      ∀ x, Complex.exp ((θ x : ℂ) * Complex.I) = Complex.exp ((θ 0 : ℂ) * Complex.I) := by
  constructor
  · intro h x
    have H := paperCirclePhaseMoment_pair_defect_le a M k t θ x 0
    rw [h, sub_self] at H
    have hp := paperCirclePhasePairWeight_pos a M k t x 0
    have hz : ‖Complex.exp ((θ x : ℂ) * Complex.I) -
        Complex.exp ((θ 0 : ℂ) * Complex.I)‖^2 = 0 := by
      nlinarith [sq_nonneg (‖Complex.exp ((θ x : ℂ) * Complex.I) -
        Complex.exp ((θ 0 : ℂ) * Complex.I)‖)]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · intro h
    have H := paperCirclePhaseMoment_defect a M k t θ
    simp only [h, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, Finset.sum_const_zero] at H
    exact (sub_eq_zero.mp H).symm

/-- Every nonconstant complex phase pattern strictly lowers the second moment. -/
theorem paperCirclePhaseMoment_one_lt_iff (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    paperCirclePhaseMoment a M k t θ 1 < paperCirclePhaseMoment a M k t (fun _ => 0) 1 ↔
      ∃ x, Complex.exp ((θ x : ℂ) * Complex.I) ≠ Complex.exp ((θ 0 : ℂ) * Complex.I) := by
  rw [lt_iff_le_and_ne, and_iff_right (paperCirclePhaseMoment_majorant a M k t θ 1),
    ne_eq, paperCirclePhaseMoment_one_eq_iff, not_forall]

/-- Adding one phase to every coefficient leaves every moment unchanged. -/
theorem paperCirclePhaseMoment_add_const (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (β : ℝ) (N : ℕ) :
    paperCirclePhaseMoment a M k t (fun x => θ x + β) N =
      paperCirclePhaseMoment a M k t θ N := by
  have hp (y : Grid M) : paperCirclePhasePolynomial a M k t (fun x => θ x + β) y =
      Complex.exp ((β : ℂ) * Complex.I) * paperCirclePhasePolynomial a M k t θ y := by
    unfold paperCirclePhasePolynomial Thermal.ply
    simp only [Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [← Law.Cx_lmul]
    congr 1
    funext x
    ring
  unfold paperCirclePhaseMoment
  simp only [hp, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The logarithmic penalty is invariant under a common phase shift. -/
theorem paperCirclePhasePenalty_add_const (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (β : ℝ) (N : ℕ) :
    paperCirclePhasePenalty a M k t (fun x => θ x + β) N =
      paperCirclePhasePenalty a M k t θ N := by
  rw [paperCirclePhasePenalty, paperCirclePhaseMoment_add_const, paperCirclePhasePenalty]

/-- At every order the cost vanishes exactly when the majorant is attained. -/
theorem paperCirclePhasePenalty_eq_zero_iff (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) :
    paperCirclePhasePenalty a M k t θ N = 0 ↔
      paperCirclePhaseMoment a M k t θ N = paperCirclePhaseMoment a M k t (fun _ => 0) N := by
  constructor
  · intro h
    have H := paperCirclePhasePenalty_exp a M k t θ N
    rw [h, neg_zero, Real.exp_zero] at H
    have hb := (paperCirclePhaseMoment_zero_phase_pos a M k t N).ne'
    field_simp at H
    nlinarith
  · intro h
    unfold paperCirclePhasePenalty paperCirclePhaseMomentCost
    rw [h, sub_self]

/-- Zero second-order cancellation cost is precisely one common complex phase. -/
theorem paperCirclePhasePenalty_one_eq_zero_iff (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    paperCirclePhasePenalty a M k t θ 1 = 0 ↔
      ∀ x, Complex.exp ((θ x : ℂ) * Complex.I) = Complex.exp ((θ 0 : ℂ) * Complex.I) := by
  rw [paperCirclePhasePenalty_eq_zero_iff, paperCirclePhaseMoment_one_eq_iff]

end
end RHTower
