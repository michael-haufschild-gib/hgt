import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed

/-!
# Prime--Hodge history survival Fredholm colligation

The exact tails of the pre-divisor prime--history nuclear defect force a positive weighted
unilateral shift. Its one-sided inverse minus its Hilbert adjoint emits the positive Hodge exit
operator. Finite exit records and the surviving remainder telescope to the identity; the shift
has Fredholm index `-1`; every time-labelled exit is exactly the corresponding prime-fibre
marginal of the integral nuclear object `T`; and total exit, Hodge flux, nuclear trace, and negative
index are the same unit. No zero, divisor, ordinate, or RH hypothesis enters the construction.
-/

open Filter Topology BigOperators

namespace PrimeHodgeHistory

noncomputable section

/-- One-step probability of surviving from history grade `n` to `n+1`. -/
def survivalRatio (n : ℕ) : ℝ := m (n + 1) / m n

/-- One-step probability of exiting at history grade `n`, conditional on survival to `n`. -/
def exitHazard (n : ℕ) : ℝ := 1 - survivalRatio n

theorem m_pos (n : ℕ) : 0 < m n := by
  rw [m]
  positivity

theorem survivalRatio_formula (n : ℕ) :
    survivalRatio n = ((2 * n + 3 : ℕ) : ℝ) / ((2 * n + 9 : ℕ) : ℝ) := by
  rw [survivalRatio, m, m]
  push_cast
  field_simp
  ring

theorem exitHazard_formula (n : ℕ) :
    exitHazard n = 6 / ((2 * n + 9 : ℕ) : ℝ) := by
  rw [exitHazard, survivalRatio_formula]
  push_cast
  field_simp
  ring

theorem survivalRatio_pos (n : ℕ) : 0 < survivalRatio n := by
  rw [survivalRatio_formula]
  positivity

theorem survivalRatio_lt_one (n : ℕ) : survivalRatio n < 1 := by
  rw [survivalRatio_formula]
  apply (div_lt_one (by positivity)).2
  norm_num

theorem survivalRatio_le_one (n : ℕ) : survivalRatio n ≤ 1 :=
  (survivalRatio_lt_one n).le

theorem one_third_le_survivalRatio (n : ℕ) : 1 / 3 ≤ survivalRatio n := by
  rw [survivalRatio_formula]
  push_cast
  apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
  nlinarith

theorem exitHazard_pos (n : ℕ) : 0 < exitHazard n := by
  rw [exitHazard_formula]
  positivity

theorem exitHazard_le_one (n : ℕ) : exitHazard n ≤ 1 := by
  rw [exitHazard]
  linarith [survivalRatio_pos n]

theorem m_succ_eq_survivalRatio_mul (n : ℕ) :
    m (n + 1) = survivalRatio n * m n := by
  rw [survivalRatio]
  field_simp [ne_of_gt (m_pos n)]

theorem w_eq_m_mul_exitHazard (n : ℕ) :
    w n = m n * exitHazard n := by
  rw [w, exitHazard, survivalRatio]
  field_simp [ne_of_gt (m_pos n)]

theorem m_antitone : Antitone m := by
  intro a b hab
  rw [m, m]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  gcongr

theorem survival_product (k N : ℕ) :
    (∏ j ∈ Finset.range N, survivalRatio (k + j)) = m (k + N) / m k := by
  induction N with
  | zero => simp [ne_of_gt (m_pos k)]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih, survivalRatio]
      have hk : m k ≠ 0 := ne_of_gt (m_pos k)
      have hkN : m (k + N) ≠ 0 := ne_of_gt (m_pos (k + N))
      rw [show k + N + 1 = k + (N + 1) by omega]
      field_simp

theorem shifted_exit_sum (k N : ℕ) :
    (∑ j ∈ Finset.range N, w (k + j)) = m k - m (k + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, w]
      rw [show k + (N + 1) = k + N + 1 by omega]
      ring

/-- Scalar exit telescope: conditional exit mass plus surviving mass is exactly one. -/
theorem conditional_exit_telescope (k N : ℕ) :
    (∑ j ∈ Finset.range N, w (k + j) / m k) + m (k + N) / m k = 1 := by
  rw [← Finset.sum_div, shifted_exit_sum]
  field_simp [ne_of_gt (m_pos k)]
  ring

/-- Exit mass at age `k+j`, conditioned on survival to age `k`. -/
def conditionalExitWeight (j k : ℕ) : ℝ := w (k + j) / m k

/-- Surviving mass after `N` further steps, conditioned on survival to age `k`. -/
def survivalRemainderWeight (N k : ℕ) : ℝ := m (k + N) / m k

theorem conditionalExitWeight_nonneg (j k : ℕ) :
    0 ≤ conditionalExitWeight j k := by
  exact div_nonneg (w_pos (k + j)).le (m_pos k).le

theorem conditionalExitWeight_le_one (j k : ℕ) :
    conditionalExitWeight j k ≤ 1 := by
  rw [conditionalExitWeight, div_le_one (m_pos k)]
  have hw : w (k + j) ≤ m (k + j) := by
    rw [w]
    linarith [m_pos (k + j + 1)]
  exact hw.trans (m_antitone (by omega))

theorem survivalRemainderWeight_nonneg (N k : ℕ) :
    0 ≤ survivalRemainderWeight N k := by
  exact div_nonneg (m_pos (k + N)).le (m_pos k).le

theorem survivalRemainderWeight_le_one (N k : ℕ) :
    survivalRemainderWeight N k ≤ 1 := by
  rw [survivalRemainderWeight, div_le_one (m_pos k)]
  exact m_antitone (by omega)

theorem conditionalExitWeight_telescope (k N : ℕ) :
    (∑ j ∈ Finset.range N, conditionalExitWeight j k) +
        survivalRemainderWeight N k = 1 := by
  exact conditional_exit_telescope k N

theorem conditionalExitWeight_zero (k : ℕ) :
    conditionalExitWeight 0 k = exitHazard k := by
  rw [conditionalExitWeight, add_zero, w_eq_m_mul_exitHazard]
  field_simp [ne_of_gt (m_pos k)]

end

end PrimeHodgeHistory

namespace RHTower

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

abbrev PrimeHodgeHistorySpace := ArithmeticDilationHilbert

/-- Positive amplitude of the forced one-step Hodge survival law. -/
def primeHodgeHistorySurvivalWeight (n : ℕ) : ℂ :=
  (Real.sqrt (PrimeHodgeHistory.survivalRatio n) : ℝ)

theorem norm_primeHodgeHistorySurvivalWeight_le_one (n : ℕ) :
    ‖primeHodgeHistorySurvivalWeight n‖ ≤ 1 := by
  rw [primeHodgeHistorySurvivalWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (PrimeHodgeHistory.survivalRatio_le_one n)

theorem primeHodgeHistorySurvivalWeight_ne_zero (n : ℕ) :
    primeHodgeHistorySurvivalWeight n ≠ 0 := by
  rw [primeHodgeHistorySurvivalWeight]
  exact_mod_cast (Real.sqrt_pos.2 (PrimeHodgeHistory.survivalRatio_pos n)).ne'

/-- Bounded positive diagonal part of the forced survival shift. -/
def primeHodgeHistorySurvivalDiagonal :
    PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace :=
  HTGeometry.ellTwoDiagonal primeHodgeHistorySurvivalWeight
    norm_primeHodgeHistorySurvivalWeight_le_one

/-- Forced open-history evolution `C e_n = sqrt(r_n) e_(n+1)`. -/
def primeHodgeHistorySurvivalShift :
    PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace :=
  GaloisForLFunctions.HTGeometry.shiftOp 1 ∘L primeHodgeHistorySurvivalDiagonal

theorem primeHodgeHistorySurvivalShift_apply (f : PrimeHodgeHistorySpace) (n : ℕ) :
    (primeHodgeHistorySurvivalShift f : ℕ → ℂ) (n + 1) =
      primeHodgeHistorySurvivalWeight n * f n := by
  rw [primeHodgeHistorySurvivalShift, ContinuousLinearMap.comp_apply,
    GaloisForLFunctions.HTGeometry.shiftOp_apply,
    GaloisForLFunctions.HTGeometry.shiftFun_add, primeHodgeHistorySurvivalDiagonal,
    HTGeometry.ellTwoDiagonal_apply]

theorem primeHodgeHistorySurvivalShift_zero (f : PrimeHodgeHistorySpace) :
    (primeHodgeHistorySurvivalShift f : ℕ → ℂ) 0 = 0 := by
  rw [primeHodgeHistorySurvivalShift, ContinuousLinearMap.comp_apply,
    GaloisForLFunctions.HTGeometry.shiftOp_apply,
    GaloisForLFunctions.HTGeometry.shiftFun_of_lt (by omega)]

theorem primeHodgeHistorySurvivalShift_basis (n : ℕ) :
    primeHodgeHistorySurvivalShift (HTGeometry.ellTwoCoordinateBasis ℕ n) =
      primeHodgeHistorySurvivalWeight n •
        HTGeometry.ellTwoCoordinateBasis ℕ (n + 1) := by
  ext k
  rcases k with _ | k
  · rw [primeHodgeHistorySurvivalShift_zero]
    simp [HTGeometry.ellTwoCoordinateBasis_apply, lp.single_apply]
  · rw [primeHodgeHistorySurvivalShift_apply]
    simp only [HTGeometry.ellTwoCoordinateBasis_apply, lp.single_apply,
      Pi.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases h : k = n
    · subst k
      simp
    · have hs : k + 1 ≠ n + 1 := by omega
      simp [h]

/-- Positive diagonal square of the exit channel. -/
def primeHodgeHistoryExitDefect :
    PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace :=
  HTGeometry.ellTwoDiagonal
    (fun n => (PrimeHodgeHistory.exitHazard n : ℂ))
    (fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (PrimeHodgeHistory.exitHazard_pos n)]
      exact PrimeHodgeHistory.exitHazard_le_one n)

/-- The exit record emitted `j` steps after a surviving history state. -/
def primeHodgeHistoryExitRecordAt (j : ℕ) :
    PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace :=
  HTGeometry.ellTwoDiagonal
    (fun k => (PrimeHodgeHistory.conditionalExitWeight j k : ℂ))
    (fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (PrimeHodgeHistory.conditionalExitWeight_nonneg j k)]
      exact PrimeHodgeHistory.conditionalExitWeight_le_one j k)

/-- The history mass surviving `N` further steps. -/
def primeHodgeHistorySurvivalRemainder (N : ℕ) :
    PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace :=
  HTGeometry.ellTwoDiagonal
    (fun k => (PrimeHodgeHistory.survivalRemainderWeight N k : ℂ))
    (fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (PrimeHodgeHistory.survivalRemainderWeight_nonneg N k)]
      exact PrimeHodgeHistory.survivalRemainderWeight_le_one N k)

/-- Operator exit telescope: emitted records plus surviving history are exactly the identity. -/
theorem primeHodgeHistory_operator_exit_telescope (N : ℕ) :
    (∑ j ∈ Finset.range N, primeHodgeHistoryExitRecordAt j) +
        primeHodgeHistorySurvivalRemainder N =
      ContinuousLinearMap.id ℂ PrimeHodgeHistorySpace := by
  apply ContinuousLinearMap.ext
  intro f
  have hsumapp :
      ((∑ j ∈ Finset.range N, primeHodgeHistoryExitRecordAt j) f) =
        ∑ j ∈ Finset.range N, primeHodgeHistoryExitRecordAt j f := by
    simp
  ext k
  rw [add_apply, ContinuousLinearMap.id_apply, hsumapp,
    lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [primeHodgeHistoryExitRecordAt, primeHodgeHistorySurvivalRemainder]
  simp_rw [HTGeometry.ellTwoDiagonal_apply]
  change (∑ j ∈ Finset.range N,
      (PrimeHodgeHistory.conditionalExitWeight j k : ℂ) * f k) +
      (PrimeHodgeHistory.survivalRemainderWeight N k : ℂ) * f k = f k
  rw [← Finset.sum_mul]
  rw [← add_mul]
  have ht := PrimeHodgeHistory.conditionalExitWeight_telescope k N
  have htC :
      (∑ j ∈ Finset.range N,
          (PrimeHodgeHistory.conditionalExitWeight j k : ℂ)) +
        (PrimeHodgeHistory.survivalRemainderWeight N k : ℂ) = 1 := by
    exact_mod_cast ht
  rw [htC, one_mul]

theorem primeHodgeHistoryExitRecordAt_zero_eq_exitDefect :
    primeHodgeHistoryExitRecordAt 0 = primeHodgeHistoryExitDefect := by
  apply ContinuousLinearMap.ext
  intro f
  ext k
  simp only [primeHodgeHistoryExitRecordAt, primeHodgeHistoryExitDefect,
    HTGeometry.ellTwoDiagonal_apply]
  rw [PrimeHodgeHistory.conditionalExitWeight_zero]

/-- The initial history state reads the `n`-th emitted mass exactly. -/
theorem inner_initialHistory_primeHodgeHistoryExitRecordAt (n : ℕ) :
    ⟪HTGeometry.ellTwoCoordinateBasis ℕ 0,
      primeHodgeHistoryExitRecordAt n
        (HTGeometry.ellTwoCoordinateBasis ℕ 0)⟫_ℂ =
      (PrimeHodgeHistory.w n : ℂ) := by
  rw [primeHodgeHistoryExitRecordAt,
    HTGeometry.inner_coordinateBasis_ellTwoDiagonal]
  rw [PrimeHodgeHistory.conditionalExitWeight, zero_add,
    PrimeHodgeHistory.m_zero, div_one]

/-- Each history emission is the full prime-fibre marginal of the integral nuclear object `T`. -/
theorem tsum_primeHodgeHistoryDiagonalWeight_fiber (n : ℕ) :
    (∑' p : Nat.Primes, primeHodgeHistoryDiagonalWeight 1 (n, p)) =
      PrimeHodgeHistory.w n := by
  rw [show (fun p : Nat.Primes => primeHodgeHistoryDiagonalWeight 1 (n, p)) =
      fun p => PrimeHodgeHistory.w n *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight 1 p /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent 1 by rfl]
  rw [tsum_div_const, tsum_mul_left,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight zero_lt_one]
  field_simp [(gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos
    (by norm_num : (0 : ℝ) < 1)).ne']

/-- The complete exit record read by the survival colligation is exactly the trace of `T`. -/
theorem primeHodgeHistory_exitRecord_eq_integralNuclearTrace :
    (∑' n, ⟪HTGeometry.ellTwoCoordinateBasis ℕ 0,
      primeHodgeHistoryExitRecordAt n
        (HTGeometry.ellTwoCoordinateBasis ℕ 0)⟫_ℂ) =
      ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT := by
  calc
    (∑' n, ⟪HTGeometry.ellTwoCoordinateBasis ℕ 0,
        primeHodgeHistoryExitRecordAt n
          (HTGeometry.ellTwoCoordinateBasis ℕ 0)⟫_ℂ) =
        ∑' n, (PrimeHodgeHistory.w n : ℂ) := by
          exact tsum_congr inner_initialHistory_primeHodgeHistoryExitRecordAt
    _ = 1 := by
      rw [← Complex.ofReal_tsum, PrimeHodgeHistory.tsum_w]
      norm_num
    _ = ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT :=
      primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1.symm

@[simp] theorem primeHodgeHistoryExitDefect_apply
    (f : PrimeHodgeHistorySpace) (n : ℕ) :
    (primeHodgeHistoryExitDefect f : ℕ → ℂ) n =
      PrimeHodgeHistory.exitHazard n * f n := by
  rw [primeHodgeHistoryExitDefect, HTGeometry.ellTwoDiagonal_apply]

theorem adjoint_primeHodgeHistorySurvivalDiagonal :
    ContinuousLinearMap.adjoint primeHodgeHistorySurvivalDiagonal =
      primeHodgeHistorySurvivalDiagonal := by
  rw [primeHodgeHistorySurvivalDiagonal,
    HTGeometry.adjoint_ellTwoDiagonal]
  congr 1
  funext n
  simp [primeHodgeHistorySurvivalWeight]

theorem adjoint_comp_primeHodgeHistorySurvivalShift :
    ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift ∘L
        primeHodgeHistorySurvivalShift =
      primeHodgeHistorySurvivalDiagonal ∘L
        primeHodgeHistorySurvivalDiagonal := by
  rw [primeHodgeHistorySurvivalShift, ContinuousLinearMap.adjoint_comp,
    adjoint_primeHodgeHistorySurvivalDiagonal,
    GaloisForLFunctions.HTGeometry.adjoint_shiftOp]
  calc
    (primeHodgeHistorySurvivalDiagonal ∘L
          GaloisForLFunctions.HTGeometry.backOp 1) ∘L
        (GaloisForLFunctions.HTGeometry.shiftOp 1 ∘L
          primeHodgeHistorySurvivalDiagonal) =
      primeHodgeHistorySurvivalDiagonal ∘L
        (GaloisForLFunctions.HTGeometry.backOp 1 ∘L
          GaloisForLFunctions.HTGeometry.shiftOp 1) ∘L
        primeHodgeHistorySurvivalDiagonal := rfl
    _ = primeHodgeHistorySurvivalDiagonal ∘L
        primeHodgeHistorySurvivalDiagonal := by
      rw [GaloisForLFunctions.HTGeometry.backOp_comp_shiftOp]
      rfl

/-- The positive exit operator is exactly the adjoint defect `I-C*C`. -/
theorem primeHodgeHistoryExitDefect_eq_adjoint_fracture :
    primeHodgeHistoryExitDefect =
      ContinuousLinearMap.id ℂ PrimeHodgeHistorySpace -
        ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift ∘L
          primeHodgeHistorySurvivalShift := by
  rw [adjoint_comp_primeHodgeHistorySurvivalShift]
  apply ContinuousLinearMap.ext
  intro f
  ext n
  change (PrimeHodgeHistory.exitHazard n : ℂ) * f n =
    f n - primeHodgeHistorySurvivalWeight n *
      (primeHodgeHistorySurvivalWeight n * f n)
  have hs : primeHodgeHistorySurvivalWeight n *
      primeHodgeHistorySurvivalWeight n =
      (PrimeHodgeHistory.survivalRatio n : ℂ) := by
    rw [primeHodgeHistorySurvivalWeight, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (PrimeHodgeHistory.survivalRatio_pos n).le]
  rw [← mul_assoc, hs]
  have hh : (PrimeHodgeHistory.exitHazard n : ℂ) =
      1 - (PrimeHodgeHistory.survivalRatio n : ℂ) := by
    exact_mod_cast (by rw [PrimeHodgeHistory.exitHazard] :
      PrimeHodgeHistory.exitHazard n = 1 - PrimeHodgeHistory.survivalRatio n)
  rw [hh]
  ring

theorem half_le_sqrt_survivalRatio (n : ℕ) :
    1 / 2 ≤ Real.sqrt (PrimeHodgeHistory.survivalRatio n) := by
  have hquarter : (1 / 4 : ℝ) ≤ PrimeHodgeHistory.survivalRatio n := by
    linarith [PrimeHodgeHistory.one_third_le_survivalRatio n]
  have h := Real.sqrt_le_sqrt hquarter
  norm_num at h ⊢
  exact h

/-- Bounded reciprocal amplitude used by the canonical Fredholm left inverse. -/
def primeHodgeHistorySurvivalInverseWeight (n : ℕ) : ℂ :=
  (1 / Real.sqrt (PrimeHodgeHistory.survivalRatio n) : ℝ)

theorem norm_primeHodgeHistorySurvivalInverseWeight_le_two (n : ℕ) :
    ‖primeHodgeHistorySurvivalInverseWeight n‖ ≤ 2 := by
  rw [primeHodgeHistorySurvivalInverseWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos zero_lt_one
      (Real.sqrt_pos.2 (PrimeHodgeHistory.survivalRatio_pos n)))]
  rw [div_le_iff₀ (Real.sqrt_pos.2 (PrimeHodgeHistory.survivalRatio_pos n))]
  nlinarith [half_le_sqrt_survivalRatio n]

def primeHodgeHistorySurvivalInverseDiagonal :
    PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace :=
  HTGeometry.ellTwoDiagonal primeHodgeHistorySurvivalInverseWeight
    norm_primeHodgeHistorySurvivalInverseWeight_le_two

theorem survivalInverseWeight_mul_survivalWeight (n : ℕ) :
    primeHodgeHistorySurvivalInverseWeight n *
      primeHodgeHistorySurvivalWeight n = 1 := by
  rw [primeHodgeHistorySurvivalInverseWeight, primeHodgeHistorySurvivalWeight]
  norm_cast
  field_simp [ne_of_gt (Real.sqrt_pos.2 (PrimeHodgeHistory.survivalRatio_pos n))]

theorem survivalWeight_mul_survivalInverseWeight (n : ℕ) :
    primeHodgeHistorySurvivalWeight n *
      primeHodgeHistorySurvivalInverseWeight n = 1 := by
  rw [mul_comm, survivalInverseWeight_mul_survivalWeight]

theorem primeHodgeHistorySurvivalInverseDiagonal_comp :
    primeHodgeHistorySurvivalInverseDiagonal ∘L
        primeHodgeHistorySurvivalDiagonal =
      ContinuousLinearMap.id ℂ PrimeHodgeHistorySpace := by
  apply ContinuousLinearMap.ext
  intro f
  ext n
  change primeHodgeHistorySurvivalInverseWeight n *
      (primeHodgeHistorySurvivalWeight n * f n) = f n
  rw [← mul_assoc, survivalInverseWeight_mul_survivalWeight, one_mul]

theorem primeHodgeHistorySurvivalDiagonal_comp_inverse :
    primeHodgeHistorySurvivalDiagonal ∘L
        primeHodgeHistorySurvivalInverseDiagonal =
      ContinuousLinearMap.id ℂ PrimeHodgeHistorySpace := by
  apply ContinuousLinearMap.ext
  intro f
  ext n
  change primeHodgeHistorySurvivalWeight n *
      (primeHodgeHistorySurvivalInverseWeight n * f n) = f n
  rw [← mul_assoc, survivalWeight_mul_survivalInverseWeight, one_mul]

/-- Canonical bounded backward transport; unlike the Hilbert adjoint it is a left inverse. -/
def primeHodgeHistorySurvivalLeftInverse :
    PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace :=
  primeHodgeHistorySurvivalInverseDiagonal ∘L
    GaloisForLFunctions.HTGeometry.backOp 1

theorem primeHodgeHistorySurvivalLeftInverse_comp_shift :
    primeHodgeHistorySurvivalLeftInverse ∘L
        primeHodgeHistorySurvivalShift =
      ContinuousLinearMap.id ℂ PrimeHodgeHistorySpace := by
  rw [primeHodgeHistorySurvivalLeftInverse, primeHodgeHistorySurvivalShift]
  calc
    (primeHodgeHistorySurvivalInverseDiagonal ∘L
          GaloisForLFunctions.HTGeometry.backOp 1) ∘L
        (GaloisForLFunctions.HTGeometry.shiftOp 1 ∘L
          primeHodgeHistorySurvivalDiagonal) =
      primeHodgeHistorySurvivalInverseDiagonal ∘L
        (GaloisForLFunctions.HTGeometry.backOp 1 ∘L
          GaloisForLFunctions.HTGeometry.shiftOp 1) ∘L
        primeHodgeHistorySurvivalDiagonal := rfl
    _ = primeHodgeHistorySurvivalInverseDiagonal ∘L
        primeHodgeHistorySurvivalDiagonal := by
      rw [GaloisForLFunctions.HTGeometry.backOp_comp_shiftOp]
      rfl
    _ = ContinuousLinearMap.id ℂ PrimeHodgeHistorySpace :=
      primeHodgeHistorySurvivalInverseDiagonal_comp

/-- One-sided duality minus Hilbert adjunction is exactly the positive exit defect. -/
theorem primeHodgeHistory_dualityAdjunctionFracture_mul :
    (primeHodgeHistorySurvivalLeftInverse -
        ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift) ∘L
      primeHodgeHistorySurvivalShift = primeHodgeHistoryExitDefect := by
  rw [ContinuousLinearMap.sub_comp,
    primeHodgeHistorySurvivalLeftInverse_comp_shift,
    primeHodgeHistoryExitDefect_eq_adjoint_fracture]

theorem ker_primeHodgeHistorySurvivalShift :
    LinearMap.ker primeHodgeHistorySurvivalShift.toLinearMap = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro f hf
  have hcomp := congrArg (fun A : PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace => A f)
    primeHodgeHistorySurvivalLeftInverse_comp_shift
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hcomp
  have hf' : primeHodgeHistorySurvivalShift f = 0 := hf
  rw [hf', map_zero] at hcomp
  exact hcomp.symm

theorem range_primeHodgeHistorySurvivalShift :
    LinearMap.range primeHodgeHistorySurvivalShift.toLinearMap =
      LinearMap.range
        (GaloisForLFunctions.HTGeometry.shiftOp 1).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨primeHodgeHistorySurvivalDiagonal x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨primeHodgeHistorySurvivalInverseDiagonal x, ?_⟩
    change GaloisForLFunctions.HTGeometry.shiftOp 1
      (primeHodgeHistorySurvivalDiagonal
        (primeHodgeHistorySurvivalInverseDiagonal x)) =
      GaloisForLFunctions.HTGeometry.shiftOp 1 x
    have hcomp := congrArg
      (fun A : PrimeHodgeHistorySpace →L[ℂ] PrimeHodgeHistorySpace => A x)
      primeHodgeHistorySurvivalDiagonal_comp_inverse
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hcomp
    rw [hcomp]

/-- Fredholm index of the forced survival shift, written through algebraic kernel and cokernel. -/
def primeHodgeHistorySurvivalShiftIndex : ℤ :=
  (Module.finrank ℂ
      (LinearMap.ker primeHodgeHistorySurvivalShift.toLinearMap) : ℤ) -
    (Module.finrank ℂ
      (PrimeHodgeHistorySpace ⧸
        LinearMap.range primeHodgeHistorySurvivalShift.toLinearMap) : ℤ)

theorem primeHodgeHistorySurvivalShiftIndex_eq_neg_one :
    primeHodgeHistorySurvivalShiftIndex = -1 := by
  rw [primeHodgeHistorySurvivalShiftIndex,
    ker_primeHodgeHistorySurvivalShift,
    range_primeHodgeHistorySurvivalShift]
  rw [GaloisForLFunctions.HTGeometry.finrank_coker_shiftOp]
  norm_num

/-- Exit energy of the initial history vector at time `n`. -/
def primeHodgeHistoryExitEnergy (n : ℕ) : ℝ :=
  PrimeHodgeHistory.m n * PrimeHodgeHistory.exitHazard n

theorem primeHodgeHistoryExitEnergy_eq_w (n : ℕ) :
    primeHodgeHistoryExitEnergy n = PrimeHodgeHistory.w n := by
  rw [primeHodgeHistoryExitEnergy, PrimeHodgeHistory.w_eq_m_mul_exitHazard]

theorem hasSum_primeHodgeHistoryExitEnergy :
    HasSum primeHodgeHistoryExitEnergy 1 := by
  convert PrimeHodgeHistory.hasSum_w using 1
  funext n
  exact primeHodgeHistoryExitEnergy_eq_w n

theorem tsum_primeHodgeHistoryExitEnergy :
    ∑' n, primeHodgeHistoryExitEnergy n = 1 :=
  hasSum_primeHodgeHistoryExitEnergy.tsum_eq

/-- Four-organ conservation: Fredholm boundary index, exact exit energy, Hodge flux, and the
prime-mixed integral nuclear defect all carry the same unit. -/
theorem primeHodgeHistory_index_exitFlux_integralNuclear_conservation :
    ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) =
        ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT ∧
      ((∑' n, primeHodgeHistoryExitEnergy n : ℝ) : ℂ) =
        ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT ∧
      ContinuousLinearMap.opTrace primeHodgeHistoryFluxOperator =
        ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT := by
  rw [primeHodgeHistorySurvivalShiftIndex_eq_neg_one,
    tsum_primeHodgeHistoryExitEnergy,
    opTrace_primeHodgeHistoryFluxOperator]
  have hT := primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1
  rw [hT]
  norm_num

/-- Closed certificate for the source mechanism: finite record completeness, the positive
duality--adjunction fracture, Fredholm charge, timewise prime-fibre ownership, and total integral
conservation hold simultaneously without divisor data or hypotheses. -/
theorem primeHodgeHistorySurvivalFredholmColligation_closed :
    (∀ N,
      (∑ j ∈ Finset.range N, primeHodgeHistoryExitRecordAt j) +
          primeHodgeHistorySurvivalRemainder N =
        ContinuousLinearMap.id ℂ PrimeHodgeHistorySpace) ∧
      (primeHodgeHistorySurvivalLeftInverse -
          ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift) ∘L
        primeHodgeHistorySurvivalShift = primeHodgeHistoryExitDefect ∧
      primeHodgeHistorySurvivalShiftIndex = -1 ∧
      (∀ n,
        ⟪HTGeometry.ellTwoCoordinateBasis ℕ 0,
          primeHodgeHistoryExitRecordAt n
            (HTGeometry.ellTwoCoordinateBasis ℕ 0)⟫_ℂ =
          ((∑' p : Nat.Primes,
            primeHodgeHistoryDiagonalWeight 1 (n, p) : ℝ) : ℂ)) ∧
      ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) =
          ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT ∧
        ((∑' n, primeHodgeHistoryExitEnergy n : ℝ) : ℂ) =
          ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT ∧
        ContinuousLinearMap.opTrace primeHodgeHistoryFluxOperator =
          ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT := by
  refine ⟨primeHodgeHistory_operator_exit_telescope,
    primeHodgeHistory_dualityAdjunctionFracture_mul,
    primeHodgeHistorySurvivalShiftIndex_eq_neg_one, ?_,
    primeHodgeHistory_index_exitFlux_integralNuclear_conservation⟩
  intro n
  rw [inner_initialHistory_primeHodgeHistoryExitRecordAt,
    tsum_primeHodgeHistoryDiagonalWeight_fiber]

end


end RHTower
