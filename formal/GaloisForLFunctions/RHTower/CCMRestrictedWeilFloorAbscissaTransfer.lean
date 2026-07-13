import GaloisForLFunctions.RHTower.CCMRectangularFiniteChannelNonDilution
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaPolarSourceLaw

/-!
# From the restricted Weil floor to the sharp prime--polar abscissa

This module is the formal consumer for the inward-edge regularization argument.  It isolates the
two properties of the sampled negative restricted-Weil floor that the analytic construction
supplies:

* nonnegativity of the negative-floor magnitude;
* domination of the sharp rectangular Weil negative part by the exact sharp-profile mass times
  that magnitude.

The bounded Gamma--polar correction then transfers the literal finite prime--polar source into the
same positive carrier.  Consequently an abscissa bound for the actual negative floor forces the
corresponding horizontal zero-free region.  At the critical endpoint, if Weil positivity makes the
floor vanish under RH, the floor-abscissa condition is equivalent to RH.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

/-- The sampled negative restricted-Weil floor is an admissible sharp rectangular envelope when
it is nonnegative and the sharp rectangular Weil negative part is bounded by the exact sharp
profile mass `2 * L` times that floor. -/
def XiRestrictedWeilNegativeFloorEnvelope
    (L : ℝ) (N : ℕ) (eta : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ eta n) ∧
    ∀ n, xiRectangularWeilTailNegativePart L N n ≤ 2 * L * eta n

/-- The positive carrier obtained from the sampled floor after paying the bounded Gamma--polar
correction. -/
def restrictedWeilFloorPrimePolarCarrier
    (L : ℝ) (eta : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * L * eta n + rectangularGammaPolarUniformBound L

theorem restrictedWeilFloorPrimePolarCarrier_nonneg
    {L : ℝ} (hL : 0 ≤ L) {eta : ℕ → ℝ}
    (heta : ∀ n, 0 ≤ eta n) (n : ℕ) :
    0 ≤ restrictedWeilFloorPrimePolarCarrier L eta n := by
  unfold restrictedWeilFloorPrimePolarCarrier
  exact add_nonneg (mul_nonneg (mul_nonneg (by positivity) hL) (heta n))
    (rectangularGammaPolarUniformBound_nonneg hL)

/-- Inward regularization plus the bounded Gamma correction makes the literal finite prime--polar
negative part a coefficientwise subcarrier of the augmented sampled floor. -/
theorem rectangularPrimePolarSourceTailNegativePart_le_restrictedWeilFloorCarrier
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} {eta : ℕ → ℝ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta) (n : ℕ) :
    rectangularPrimePolarSourceTailNegativePart L N n ≤
      restrictedWeilFloorPrimePolarCarrier L eta n := by
  calc
    rectangularPrimePolarSourceTailNegativePart L N n ≤
        xiRectangularWeilTailNegativePart L N n +
          rectangularGammaPolarUniformBound L :=
      rectangularPrimePolarSourceTailNegativePart_le_xiRectangularWeilTail hL hN n
    _ ≤ 2 * L * eta n + rectangularGammaPolarUniformBound L := by
      simpa [add_comm] using
        (add_le_add_right (henv.2 n) (rectangularGammaPolarUniformBound L))
    _ = restrictedWeilFloorPrimePolarCarrier L eta n := rfl

/-- Absolute convergence of the sampled floor to the right of one is inherited by the augmented
prime--polar carrier. -/
theorem restrictedWeilFloorPrimePolarCarrier_LSeriesSummable
    {L sigma : ℝ} (hL : 0 ≤ L) {eta : ℕ → ℝ}
    (hsigma : 1 < sigma)
    (heta : LSeriesSummable (fun n => ((eta n : ℝ) : ℂ)) (sigma : ℂ)) :
    LSeriesSummable
      (fun n => ((restrictedWeilFloorPrimePolarCarrier L eta n : ℝ) : ℂ))
      (sigma : ℂ) := by
  have hscaled : LSeriesSummable
      (fun n => (((2 * L : ℝ) : ℂ) * ((eta n : ℝ) : ℂ))) (sigma : ℂ) :=
    by
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (heta.smul (((2 * L : ℝ) : ℂ)))
  have hconstant : LSeriesSummable
      (fun _n : ℕ => ((rectangularGammaPolarUniformBound L : ℝ) : ℂ))
      (sigma : ℂ) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re
      (m := rectangularGammaPolarUniformBound L)
    · intro n hn
      rw [norm_real, Real.norm_eq_abs,
        abs_of_nonneg (rectangularGammaPolarUniformBound_nonneg hL)]
    · simp only [ofReal_re]
      exact hsigma
  have hadd := hscaled.add hconstant
  simpa only [restrictedWeilFloorPrimePolarCarrier, ofReal_add, ofReal_mul,
    ofReal_ofNat, Pi.add_apply] using hadd

/-- **Restricted-floor half-plane transfer.**  If the sampled negative restricted-Weil floor has
absolute-convergence abscissa at most `1 + alpha`, then every Xi zero lies in the horizontal strip
`Re rho ≤ 1/2 + alpha`.  The statement is quantitative for every nonnegative transverse width,
not only at the RH endpoint. -/
theorem all_xiZeros_re_le_of_restrictedWeilFloor_negativeAbscissa_le
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta)
    (hetaAbscissa :
      LSeries.abscissaOfAbsConv (fun n => ((eta n : ℝ) : ℂ)) ≤
        ((1 + alpha : ℝ) : EReal)) :
    ∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha := by
  apply (all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeAbscissa_le
    hL halpha hN).mpr
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
  intro sigma hsigma
  have hsigmaReal : 1 + alpha < sigma := by
    exact_mod_cast hsigma
  have hetaSum :
      LSeriesSummable (fun n => ((eta n : ℝ) : ℂ)) (sigma : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa only [ofReal_re] using hetaAbscissa.trans_lt hsigma)
  have hcarrierSum := restrictedWeilFloorPrimePolarCarrier_LSeriesSummable
    hL.le (by linarith) hetaSum
  exact LSeriesSummable_of_nonneg_of_le
    (rectangularPrimePolarSourceTailNegativePart_nonneg L N)
    (restrictedWeilFloorPrimePolarCarrier_nonneg hL.le henv.1)
    (rectangularPrimePolarSourceTailNegativePart_le_restrictedWeilFloorCarrier
      hL.le hN henv)
    hcarrierSum

/-- The same transfer stated intrinsically through the right-transverse Xi supremum. -/
theorem xiRightTransverseSup_le_of_restrictedWeilFloor_negativeAbscissa_le
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta)
    (hetaAbscissa :
      LSeries.abscissaOfAbsConv (fun n => ((eta n : ℝ) : ℂ)) ≤
        ((1 + alpha : ℝ) : EReal)) :
    xiRightTransverseSup ≤ alpha := by
  have hzeros := all_xiZeros_re_le_of_restrictedWeilFloor_negativeAbscissa_le
    hL halpha hN henv hetaAbscissa
  exact (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove
    hL halpha hN).mp hzeros |>
    (xiRightTransverseSup_le_iff_negativePartEnergyAbove hL halpha hN).mpr

/-- **Critical restricted-floor criterion.**  Suppose the sampled floor envelope is supplied by
inward regularization and Weil positivity makes its negative magnitude vanish under RH.  Then RH
is equivalent to the negative-floor Dirichlet abscissa being at most one. -/
theorem riemannHypothesis_iff_restrictedWeilFloor_negativeAbscissa_le_one
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta)
    (hzero : RiemannHypothesis → ∀ n, eta n = 0) :
    RiemannHypothesis ↔
      LSeries.abscissaOfAbsConv (fun n => ((eta n : ℝ) : ℂ)) ≤
        ((1 : ℝ) : EReal) := by
  constructor
  · intro hRH
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
    intro sigma hsigma
    have hz : (fun n => ((eta n : ℝ) : ℂ)) = 0 := by
      funext n
      simp only [Pi.zero_apply]
      rw [hzero hRH n]
      norm_num
    rw [hz]
    exact LSeriesSummable_zero
  · intro heta
    have hzeros := all_xiZeros_re_le_of_restrictedWeilFloor_negativeAbscissa_le
      hL (alpha := 0) (by positivity) hN henv (by simpa using heta)
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hrho hzero
    have hbound := hzeros rho hzero
    rw [mem_rightHalf] at hrho
    norm_num at hbound
    linarith

end

end RHTower
