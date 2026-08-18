import GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldTransverseDefectBudgetReporter
import GaloisForLFunctions.RHTower.BilateralPrimeAnglePacketSewing

/-!
# Indefinite endpoint-excess annihilation and its bilateral admission firewall

The literal Route-P endpoint response eventually exceeds its primitive Euler budget.  The unique
diagonal counterleg retaining the endpoint as first corner and the transverse source reporter as
trace is the difference `T-R`; it is cofinally negative.  Hence signed annihilation exists before
scalar domination, exactly as an indefinite block.  Its physical fundamental-symmetry rotation has
trace `2R-T` and overspends even more.

The second half transports this endpoint scale to the two prime-angle Hardy orientations.  Their
Stokes defects still cancel identically, but nonzero scalar multiplication cannot change bilateral
moderation.  Both scaled orientations are source-admissible exactly on the critical line.  Every
actual strict-right Xi copy therefore has exact signed cancellation and exact analytic multiplicity,
yet fails coefficient-faithful bilateral admission.

All statements are unconditional.  The module proves a sharp no-go/classification, not RH.
-/

open Complex Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

theorem bilateralModerate_const_mul (a : ℂ) {f : ℤ → ℂ}
    (hf : bilateralModerate f) :
    bilateralModerate (fun e => a * f e) := by
  rcases hf with ⟨C, m, hC⟩
  refine ⟨‖a‖ * C, m, fun e => ?_⟩
  rw [norm_mul]
  calc
    ‖a‖ * ‖f e‖ ≤ ‖a‖ * (C * (1 + (e.natAbs : ℝ)) ^ m) :=
      mul_le_mul_of_nonneg_left (hC e) (norm_nonneg a)
    _ = (‖a‖ * C) * (1 + (e.natAbs : ℝ)) ^ m := by ring

theorem bilateralModerate_const_mul_iff {a : ℂ} (ha : a ≠ 0) (f : ℤ → ℂ) :
    bilateralModerate (fun e => a * f e) ↔ bilateralModerate f := by
  constructor
  · intro haf
    have h := bilateralModerate_const_mul a⁻¹ haf
    simpa [ha, mul_assoc] using h
  · exact bilateralModerate_const_mul a

theorem bilateralSewing_const_mul (lam a : ℂ) (f : ℤ → ℂ) :
    bilateralSewing lam (fun e => a * f e) =
      fun e => a * bilateralSewing lam f e := by
  funext e
  simp only [bilateralSewing]
  ring

/-- Unique counterleg cancelling literal endpoint response down to the transverse source-budgeted
reporter before scalar domination. -/
def sourceHorizontalEulerWoldEndpointCounterleg
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) : ℝ :=
  sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N -
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N

/-- Signed endpoint block.  Its positive corner is literal endpoint response; its negative corner
is the source-derived counterleg. -/
def sourceHorizontalEulerWoldIndefiniteEndpointBlock
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N, 0;
    0, sourceHorizontalEulerWoldEndpointCounterleg c q N]

/-- Real fundamental symmetry used only after signed cancellation. -/
def sourceHorizontalEulerWoldRealFundamentalSymmetry :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- Signed trace cancels endpoint excess exactly and leaves the transverse reporter. -/
theorem sourceHorizontalEulerWoldIndefiniteEndpointBlock_trace
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    (sourceHorizontalEulerWoldIndefiniteEndpointBlock c q N).trace =
      sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N := by
  simp [sourceHorizontalEulerWoldIndefiniteEndpointBlock,
    sourceHorizontalEulerWoldEndpointCounterleg, Matrix.trace, Fin.sum_univ_two]

/-- Counterleg is forced: no alternative diagonal second corner can retain both literal endpoint
first corner and the transverse reporter trace. -/
theorem sourceHorizontalEulerWoldEndpointCounterleg_unique
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (k : ℝ) :
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N + k =
        sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N ↔
      k = sourceHorizontalEulerWoldEndpointCounterleg c q N := by
  rw [sourceHorizontalEulerWoldEndpointCounterleg]
  constructor <;> intro h <;> linarith

/-- On every nonzero conormal the signed cancellation is genuinely indefinite cofinally. -/
theorem eventually_sourceHorizontalEulerWoldIndefiniteEndpointBlock_inertia
    {c : ℂ} (hc : c ≠ 0) (q : XiRightZeroCopy) :
    ∀ᶠ N : ℕ in atTop,
      0 < sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N ∧
      sourceHorizontalEulerWoldEndpointCounterleg c q N < 0 := by
  have hbudget := sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_pos hc
  filter_upwards
    [eventually_sourceHorizontalEulerWoldTransverseDefectBudgetReporter_between hc q,
      eventually_sourceBudget_lt_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse hc q]
      with N hT hR
  constructor
  · linarith
  · rw [sourceHorizontalEulerWoldEndpointCounterleg]
    linarith

/-- Physical `J`-rotation turns the negative counterleg positive, producing `2R-T`. -/
theorem sourceHorizontalEulerWoldPhysicalEndpointBlock_trace
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    (sourceHorizontalEulerWoldRealFundamentalSymmetry *
      sourceHorizontalEulerWoldIndefiniteEndpointBlock c q N).trace =
        2 * sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N -
          sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N := by
  simp [sourceHorizontalEulerWoldRealFundamentalSymmetry,
    sourceHorizontalEulerWoldIndefiniteEndpointBlock,
    sourceHorizontalEulerWoldEndpointCounterleg,
    Matrix.trace, Fin.sum_univ_two]
  ring

/-- Krein rotation destroys cancellation: physical trace cofinally overspends source budget. -/
theorem eventually_sourceBudget_lt_sourceHorizontalEulerWoldPhysicalEndpointBlock_trace
    {c : ℂ} (hc : c ≠ 0) (q : XiRightZeroCopy) :
    ∀ᶠ N : ℕ in atTop,
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
        (sourceHorizontalEulerWoldRealFundamentalSymmetry *
          sourceHorizontalEulerWoldIndefiniteEndpointBlock c q N).trace := by
  filter_upwards
    [eventually_sourceHorizontalEulerWoldTransverseDefectBudgetReporter_between hc q,
      eventually_sourceBudget_lt_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse hc q]
      with N hT hR
  rw [sourceHorizontalEulerWoldPhysicalEndpointBlock_trace]
  linarith

/-- Positive Hardy orientation scaled by literal endpoint ghost energy. -/
def sourceHorizontalEndpointScaledHardyPositiveHalf
    (c : ℂ) (N : ℕ) (lam : ℂ) : ℤ → ℂ :=
  fun e => (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) *
    hardyPositiveHalf lam e

/-- Negative Hardy orientation scaled by the same literal endpoint ghost energy. -/
def sourceHorizontalEndpointScaledHardyNegativeHalf
    (c : ℂ) (N : ℕ) (lam : ℂ) : ℤ → ℂ :=
  fun e => (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) *
    hardyNegativeHalf lam e

/-- Exact order-indefinite Stokes annihilation survives literal endpoint scaling at every grade. -/
theorem sourceHorizontalEndpointScaledHardySewing_cancel
    (c : ℂ) (N : ℕ) {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralSewing lam (sourceHorizontalEndpointScaledHardyPositiveHalf c N lam) +
      bilateralSewing lam (sourceHorizontalEndpointScaledHardyNegativeHalf c N lam) = 0 := by
  change
    bilateralSewing lam (fun e =>
      (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) * hardyPositiveHalf lam e) +
    bilateralSewing lam (fun e =>
      (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) * hardyNegativeHalf lam e) = 0
  rw [bilateralSewing_const_mul, bilateralSewing_const_mul]
  have hcancel := bilateralSewing_halves_cancel hlam
  funext e
  have he := congrFun hcancel e
  simp only [Pi.add_apply, Pi.zero_apply] at he ⊢
  rw [← mul_add, he, mul_zero]

/-- Coefficient-faithful endpoint scaling cannot repair bilateral admission: both scaled
orientations are moderate exactly on the critical line. -/
theorem sourceHorizontalEndpointScaledHardy_both_moderate_iff_re_eq_half
    {c : ℂ} (N : ℕ) (hc : c ≠ 0)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    (bilateralModerate
        (sourceHorizontalEndpointScaledHardyPositiveHalf c N
          (bilateralHalfDensityCharacter p rho)) ∧
      bilateralModerate
        (sourceHorizontalEndpointScaledHardyNegativeHalf c N
          (bilateralHalfDensityCharacter p rho))) ↔
      (rho : ℂ).re = 1 / 2 := by
  have hg : sourceHorizontalWoldBVKreinGhostEnergy c N ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (by norm_num)
      (Complex.normSq_pos.mpr hc)) hjet)
  have hgc : (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) ≠ 0 := by
    exact_mod_cast hg
  change
    (bilateralModerate (fun e =>
        (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) *
          hardyPositiveHalf (bilateralHalfDensityCharacter p rho) e) ∧
      bilateralModerate (fun e =>
        (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) *
          hardyNegativeHalf (bilateralHalfDensityCharacter p rho) e)) ↔
      (rho : ℂ).re = 1 / 2
  rw [bilateralModerate_const_mul_iff hgc,
    bilateralModerate_const_mul_iff hgc]
  exact hardyHalves_both_moderate_iff_re_eq_half p.property.two_le rho

/-- Actual positive endpoint-scaled Hardy orientation on one Gamma--Julia Xi multiplicity copy. -/
def sourceHorizontalActualXiEndpointScaledHardyPositiveHalf
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) : ℤ → ℂ :=
  sourceHorizontalEndpointScaledHardyPositiveHalf
    (sourceHorizontalActualXiConormalCoefficient x u q r) N
    (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport))

/-- Actual reflected endpoint-scaled Hardy orientation on the same multiplicity copy. -/
def sourceHorizontalActualXiEndpointScaledHardyNegativeHalf
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) : ℤ → ℂ :=
  sourceHorizontalEndpointScaledHardyNegativeHalf
    (sourceHorizontalActualXiConormalCoefficient x u q r) N
    (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport))

/-- Positive scaled orientation is independent of multiplicity-copy choice in one support fibre. -/
theorem sourceHorizontalActualXiEndpointScaledHardyPositiveHalf_eq_of_support
    (x u r : ℝ) {q s : XiRightZeroCopy} (h : s.1.1 = q.1.1)
    (N : ℕ) (p : Nat.Primes) :
    sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u s r N p =
      sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p := by
  rw [sourceHorizontalActualXiEndpointScaledHardyPositiveHalf,
    sourceHorizontalActualXiEndpointScaledHardyPositiveHalf,
    sourceHorizontalActualXiConormalCoefficient_eq_of_support x u r h, h]

/-- Reflected scaled orientation is likewise support-copy independent. -/
theorem sourceHorizontalActualXiEndpointScaledHardyNegativeHalf_eq_of_support
    (x u r : ℝ) {q s : XiRightZeroCopy} (h : s.1.1 = q.1.1)
    (N : ℕ) (p : Nat.Primes) :
    sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u s r N p =
      sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by
  rw [sourceHorizontalActualXiEndpointScaledHardyNegativeHalf,
    sourceHorizontalActualXiEndpointScaledHardyNegativeHalf,
    sourceHorizontalActualXiConormalCoefficient_eq_of_support x u r h, h]

/-- Summing the positive orientation over the actual support fibre restores analytic
multiplicity exactly. -/
theorem sourceHorizontalActualXiEndpointScaledHardyPositiveHalf_fiber_sum
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) :
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u s.1 r N p) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p := by
  calc
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u s.1 r N p) =
        ∑ _s : XiRightSupportFiber q,
          sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact sourceHorizontalActualXiEndpointScaledHardyPositiveHalf_eq_of_support
              x u r s.2 N p
    _ = Fintype.card (XiRightSupportFiber q) •
          sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p := by simp
    _ = xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p := by
            rw [routePPrimitiveGammaJuliaXiActualSupportFiber_card]

/-- Summing the reflected orientation restores the same analytic multiplicity. -/
theorem sourceHorizontalActualXiEndpointScaledHardyNegativeHalf_fiber_sum
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) :
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u s.1 r N p) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by
  calc
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u s.1 r N p) =
        ∑ _s : XiRightSupportFiber q,
          sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact sourceHorizontalActualXiEndpointScaledHardyNegativeHalf_eq_of_support
              x u r s.2 N p
    _ = Fintype.card (XiRightSupportFiber q) •
          sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by simp
    _ = xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by
            rw [routePPrimitiveGammaJuliaXiActualSupportFiber_card]

/-- Every retained strict-right Xi copy exhibits exact signed sewing cancellation but fails
coefficient-faithful bilateral admission whenever endpoint scale is nonzero. -/
theorem sourceHorizontalActualXiEndpointScaledHardy_cancel_and_not_both_moderate
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    let c := sourceHorizontalActualXiConormalCoefficient x u q r
    let lam := bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)
    bilateralSewing lam (sourceHorizontalEndpointScaledHardyPositiveHalf c N lam) +
        bilateralSewing lam (sourceHorizontalEndpointScaledHardyNegativeHalf c N lam) = 0 ∧
      ¬ (bilateralModerate (sourceHorizontalEndpointScaledHardyPositiveHalf c N lam) ∧
        bilateralModerate (sourceHorizontalEndpointScaledHardyNegativeHalf c N lam)) := by
  dsimp only
  have hc := sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr
  have hp0 : 0 < (p : ℕ) := lt_of_lt_of_le two_pos p.property.two_le
  constructor
  · exact sourceHorizontalEndpointScaledHardySewing_cancel _ N
      (bilateralHalfDensityCharacter_ne_zero hp0 (q.1.1 : XiDivisorSupport))
  · rw [sourceHorizontalEndpointScaledHardy_both_moderate_iff_re_eq_half N hc hjet
      (q.1.1 : XiDivisorSupport) p]
    have hright : 1 / 2 < ((q.1.1 : XiDivisorSupport) : ℂ).re := by
      have hcenter := xiRightCenteredZero_re_pos q
      rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
      norm_num at hcenter ⊢
      linarith
    exact ne_of_gt hright

/-- **Capstone.** Nonlinear signed endpoint annihilation exists, is unique on the diagonal,
preserves the literal Gamma--Julia coefficient and analytic multiplicity, and cancels the two
Hardy--Stokes boundary orientations exactly.  Nevertheless physical `J`-rotation overspends and
the actual strict-right Xi fibre cannot enter the bilateral source topology. -/
theorem sourceHorizontalActualXiIndefiniteEndpointAnnihilation_capstone
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    let c := sourceHorizontalActualXiConormalCoefficient x u q r
    (sourceHorizontalEulerWoldIndefiniteEndpointBlock c q N).trace =
        sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N ∧
      0 < sourceHorizontalWoldBVKreinGhostEnergy c N ∧
      (let lam := bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport);
        bilateralSewing lam (sourceHorizontalEndpointScaledHardyPositiveHalf c N lam) +
            bilateralSewing lam (sourceHorizontalEndpointScaledHardyNegativeHalf c N lam) = 0 ∧
          ¬ (bilateralModerate (sourceHorizontalEndpointScaledHardyPositiveHalf c N lam) ∧
            bilateralModerate
              (sourceHorizontalEndpointScaledHardyNegativeHalf c N lam))) ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u s.1 r N p) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u s.1 r N p) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by
  dsimp only
  have hc := sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr
  exact ⟨sourceHorizontalEulerWoldIndefiniteEndpointBlock_trace _ q N,
    mul_pos (mul_pos (by norm_num) (Complex.normSq_pos.mpr hc)) hjet,
    sourceHorizontalActualXiEndpointScaledHardy_cancel_and_not_both_moderate
      q hkappa hr N hjet p,
    sourceHorizontalActualXiEndpointScaledHardyPositiveHalf_fiber_sum x u q r N p,
    sourceHorizontalActualXiEndpointScaledHardyNegativeHalf_fiber_sum x u q r N p⟩

end

end RHTower
