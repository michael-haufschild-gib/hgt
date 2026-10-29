import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheChargeDeficitKeepsAUniformPrimeReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixKeepsItsBoundaryCorrection
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSelfAndPoleErrorsStayUniformAtTouching

/-!
# One complete-energy reserve through touching

Strict profile charge, uniform cross errors, and the vanishing actual boundary
prime source leave one positive fraction of the prime defect. Both the mass
floor and the eventual horizon are common to every ratio in `(0,1]`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  ArithmeticLorentzianGeometry ArithmeticElectrostatics SelectiveMultiscaleArithmeticPositivity

/-- One horizon and one mass floor retain a fixed positive prime-defect fraction
simultaneously at every width ratio up to and including one. -/
theorem exists_uniform_completeWeil_primeDefect_reserve_through_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    0 < (1 - completeWeilPoleShift φ 1) / 4 ∧
    ∃ a : ℝ, ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        a * ‖x‖ ^ 2 + ((1 - completeWeilPoleShift φ 1) / 4) *
          poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x := by
  let q := completeWeilPoleShift φ 1
  have hq0 : 0 ≤ q := completeWeilPoleShift_nonneg φ zero_le_one
  have hq1 : q < 1 := completeWeilPoleShift_lt_width hφ.continuous hsupp hM zero_lt_one
  let ε : ℝ := (1 - q) / 4
  let lam : ℝ := 2 / (1 - q)
  have hε : 0 < ε := div_pos (sub_pos.mpr hq1) (by norm_num)
  have hlam : 0 < lam := div_pos (by norm_num) (sub_pos.mpr hq1)
  have hK : 0 ≤ (1 + lam) * psiConstant + 15 := by
    have hp := psiConstant_pos.le
    positivity
  obtain ⟨C, hC, hcrossBound⟩ := exists_uniform_fullWeilCrossError_at_touching hφ hsupp hM
  let P := |atomPoleMomentErrorConstant φ|
  let a := completeWeilSelfFinitePart φ 1 - ε - Real.exp (1 / 2) / 2 -
    q * ((1 + lam) * psiConstant + 15) - 4 * C - 2 * P - 1
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  refine ⟨hε, a, ?_⟩
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1,
    eventually_fullWeilNonRatioMatrix_small_uniformly hφ hsupp hM zero_lt_one]
    with N hN hN1 hNR
  intro c hc0 hc1 x
  let α := completeWeilPoleShift φ c
  have hα0 : 0 ≤ α := completeWeilPoleShift_nonneg φ hc0.le
  have hαq : α ≤ q := by
    have he : α = c * q := by dsimp only [α, q, completeWeilPoleShift]; ring
    rw [he]
    exact (mul_le_mul_of_nonneg_right hc1 hq0).trans_eq (one_mul q)
  have hcoef : α * (1 + 1 / lam) ≤ (1 + q) / 2 := by
    calc
      _ ≤ q * (1 + 1 / lam) := mul_le_mul_of_nonneg_right hαq (by positivity)
      _ = q * (1 + (1 - q) / 2) := by dsimp only [lam]; rw [one_div_div]
      _ ≤ _ := by nlinarith only [sq_nonneg (1 - q)]
  have hcSq : c ^ 2 ≤ 1 := by
    simpa only [← pow_two, one_pow] using mul_le_mul hc1 hc1 hc0.le zero_le_one
  have hselfFloor : completeWeilSelfFinitePart φ 1 ≤ completeWeilSelfFinitePart φ c := by
    unfold completeWeilSelfFinitePart
    apply add_le_add ?_ le_rfl
    simp only [mul_one]
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le (by positivity)
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hc1 (show 0 ≤ 2 * Real.pi by positivity))
  have hP : 2 * atomPoleMomentErrorConstant φ * c ^ 2 ≤ 2 * P := by
    calc
      _ ≤ (2 * P) * c ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) (sq_nonneg c)
      _ ≤ 2 * P := (mul_le_mul_of_nonneg_left hcSq (by dsimp only [P]; positivity)).trans_eq (mul_one _)
  have hp := hN₀ N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension] at hp
  have hcenter := fullWeilCenterMatrix_inner_ge hα0 hlam hN1 x
  have hcenterCost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hαq hK) (sq_nonneg ‖x‖)
  have hcross := (abs_le.mp (hcrossBound c hc0 hc1 N hN1 x)).2
  have hcrossCost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcSq (by positivity : 0 ≤ 4 * C)) (sq_nonneg ‖x‖)
  have hpole := (abs_le.mp
    (abs_fullWeilPoleErrorMatrix_inner_le_at_touching hφ hsupp hM hc0 hc1 hN1 x)).1
  have hpoleCost := mul_le_mul_of_nonneg_right hP (sq_nonneg ‖x‖)
  have hself := (abs_le.mp
    (abs_completeWeilSelfError_le_at_touching hφ hsupp hM hc0 hc1 hN1)).1
  have hw : c / (N : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hN1)).mpr
    (hc1.trans (by exact_mod_cast hN1))
  have hwidth := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ Real.exp (1 / 2) / 2 by positivity)
  have hselfLower : -Real.exp (1 / 2) / 2 ≤ completeWeilSelfError φ c N := by
    linarith only [hself, hwidth]
  have hselfCost := mul_le_mul_of_nonneg_right hselfLower (sq_nonneg ‖x‖)
  have hfloorCost := mul_le_mul_of_nonneg_right hselfFloor (sq_nonneg ‖x‖)
  have hdefect := mul_le_mul_of_nonneg_right hcoef
    (poleDefect_nonneg N (primeHorizonExtension x))
  have hnonRatio := (abs_le.mp (hNR c hc0 hc1 x)).2
  rw [completeWeilEnergy_eq_decomposition_at_touching hφ hsupp hM hc0 hc1 hN1]
  dsimp only [a, ε] at *
  unfold renormalizedPrimeEnergy
  linarith only [hp, hcenter, hcenterCost, hcross, hcrossCost, hpole, hpoleCost,
    hselfCost, hfloorCost, hdefect, hnonRatio]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_uniform_completeWeil_primeDefect_reserve_through_touching
