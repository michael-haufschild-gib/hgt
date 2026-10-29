import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTouchingCrossMatrixHasAUniformErrorBudget

/-!
# The actual charge leaves a uniform prime-defect reserve

A nonzero continuous interval-supported profile has strictly positive variance
against constants. Its normalized charge is therefore strictly below one.
Retaining this charge in the complete center estimate, and using the uniform
cross-error bound, leaves one defect coefficient and one mass floor for every
strictly separated ratio. The eventual horizon may still depend on that ratio.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  ArithmeticLorentzianGeometry ArithmeticElectrostatics SelectiveMultiscaleArithmeticPositivity

/-- A nonzero continuous unit-interval profile has positive variance against constants. -/
theorem profile_square_charge_lt_mass {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    (∫ u, φ u) ^ 2 < ∫ u, φ u ^ 2 := by
  let I : ℝ := ∫ u, φ u
  change I ^ 2 < ∫ u, φ u ^ 2
  by_cases hI : I = 0
  · simpa only [hI, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hM
  have h0 : φ 0 = 0 := by
    have hz : IsClosed {u : ℝ | φ u = 0} := isClosed_eq hφ continuous_const
    have hleft : Set.Iio (0 : ℝ) ⊆ {u : ℝ | φ u = 0} := by
      intro u hu
      exact hsupp u (fun h => (not_le_of_gt hu) h.1)
    have hc := closure_minimal hleft hz
    rw [closure_Iio] at hc
    exact hc (by simp)
  have hi : IntegrableOn φ (Set.Icc (0 : ℝ) 1) := hφ.integrableOn_Icc
  have hi2 : IntegrableOn (fun u => φ u ^ 2) (Set.Icc (0 : ℝ) 1) :=
    (hφ.pow 2).integrableOn_Icc
  have hIres : (∫ u in Set.Icc (0 : ℝ) 1, φ u) = I :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
  have hMres : (∫ u in Set.Icc (0 : ℝ) 1, φ u ^ 2) = ∫ u, φ u ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [hsupp u hu, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hvariance : (∫ u in Set.Icc (0 : ℝ) 1, (φ u - I) ^ 2) =
      (∫ u, φ u ^ 2) - I ^ 2 := by
    have heq : (fun u => (φ u - I) ^ 2) = (fun u => φ u ^ 2 - (2 * I) * φ u + I ^ 2) := by
      funext u
      ring
    have hisub : Integrable (fun u => φ u ^ 2 - (2 * I) * φ u)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      have hc : Continuous (fun u => φ u ^ 2 - (2 * I) * φ u) := by fun_prop
      exact hc.integrableOn_Icc
    rw [heq, integral_add (f := fun u => φ u ^ 2 - (2 * I) * φ u)
      (g := fun _ => I ^ 2) (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
        hisub continuous_const.integrableOn_Icc,
      integral_sub (f := fun u => φ u ^ 2) (g := fun u => (2 * I) * φ u)
        (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
        hi2 (hi.const_mul (2 * I)), integral_const_mul, hIres, hMres]
    simp only [integral_const]
    norm_num
    ring
  have hpos : 0 < ∫ u in (0 : ℝ)..1, (φ u - I) ^ 2 := by
    apply intervalIntegral.integral_pos (by norm_num)
      ((hφ.sub continuous_const).pow 2).continuousOn (fun u _ => sq_nonneg _)
    refine ⟨0, by simp, ?_⟩
    change 0 < (φ 0 - I) ^ 2
    simpa only [h0, zero_sub, neg_sq] using sq_pos_of_ne_zero hI
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
    hvariance] at hpos
  linarith only [hpos]

/-- The actual normalized pole charge is strictly smaller than the width ratio. -/
theorem completeWeilPoleShift_lt_width {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) : completeWeilPoleShift φ c < c := by
  rw [completeWeilPoleShift, div_lt_iff₀ hM]
  exact mul_lt_mul_of_pos_left (profile_square_charge_lt_mass hφ hsupp hM) hc

/-- One mass floor and one positive prime-defect coefficient work at every fixed
strictly separated ratio. Only the eventual horizon may depend on the ratio. -/
theorem exists_uniform_chargeDefect_reserve {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    0 < (1 - completeWeilPoleShift φ 1) / 4 ∧
    ∃ a : ℝ, ∀ c : ℝ, 0 < c → c < 1 →
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
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
    q * ((1 + lam) * psiConstant + 15) - 4 * C - 2 * P
  refine ⟨hε, a, fun c hc0 hc1 => ?_⟩
  let α := completeWeilPoleShift φ c
  have hα0 : 0 ≤ α := completeWeilPoleShift_nonneg φ hc0.le
  have hαq : α ≤ q := by
    have he : α = c * q := by dsimp only [α, q, completeWeilPoleShift]; ring
    rw [he]
    exact (mul_le_mul_of_nonneg_right hc1.le hq0).trans_eq (one_mul q)
  have hcoef : α * (1 + 1 / lam) ≤ (1 + q) / 2 := by
    calc
      _ ≤ q * (1 + 1 / lam) := mul_le_mul_of_nonneg_right hαq (by positivity)
      _ = q * (1 + (1 - q) / 2) := by dsimp only [lam]; rw [one_div_div]
      _ ≤ _ := by nlinarith only [sq_nonneg (1 - q)]
  have hcSq : c ^ 2 ≤ 1 := by
    simpa only [← pow_two, one_pow] using mul_le_mul hc1.le hc1.le hc0.le zero_le_one
  have hselfFloor : completeWeilSelfFinitePart φ 1 ≤ completeWeilSelfFinitePart φ c := by
    unfold completeWeilSelfFinitePart
    apply add_le_add ?_ le_rfl
    simp only [mul_one]
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le (by positivity)
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hc1.le (show 0 ≤ 2 * Real.pi by positivity))
  have hP : 2 * atomPoleMomentErrorConstant φ * c ^ 2 ≤ 2 * P := by
    calc
      _ ≤ (2 * P) * c ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) (sq_nonneg c)
      _ ≤ 2 * P := (mul_le_mul_of_nonneg_left hcSq (by dsimp only [P]; positivity)).trans_eq (mul_one _)
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1,
    eventually_div_horizon_lt_atomSpacing hc0 hc1] with N hN hN1 hsep x
  have hp := hN₀ N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension] at hp
  have hcenter := fullWeilCenterMatrix_inner_ge hα0 hlam hN1 x
  have hcenterCost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hαq hK) (sq_nonneg ‖x‖)
  have hcross := (abs_le.mp (hcrossBound c hc0 hc1.le N hN1 x)).2
  have hcrossCost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcSq (by positivity : 0 ≤ 4 * C)) (sq_nonneg ‖x‖)
  have hpole := (abs_le.mp (abs_fullWeilPoleErrorMatrix_inner_le hφ hsupp hM hc0 hc1 hN1 x)).1
  have hpoleCost := mul_le_mul_of_nonneg_right hP (sq_nonneg ‖x‖)
  have hself := (abs_le.mp (abs_completeWeilSelfError_le hφ hsupp hM hc0 hc1 hN1)).1
  have hwidth := mul_le_mul_of_nonneg_left hsep.2.1
    (show 0 ≤ Real.exp (1 / 2) / 2 by positivity)
  have hselfLower : -Real.exp (1 / 2) / 2 ≤ completeWeilSelfError φ c N := by
    linarith only [hself, hwidth]
  have hselfCost := mul_le_mul_of_nonneg_right hselfLower (sq_nonneg ‖x‖)
  have hfloorCost := mul_le_mul_of_nonneg_right hselfFloor (sq_nonneg ‖x‖)
  have hdefect := mul_le_mul_of_nonneg_right hcoef
    (poleDefect_nonneg N (primeHorizonExtension x))
  rw [completeWeilEnergy_eq_decomposition hφ hsupp hM hc0 hN1 hsep.2.2]
  dsimp only [a, ε] at *
  unfold renormalizedPrimeEnergy
  linarith only [hp, hcenter, hcenterCost, hcross, hcrossCost, hpole, hpoleCost,
    hselfCost, hfloorCost, hdefect]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.profile_square_charge_lt_mass
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_uniform_chargeDefect_reserve
