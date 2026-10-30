import GaloisForLFunctions.CompletedArithmeticForms.WeilPolynomialResidual
import GaloisForLFunctions.CompletedArithmeticForms.WeilGreenModes
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTiltedSplineHasAPolynomialConductorFloor
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGevreyWindow

/-!
# Relative complete Weil quasimodes at growing overlap

Every literal residual term is small relative to the actual vanishing
conductor reserve along `c_N = (log N)^α`, `0 < α < 1/40`.
The joint strip and horizon inequalities are paid on this same schedule.
This statement concerns each fixed conductor, with no full-matrix positivity
claim at growing overlap.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- An explicit unbounded overlap schedule for complete conductor packets. -/
def logarithmicPacketOverlap (α : ℝ) (N : ℕ) : ℝ := Real.log (N : ℝ) ^ α

/-- The positive coefficient of the actual common conductor floor. -/
def tiltedConductorFloorCoefficient : ℝ :=
  2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)

theorem tiltedConductorFloorCoefficient_pos : 0 < tiltedConductorFloorCoefficient :=
  div_pos (mul_pos zero_lt_two tiltedSplineTailConstant_pos) integral_tiltedUnitSpline_sq_pos

private theorem packetOverlap_pow (α : ℝ) (N k : ℕ) :
    logarithmicPacketOverlap α N ^ k = Real.log (N : ℝ) ^ (α * (k : ℝ)) := by
  rw [Real.rpow_mul (Real.log_natCast_nonneg N), Real.rpow_natCast]
  rfl

private theorem tendsto_packetOverlap_pow_div (α : ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => logarithmicPacketOverlap α N ^ k / N) atTop (𝓝 0) := by
  simpa only [packetOverlap_pow, Nat.mul_one] using
    (tendsto_log_rpow_div (r := α * (k : ℝ)) (B := 1) (by decide))

theorem tendsto_logarithmicPacketOverlap_atTop {α : ℝ} (hα : 0 < α) :
    Tendsto (logarithmicPacketOverlap α) atTop atTop :=
  (tendsto_rpow_atTop hα).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The explicit moving overlap satisfies every literal source domain eventually. -/
theorem eventually_logarithmicPacketOverlap_source_domain {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ logarithmicPacketOverlap α N ∧ logarithmicPacketOverlap α N / N ≤ 1 / 3 ∧
      linearPrimeStrip (logarithmicPacketOverlap α N) ≤ N ∧
      2 * ((Real.exp 1 + 3) * logarithmicPacketOverlap α N) *
        linearPrimeStrip (logarithmicPacketOverlap α N) ≤ (N : ℝ) := by
  let M := 2 * (Real.exp 1 + 3) * (Real.exp 1 + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  have h1 := (tendsto_packetOverlap_pow_div α 1).eventually
    (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  have h2 := (tendsto_packetOverlap_pow_div α 2).eventually
    (ge_mem_nhds (inv_pos.mpr hM))
  filter_upwards [(tendsto_logarithmicPacketOverlap_atTop hα).eventually_ge_atTop 1,
    h1, h2, eventually_ge_atTop 1] with N hc hw hsq hN
  let c := logarithmicPacketOverlap α N
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ c * Real.exp 1 by positivity)
    change (linearPrimeStrip c : ℝ) < c * Real.exp 1 + 1 at h
    nlinarith only [h, hc]
  have hMN : M * c ^ 2 ≤ (N : ℝ) := by
    have h := (div_le_iff₀ hN0).mp hsq
    have hp := mul_le_mul_of_nonneg_left h hM.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul] using hp
  have hlarge : 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) := by
    calc
      _ ≤ 2 * ((Real.exp 1 + 3) * c) * ((Real.exp 1 + 1) * c) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = M * c ^ 2 := by dsimp only [M]; ring
      _ ≤ _ := hMN
  have hBN : linearPrimeStrip c ≤ N := by
    have hf : 1 ≤ 2 * ((Real.exp 1 + 3) * c) := by
      have he := Real.exp_pos (1 : ℝ)
      nlinarith only [hc, he, mul_nonneg he.le (sub_nonneg.mpr hc)]
    have h := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg (linearPrimeStrip c))
    have h' : (linearPrimeStrip c : ℝ) ≤ N := by linarith only [h, hlarge]
    exact_mod_cast h'
  exact ⟨hc, by simpa only [pow_one] using hw, hBN, hlarge⟩

/-- The squared residual cost after division by the common `c⁻⁷` reserve. -/
def relativeWeilResidualScale (c : ℝ) (N : ℕ) : ℝ :=
  c ^ 24 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 20 / Real.sqrt (Real.log N)

theorem relativeWeilResidualScale_eq (c : ℝ) (N : ℕ) :
    relativeWeilResidualScale c N = c ^ 14 * weilResidualScale c N := by
  unfold relativeWeilResidualScale weilResidualScale
  ring

/-- Every source term is paid relative to the actual completed conductor energy. -/
theorem exists_tiltedWeil_relative_polynomial_residual_bound {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 / 3 →
      linearPrimeStrip c ≤ N → 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
        completedConductorEnergy tiltedUnitSpline c m ^ 2 ≤ C * relativeWeilResidualScale c N := by
  obtain ⟨C, hC, hbound⟩ := exists_tiltedWeil_polynomial_residual_bound hm
  let κ := tiltedConductorFloorCoefficient
  have hκ : 0 < κ := tiltedConductorFloorCoefficient_pos
  refine ⟨C / κ ^ 2, by positivity, ?_⟩
  filter_upwards [hbound] with N hN
  intro c hc hw hB hg
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hf := tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc hm
  change κ / c ^ 7 ≤ _ at hf
  have hf0 : 0 < κ / c ^ 7 := div_pos hκ (pow_pos hc0 7)
  have hfsq := pow_le_pow_left₀ hf0.le hf 2
  calc
    _ ≤ (C * weilResidualScale c N) / completedConductorEnergy tiltedUnitSpline c m ^ 2 :=
      div_le_div_of_nonneg_right (hN c hc hw hB hg) (sq_nonneg _)
    _ ≤ (C * weilResidualScale c N) / (κ / c ^ 7) ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg hC.le (weilResidualScale_nonneg c N))
        (sq_pos_of_pos hf0) hfsq
    _ = _ := by
      rw [relativeWeilResidualScale_eq]
      field_simp
      <;> ring

private theorem tendsto_log_power_zero {r : ℝ} (hr : r < 0) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ r) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (neg_pos.mpr hr)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  simpa only [Real.rpow_neg (Real.log_natCast_nonneg _), inv_inv] using h

/-- A fixed overlap power is paid by the logarithmic Gram denominator below its exact threshold. -/
theorem tendsto_packetOverlap_pow_div_log {α : ℝ} (k : ℕ) (hk : α * (k : ℝ) < 1) :
    Tendsto (fun N : ℕ => logarithmicPacketOverlap α N ^ k / Real.log N)
      atTop (𝓝 0) := by
  apply (tendsto_log_power_zero (sub_neg.mpr hk)).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [packetOverlap_pow, Real.rpow_sub hL, Real.rpow_one]

/-- Both complete-source costs vanish on the same explicit overlap schedule. -/
theorem tendsto_relativeWeilResidualScale_zero {α : ℝ} (hα : α < 1 / 40) :
    Tendsto (fun N : ℕ => relativeWeilResidualScale (logarithmicPacketOverlap α N) N)
      atTop (𝓝 0) := by
  have hfirst := ((tendsto_log_rpow_div (r := 24 * α + 2) (B := 1) (by decide)).mul
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop))
  have hsecond := tendsto_log_power_zero (r := 20 * α - 1 / 2) (by linarith only [hα])
  have h := hfirst.add hsecond
  simp only [zero_mul, zero_add, Nat.mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [relativeWeilResidualScale, packetOverlap_pow, packetOverlap_pow,
    Real.sqrt_eq_rpow, Real.rpow_sub hL, Real.rpow_add hL]
  rw [show α * (24 : ℝ) = 24 * α by ring, show α * (20 : ℝ) = 20 * α by ring,
    Real.rpow_two]
  ring

/-- Every actual normalized conductor residual vanishes after multiplication by `c⁷`. -/
theorem tendsto_tiltedWeil_scaled_residual_norm {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 40)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => logarithmicPacketOverlap α N ^ 7 *
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (logarithmicPacketOverlap α N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) m •
          normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_tiltedWeil_polynomial_residual_bound hm
  have hlim := (tendsto_relativeWeilResidualScale_zero hα).const_mul C
  simp only [mul_zero] at hlim
  have hsq : Tendsto (fun N : ℕ => (logarithmicPacketOverlap α N ^ 7 *
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (logarithmicPacketOverlap α N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) m •
          normalizedRamanujanHorizonVector m N‖) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) _ hlim
    filter_upwards [hbound, eventually_logarithmicPacketOverlap_source_domain hα0] with N hN hd
    have h := mul_le_mul_of_nonneg_left (hN _ hd.1 hd.2.1 hd.2.2.1 hd.2.2.2)
      (pow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) α) 14)
    rw [relativeWeilResidualScale_eq]
    convert h using 1 <;> ring
  have h := hsq.sqrt
  rw [Real.sqrt_zero] at h
  apply h.congr
  intro N
  exact Real.sqrt_sq (by dsimp only [logarithmicPacketOverlap]; positivity)

/-- The actual residual is small relative to the actual completed conductor energy. -/
theorem tendsto_tiltedWeil_relative_residual_norm {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 40)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (logarithmicPacketOverlap α N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) m •
          normalizedRamanujanHorizonVector m N‖ /
        completedConductorEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) m)
      atTop (𝓝 0) := by
  have hlim := (tendsto_tiltedWeil_scaled_residual_norm hα0 hα hm).div_const
    tiltedConductorFloorCoefficient
  simp only [zero_div] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_logarithmicPacketOverlap_source_domain hα0] with N hd
    exact div_nonneg (norm_nonneg _) (tiltedWeilConductorEnergy_pos (zero_lt_one.trans_le hd.1) hm).le
  · filter_upwards [eventually_logarithmicPacketOverlap_source_domain hα0] with N hd
    have hc : 0 < logarithmicPacketOverlap α N := zero_lt_one.trans_le hd.1
    have hE := tiltedWeilConductorEnergy_pos hc hm
    have hf := tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hd.1 hm
    change tiltedConductorFloorCoefficient / logarithmicPacketOverlap α N ^ 7 ≤ _ at hf
    rw [div_le_iff₀ (pow_pos hc 7)] at hf
    rw [div_le_div_iff₀ hE tiltedConductorFloorCoefficient_pos]
    have h := mul_le_mul_of_nonneg_left hf (norm_nonneg
      (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (logarithmicPacketOverlap α N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) m •
          normalizedRamanujanHorizonVector m N))
    nlinarith only [h]

#print axioms eventually_logarithmicPacketOverlap_source_domain
#print axioms exists_tiltedWeil_relative_polynomial_residual_bound
#print axioms tendsto_relativeWeilResidualScale_zero
#print axioms tendsto_tiltedWeil_scaled_residual_norm
#print axioms tendsto_tiltedWeil_relative_residual_norm

end GaloisForLFunctions.CompletedArithmeticForms
