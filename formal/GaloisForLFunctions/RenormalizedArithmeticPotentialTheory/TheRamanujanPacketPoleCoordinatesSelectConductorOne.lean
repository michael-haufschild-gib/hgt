import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneIsTheHarmonicHyperplane

/-!
# The two pole coordinates of finite Ramanujan packets

Ordinary and logarithmic averaging select the constant Ramanujan mode.
The actual exponential atom moments retain their quadratic dilation error,
so both poles contribute exactly twice the ground-mode pole shift to the
limiting packet form.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry

/-- The constant-mode coefficient, extended by zero outside the packet. -/
def ramanujanPacketGroundCoefficient (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  if 1 ∈ S then b 1 else 0

/-- The actual shrinking-atom test synthesized from a finite Ramanujan packet. -/
def ramanujanPacketTest (φ : ℝ → ℝ) (c : ℝ) (S : Finset ℕ) (b : ℕ → ℝ)
    (N : ℕ) : ℝ → ℝ :=
  atomicTest N (ramanujanPacketProfile S b) (atomDilate φ (c / N))

private theorem packet_mode_one (n : ℕ) : normalizedRamanujanMode 1 n = 1 := by
  simp only [normalizedRamanujanMode, ramanujanMode_one,
    Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one]

/-- The harmonic pole coordinate of a mode tends to its constant-mode label. -/
theorem tendsto_ramanujan_mode_harmonic_pole {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n / Real.sqrt n) / Real.log N)
      atTop (𝓝 (if m = 1 then 1 else 0)) := by
  simpa only [ramanujanPoleProfile, packet_mode_one, mul_one_div] using
    tendsto_ramanujanPoleProfile_gram hm zero_lt_one

private theorem packet_mode_period_sum_zero {m : ℕ} (hm : 0 < m) (hm1 : m ≠ 1) :
    ∑ j ∈ range m, normalizedRamanujanMode m j = 0 := by
  have h := periodMean_normalizedRamanujanMode_mul hm zero_lt_one dvd_rfl (one_dvd m) hm
  simp only [packet_mode_one, mul_one, if_neg hm1, RenormalizedBiarithmeticGeometry.periodMean] at h
  rcases div_eq_zero_iff.mp h with h | h
  · exact h
  · exact False.elim ((by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0) h)

/-- The ordinary mean of each positive-conductor mode is its constant-mode label. -/
theorem tendsto_ramanujan_mode_ordinary_mean {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n) / (N : ℝ))
      atTop (𝓝 (if m = 1 then 1 else 0)) := by
  by_cases hm1 : m = 1
  · subst m
    rw [if_pos rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp only [packet_mode_one, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, mul_one, div_self hN0]
  · rw [if_neg hm1]
    have hbound (N : ℕ) : |∑ n ∈ Icc 1 N, normalizedRamanujanMode m n| ≤
        2 * ∑ j ∈ range m, |normalizedRamanujanMode m j| := by
      simpa only [Ico_add_one_right_eq_Icc] using
        HTGeometry.abs_sum_Ico_le_of_periodic hm (normalizedRamanujanMode_periodic hm)
          (packet_mode_period_sum_zero hm hm1) 1 (N + 1) (by omega)
    apply squeeze_zero_norm (fun N => ?_)
      (show Tendsto (fun N : ℕ =>
        (2 * ∑ j ∈ range m, |normalizedRamanujanMode m j|) / (N : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)]
    exact div_le_div_of_nonneg_right (hbound N) (Nat.cast_nonneg N)

/-- The second pole coordinate is the ordinary mean of the mode. -/
theorem tendsto_ramanujan_mode_ordinary_pole {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * Real.sqrt n) / (N : ℝ))
      atTop (𝓝 (if m = 1 then 1 else 0)) := by
  refine (tendsto_ramanujan_mode_ordinary_mean hm).congr fun N => ?_
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n from (mem_Icc.mp hn).1))).ne'
  rw [ramanujanPoleProfile, div_mul_cancel₀ _ hn0]

/-- The first packet pole coordinate converges to the constant-mode coefficient. -/
theorem tendsto_ramanujanPacket_harmonic_pole
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ramanujanPacketProfile S b n / Real.sqrt n) / Real.log N)
      atTop (𝓝 (ramanujanPacketGroundCoefficient S b)) := by
  classical
  have h := tendsto_finsetSum S fun m hm =>
    (tendsto_ramanujan_mode_harmonic_pole (hS m hm)).const_mul (b m)
  have heq (N : ℕ) :
      (∑ m ∈ S, b m * ((∑ n ∈ Icc 1 N, ramanujanPoleProfile m n / Real.sqrt n) / Real.log N)) =
        (∑ n ∈ Icc 1 N, ramanujanPacketProfile S b n / Real.sqrt n) / Real.log N := by
    simp only [ramanujanPacketProfile, sum_div, mul_div_assoc, mul_sum]
    rw [sum_comm]
  simpa only [heq, mul_ite, mul_one, mul_zero, sum_ite_eq', sum_ite_eq,
    ramanujanPacketGroundCoefficient] using h

/-- The second packet pole coordinate has the same constant-mode limit. -/
theorem tendsto_ramanujanPacket_ordinary_pole
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ramanujanPacketProfile S b n * Real.sqrt n) / (N : ℝ))
      atTop (𝓝 (ramanujanPacketGroundCoefficient S b)) := by
  classical
  have h := tendsto_finsetSum S fun m hm =>
    (tendsto_ramanujan_mode_ordinary_pole (hS m hm)).const_mul (b m)
  have heq (N : ℕ) :
      (∑ m ∈ S, b m * ((∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * Real.sqrt n) / (N : ℝ))) =
        (∑ n ∈ Icc 1 N, ramanujanPacketProfile S b n * Real.sqrt n) / (N : ℝ) := by
    simp only [ramanujanPacketProfile, sum_div, sum_mul, mul_div_assoc, mul_sum, mul_assoc]
    rw [sum_comm]
  simpa only [heq, mul_ite, mul_one, mul_zero, sum_ite_eq', sum_ite_eq,
    ramanujanPacketGroundCoefficient] using h

/-- Multiplying the actual normalized pole product by the horizon leaves its charge. -/
theorem tendsto_horizon_mul_normalized_atom_pole_product {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) *
      (atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) *
        atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) /
          (∫ u, atomDilate φ (c / N) u ^ 2))) atTop (𝓝 (completeWeilPoleShift φ c)) := by
  have herr : Tendsto (fun N : ℕ => (N : ℝ) * atomPoleErrorCoefficient φ c N)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      (show Tendsto (fun N : ℕ => atomPoleMomentErrorConstant φ * c ^ 2 / (N : ℝ))
        atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hN0]
    calc
      _ ≤ (N : ℝ) * (atomPoleMomentErrorConstant φ * (c / N) ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_atomPoleErrorCoefficient_le hφ hsupp hM hc0 hc1 hN) hN0.le
      _ = _ := by field_simp [hN0.ne']
  have heq : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * atomPoleErrorCoefficient φ c N + completeWeilPoleShift φ c =
        (N : ℝ) * (atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) *
          atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) /
            (∫ u, atomDilate φ (c / N) u ^ 2)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [atomPoleErrorCoefficient, mul_sub]
    have hcancel : (N : ℝ) * (completeWeilPoleShift φ c / N) = completeWeilPoleShift φ c := by
      field_simp [hN0]
    rw [hcancel]
    ring
  simpa only [zero_add] using (herr.add_const (completeWeilPoleShift φ c)).congr' heq

private theorem packet_atom_moment_neg_half (g : ℝ → ℝ) :
    atomExponentialMoment g (-(1 / 2)) = ∫ u, g u * Real.exp (-(u / 2)) := by
  unfold atomExponentialMoment
  congr 1
  funext u
  congr 2
  ring

private theorem packet_atom_moment_half (g : ℝ → ℝ) :
    atomExponentialMoment g (1 / 2) = ∫ u, g u * Real.exp (u / 2) := by
  unfold atomExponentialMoment
  congr 1
  funext u
  congr 2
  ring

/-- Both actual poles select twice the squared constant Ramanujan coordinate. -/
theorem tendsto_ramanujanPacketTest_two_poles {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (2 * (∫ u, ramanujanPacketTest φ c S b N u * Real.exp (-(u / 2))) *
        (∫ u, ramanujanPacketTest φ c S b N u * Real.exp (u / 2))) / ((c / N) * Real.log N))
      atTop (𝓝 (2 * c * (∫ u, φ u) ^ 2 * ramanujanPacketGroundCoefficient S b ^ 2)) := by
  have h := (((tendsto_horizon_mul_normalized_atom_pole_product hφ hsupp hM hc0 hc1).const_mul
    (2 * ∫ u, φ u ^ 2)).mul (tendsto_ramanujanPacket_harmonic_pole S hS b)).mul
      (tendsto_ramanujanPacket_ordinary_pole S hS b)
  have hvalue : (2 * (∫ u, φ u ^ 2) * completeWeilPoleShift φ c *
      ramanujanPacketGroundCoefficient S b) * ramanujanPacketGroundCoefficient S b =
        2 * c * (∫ u, φ u) ^ 2 * ramanujanPacketGroundCoefficient S b ^ 2 := by
    rw [completeWeilPoleShift]
    field_simp [hM.ne']
  rw [hvalue] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw : 0 < c / N := div_pos hc0 hN0
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  rw [ramanujanPacketTest,
    SelectiveMultiscaleArithmeticPositivity.integral_atomicTest_mul_exp_neg_half hg.continuous hgs,
    SelectiveMultiscaleArithmeticPositivity.integral_atomicTest_mul_exp_half hg.continuous hgs,
    ← packet_atom_moment_neg_half, ← packet_atom_moment_half, integral_atomDilate_sq hw]
  field_simp [hN0.ne', hc0.ne', hM.ne', hlog.ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
