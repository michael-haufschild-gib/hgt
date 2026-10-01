import GaloisForLFunctions.RHTower.PMPrimeLogMeanMellin
import GaloisForLFunctions.RHTower.FermiNymanLogMobiusAuxiliaryVariance

/-!
# The continuous scalar budget forced by fixed logarithmic coefficients

Exact coefficient cells and prime-mean increments transfer the canonical Fermi
error budget to the literal continuous mean defect. If that canonical error
tends to zero, the defect is `o(log x / sqrt x)`. This is a necessary condition;
no convergence of the canonical approximation is asserted here.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem pmLogMobius_realCutoff_eq_floor {x : ℝ} (hx : 1 ≤ x) :
    Sieve.moebiusShiftedLogKernelReal 0 x = logMobiusHarmonicSum ⌊x⌋₊ +
      Real.log (x / (⌊x⌋₊ : ℝ)) * deningerHarmonicPartial ⌊x⌋₊ := by
  rw [Sieve.moebiusShiftedLogKernelReal_eq]
  simp only [zero_mul, add_zero]
  exact Sieve.coprimeLogMoebius_one_eq_floor x hx

theorem pmLogMobius_realCutoff_cell_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |Sieve.moebiusShiftedLogKernelReal 0 x - logMobiusHarmonicSum ⌊x⌋₊| ≤
        C / (⌊x⌋₊ : ℝ) := by
  obtain ⟨C, hC⟩ := deningerHarmonicPartial_bounded
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨C, hC0, ?_⟩
  intro x hx
  let N := ⌊x⌋₊
  have hn1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
  have hnle : (N : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hxt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hratio : 1 ≤ x / (N : ℝ) := (one_le_div hnpos).mpr hnle
  have hlog0 : 0 ≤ Real.log (x / (N : ℝ)) := Real.log_nonneg hratio
  have hlog : Real.log (x / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    calc
      _ ≤ x / (N : ℝ) - 1 := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hratio)
      _ = (x - N) / (N : ℝ) := by field_simp
      _ ≤ 1 / (N : ℝ) := div_le_div_of_nonneg_right (by linarith) hnpos.le
  rw [pmLogMobius_realCutoff_eq_floor hx, add_sub_cancel_left, abs_mul,
    abs_of_nonneg hlog0]
  calc
    _ ≤ (1 / (N : ℝ)) * C :=
      mul_le_mul hlog (hC N) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem pm_psi_div_le_seven {x : ℝ} (hx : 0 < x) :
    Chebyshev.psi x / x ≤ 7 := by
  have h := Chebyshev.psi_le_const_mul_self hx.le
  have hc : Real.log 4 + 4 ≤ (7 : ℝ) := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  exact (div_le_iff₀ hx).mpr (h.trans (mul_le_mul_of_nonneg_right hc hx.le))

theorem pm_integrable_psi_div_Ioc {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x => Chebyshev.psi x / x) (Ioc a b) := by
  have h : IntegrableOn (fun x => Chebyshev.psi x / x) (Ioo 0 b) := by
    exact (integrableOn_sub_psi_div 0 b).neg.congr_fun
      (fun x _ => by simp) measurableSet_Ioo
  have h' : IntegrableOn (fun x => Chebyshev.psi x / x) (Ioc 0 b) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr h
  exact h'.mono_set (fun x hx => ⟨lt_of_le_of_lt ha hx.1, hx.2⟩)

theorem pmPrimeLogMean_eq_integral_Ioo {x : ℝ} (hx : 1 ≤ x) :
    pmPrimeLogMean x = x⁻¹ * ∫ y in Ioo (0 : ℝ) x, Chebyshev.psi y / y := by
  rw [pmPrimeLogMean_eq_integral_Ioc hx, ← integral_Ioc_eq_integral_Ioo]
  have hsplit : (∫ y in Ioc (0 : ℝ) x, Chebyshev.psi y / y) =
      (∫ y in Ioc (0 : ℝ) 1, Chebyshev.psi y / y) +
        ∫ y in Ioc (1 : ℝ) x, Chebyshev.psi y / y := by
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hx]
    apply setIntegral_union
    · rw [disjoint_left]
      exact fun y hy hy' => (not_lt_of_ge hy.2) hy'.1
    · exact measurableSet_Ioc
    · exact pm_integrable_psi_div_Ioc (by norm_num)
    · exact pm_integrable_psi_div_Ioc zero_le_one
  have hz : (∫ y in Ioc (0 : ℝ) 1, Chebyshev.psi y / y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith [hy.2]), zero_div]
  rw [hsplit, hz, zero_add]

theorem pmPrimeLogMean_nat_succ (N : ℕ) :
    pmPrimeLogMean ((N : ℝ) + 1) = chebyshevProfileMean N := by
  rw [pmPrimeLogMean_eq_integral_Ioo
      (by linarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N] : (1 : ℝ) ≤ (N : ℝ) + 1),
    chebyshevProfileMean]
  ring

theorem pmPrimeLogMean_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ pmPrimeLogMean x ∧ pmPrimeLogMean x ≤ 7 := by
  have hx0 := zero_lt_one.trans_le hx
  rw [pmPrimeLogMean_eq_integral_Ioo hx]
  have hI0 : 0 ≤ ∫ y in Ioo (0 : ℝ) x, Chebyshev.psi y / y := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact div_nonneg (Chebyshev.psi_nonneg _) hy.1.le
  have hI : (∫ y in Ioo (0 : ℝ) x, Chebyshev.psi y / y) ≤ 7 * x := by
    have hq : IntegrableOn (fun y => Chebyshev.psi y / y) (Ioo 0 x) :=
      (pm_integrable_psi_div_Ioc (a := 0) (b := x) le_rfl).mono_set Ioo_subset_Ioc_self
    have hc : IntegrableOn (fun _ : ℝ => (7 : ℝ)) (Ioo 0 x) :=
      integrableOn_const measure_Ioo_lt_top.ne
    calc
      _ ≤ ∫ y in Ioo (0 : ℝ) x, (7 : ℝ) := by
        apply integral_mono_ae hq hc
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        exact pm_psi_div_le_seven hy.1
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hx0.le]
        simp only [sub_zero, smul_eq_mul]
        ring
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hx0.le) hI0
  · calc
      _ ≤ x⁻¹ * (7 * x) := mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hx0.le)
      _ = 7 := by field_simp

theorem pmPrimeLogMean_increment {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    y * pmPrimeLogMean y - x * pmPrimeLogMean x =
      ∫ t in Ioc x y, Chebyshev.psi t / t := by
  have hx0 := zero_lt_one.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hxmean : x * pmPrimeLogMean x = ∫ t in Ioc (1 : ℝ) x, Chebyshev.psi t / t := by
    rw [pmPrimeLogMean_eq_integral_Ioc hx, ← mul_assoc, mul_inv_cancel₀ hx0.ne', one_mul]
  have hymean : y * pmPrimeLogMean y = ∫ t in Ioc (1 : ℝ) y, Chebyshev.psi t / t := by
    rw [pmPrimeLogMean_eq_integral_Ioc (hx.trans hxy), ← mul_assoc,
      mul_inv_cancel₀ hy0.ne', one_mul]
  have hsplit : (∫ t in Ioc (1 : ℝ) y, Chebyshev.psi t / t) =
      (∫ t in Ioc (1 : ℝ) x, Chebyshev.psi t / t) +
        ∫ t in Ioc x y, Chebyshev.psi t / t := by
    rw [← Ioc_union_Ioc_eq_Ioc hx hxy]
    apply setIntegral_union
    · rw [disjoint_left]
      exact fun t ht ht' => (not_lt_of_ge ht.2) ht'.1
    · exact measurableSet_Ioc
    · exact pm_integrable_psi_div_Ioc zero_le_one
    · exact pm_integrable_psi_div_Ioc hx0.le
  rw [hxmean, hymean, hsplit]
  ring

theorem pmPrimeLogMean_increment_bounds {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    0 ≤ y * pmPrimeLogMean y - x * pmPrimeLogMean x ∧
      y * pmPrimeLogMean y - x * pmPrimeLogMean x ≤ 7 * (y - x) := by
  rw [pmPrimeLogMean_increment hx hxy]
  have hx0 := zero_lt_one.trans_le hx
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (Chebyshev.psi_nonneg _) (hx0.trans ht.1).le
  · have hq := pm_integrable_psi_div_Ioc (b := y) hx0.le
    have hc : IntegrableOn (fun _ : ℝ => (7 : ℝ)) (Ioc x y) :=
      integrableOn_const measure_Ioc_lt_top.ne
    calc
      _ ≤ ∫ t in Ioc x y, (7 : ℝ) := by
        apply integral_mono_ae hq hc
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact pm_psi_div_le_seven (hx0.trans ht.1)
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hxy]
        simp only [smul_eq_mul]
        ring

theorem pmPrimeLogMean_variation_le {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    |pmPrimeLogMean y - pmPrimeLogMean x| ≤ 7 * (y - x) / y := by
  have hy0 := zero_lt_one.trans_le (hx.trans hxy)
  have hb := pmPrimeLogMean_bounds hx
  have hi := pmPrimeLogMean_increment_bounds hx hxy
  have hnon := mul_nonneg (sub_nonneg.mpr hxy) hb.1
  have hle := mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr hxy)
  have hp : |y * (pmPrimeLogMean y - pmPrimeLogMean x)| ≤ 7 * (y - x) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  apply (le_div_iff₀ hy0).mpr
  simpa only [abs_mul, abs_of_pos hy0, mul_comm] using hp

theorem pmPrimeLogMean_cell_bound {x : ℝ} (hx : 1 ≤ x) :
    |pmPrimeLogMean x - chebyshevProfileMean ⌊x⌋₊| ≤ 7 / (⌊x⌋₊ : ℝ) := by
  let N := ⌊x⌋₊
  have hn1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
  have hnle : (N : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hxy : x ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  rw [← pmPrimeLogMean_nat_succ, abs_sub_comm]
  calc
    _ ≤ 7 * (((N : ℝ) + 1) - x) / ((N : ℝ) + 1) := pmPrimeLogMean_variation_le hx hxy
    _ ≤ 7 / ((N : ℝ) + 1) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hn0 (by linarith)

theorem pmLogMobiusMeanDefect_cell_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |pmLogMobiusMeanDefect x -
        (logMobiusHarmonicSum ⌊x⌋₊ - chebyshevProfileMean ⌊x⌋₊)| ≤ C / (⌊x⌋₊ : ℝ) := by
  obtain ⟨C, hC, hcell⟩ := pmLogMobius_realCutoff_cell_bound
  refine ⟨C + 7, by positivity, ?_⟩
  intro x hx
  calc
    _ = |(Sieve.moebiusShiftedLogKernelReal 0 x - logMobiusHarmonicSum ⌊x⌋₊) -
        (pmPrimeLogMean x - chebyshevProfileMean ⌊x⌋₊)| := by
      congr 1
      dsimp [pmLogMobiusMeanDefect]
      ring
    _ ≤ |Sieve.moebiusShiftedLogKernelReal 0 x - logMobiusHarmonicSum ⌊x⌋₊| +
        |pmPrimeLogMean x - chebyshevProfileMean ⌊x⌋₊| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (Sieve.moebiusShiftedLogKernelReal 0 x - logMobiusHarmonicSum ⌊x⌋₊)
        (pmPrimeLogMean x - chebyshevProfileMean ⌊x⌋₊)
    _ ≤ C / (⌊x⌋₊ : ℝ) + 7 / (⌊x⌋₊ : ℝ) :=
      add_le_add (hcell x hx) (pmPrimeLogMean_cell_bound hx)
    _ = _ := by ring

theorem pmLogMobiusMeanDefect_continuous_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      x * pmLogMobiusMeanDefect x ^ 2 / Real.log x ^ 2 ≤
        12 * logMobiusFermiErrorEnergy ⌊x⌋₊ + C / (x * Real.log x ^ 2) := by
  obtain ⟨D, hD, hcell⟩ := pmLogMobiusMeanDefect_cell_bound
  refine ⟨8 * D ^ 2, by positivity, ?_⟩
  intro x hx
  let N := ⌊x⌋₊
  let d := logMobiusHarmonicSum N - chebyshevProfileMean N
  have hx0 : 0 < x := by linarith
  have hn2 : 2 ≤ N := (Nat.le_floor_iff hx0.le).mpr (by exact_mod_cast hx)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hn0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hn1
  have hnlt : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hnle : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxt : x ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hx2N : x ≤ 2 * (N : ℝ) := by linarith
  have hln0 : 0 < Real.log (N : ℝ) := Real.log_pos hnlt
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log hn0 hnle
  have hmain : x * d ^ 2 / Real.log x ^ 2 ≤ 6 * logMobiusFermiErrorEnergy N := by
    calc
      _ ≤ x * d ^ 2 / Real.log (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hln0)
          (pow_le_pow_left₀ hln0.le hlog 2)
      _ ≤ ((N : ℝ) + 1) * d ^ 2 / Real.log (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxt (sq_nonneg _))
          (sq_nonneg _)
      _ ≤ _ := logMobiusNormalizationBudget_le_six_error N hn2
  have hratio0 : 0 ≤ x / (N : ℝ) := div_nonneg hx0.le hn0.le
  have hratio : x / (N : ℝ) ≤ 2 := (div_le_iff₀ hn0).mpr hx2N
  have hsqratio : (x / (N : ℝ)) ^ 2 ≤ 4 := by nlinarith
  have herr : x * (D / (N : ℝ)) ^ 2 / Real.log x ^ 2 ≤
      4 * D ^ 2 / (x * Real.log x ^ 2) := by
    have hnum : x * (D / (N : ℝ)) ^ 2 ≤ 4 * D ^ 2 / x := by
      apply (le_div_iff₀ hx0).mpr
      calc
        _ = (x / (N : ℝ)) ^ 2 * D ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsqratio (sq_nonneg D)
    calc
      _ ≤ (4 * D ^ 2 / x) / Real.log x ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = _ := by ring
  have hc := hcell x (by linarith)
  change |pmLogMobiusMeanDefect x - d| ≤ D / (N : ℝ) at hc
  have hcsq := pow_le_pow_left₀ (abs_nonneg _) hc 2
  rw [sq_abs] at hcsq
  have hquad : pmLogMobiusMeanDefect x ^ 2 ≤ 2 * d ^ 2 + 2 * (D / (N : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (pmLogMobiusMeanDefect x - 2 * d)]
  calc
    _ ≤ x * (2 * d ^ 2 + 2 * (D / (N : ℝ)) ^ 2) / Real.log x ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hquad hx0.le) (sq_nonneg _)
    _ = 2 * (x * d ^ 2 / Real.log x ^ 2) +
        2 * (x * (D / (N : ℝ)) ^ 2 / Real.log x ^ 2) := by ring
    _ ≤ 2 * (6 * logMobiusFermiErrorEnergy N) +
        2 * (4 * D ^ 2 / (x * Real.log x ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num))
        (mul_le_mul_of_nonneg_left herr (by norm_num))
    _ = _ := by ring

theorem tendsto_pmLogMobiusMeanDefect_sq_of_error
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => x * pmLogMobiusMeanDefect x ^ 2 / Real.log x ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbudget⟩ := pmLogMobiusMeanDefect_continuous_budget
  have hfloor : Tendsto (fun x : ℝ => logMobiusFermiErrorEnergy ⌊x⌋₊)
      atTop (𝓝 0) := hE.comp tendsto_nat_floor_atTop
  have hlim : Tendsto (fun x : ℝ => 12 * logMobiusFermiErrorEnergy ⌊x⌋₊ + C / x)
      atTop (𝓝 0) := by
    simpa using (hfloor.const_mul 12).add (tendsto_id.const_div_atTop C)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (max (2 : ℝ) (Real.exp 1))] with x hx
    have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
    have hx0 : 0 < x := by linarith
    have hlog : 1 ≤ Real.log x :=
      (Real.le_log_iff_exp_le hx0).mpr ((le_max_right _ _).trans hx)
    have hlogsq : 1 ≤ Real.log x ^ 2 := by nlinarith
    have hden : x ≤ x * Real.log x ^ 2 := by nlinarith
    exact (hbudget x hx2).trans (add_le_add le_rfl
      (div_le_div_of_nonneg_left hC hx0 hden))

theorem pmLogMobiusMeanDefect_isLittleO_of_error
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0)) :
    pmLogMobiusMeanDefect =o[atTop] (fun x : ℝ => Real.log x / Real.sqrt x) := by
  have hsq := tendsto_pmLogMobiusMeanDefect_sq_of_error hE
  have hsqrt : Tendsto
      (fun x : ℝ => Real.sqrt (x * pmLogMobiusMeanDefect x ^ 2 / Real.log x ^ 2))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have habs : Tendsto (fun x : ℝ =>
      |pmLogMobiusMeanDefect x / (Real.log x / Real.sqrt x)|) atTop (𝓝 0) := by
    apply hsqrt.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 ≤ x := by linarith
    have heq : x * pmLogMobiusMeanDefect x ^ 2 / Real.log x ^ 2 =
        (pmLogMobiusMeanDefect x / (Real.log x / Real.sqrt x)) ^ 2 := by
      rw [div_div_eq_mul_div, div_pow, mul_pow, Real.sq_sqrt hx0]
      ring
    rw [heq, Real.sqrt_sq_eq_abs]
  have hratio : Tendsto (fun x : ℝ =>
      pmLogMobiusMeanDefect x / (Real.log x / Real.sqrt x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  apply (Asymptotics.isLittleO_iff_tendsto' _).mpr hratio
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx hzero
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  exact (div_ne_zero hl.ne' (Real.sqrt_pos.mpr hx0).ne' hzero).elim

end RHTower
