/-
# Logarithmic integer confinement of finite Euler energy

Write `a = 1 - sigma`, with `0 < a <= 1/2`. For any `0 < b < a < c`, retain
exactly the squarefree prime configurations whose formed integer satisfies
`Y^b < log n <= Y^c`. Their energy on `[-1,1]` is asymptotic to the energy
of the full prime product, for every continuous nonnegative weight positive at zero.
In particular this holds for the literal archimedean Gamma weight.

The low-integer section has vanishing relative energy. The high-integer tail
tends uniformly to zero in absolute norm, at every real frequency. The proof
combines logarithmic tilting of exact signed configuration sums with the
full-prime antiscale peak lower bound.

These are prime-supported configurations, not all integers in the same size
window. No cancellation bound for literal Mobius prefixes or RH is asserted.
-/

import GaloisForLFunctions.RHTower.GibbsPrimeIntegerFootprint
import GaloisForLFunctions.RHTower.PrimeRpowUniformUpper

open Filter Topology Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Logarithm of the integer formed by one squarefree prime configuration. -/
def eulerConfigurationLog (T : Finset ℕ) : ℝ := ∑ p ∈ T, Real.log p

theorem eulerConfigurationLog_eq_log_prod (T : Finset ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    eulerConfigurationLog T = Real.log (∏ p ∈ T, (p : ℝ)) := by
  exact (Real.log_prod fun p hp => by exact_mod_cast (hT p hp).ne_zero).symm

/-- The unsquared signed Mellin contribution of one prime configuration. -/
def eulerConfigurationTerm (a t : ℝ) (T : Finset ℕ) : ℂ :=
  (-1 : ℂ) ^ T.card * (Real.exp ((a - 1) * eulerConfigurationLog T) : ℂ) *
    Complex.exp (((-t * eulerConfigurationLog T : ℝ) : ℂ) * Complex.I)

theorem norm_eulerConfigurationTerm (a t : ℝ) (T : Finset ℕ) :
    ‖eulerConfigurationTerm a t T‖ = Real.exp ((a - 1) * eulerConfigurationLog T) := by
  simp only [eulerConfigurationTerm, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]

theorem continuous_eulerConfigurationTerm (a : ℝ) (T : Finset ℕ) :
    Continuous (fun t => eulerConfigurationTerm a t T) := by
  unfold eulerConfigurationTerm
  fun_prop

theorem eulerConfigurationTerm_eq_prod (a t : ℝ) (T : Finset ℕ) :
    eulerConfigurationTerm a t T =
      ∏ p ∈ T, ((-1 : ℂ) * (Real.exp ((a - 1) * Real.log p) : ℂ) *
        Complex.exp (((-t * Real.log p : ℝ) : ℂ) * Complex.I)) := by
  simp only [Finset.prod_mul_distrib, Finset.prod_const]
  rw [← Complex.exp_sum]
  have hr : (∏ p ∈ T, (Real.exp ((a - 1) * Real.log p) : ℂ)) =
      (Real.exp ((a - 1) * eulerConfigurationLog T) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum]
    rfl
  rw [hr]
  unfold eulerConfigurationTerm eulerConfigurationLog
  congr 2
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.mul_sum]

theorem fullEulerMellinProduct_eq_configurationSum (a Y t : ℝ) :
    fullEulerMellinProduct a Y t =
      ∑ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset, eulerConfigurationTerm a t T := by
  rw [fullEulerMellinProduct]
  calc
    _ = ∏ p ∈ Nat.primesLE ⌊Y⌋₊,
        (1 + ((-1 : ℂ) * (Real.exp ((a - 1) * Real.log p) : ℂ) *
          Complex.exp (((-t * Real.log p : ℝ) : ℂ) * Complex.I))) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
      rw [Real.rpow_def_of_pos hp0, mul_comm (Real.log (p : ℝ)) (a - 1)]
      simp only [neg_mul, sub_eq_add_neg, one_mul]
    _ = _ := by
      rw [Finset.prod_one_add]
      exact Finset.sum_congr rfl fun T hT => (eulerConfigurationTerm_eq_prod a t T).symm

/-- The absolute configuration mass; no probability normalization is made. -/
def eulerConfigurationEnvelope (a Y : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 + Real.exp ((a - 1) * Real.log p))

theorem eulerConfigurationEnvelope_eq_sum (a Y : ℝ) :
    eulerConfigurationEnvelope a Y =
      ∑ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset,
        Real.exp ((a - 1) * eulerConfigurationLog T) := by
  rw [eulerConfigurationEnvelope, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Real.exp_sum, ← Finset.mul_sum]
  rfl

/-- A literal integer-height section of the full finite prime product. -/
def eulerConfigurationLow (a Y L t : ℝ) : ℂ :=
  ∑ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset.filter (fun T => eulerConfigurationLog T ≤ L),
    eulerConfigurationTerm a t T

def eulerConfigurationHigh (a Y L t : ℝ) : ℂ :=
  ∑ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset.filter (fun T => ¬ eulerConfigurationLog T ≤ L),
    eulerConfigurationTerm a t T

theorem eulerConfigurationLow_add_high (a Y L t : ℝ) :
    eulerConfigurationLow a Y L t + eulerConfigurationHigh a Y L t =
      fullEulerMellinProduct a Y t := by
  rw [eulerConfigurationLow, eulerConfigurationHigh,
    Finset.sum_filter_add_sum_filter_not, fullEulerMellinProduct_eq_configurationSum]

theorem continuous_eulerConfigurationLow (a Y L : ℝ) :
    Continuous (eulerConfigurationLow a Y L) := by
  unfold eulerConfigurationLow
  exact continuous_finsetSum _ fun T hT => continuous_eulerConfigurationTerm a T

theorem continuous_eulerConfigurationHigh (a Y L : ℝ) :
    Continuous (eulerConfigurationHigh a Y L) := by
  unfold eulerConfigurationHigh
  exact continuous_finsetSum _ fun T hT => continuous_eulerConfigurationTerm a T

/-- A logarithmic tilt bounds every low-integer configuration, uniformly in frequency. -/
theorem norm_eulerConfigurationLow_le (a Y L t : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    ‖eulerConfigurationLow a Y L t‖ ≤
      Real.exp (d * L) * eulerConfigurationEnvelope (a - d) Y := by
  rw [eulerConfigurationEnvelope_eq_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset.filter (fun T => eulerConfigurationLog T ≤ L),
        Real.exp (d * L) * Real.exp ((a - d - 1) * eulerConfigurationLog T) := by
      apply Finset.sum_le_sum
      intro T hT
      rw [norm_eulerConfigurationTerm, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hT).2 hd
      nlinarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun T hT hnot => by positivity)

/-- The complementary tilt bounds the high-integer tail, uniformly in frequency. -/
theorem norm_eulerConfigurationHigh_le (a Y L t : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    ‖eulerConfigurationHigh a Y L t‖ ≤
      Real.exp (-d * L) * eulerConfigurationEnvelope (a + d) Y := by
  rw [eulerConfigurationEnvelope_eq_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset.filter (fun T => ¬eulerConfigurationLog T ≤ L),
        Real.exp (-d * L) * Real.exp ((a + d - 1) * eulerConfigurationLog T) := by
      apply Finset.sum_le_sum
      intro T hT
      rw [norm_eulerConfigurationTerm, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp (Finset.mem_filter.mp hT).2)) hd
      nlinarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun T hT hnot => by positivity)

theorem exists_eulerConfigurationEnvelope_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℝ, 0 ≤ Y →
      eulerConfigurationEnvelope a Y ≤ Real.exp (K * Y ^ a) := by
  let K : ℝ := uniformPrimeLogRpowConst / a / Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K, by dsimp [K]; exact div_pos (div_pos uniformPrimeLogRpowConst_pos ha) hlog,
    fun Y hY => ?_⟩
  have hweighted := primeLogSum_rpow_sub_one_le_uniform ha ha1 Y hY
  have hprimeLog : primeLogSum (fun t : ℝ => t ^ (a - 1)) 0 Y =
      ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (a - 1) * Real.log p := by
    rw [primeLogSum, Nat.floor_zero]
    have hfin : (Finset.Ioc 0 ⌊Y⌋₊).filter Nat.Prime = Nat.primesLE ⌊Y⌋₊ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨hp0, hpY⟩, hp⟩; exact ⟨hpY, hp⟩
      · rintro ⟨hpY, hp⟩; exact ⟨⟨hp.pos, hpY⟩, hp⟩
    rw [hfin]
    exact Finset.sum_congr rfl fun p hp => by ring
  rw [hprimeLog] at hweighted
  have hs : (∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (a - 1)) * Real.log 2 ≤
      uniformPrimeLogRpowConst / a * Y ^ a := by
    rw [Finset.sum_mul]
    refine (Finset.sum_le_sum fun p hp => ?_).trans hweighted
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact Real.log_le_log (by norm_num)
      (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le)
  have hs' : (∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (a - 1)) ≤ K * Y ^ a := by
    apply (le_div_iff₀ hlog).mpr hs |>.trans_eq
    dsimp [K]
    ring
  have henv : eulerConfigurationEnvelope a Y =
      ∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 + (p : ℝ) ^ (a - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Real.rpow_def_of_pos (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos)]
    congr 2
    ring
  rw [henv]
  calc
    _ ≤ ∏ p ∈ Nat.primesLE ⌊Y⌋₊, Real.exp ((p : ℝ) ^ (a - 1)) := by
      apply Finset.prod_le_prod (fun p hp => by positivity)
      intro p hp
      simpa [add_comm] using Real.add_one_le_exp ((p : ℝ) ^ (a - 1))
    _ = Real.exp (∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (a - 1)) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hs'

private theorem tendsto_rpow_ratio_zero {b c : ℝ} (hbc : b < c) :
    Tendsto (fun Y : ℝ => Y ^ b / Y ^ c) atTop (nhds 0) := by
  apply (tendsto_rpow_neg_atTop (sub_pos.mpr hbc)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  rw [show -(c - b) = b - c by ring, Real.rpow_sub hY]

/-- Above the logarithmic exponent `a`, the discarded integer tail tends uniformly to zero
in absolute norm, despite growth of the full finite Euler product. -/
theorem exists_eulerConfigurationHigh_vanishing_majorant
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hab : a < b) :
    ∃ B : ℝ → ℝ, Tendsto B atTop (nhds 0) ∧
      ∀ᶠ Y : ℝ in atTop, ∀ t : ℝ,
        ‖eulerConfigurationHigh a Y (Y ^ b) t‖ ≤ B Y := by
  let d := min ((b - a) / 2) ((1 - a) / 2)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hadb : a + d < b := by have := min_le_left ((b-a)/2) ((1-a)/2); dsimp [d]; linarith
  have had1 : a + d ≤ 1 := by have := min_le_right ((b-a)/2) ((1-a)/2); dsimp [d]; linarith
  obtain ⟨K, hK, hbound⟩ := exists_eulerConfigurationEnvelope_bound
    (by linarith : 0 < a + d) had1
  refine ⟨fun Y => Real.exp (-d * Y ^ b + K * Y ^ (a + d)), ?_, ?_⟩
  · have hcoeff : Tendsto (fun Y : ℝ => d - K * (Y ^ (a + d) / Y ^ b))
        atTop (nhds d) := by
      simpa using tendsto_const_nhds.sub ((tendsto_rpow_ratio_zero hadb).const_mul K)
    have hgrow := hcoeff.pos_mul_atTop hd (tendsto_rpow_atTop (by linarith : 0 < b))
    have hgrow' : Tendsto (fun Y : ℝ => d * Y ^ b - K * Y ^ (a + d)) atTop atTop := by
      apply hgrow.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
      have hy : Y ^ b ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
      field_simp
    have hz := (Real.tendsto_exp_atTop.comp hgrow').inv_tendsto_atTop
    change Tendsto (fun Y : ℝ => (Real.exp (d * Y ^ b - K * Y ^ (a + d)))⁻¹)
      atTop (nhds 0) at hz
    apply hz.congr'
    filter_upwards [] with Y
    rw [← Real.exp_neg]
    congr 1
    ring
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Y hY
    intro t
    calc
      _ ≤ Real.exp (-d * Y ^ b) * eulerConfigurationEnvelope (a + d) Y :=
        norm_eulerConfigurationHigh_le a Y (Y ^ b) t hd.le
      _ ≤ Real.exp (-d * Y ^ b) * Real.exp (K * Y ^ (a + d)) :=
        mul_le_mul_of_nonneg_left (hbound Y hY) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm

theorem eulerConfigurationHigh_uniformly_tendsto_zero
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hab : a < b) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℝ in atTop, ∀ t : ℝ,
      ‖eulerConfigurationHigh a Y (Y ^ b) t‖ < ε := by
  obtain ⟨B, hB, hbound⟩ := exists_eulerConfigurationHigh_vanishing_majorant ha0 ha1 hab
  intro ε hε
  filter_upwards [hbound, hB.eventually (gt_mem_nhds hε)] with Y hY hsmall
  exact fun t => (hY t).trans_lt hsmall

/-- Below exponent `a`, the low-integer signal has strictly smaller stretched-exponential
growth than the full Euler peak. -/
theorem exists_eulerConfigurationLow_subcritical_majorant
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hba : b < a) :
    ∃ c K : ℝ, 0 < c ∧ c < a ∧ 0 < K ∧
      ∀ᶠ Y : ℝ in atTop, ∀ t : ℝ,
        ‖eulerConfigurationLow a Y (Y ^ b) t‖ ≤ Real.exp (K * Y ^ c) := by
  obtain ⟨K, hK, hbound⟩ := exists_eulerConfigurationEnvelope_bound
    (by linarith : 0 < a / 2) (by linarith : a / 2 ≤ 1)
  refine ⟨max b (a / 2), a / 2 + K, lt_max_of_lt_left hb0,
    max_lt hba (by linarith), by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  intro t
  have hb := Real.rpow_le_rpow_of_exponent_le hY (le_max_left b (a / 2))
  have ha := Real.rpow_le_rpow_of_exponent_le hY (le_max_right b (a / 2))
  calc
    _ ≤ Real.exp ((a / 2) * Y ^ b) * eulerConfigurationEnvelope (a - a / 2) Y :=
      norm_eulerConfigurationLow_le a Y (Y ^ b) t (by linarith)
    _ = Real.exp ((a / 2) * Y ^ b) * eulerConfigurationEnvelope (a / 2) Y := by congr 2; ring
    _ ≤ Real.exp ((a / 2) * Y ^ b) * Real.exp (K * Y ^ (a / 2)) :=
      mul_le_mul_of_nonneg_left (hbound Y (by linarith)) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

private theorem tendsto_rpow_log_div_rpow_zero {b a : ℝ} (hba : b < a) :
    Tendsto (fun Y : ℝ => Y ^ b * Real.log Y / Y ^ a) atTop (nhds 0) := by
  apply ((isLittleO_log_rpow_atTop (sub_pos.mpr hba)).tendsto_div_nhds_zero).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  rw [Real.rpow_sub hY]
  field_simp

/-- The Euler peak beats every exponential correction with logarithmic exponent below `a`. -/
theorem tendsto_fullEulerEscapeExponent_sub_rpow
    {a b : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) (hba : b < a) (k : ℝ) :
    Tendsto (fun Y => fullEulerEscapeExponent a Y - k * Y ^ b) atTop atTop := by
  have ha1 : a < 1 := by linarith
  have hD := tendsto_eulerLogDeficit ha0 ha2
  have hL2 : Tendsto (fun Y : ℝ => Real.log Y ^ 2) atTop atTop := by
    simpa [pow_two] using Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hDsmall : Tendsto (fun Y : ℝ =>
      eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) atTop (nhds 0) := by
    refine (hD.div_atTop hL2).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    have hlog : Real.log Y ≠ 0 := (Real.log_pos hY).ne'
    have hy : Y ^ a ≠ 0 := (Real.rpow_pos_of_pos (by linarith) a).ne'
    field_simp
  have hP := tendsto_primeRpowLogSumLE ha0
  have hsmall := HTGeometry.tendsto_logPow_div_rpow ha0 2
  have hcorrection := (tendsto_rpow_log_div_rpow_zero hba).const_mul k
  have hcoefficient : Tendsto (fun Y : ℝ =>
      primeRpowLogSumLE a Y / Y ^ a -
        2 * (eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) -
        2 * (Real.log Y ^ 2 / Y ^ a) -
        k * (Y ^ b * Real.log Y / Y ^ a)) atTop (nhds (1 / a)) := by
    simpa using ((hP.sub (hDsmall.const_mul 2)).sub (hsmall.const_mul 2)).sub hcorrection
  have hscale0 : Tendsto (fun Y : ℝ => Real.log Y / Y ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
  have hscalePositive : ∀ᶠ Y : ℝ in atTop, Real.log Y / Y ^ a ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    exact div_pos (Real.log_pos hY) (Real.rpow_pos_of_pos (by linarith) a)
  have hscale : Tendsto (fun Y : ℝ => Y ^ a / Real.log Y) atTop atTop := by
    simpa [Function.comp_def] using tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hscale0, hscalePositive⟩)
  apply tendsto_atTop_mono' _ _ (hcoefficient.pos_mul_atTop (one_div_pos.mpr ha0) hscale)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  have hlog : Real.log Y ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hy : Y ^ a ≠ 0 := (Real.rpow_pos_of_pos (by linarith) a).ne'
  have heq :
      (primeRpowLogSumLE a Y / Y ^ a -
        2 * (eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) -
        2 * (Real.log Y ^ 2 / Y ^ a) - k * (Y ^ b * Real.log Y / Y ^ a)) *
          (Y ^ a / Real.log Y) =
      primeRpowLogSumLE a Y / Real.log Y -
        2 * eulerLogDeficit a (antiscaleFrequency a Y) Y - 2 * Real.log Y - k * Y ^ b := by
    field_simp
  rw [heq, fullEulerEscapeExponent]
  linarith [primeRpowLogSumLE_div_log_le_log_positiveEulerSquare ha1 hY]

private theorem eventually_fullEuler_window_lower
    (w : ℝ → ℝ) (hw : Continuous w) (hwn : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ᶠ Y : ℝ in atTop, (w 0 / 8) * Real.exp (fullEulerEscapeExponent a Y) ≤
      mellinWindowEnergy w (fullEulerMellinProduct a Y) := by
  obtain ⟨δ, hδ, hfloor⟩ := exists_local_half_floor_of_continuousAt_of_pos hw.continuousAt hw0
  have hsmall : Tendsto (fun Y : ℝ => |antiscaleFrequency a Y| + fullEulerPeakWidth a Y)
      atTop (nhds 0) := by
    simpa using (tendsto_antiscaleFrequency ha0).abs.add (tendsto_fullEulerPeakWidth ha1)
  have hnear := hsmall.eventually (gt_mem_nhds (lt_min hδ (by norm_num : (0 : ℝ) < 1)))
  filter_upwards [hnear, eventually_ge_atTop (2 : ℝ)] with Y hnear hY
  have hd : 0 < fullEulerPeakWidth a Y :=
    div_pos (fullEulerEnvelopeRatio_pos ha1 _ _) (by positivity)
  have hnearδ := hnear.trans_le (min_le_left _ _)
  have hnear1 := hnear.trans_le (min_le_right _ _)
  have hband : ∀ t ∈ Icc (antiscaleFrequency a Y - fullEulerPeakWidth a Y)
      (antiscaleFrequency a Y + fullEulerPeakWidth a Y), |t| < δ := by
    intro t ht
    have hlo := neg_abs_le (antiscaleFrequency a Y)
    have hhi := le_abs_self (antiscaleFrequency a Y)
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hpeak := fullEulerPeak_weighted_integral_lower w hw ha1 hY
    (show 0 ≤ w 0 / 2 by positivity) (fun t ht => hfloor t (hband t ht))
  have hcont : Continuous (fun t : ℝ => w t * eulerMellinNormSq a t Y) := by
    unfold eulerMellinNormSq
    fun_prop
  have hnonneg : ∀ t, 0 ≤ w t * eulerMellinNormSq a t Y := by
    intro t
    rw [← norm_fullEulerMellinProduct_sq]
    exact mul_nonneg (hwn t) (sq_nonneg _)
  have hca : (-1 : ℝ) ≤ antiscaleFrequency a Y - fullEulerPeakWidth a Y := by
    linarith [neg_abs_le (antiscaleFrequency a Y)]
  have hab : antiscaleFrequency a Y - fullEulerPeakWidth a Y ≤
      antiscaleFrequency a Y + fullEulerPeakWidth a Y := by linarith
  have hbd : antiscaleFrequency a Y + fullEulerPeakWidth a Y ≤ 1 := by
    linarith [le_abs_self (antiscaleFrequency a Y)]
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) hca hab hbd
    (Filter.Eventually.of_forall hnonneg) (hcont.intervalIntegrable (-1) 1)
  rw [mellinWindowEnergy_fullEuler_eq]
  calc
    (w 0 / 8) * Real.exp (fullEulerEscapeExponent a Y) =
        ((w 0 / 2) / 4) * Real.exp (fullEulerEscapeExponent a Y) := by ring
    _ ≤ _ := hpeak.trans hmono

theorem fullEuler_weighted_energy_div_exp_rpow_tendsto
    (w : ℝ → ℝ) (hw : Continuous w) (hwn : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a b : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) (hba : b < a) (k : ℝ) :
    Tendsto (fun Y => mellinWindowEnergy w (fullEulerMellinProduct a Y) /
      Real.exp (k * Y ^ b)) atTop atTop := by
  have hgrowth := (Real.tendsto_exp_atTop.comp
    (tendsto_fullEulerEscapeExponent_sub_rpow ha0 ha2 hba k)).const_mul_atTop
      (show 0 < w 0 / 8 by positivity)
  apply tendsto_atTop_mono' _ _ hgrowth
  filter_upwards [eventually_fullEuler_window_lower w hw hwn hw0 ha0 (by linarith)] with Y hY
  change (w 0 / 8) * Real.exp (fullEulerEscapeExponent a Y - k * Y ^ b) ≤ _
  rw [Real.exp_sub]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hY (Real.exp_pos _).le

theorem fullEuler_subcritical_correction_energy_ratio_zero
    (w : ℝ → ℝ) (hw : Continuous w) (hwn : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a b : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) (hba : b < a)
    (G : ℝ → ℝ → ℂ) (hG : ∀ Y, Continuous (G Y))
    {M : ℝ} (hM : 0 ≤ M) (k : ℝ)
    (hbound : ∀ᶠ Y : ℝ in atTop, ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖G Y t‖ ≤ M * Real.exp (k * Y ^ b)) :
    Tendsto (fun Y => mellinWindowEnergy w (G Y) /
      mellinWindowEnergy w (fullEulerMellinProduct a Y)) atTop (nhds 0) := by
  have hgrowth := fullEuler_weighted_energy_div_exp_rpow_tendsto w hw hwn hw0 ha0 ha2 hba (2 * k)
  have hnum : ∀ᶠ Y : ℝ in atTop,
      mellinWindowEnergy w (G Y) / Real.exp ((2 * k) * Y ^ b) ≤
        (∫ t in (-1 : ℝ)..1, w t) * M ^ 2 := by
    filter_upwards [hbound] with Y hY
    have hE := mellinWindowEnergy_le_of_norm_le w hw hwn (G Y) (hG Y)
      (mul_nonneg hM (Real.exp_pos _).le) hY
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    calc
      _ ≤ (∫ t in (-1 : ℝ)..1, w t) * (M * Real.exp (k * Y ^ b)) ^ 2 := hE
      _ = _ := by
        rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
        have heq : k * Y ^ b + k * Y ^ b = (2 * k) * Y ^ b := by ring
        rw [heq]
        ring
  have hzero := tendsto_bdd_div_atTop_nhds_zero
    (Filter.Eventually.of_forall (fun Y : ℝ =>
      div_nonneg (mellinWindowEnergy_nonneg w hwn (G Y)) (Real.exp_pos _).le)) hnum hgrowth
  apply hzero.congr'
  filter_upwards [] with Y
  field_simp

private theorem fullEuler_correction_residual_ratio_one_of_energy_ratio_zero
    (w : ℝ → ℝ) (hw : Continuous w) (hwn : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2)
    (G : ℝ → ℝ → ℂ) (hG : ∀ Y, Continuous (G Y))
    (hzero : Tendsto (fun Y => mellinWindowEnergy w (G Y) /
      mellinWindowEnergy w (fullEulerMellinProduct a Y)) atTop (nhds 0)) :
    Tendsto (fun Y => mellinWindowEnergy w (fullEulerMellinProduct a Y - G Y) /
      mellinWindowEnergy w (fullEulerMellinProduct a Y)) atTop (nhds 1) := by
  have hinfty : Tendsto (fun Y => mellinWindowEnergy w (fullEulerMellinProduct a Y))
      atTop atTop := by
    simpa only [mellinWindowEnergy_fullEuler_eq] using
      fullEuler_weighted_energy_tendsto w hw hwn hw0 ha0 ha2
  apply Metric.tendsto_nhds.2
  intro d hd
  have he : 0 < d / 2 := by positivity
  have hc : 0 < 1 + 1 / (d / 2) := by positivity
  have hsmall := hzero.eventually (gt_mem_nhds (show 0 < (d / 2) / (1 + 1 / (d / 2)) by positivity))
  filter_upwards [hinfty.eventually_gt_atTop 0, hsmall] with Y hY hsmall
  have hpert := mellinWindowEnergy_perturbation w hw hwn
    (fullEulerMellinProduct a Y) (G Y) (continuous_fullEulerMellinProduct a Y) (hG Y) he
  have hdiv := div_le_div_of_nonneg_right hpert hY.le
  have heq :
      ((d / 2) * mellinWindowEnergy w (fullEulerMellinProduct a Y) +
        (1 + 1 / (d / 2)) * mellinWindowEnergy w (G Y)) /
          mellinWindowEnergy w (fullEulerMellinProduct a Y) =
      d / 2 + (1 + 1 / (d / 2)) *
        (mellinWindowEnergy w (G Y) / mellinWindowEnergy w (fullEulerMellinProduct a Y)) := by
    field_simp
  rw [heq] at hdiv
  have hsmall' := (lt_div_iff₀ hc).1 hsmall
  rw [Real.dist_eq]
  calc
    _ = |mellinWindowEnergy w (fullEulerMellinProduct a Y - G Y) -
        mellinWindowEnergy w (fullEulerMellinProduct a Y)| /
          mellinWindowEnergy w (fullEulerMellinProduct a Y) := by
      rw [show mellinWindowEnergy w (fullEulerMellinProduct a Y - G Y) /
          mellinWindowEnergy w (fullEulerMellinProduct a Y) - 1 =
          (mellinWindowEnergy w (fullEulerMellinProduct a Y - G Y) -
          mellinWindowEnergy w (fullEulerMellinProduct a Y)) /
          mellinWindowEnergy w (fullEulerMellinProduct a Y) by field_simp]
      rw [abs_div, abs_of_pos hY]
    _ < d := by linarith

theorem fullEuler_low_configuration_energy_ratio_zero
    (w : ℝ → ℝ) (hw : Continuous w) (hwn : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a b : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) (hb0 : 0 < b) (hba : b < a) :
    Tendsto (fun Y => mellinWindowEnergy w (eulerConfigurationLow a Y (Y ^ b)) /
      mellinWindowEnergy w (fullEulerMellinProduct a Y)) atTop (nhds 0) := by
  obtain ⟨c, K, hc0, hca, hK, hbound⟩ :=
    exists_eulerConfigurationLow_subcritical_majorant ha0 (by linarith) hb0 hba
  apply fullEuler_subcritical_correction_energy_ratio_zero w hw hwn hw0 ha0 ha2 hca
    (fun Y => eulerConfigurationLow a Y (Y ^ b))
    (fun Y => continuous_eulerConfigurationLow _ _ _) (show 0 ≤ (1 : ℝ) by norm_num) K
  filter_upwards [hbound] with Y hY
  simpa only [one_mul] using fun t (ht : t ∈ Icc (-1 : ℝ) 1) => hY t

/-- The retained logarithmic band is the full signed source minus its two complementary tails. -/
def eulerConfigurationBand (a Y L U : ℝ) : ℝ → ℂ :=
  fullEulerMellinProduct a Y - eulerConfigurationLow a Y L - eulerConfigurationHigh a Y U

theorem eulerConfigurationBand_eq_sum (a Y L U t : ℝ) (hLU : L ≤ U) :
    eulerConfigurationBand a Y L U t =
      ∑ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset.filter
        (fun T => L < eulerConfigurationLog T ∧ eulerConfigurationLog T ≤ U),
        eulerConfigurationTerm a t T := by
  simp only [eulerConfigurationBand, Pi.sub_apply, fullEulerMellinProduct_eq_configurationSum,
    eulerConfigurationLow, eulerConfigurationHigh, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hL : eulerConfigurationLog T ≤ L
  · have hU := hL.trans hLU
    simp [hL, hU, not_lt.mpr hL]
  · have hL' := not_le.mp hL
    by_cases hU : eulerConfigurationLog T ≤ U <;> simp [hL, hL', hU]

/-- Full finite-prime energy is confined between every pair of logarithmic exponents
`0 < b < a < c`. This concerns prime-supported configurations, not all integers in that band. -/
theorem fullEuler_configuration_band_energy_ratio_one
    (w : ℝ → ℝ) (hw : Continuous w) (hwn : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a b c : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2)
    (hb0 : 0 < b) (hba : b < a) (hac : a < c) :
    Tendsto (fun Y => mellinWindowEnergy w (eulerConfigurationBand a Y (Y ^ b) (Y ^ c)) /
      mellinWindowEnergy w (fullEulerMellinProduct a Y)) atTop (nhds 1) := by
  obtain ⟨q, K, hq0, hqa, hK, hlow⟩ :=
    exists_eulerConfigurationLow_subcritical_majorant ha0 (by linarith) hb0 hba
  have hhigh := eulerConfigurationHigh_uniformly_tendsto_zero ha0 (by linarith) hac 1 (by norm_num)
  let G : ℝ → ℝ → ℂ := fun Y =>
    eulerConfigurationLow a Y (Y ^ b) + eulerConfigurationHigh a Y (Y ^ c)
  have hG : ∀ Y, Continuous (G Y) := fun Y =>
    (continuous_eulerConfigurationLow _ _ _).add (continuous_eulerConfigurationHigh _ _ _)
  have hbound : ∀ᶠ Y : ℝ in atTop, ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖G Y t‖ ≤ 2 * Real.exp (K * Y ^ q) := by
    filter_upwards [hlow, hhigh, eventually_ge_atTop (0 : ℝ)] with Y hlow hhigh hY
    intro t ht
    have he : 1 ≤ Real.exp (K * Y ^ q) := Real.one_le_exp_iff.mpr (by positivity)
    have hnorm := norm_add_le (eulerConfigurationLow a Y (Y ^ b) t)
      (eulerConfigurationHigh a Y (Y ^ c) t)
    change ‖eulerConfigurationLow a Y (Y ^ b) t + eulerConfigurationHigh a Y (Y ^ c) t‖ ≤ _
    linarith [hlow t, hhigh t]
  have hzero := fullEuler_subcritical_correction_energy_ratio_zero w hw hwn hw0 ha0 ha2 hqa
    G hG (show 0 ≤ (2 : ℝ) by norm_num) K hbound
  have hres := fullEuler_correction_residual_ratio_one_of_energy_ratio_zero
    w hw hwn hw0 ha0 ha2 G hG hzero
  simpa only [eulerConfigurationBand, G, sub_add_eq_sub_sub] using hres

/-- The same logarithmic confinement for the actual archimedean Gamma weight. -/
theorem fullPrimeEulerGamma_configuration_band_energy_ratio_one
    {sigma b c : ℝ} (hsigma : 1 / 2 ≤ sigma) (hsigma1 : sigma < 1)
    (hb0 : 0 < b) (hb : b < 1 - sigma) (hc : 1 - sigma < c) :
    Tendsto (fun Y => mellinWindowEnergy
      (fun t => ‖Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (eulerConfigurationBand (1 - sigma) Y (Y ^ b) (Y ^ c)) /
      fullPrimeEulerGammaEnergy sigma Y) atTop (nhds 1) := by
  have hsigma0 : 0 < sigma := by linarith
  have hΓ : Continuous (fun t : ℝ => Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : ∀ m : ℕ, (sigma : ℂ) + (t : ℂ) * Complex.I ≠ -m := by
      intro m hm
      have h := congrArg Complex.re hm
      simp at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have harg : ContinuousAt (fun u : ℝ => (sigma : ℂ) + (u : ℂ) * Complex.I) t := by
      fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => (sigma : ℂ) + (u : ℂ) * Complex.I)
      (x := t) ((Complex.differentiableAt_Gamma _ hne).continuousAt) harg
  have hw0 : 0 < ‖Complex.Gamma ((sigma : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.Gamma_ofReal,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact sq_pos_of_pos (Real.Gamma_pos_of_pos hsigma0)
  simpa only [mellinWindowEnergy_fullEuler_eq, fullPrimeEulerGammaEnergy] using
    fullEuler_configuration_band_energy_ratio_one
      (fun t : ℝ => ‖Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (hΓ.norm.pow 2) (fun t => sq_nonneg _) hw0
      (sub_pos.mpr hsigma1) (by linarith : 1 - sigma ≤ 1 / 2) hb0 hb hc


end RHTower
