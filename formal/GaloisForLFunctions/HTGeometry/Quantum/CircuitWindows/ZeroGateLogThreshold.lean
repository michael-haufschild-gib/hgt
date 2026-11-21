import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyArcPacking
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupationScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The logarithmic threshold for zero-gate occupation

Above the largest-gap scale the anchor union bound rules out enclosure.
Below that scale, many disjoint trial arcs fit on the circle and their
expected empty count diverges.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def qubitDimension (n : ℕ) : ℝ := (2 : ℝ) ^ n

private theorem qubitDimension_ge_one (n : ℕ) : 1 ≤ qubitDimension n := one_le_pow₀ (by norm_num)

private theorem qubitDimension_pos (n : ℕ) : 0 < qubitDimension n :=
  zero_lt_one.trans_le (qubitDimension_ge_one n)

private theorem tendsto_qubitDimension : Tendsto qubitDimension atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

private theorem cast_qubitDimension_sub_one (n : ℕ) : ((2 ^ n - 1 : ℕ) : ℝ) = qubitDimension n - 1 := by
  have h : 1 ≤ (2 : ℕ) ^ n := one_le_pow₀ (by norm_num)
  simp only [qubitDimension, Nat.cast_sub h, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

private def logArcGap (c : ℝ≥0) (n : ℕ) : ℝ := (c : ℝ) * Real.log (qubitDimension n) / qubitDimension n

private theorem logArcGap_nonneg (c : ℝ≥0) (n : ℕ) : 0 ≤ logArcGap c n :=
  div_nonneg (mul_nonneg c.2 (Real.log_nonneg (qubitDimension_ge_one n))) (qubitDimension_pos n).le

/-- The complementary length is `c * log D / D` once it fits in a turn. -/
def zeroGateLogArcRadius (c : ℝ≥0) (n : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (1 - logArcGap c n), le_max_left _ _, max_le zero_le_one (sub_le_self _ (logArcGap_nonneg c n))⟩

private theorem tendsto_logArcGap (c : ℝ≥0) : Tendsto (logArcGap c) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  change Tendsto (fun n => (c : ℝ) * Real.log (qubitDimension n) / qubitDimension n) atTop (𝓝 0)
  simpa only [Function.comp_apply, mul_div_assoc, mul_zero] using
    (h.comp tendsto_qubitDimension).const_mul (c : ℝ)

private theorem eventually_logArcGap_lt_one (c : ℝ≥0) : ∀ᶠ n in atTop, logArcGap c n < 1 :=
  (tendsto_order.mp (tendsto_logArcGap c)).2 1 zero_lt_one

/-- The radius equals the untruncated logarithmic threshold for large registers. -/
theorem eventually_zeroGateLogArcRadius_eq (c : ℝ≥0) :
    ∀ᶠ n in atTop, (zeroGateLogArcRadius c n : ℝ) = 1 - (c : ℝ) * Real.log ((2 : ℝ) ^ n) / (2 : ℝ) ^ n :=
  (eventually_logArcGap_lt_one c).mono fun _ h => max_eq_right (sub_nonneg.mpr h.le)

/-- Enclosure tends to probability zero above the logarithmic gap scale. -/
theorem tendsto_zeroGateFullArcMass_logArcRadius_zero (c : ℝ≥0) (hc : 1 < (c : ℝ)) :
    Tendsto (fun n => zeroGateFullArcMass n (zeroGateLogArcRadius c n)) atTop (𝓝 0) := by
  apply tendsto_zeroGateFullArcMass_zero_of_complement
  have hlog : Tendsto (fun n => ((c : ℝ) - 1) * Real.log (qubitDimension n)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_qubitDimension).const_mul_atTop (sub_pos.mpr hc)
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_logArcGap_lt_one c, (tendsto_atTop.mp hlog) (M + 1)] with n hg hn
  have hr : (zeroGateLogArcRadius c n : ℝ) = 1 - logArcGap c n := max_eq_right (sub_nonneg.mpr hg.le)
  have hmul : qubitDimension n * logArcGap c n = (c : ℝ) * Real.log (qubitDimension n) := by
    rw [logArcGap, mul_comm (qubitDimension n), div_mul_cancel₀ _ (qubitDimension_pos n).ne']
  have hscale : ((2 ^ n - 1 : ℕ) : ℝ) * (1 - (zeroGateLogArcRadius c n : ℝ)) -
      Real.log ((2 : ℝ) ^ n) = ((c : ℝ) - 1) * Real.log (qubitDimension n) - logArcGap c n := by
    rw [cast_qubitDimension_sub_one, hr, sub_sub_cancel, sub_mul, hmul, one_mul]
    change (c : ℝ) * Real.log (qubitDimension n) - logArcGap c n - Real.log (qubitDimension n) = _
    ring
  rw [hscale]
  linarith only [hg, hn]

private theorem tendsto_rpow_mul_logArcGap (c : ℝ≥0) {b : ℝ} (hb : b < 1) :
    Tendsto (fun n => qubitDimension n ^ b * logArcGap c n) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x ^ (1 - b)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hb)).tendsto_div_nhds_zero
  have h' : Tendsto (fun n => (c : ℝ) * (Real.log (qubitDimension n) / qubitDimension n ^ (1 - b)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using (h.comp tendsto_qubitDimension).const_mul (c : ℝ)
  refine h'.congr fun n => ?_
  rw [Real.rpow_sub (qubitDimension_pos n), Real.rpow_one]
  dsimp only [logArcGap]
  field_simp [(qubitDimension_pos n).ne', (Real.rpow_pos_of_pos (qubitDimension_pos n) b).ne']

private theorem qubitDimension_rpow_neg_le_gap_power (c : ℝ≥0) {a : ℝ} (n : ℕ)
    (hg : logArcGap c n < 1) (hcoeff : (c : ℝ) ≤ a * (1 - logArcGap c n)) :
    qubitDimension n ^ (-a) ≤ (1 - logArcGap c n) ^ (2 ^ n - 1) := by
  let s := logArcGap c n
  let k : ℕ := 2 ^ n - 1
  let L := Real.log (qubitDimension n)
  have hs : 0 < 1 - s := sub_pos.mpr hg
  have hL : 0 ≤ L := Real.log_nonneg (qubitDimension_ge_one n)
  have hlog : -(s / (1 - s)) ≤ Real.log (1 - s) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
    have he : (1 - s)⁻¹ - 1 = s / (1 - s) := by
      apply (eq_div_iff hs.ne').mpr
      rw [sub_mul, inv_mul_cancel₀ hs.ne', one_mul, sub_sub_cancel]
    rw [Real.log_inv, he] at h
    linarith only [h]
  have hk : (k : ℝ) ≤ qubitDimension n := by
    dsimp only [k]
    rw [cast_qubitDimension_sub_one]
    exact sub_le_self _ zero_le_one
  have hmul : qubitDimension n * s = (c : ℝ) * L := by
    change qubitDimension n * ((c : ℝ) * L / qubitDimension n) = _
    rw [mul_comm (qubitDimension n), div_mul_cancel₀ _ (qubitDimension_pos n).ne']
  have hscale : (k : ℝ) * s / (1 - s) ≤ a * L := by
    apply (div_le_iff₀ hs).mpr
    calc
      _ ≤ qubitDimension n * s := mul_le_mul_of_nonneg_right hk (logArcGap_nonneg c n)
      _ = (c : ℝ) * L := hmul
      _ ≤ (a * (1 - s)) * L := mul_le_mul_of_nonneg_right hcoeff hL
      _ = _ := by ring
  have hpow : -(a * L) ≤ (k : ℝ) * Real.log (1 - s) := calc
    _ ≤ -((k : ℝ) * s / (1 - s)) := neg_le_neg hscale
    _ = (k : ℝ) * (-(s / (1 - s))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
  calc
    qubitDimension n ^ (-a) = Real.exp (-(a * L)) := by
      rw [Real.rpow_def_of_pos (qubitDimension_pos n)]
      congr 1
      dsimp only [L]
      ring
    _ ≤ Real.exp ((k : ℝ) * Real.log (1 - s)) := Real.exp_le_exp_of_le hpow
    _ = (1 - s) ^ k := by rw [← Real.log_pow, Real.exp_log (pow_pos hs _)]

local instance logArcCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

private theorem zeroGateFullArcMass_le_one (n : ℕ) (r : ℝ) : zeroGateFullArcMass n r ≤ 1 := by
  change (volume (relativeEnclosingUnitArc (fun _ : Fin n => false) r)).toReal ≤ 1
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) prob_le_one

/-- Enclosure tends to probability one below the logarithmic gap scale. -/
theorem tendsto_zeroGateFullArcMass_logArcRadius_one (c : ℝ≥0) (hc : (c : ℝ) < 1) :
    Tendsto (fun n => zeroGateFullArcMass n (zeroGateLogArcRadius c n)) atTop (𝓝 1) := by
  obtain ⟨b, hcb, hb⟩ := exists_between hc
  obtain ⟨a, hca, hab⟩ := exists_between hcb
  have ha0 : 0 < a := c.2.trans_lt hca
  let m (n : ℕ) := ⌊qubitDimension n ^ b⌋₊
  let q (n : ℕ) := (m n : ℝ) * (1 - logArcGap c n) ^ (2 ^ n - 1)
  have hbTop : Tendsto (fun n => qubitDimension n ^ b) atTop atTop :=
    (tendsto_rpow_atTop (ha0.trans hab)).comp tendsto_qubitDimension
  have hbig : ∀ᶠ n in atTop, 2 ≤ qubitDimension n ^ b := (tendsto_atTop.mp hbTop) 2
  have hfloor (n : ℕ) (hn : 2 ≤ qubitDimension n ^ b) : qubitDimension n ^ b / 2 ≤ (m n : ℝ) := by
    have h := Nat.lt_floor_add_one (qubitDimension n ^ b)
    change qubitDimension n ^ b < (m n : ℝ) + 1 at h
    linarith only [h, hn]
  have hfit : ∀ᶠ n in atTop, (m n : ℝ) * logArcGap c n ≤ 1 := by
    filter_upwards [(tendsto_order.mp (tendsto_rpow_mul_logArcGap c hb)).2 1 zero_lt_one] with n hn
    exact (mul_le_mul_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg (qubitDimension_pos n).le _))
      (logArcGap_nonneg c n)).trans hn.le
  have hsmall : ∀ᶠ n in atTop, logArcGap c n < 1 - (c : ℝ) / a :=
    (tendsto_order.mp (tendsto_logArcGap c)).2 _ (sub_pos.mpr ((div_lt_one ha0).mpr hca))
  have hqge : ∀ᶠ n in atTop, qubitDimension n ^ (b - a) / 2 ≤ q n := by
    filter_upwards [hbig, hsmall, eventually_logArcGap_lt_one c] with n hn hs hg
    have hcoeff : (c : ℝ) ≤ a * (1 - logArcGap c n) := by
      have he : (c : ℝ) / a ≤ 1 - logArcGap c n := by linarith only [hs]
      simpa only [mul_comm] using (div_le_iff₀ ha0).mp he
    calc
      _ = (qubitDimension n ^ b * qubitDimension n ^ (-a)) / 2 := by
        rw [← Real.rpow_add (qubitDimension_pos n), sub_eq_add_neg]
      _ = qubitDimension n ^ b / 2 * qubitDimension n ^ (-a) := by ring
      _ ≤ q n := mul_le_mul (hfloor n hn) (qubitDimension_rpow_neg_le_gap_power c n hg hcoeff)
        (Real.rpow_nonneg (qubitDimension_pos n).le _) (Nat.cast_nonneg _)
  have ht : Tendsto (fun n => qubitDimension n ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_qubitDimension
  have hq : Tendsto q atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [(tendsto_atTop.mp ht) (2 * M), hqge] with n hn hge
    exact (by linarith only [hn] : M ≤ qubitDimension n ^ (b - a) / 2).trans hge
  have hsum : Tendsto (fun n => 1 + q n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [(tendsto_atTop.mp hq) M] with n hn
    linarith only [hn]
  have hlim : Tendsto (fun n => q n / (1 + q n)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n => (1 + q n)⁻¹) atTop (𝓝 0) := hsum.inv_tendsto_atTop
    have hr : Tendsto (fun n => 1 - (1 + q n)⁻¹) atTop (𝓝 1) := by
      simpa only [sub_zero] using hinv.const_sub 1
    apply hr.congr'
    filter_upwards [(tendsto_atTop.mp hq) 0] with n hn
    have hne : 1 + q n ≠ 0 := (by linarith only [hn] : 0 < 1 + q n).ne'
    calc
      _ = (1 + q n) / (1 + q n) - 1 / (1 + q n) := by rw [div_self hne, one_div]
      _ = _ := by rw [← sub_div, add_sub_cancel_left]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [hbig, hfit, eventually_logArcGap_lt_one c] with n hn hpack hg
    have hm : 0 < m n := by
      have := hfloor n hn
      exact_mod_cast (by linarith only [hn, this] : 0 < (m n : ℝ))
    let s : Ico (0 : ℝ) 1 := ⟨logArcGap c n, logArcGap_nonneg c n, hg⟩
    have hr : (zeroGateLogArcRadius c n : ℝ) = 1 - (s : ℝ) := max_eq_right (sub_nonneg.mpr hg.le)
    rw [hr]
    exact zeroGateFullArcMass_complement_ge_emptyArcs n hm s hpack
  · exact Eventually.of_forall fun n => zeroGateFullArcMass_le_one n _

/-- In projective operator norm, the deficit from error two is quadratic in
the logarithmic arc gap. -/
theorem tendsto_zeroGateLogArcTolerance_deficit (c : ℝ≥0) :
    Tendsto (fun n => (2 - zeroGateArcTolerance (zeroGateLogArcRadius c n)) /
      (Real.log ((2 : ℝ) ^ n) / (2 : ℝ) ^ n) ^ 2) atTop (𝓝 ((Real.pi * (c : ℝ) / 2) ^ 2)) := by
  let w (n : ℕ) := Real.log (qubitDimension n) / qubitDimension n
  let x (n : ℕ) := Real.pi * logArcGap c n / 4
  have hx : Tendsto x atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using ((tendsto_logArcGap c).const_mul Real.pi).div_const 4
  have hs : Tendsto (fun n => Real.sinc (x n)) atTop (𝓝 1) := by
    have h := (Real.continuous_sinc.continuousAt (x := (0 : ℝ))).tendsto.comp hx
    change Tendsto (fun n => Real.sinc (x n)) atTop (𝓝 (Real.sinc 0)) at h
    rw [Real.sinc_zero] at h
    exact h
  have hlim : Tendsto (fun n => (Real.pi * (c : ℝ) / 2 * Real.sinc (x n)) ^ 2)
      atTop (𝓝 ((Real.pi * (c : ℝ) / 2) ^ 2)) := by
    simpa only [mul_one] using (hs.const_mul (Real.pi * (c : ℝ) / 2)).pow 2
  apply hlim.congr'
  filter_upwards [eventually_logArcGap_lt_one c, (tendsto_atTop.mp tendsto_qubitDimension) 2] with n hn hd
  have hw : 0 < w n := div_pos (Real.log_pos (by linarith only [hd])) (qubitDimension_pos n)
  have hr : (zeroGateLogArcRadius c n : ℝ) = 1 - logArcGap c n := max_eq_right (sub_nonneg.mpr hn.le)
  have hangle : Real.pi * (1 - logArcGap c n) / 2 = Real.pi / 2 - 2 * x n := by
    dsimp only [x]
    ring
  have hcost : 2 - zeroGateArcTolerance (zeroGateLogArcRadius c n) = 4 * Real.sin (x n) ^ 2 := by
    rw [zeroGateArcTolerance, hr, hangle, Real.sin_pi_div_two_sub, Real.cos_two_mul']
    nlinarith only [Real.sin_sq_add_cos_sq (x n)]
  have hsin : Real.sin (x n) = x n * Real.sinc (x n) := by
    by_cases he : x n = 0
    · simp only [he, Real.sin_zero, zero_mul]
    · rw [Real.sinc_of_ne_zero he, ← mul_div_assoc, mul_comm (x n), mul_div_cancel_right₀ _ he]
  have harg : x n = Real.pi * (c : ℝ) * w n / 4 := by
    dsimp only [x, logArcGap, w]
    ring
  change _ = (2 - zeroGateArcTolerance (zeroGateLogArcRadius c n)) / w n ^ 2
  rw [hcost, hsin, harg]
  field_simp [hw.ne']
  ring

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- On the same Gaussian draw, the long-time return fractions on successive
prefixes exhibit the logarithmic transition for every coefficient and start. -/
theorem gaussian_path_zeroGateLogArcRadius_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ c : ℝ≥0, ∀ a : ℝ,
      (∀ k : ℕ,
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        let r := zeroGateLogArcRadius c (k + 3)
        Tendsto (fun T => volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a)) atTop
          (𝓝 (zeroGateFullArcMass (k + 3) r))) ∧
      ((c : ℝ) < 1 → Tendsto (fun k : ℕ => zeroGateFullArcMass (k + 3) (zeroGateLogArcRadius c (k + 3))) atTop (𝓝 1)) ∧
      (1 < (c : ℝ) → Tendsto (fun k : ℕ => zeroGateFullArcMass (k + 3) (zeroGateLogArcRadius c (k + 3))) atTop (𝓝 0)) := by
  filter_upwards [gaussian_path_zeroGateFullOccupation_from_start] with ω hω
  intro c a
  have hshift : Tendsto (fun k : ℕ => k + 3) atTop atTop :=
    tendsto_atTop.mpr fun b => (eventually_ge_atTop b).mono fun _ _ => by omega
  exact ⟨fun k => hω k (zeroGateLogArcRadius c (k + 3)) a,
    fun hc => (tendsto_zeroGateFullArcMass_logArcRadius_one c hc).comp hshift,
    fun hc => (tendsto_zeroGateFullArcMass_logArcRadius_zero c hc).comp hshift⟩

#print axioms tendsto_zeroGateFullArcMass_logArcRadius_zero
#print axioms tendsto_zeroGateFullArcMass_logArcRadius_one
#print axioms tendsto_zeroGateLogArcTolerance_deficit
#print axioms gaussian_path_zeroGateLogArcRadius_occupation

end

end GaloisForLFunctions.HTGeometry
