import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact overlap of logarithmic prime-entry tents

The critical deficit uses the causal tent at each logarithmic prime entry.
Its finite overlap has an exact boundary correction. The limiting kernel
retains both the larger entry time and their difference; in half-density
coordinates it is the exponential kernel `(2+|a-b|) exp(-|a-b|/2)`.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

def ccmPrimeEntryTent (a t : ℝ) : ℝ := max (t - a) 0

def ccmPrimeEntryOverlap (T a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, Real.exp (-t) * ccmPrimeEntryTent a t * ccmPrimeEntryTent b t

def ccmPrimeEntryOverlapLimit (a b : ℝ) : ℝ :=
  Real.exp (-max a b) * (2 + |a - b|)

def ccmPrimeEntryRatioKernel (s : ℝ) : ℝ := (2 + |s|) * Real.exp (-|s| / 2)

private theorem weighted_product_integral (a b c T : ℝ) :
    (∫ t in c..T, Real.exp (-t) * (t - a) * (t - b)) =
      Real.exp (-c) * ((c - a) * (c - b) + 2 * c - a - b + 2) -
        Real.exp (-T) * ((T - a) * (T - b) + 2 * T - a - b + 2) := by
  let P : ℝ → ℝ := fun t => (t - a) * (t - b) + 2 * t - a - b + 2
  have hp (t : ℝ) : HasDerivAt P (2 * t - a - b + 2) t := by
    convert! ((((((hasDerivAt_id t).sub_const a).mul ((hasDerivAt_id t).sub_const b)).add
      ((hasDerivAt_id t).const_mul 2)).sub_const a).sub_const b).add_const 2 using 1
    dsimp only [P, id_eq]
    ring
  have hd (t : ℝ) : HasDerivAt (fun t => -(Real.exp (-t) * P t))
      (Real.exp (-t) * (t - a) * (t - b)) t := by
    convert! ((((hasDerivAt_id t).neg).exp).mul (hp t)).neg using 1
    simp only [P, id_eq, Pi.neg_apply]
    ring
  have hi : IntervalIntegrable (fun t => Real.exp (-t) * (t - a) * (t - b)) volume c T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  exact h.trans (by dsimp only [P]; ring)

theorem ccmPrimeEntryOverlap_nonneg {T : ℝ} (hT : 0 ≤ T) (a b : ℝ) :
    0 ≤ ccmPrimeEntryOverlap T a b := by
  apply intervalIntegral.integral_nonneg hT
  intro t _
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _)) (le_max_right _ _)

theorem ccmPrimeEntryOverlap_comm (T a b : ℝ) :
    ccmPrimeEntryOverlap T a b = ccmPrimeEntryOverlap T b a := by
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- Both entry times and the terminal boundary are retained in the overlap. -/
theorem ccmPrimeEntryOverlap_eq {T a b : ℝ} (hc0 : 0 ≤ max a b)
    (haT : a ≤ T) (hbT : b ≤ T) :
    ccmPrimeEntryOverlap T a b = ccmPrimeEntryOverlapLimit a b -
      Real.exp (-T) * ((T - a) * (T - b) + 2 * T - a - b + 2) := by
  let c := max a b
  have hcT : c ≤ T := max_le haT hbT
  have hi (x y : ℝ) : IntervalIntegrable (fun t =>
      Real.exp (-t) * ccmPrimeEntryTent a t * ccmPrimeEntryTent b t) volume x y := by
    apply Continuous.intervalIntegrable
    unfold ccmPrimeEntryTent
    fun_prop
  have hhead : (∫ t in (0 : ℝ)..c,
      Real.exp (-t) * ccmPrimeEntryTent a t * ccmPrimeEntryTent b t) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htc : t ≤ c := (uIcc_of_le hc0 ▸ ht).2
        rcases le_total a b with hab | hba
        · have htb : t ≤ b := by simpa only [c, max_eq_right hab] using htc
          simp only [ccmPrimeEntryTent, max_eq_right (sub_nonpos.mpr htb), mul_zero]
        · have hta : t ≤ a := by simpa only [c, max_eq_left hba] using htc
          simp only [ccmPrimeEntryTent, max_eq_right (sub_nonpos.mpr hta), mul_zero, zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  have htail : (∫ t in c..T,
      Real.exp (-t) * ccmPrimeEntryTent a t * ccmPrimeEntryTent b t) =
      ∫ t in c..T, Real.exp (-t) * (t - a) * (t - b) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hct : c ≤ t := (uIcc_of_le hcT ▸ ht).1
    simp only [ccmPrimeEntryTent]
    rw [max_eq_left (sub_nonneg.mpr ((le_max_left a b).trans hct)),
      max_eq_left (sub_nonneg.mpr ((le_max_right a b).trans hct))]
  unfold ccmPrimeEntryOverlap
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c T),
    hhead, zero_add, htail, weighted_product_integral]
  congr 1
  unfold ccmPrimeEntryOverlapLimit
  dsimp only [c]
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [max_eq_left hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

theorem ccmPrimeEntryOverlap_le_limit {T a b : ℝ} (hc0 : 0 ≤ max a b)
    (haT : a ≤ T) (hbT : b ≤ T) :
    ccmPrimeEntryOverlap T a b ≤ ccmPrimeEntryOverlapLimit a b := by
  rw [ccmPrimeEntryOverlap_eq hc0 haT hbT]
  have hp : 0 ≤ (T - a) * (T - b) + 2 * T - a - b + 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haT) (sub_nonneg.mpr hbT)]
  exact sub_le_self _ (mul_nonneg (Real.exp_pos _).le hp)

theorem ccmPrimeEntryOverlapLimit_comm (a b : ℝ) :
    ccmPrimeEntryOverlapLimit a b = ccmPrimeEntryOverlapLimit b a := by
  simp only [ccmPrimeEntryOverlapLimit, max_comm a b, abs_sub_comm a b]

theorem ccmPrimeEntryOverlapLimit_pos (a b : ℝ) : 0 < ccmPrimeEntryOverlapLimit a b := by
  unfold ccmPrimeEntryOverlapLimit
  positivity

theorem ccmPrimeEntryRatioKernel_even (s : ℝ) :
    ccmPrimeEntryRatioKernel (-s) = ccmPrimeEntryRatioKernel s := by
  simp only [ccmPrimeEntryRatioKernel, abs_neg]

/-- Exact product/ratio separation of the full overlap kernel. -/
theorem ccmPrimeEntryOverlapLimit_eq_ratio (a b : ℝ) :
    ccmPrimeEntryOverlapLimit a b =
      Real.exp (-(a + b) / 2) * ccmPrimeEntryRatioKernel (a - b) := by
  have hm : max a b = (a + b + |a - b|) / 2 := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    · rw [max_eq_left hba, abs_of_nonneg (sub_nonneg.mpr hba)]
      ring
  unfold ccmPrimeEntryOverlapLimit ccmPrimeEntryRatioKernel
  rw [hm, show -((a + b + |a - b|) / 2) = -(a + b) / 2 + -|a - b| / 2 by ring,
    Real.exp_add]
  ring

/-- The self-interaction at a logarithmic prime entry has harmonic weight. -/
theorem ccmPrimeEntryOverlapLimit_log_self {n : ℕ} (hn : 0 < n) :
    ccmPrimeEntryOverlapLimit (Real.log n) (Real.log n) = 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [ccmPrimeEntryOverlapLimit, max_self, sub_self, abs_zero, add_zero,
    Real.exp_neg, Real.exp_log hnR]
  ring

theorem integral_mul_ccmPrimeEntryTent_eq_tail (g : ℝ → ℝ) (hg : Continuous g)
    {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    (∫ t in (0 : ℝ)..T, g t * ccmPrimeEntryTent a t) =
      ∫ t in a..T, g t * (t - a) := by
  have hi (x y : ℝ) : IntervalIntegrable (fun t => g t * ccmPrimeEntryTent a t) volume x y := by
    apply Continuous.intervalIntegrable
    exact hg.mul ((continuous_id.sub continuous_const).max continuous_const)
  have hhead : (∫ t in (0 : ℝ)..a, g t * ccmPrimeEntryTent a t) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hta : t ≤ a := (uIcc_of_le ha ▸ ht).2
        simp only [ccmPrimeEntryTent, max_eq_right (sub_nonpos.mpr hta), mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a T), hhead, zero_add]
  apply intervalIntegral.integral_congr
  intro t ht
  have hat : a ≤ t := (uIcc_of_le haT ▸ ht).1
  simp only [ccmPrimeEntryTent, max_eq_left (sub_nonneg.mpr hat)]

theorem integral_exp_neg_mul_ccmPrimeEntryTent {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t) * ccmPrimeEntryTent a t) =
      Real.exp (-a) - Real.exp (-T) * (T - a + 1) := by
  rw [integral_mul_ccmPrimeEntryTent_eq_tail _ (by fun_prop) ha haT]
  let F : ℝ → ℝ := fun t => -(Real.exp (-t) * (t - a + 1))
  have hd (t : ℝ) : HasDerivAt F (Real.exp (-t) * (t - a)) t := by
    convert! (((((hasDerivAt_id t).neg).exp).mul
      (((hasDerivAt_id t).sub_const a).add_const 1)).neg) using 1
    simp only [id_eq, Pi.neg_apply]
    ring
  have hi : IntervalIntegrable (fun t : ℝ => Real.exp (-t) * (t - a)) volume a T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  exact h.trans (by dsimp only [F]; ring)

/-- Exact overlap of a prime-entry tent with the continuous background. -/
theorem ccmPrimeEntry_background_overlap {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    (∫ t in (0 : ℝ)..T, (1 - Real.exp (-t)) * ccmPrimeEntryTent a t) =
      (T - a) ^ 2 / 2 - Real.exp (-a) + Real.exp (-T) * (T - a + 1) := by
  rw [integral_mul_ccmPrimeEntryTent_eq_tail _ (by fun_prop) ha haT]
  let F : ℝ → ℝ := fun t => (t - a) ^ 2 / 2 + Real.exp (-t) * (t - a + 1)
  have hd (t : ℝ) : HasDerivAt F ((1 - Real.exp (-t)) * (t - a)) t := by
    convert! ((((hasDerivAt_id t).sub_const a).pow 2).div_const 2).add
      ((((hasDerivAt_id t).neg).exp).mul (((hasDerivAt_id t).sub_const a).add_const 1)) using 1
    simp only [id_eq, Pi.neg_apply]
    ring
  have hi : IntervalIntegrable (fun t : ℝ => (1 - Real.exp (-t)) * (t - a)) volume a T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  exact h.trans (by dsimp only [F]; ring)

theorem ccmPrimeEntry_background_energy (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t) * (Real.exp t - 1) ^ 2) =
      Real.exp T - Real.exp (-T) - 2 * T := by
  have hpoint (t : ℝ) : Real.exp (-t) * (Real.exp t - 1) ^ 2 =
      Real.exp t + Real.exp (-t) - 2 := by
    have hc : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = (Real.exp (-t) * Real.exp t) * Real.exp t -
          2 * (Real.exp (-t) * Real.exp t) + Real.exp (-t) := by ring
      _ = _ := by rw [hc]; ring
  simp_rw [hpoint]
  have he : IntervalIntegrable (fun t : ℝ => Real.exp (-t)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub
    ((Real.continuous_exp.intervalIntegrable 0 T).add he) intervalIntegrable_const,
    intervalIntegral.integral_add (Real.continuous_exp.intervalIntegrable 0 T) he,
    intervalIntegral.integral_comp_neg, integral_exp, integral_exp]
  simp only [Real.exp_zero, neg_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

end RHTower
