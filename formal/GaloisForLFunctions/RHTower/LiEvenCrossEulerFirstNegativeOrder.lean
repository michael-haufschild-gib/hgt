import GaloisForLFunctions.RHTower.LiEvenCrossEulerSmallMassProfile
import Mathlib.Analysis.Asymptotics.Defs

/-!
# The first negative LI Euler jet has logarithmic order

Actual positive-mass jet oscillation defines the least negative order. The uniform
two-term source profile makes every earlier order positive below the crossover
and supplies a rounded negative witness above it.
-/

namespace RHTower

noncomputable section

/-- Every positive mass has a strictly negative actual LI Euler jet. -/
theorem exists_liEvenCrossFirstCurrentEvenEulerJet_neg {v : ℝ} (hv : 0 < v) :
    ∃ k : ℕ, liEvenCrossFirstCurrentEvenEulerJet v k < 0 := by
  obtain ⟨k, _, hk⟩ :=
    (liEvenCrossFirstCurrentEvenEulerJet_cofinal_both_signs ⟨v, hv⟩).1 0
  exact ⟨k, hk⟩

/-- The least negative order for positive mass, extended by zero elsewhere. -/
def liEvenCrossFirstNegativeEulerOrder (v : ℝ) : ℕ :=
  if hv : 0 < v then Nat.find (exists_liEvenCrossFirstCurrentEvenEulerJet_neg hv) else 0

theorem liEvenCrossFirstNegativeEulerOrder_jet_neg {v : ℝ} (hv : 0 < v) :
    liEvenCrossFirstCurrentEvenEulerJet v (liEvenCrossFirstNegativeEulerOrder v) < 0 := by
  classical
  simpa only [liEvenCrossFirstNegativeEulerOrder, dif_pos hv] using
    Nat.find_spec (exists_liEvenCrossFirstCurrentEvenEulerJet_neg hv)

theorem liEvenCrossFirstNegativeEulerOrder_le_of_jet_neg
    {v : ℝ} (hv : 0 < v) {k : ℕ}
    (hk : liEvenCrossFirstCurrentEvenEulerJet v k < 0) :
    liEvenCrossFirstNegativeEulerOrder v ≤ k := by
  classical
  simpa only [liEvenCrossFirstNegativeEulerOrder, dif_pos hv] using
    Nat.find_min' (exists_liEvenCrossFirstCurrentEvenEulerJet_neg hv) hk

theorem liEvenCrossFirstCurrentEvenEulerJet_nonneg_before_firstNegative
    {v : ℝ} (hv : 0 < v) {k : ℕ} (hk : k < liEvenCrossFirstNegativeEulerOrder v) :
    0 ≤ liEvenCrossFirstCurrentEvenEulerJet v k := by
  classical
  apply le_of_not_gt
  exact Nat.find_min (exists_liEvenCrossFirstCurrentEvenEulerJet_neg hv)
    (by simpa only [liEvenCrossFirstNegativeEulerOrder, dif_pos hv] using hk)

/-- The source-dependent additive shift in the first-negative-order clock. -/
def liEvenCrossEulerCrossoverOffset : ℝ :=
  Real.log (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1)) / Real.log 4

/-- The real two-term crossover center. -/
def liEvenCrossEulerCrossoverCenter (v : ℝ) : ℝ :=
  -Real.log v / Real.log 4 + liEvenCrossEulerCrossoverOffset

theorem liEvenCrossEulerCrossoverCenter_rpow_balance {v : ℝ} (hv : 0 < v) :
    (4 : ℝ) ^ liEvenCrossEulerCrossoverCenter v * (4 * normalizedPrimeArchMoment 1 * v) =
      normalizedPrimeArchMoment 0 := by
  have h0 := normalizedPrimeArchMoment_pos_of_le_eleven 0 (by omega)
  have h1 := normalizedPrimeArchMoment_pos_of_le_eleven 1 (by omega)
  have h4m : 0 < 4 * normalizedPrimeArchMoment 1 := by positivity
  have hden : 0 < 4 * normalizedPrimeArchMoment 1 * v := mul_pos h4m hv
  have hl : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne'
  have hc : liEvenCrossEulerCrossoverCenter v =
      Real.log (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1 * v)) /
        Real.log 4 := by
    rw [Real.log_div h0.ne' hden.ne', Real.log_mul h4m.ne' hv.ne']
    dsimp [liEvenCrossEulerCrossoverCenter, liEvenCrossEulerCrossoverOffset]
    rw [Real.log_div h0.ne' h4m.ne']
    ring
  rw [hc, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hexp : Real.log 4 *
      (Real.log (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1 * v)) /
        Real.log 4) =
      Real.log (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1 * v)) := by
    field_simp
  rw [hexp, Real.exp_log (div_pos h0 hden)]
  exact div_mul_cancel₀ _ hden.ne'

theorem liEvenCrossEulerCrossoverCenter_early_leading_term_le
    {v : ℝ} (hv : 0 < v) (k : ℕ)
    (hk : (k : ℝ) ≤ liEvenCrossEulerCrossoverCenter v - 1) :
    (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v ≤
      normalizedPrimeArchMoment 0 / 4 := by
  have h1 := normalizedPrimeArchMoment_pos_of_le_eleven 1 (by omega)
  have hpow : (4 : ℝ) ^ (k + 1) ≤ (4 : ℝ) ^ liEvenCrossEulerCrossoverCenter v := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hmul := mul_le_mul_of_nonneg_right hpow (mul_pos h1 hv).le
  have hbalance := liEvenCrossEulerCrossoverCenter_rpow_balance hv
  nlinarith

theorem liEvenCrossEulerCrossoverCenter_late_leading_term_ge
    {v : ℝ} (hv : 0 < v) (k : ℕ)
    (hk : liEvenCrossEulerCrossoverCenter v + 1 ≤ (k : ℝ)) :
    4 * normalizedPrimeArchMoment 0 ≤
      (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v := by
  have h1 := normalizedPrimeArchMoment_pos_of_le_eleven 1 (by omega)
  have hpow : (4 : ℝ) ^ (liEvenCrossEulerCrossoverCenter v + 2) ≤ (4 : ℝ) ^ (k + 1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 4)] at hpow
  norm_num at hpow
  have hmul := mul_le_mul_of_nonneg_right hpow (mul_pos h1 hv).le
  have hbalance := liEvenCrossEulerCrossoverCenter_rpow_balance hv
  nlinarith

theorem liEvenCrossEulerCrossoverCenter_tendsto_atTop :
    Filter.Tendsto liEvenCrossEulerCrossoverCenter
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have hlog : Filter.Tendsto (fun v : ℝ => -Real.log v / Real.log 4)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    (Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).atTop_div_const
      (Real.log_pos (by norm_num : (1 : ℝ) < 4))
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [hlog.eventually_ge_atTop (b - liEvenCrossEulerCrossoverOffset)] with v hv
  dsimp [liEvenCrossEulerCrossoverCenter]
  linarith

/-- Uniform earlier positivity and a negative natural order above the crossover. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_eventually_crossover_signs :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∀ k : ℕ, (k : ℝ) ≤ liEvenCrossEulerCrossoverCenter v - 1 →
        0 < liEvenCrossFirstCurrentEvenEulerJet v k) ∧
      liEvenCrossFirstCurrentEvenEulerJet v
        (Nat.ceil (liEvenCrossEulerCrossoverCenter v + 1)) < 0 ∧
      ((Nat.ceil (liEvenCrossEulerCrossoverCenter v + 1) : ℕ) : ℝ) <
        liEvenCrossEulerCrossoverCenter v + 2 := by
  have h0 := normalizedPrimeArchMoment_pos_of_le_eleven 0 (by omega)
  have hε : 0 < normalizedPrimeArchMoment 0 / 4 := by positivity
  filter_upwards [self_mem_nhdsWithin,
    liEvenCrossEulerCrossoverCenter_tendsto_atTop.eventually_ge_atTop 0,
    liEvenCrossFirstCurrentEvenEulerJet_uniform_log_window
      (liEvenCrossEulerCrossoverOffset + 2) hε] with v hv hc hprofile
  change 0 < v at hv
  have hden : 0 < 2 * v := by positivity
  have hround : ((Nat.ceil (liEvenCrossEulerCrossoverCenter v + 1) : ℕ) : ℝ) <
      liEvenCrossEulerCrossoverCenter v + 2 := by
    calc
      _ < (liEvenCrossEulerCrossoverCenter v + 1) + 1 :=
        Nat.ceil_lt_add_one (by linarith)
      _ = liEvenCrossEulerCrossoverCenter v + 2 := by ring
  constructor
  · intro k hk
    have hwindow : (k : ℝ) ≤ -Real.log v / Real.log 4 +
        (liEvenCrossEulerCrossoverOffset + 2) := by
      dsimp [liEvenCrossEulerCrossoverCenter] at hk
      linarith
    have herr := (abs_lt.mp (hprofile k hwindow)).1
    have hleading := liEvenCrossEulerCrossoverCenter_early_leading_term_le hv k hk
    have hnormalized : 0 < liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) := by
      linarith
    simpa only [div_mul_cancel₀ _ hden.ne'] using mul_pos hnormalized hden
  · constructor
    · have hwindow : ((Nat.ceil (liEvenCrossEulerCrossoverCenter v + 1) : ℕ) : ℝ) ≤
          -Real.log v / Real.log 4 + (liEvenCrossEulerCrossoverOffset + 2) := by
        calc
          _ ≤ liEvenCrossEulerCrossoverCenter v + 2 := hround.le
          _ = -Real.log v / Real.log 4 + (liEvenCrossEulerCrossoverOffset + 2) := by
            dsimp [liEvenCrossEulerCrossoverCenter]
            ring
      have herr := (abs_lt.mp (hprofile _ hwindow)).2
      have hleading := liEvenCrossEulerCrossoverCenter_late_leading_term_ge hv
        (Nat.ceil (liEvenCrossEulerCrossoverCenter v + 1)) (Nat.le_ceil _)
      have hnormalized : liEvenCrossFirstCurrentEvenEulerJet v
          (Nat.ceil (liEvenCrossEulerCrossoverCenter v + 1)) / (2 * v) < 0 := by
        linarith
      simpa only [div_mul_cancel₀ _ hden.ne'] using mul_neg_of_neg_of_pos hnormalized hden
    · exact hround

/-- The least negative actual LI Euler order lies in a bounded source-centered interval. -/
theorem liEvenCrossFirstNegativeEulerOrder_eventually_crossover_interval :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
      liEvenCrossEulerCrossoverCenter v - 1 < (liEvenCrossFirstNegativeEulerOrder v : ℝ) ∧
      (liEvenCrossFirstNegativeEulerOrder v : ℝ) < liEvenCrossEulerCrossoverCenter v + 2 := by
  filter_upwards [self_mem_nhdsWithin,
    liEvenCrossFirstCurrentEvenEulerJet_eventually_crossover_signs] with v hv hsigns
  constructor
  · by_contra h
    have hpos := hsigns.1 (liEvenCrossFirstNegativeEulerOrder v) (le_of_not_gt h)
    exact (not_lt_of_gt hpos) (liEvenCrossFirstNegativeEulerOrder_jet_neg hv)
  · have horder := liEvenCrossFirstNegativeEulerOrder_le_of_jet_neg hv hsigns.2.1
    have horderReal : (liEvenCrossFirstNegativeEulerOrder v : ℝ) ≤
        ((Nat.ceil (liEvenCrossEulerCrossoverCenter v + 1) : ℕ) : ℝ) := by
      exact_mod_cast horder
    exact horderReal.trans_lt hsigns.2.2

/-- An explicit bounded error in the logarithmic first-negative-order law. -/
theorem liEvenCrossFirstNegativeEulerOrder_eventually_log_error_le :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
      |(liEvenCrossFirstNegativeEulerOrder v : ℝ) + Real.log v / Real.log 4| ≤
        |liEvenCrossEulerCrossoverOffset| + 2 := by
  filter_upwards [liEvenCrossFirstNegativeEulerOrder_eventually_crossover_interval]
    with v hv
  have hofflo := neg_abs_le liEvenCrossEulerCrossoverOffset
  have hoffhi := le_abs_self liEvenCrossEulerCrossoverOffset
  dsimp [liEvenCrossEulerCrossoverCenter] at hv
  simp only [neg_div] at hv
  apply abs_le.2
  constructor <;> linarith [hv.1, hv.2]

/-- The least negative order is `log (1/v) / log 4 + O(1)` as mass tends to zero. -/
theorem liEvenCrossFirstNegativeEulerOrder_log_bigO :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
      (fun v : ℝ => (liEvenCrossFirstNegativeEulerOrder v : ℝ) -
        Real.log (1 / v) / Real.log 4) (fun _ : ℝ => (1 : ℝ)) := by
  apply Asymptotics.isBigO_iff.2
  refine ⟨|liEvenCrossEulerCrossoverOffset| + 2, ?_⟩
  filter_upwards [liEvenCrossFirstNegativeEulerOrder_eventually_log_error_le] with v hv
  simpa only [Real.norm_eq_abs, norm_one, mul_one, one_div, Real.log_inv, neg_div,
    sub_neg_eq_add] using hv

/-- The least negative order has logarithmic slope `1 / log 4`. -/
theorem liEvenCrossFirstNegativeEulerOrder_log_ratio_tendsto :
    Filter.Tendsto (fun v : ℝ =>
      (liEvenCrossFirstNegativeEulerOrder v : ℝ) / Real.log (1 / v))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / Real.log 4)) := by
  let C : ℝ := |liEvenCrossEulerCrossoverOffset| + 2
  have hlog : Filter.Tendsto (fun v : ℝ => -Real.log v)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hl : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne'
  have hlo : Filter.Tendsto (fun v : ℝ => -C / (-Real.log v))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds.div_atTop hlog
  have hhi : Filter.Tendsto (fun v : ℝ => C / (-Real.log v))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds.div_atTop hlog
  have hb : ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
      -C / (-Real.log v) ≤
          (liEvenCrossFirstNegativeEulerOrder v : ℝ) / (-Real.log v) - 1 / Real.log 4 ∧
      (liEvenCrossFirstNegativeEulerOrder v : ℝ) / (-Real.log v) - 1 / Real.log 4 ≤
          C / (-Real.log v) := by
    filter_upwards [hlog.eventually_ge_atTop 1,
      liEvenCrossFirstNegativeEulerOrder_eventually_log_error_le] with v hv hbound
    have hden : 0 < -Real.log v := by linarith
    have hvlog : Real.log v ≠ 0 := by
      intro h
      rw [h] at hden
      norm_num at hden
    have hid : (liEvenCrossFirstNegativeEulerOrder v : ℝ) / (-Real.log v) -
        1 / Real.log 4 =
        ((liEvenCrossFirstNegativeEulerOrder v : ℝ) + Real.log v / Real.log 4) /
          (-Real.log v) := by
      field_simp [hvlog, hl]
      ring
    rw [hid]
    exact ⟨div_le_div_of_nonneg_right (abs_le.mp hbound).1 hden.le,
      div_le_div_of_nonneg_right (abs_le.mp hbound).2 hden.le⟩
  have hres : Filter.Tendsto (fun v : ℝ =>
      (liEvenCrossFirstNegativeEulerOrder v : ℝ) / (-Real.log v) - 1 / Real.log 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (hb.mono fun _ h => h.1)
      (hb.mono fun _ h => h.2)
  have hfinal := hres.add (tendsto_const_nhds (x := 1 / Real.log 4))
  simpa only [sub_add_cancel, zero_add, one_div, Real.log_inv] using hfinal

end

end RHTower
