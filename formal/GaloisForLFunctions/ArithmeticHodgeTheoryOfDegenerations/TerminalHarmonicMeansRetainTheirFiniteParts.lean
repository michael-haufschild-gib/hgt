import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNearCenterRetainsItsHarmonicFinitePart
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingConstantOfTheTiltedSpline
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCrossErrorOfTheBulkEntries

/-!
# Terminal harmonic means retain their finite parts

A terminal profile stays away from the origin of the rescaled horizon.
The harmonic Ramanujan finite part is therefore uniform on its support.
Conductor one also retains the logarithm of the terminal coordinate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open ArithmeticFunction (vonMangoldt)

private theorem tendsto_terminal_weighted_tail_mean
    {F g : ℝ → ℝ} {BF LF δ b : ℝ}
    (hF : ∀ x, |F x| ≤ BF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    (hδ : 0 < δ) (hzero : ∀ x, 0 ≤ x → x ≤ δ → F x = 0)
    (hg : Tendsto g atTop (𝓝 b)) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * g (a N * ((n : ℝ) / N))) / N)
      atTop (𝓝 (b * ∫ x in (0 : ℝ)..1, F x)) := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hmean := tendsto_weighted_riemannSum (w := fun _ : ℕ => (1 : ℝ))
    (M := 1) (W := 1) (by norm_num) (by intros; rfl) (by intros; norm_num)
    hFL (fun x _ => hF x) 0
  simp only [Nat.sub_zero, one_mul, sum_range_one, Nat.cast_one, div_one] at hmean
  have hz : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * (g (a N * ((n : ℝ) / N)) - b)) / N)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let η : ℝ := ε / (BF + 1)
    have hη : 0 < η := by dsimp only [η]; positivity
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp hg) η hη
    filter_upwards [eventually_ge_atTop 1, ha.eventually_ge_atTop (max 0 (T / δ))]
      with N hN haN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have ha0 : 0 ≤ a N := (le_max_left _ _).trans haN
    have hprod : ∀ n ∈ Icc 1 N,
        |F ((n : ℝ) / N) * (g (a N * ((n : ℝ) / N)) - b)| ≤ BF * η := by
      intro n hn
      have hx0 : 0 ≤ (n : ℝ) / N := by positivity
      by_cases hFx : F ((n : ℝ) / N) = 0
      · rw [hFx, zero_mul, abs_zero]
        positivity
      have hxδ : δ < (n : ℝ) / N := lt_of_not_ge fun hx => hFx (hzero _ hx0 hx)
      have harg : T ≤ a N * ((n : ℝ) / N) := by
        have hTa : T ≤ a N * δ := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans haN)
        exact hTa.trans (mul_le_mul_of_nonneg_left hxδ.le ha0)
      have hclose := hT _ harg
      rw [Real.dist_eq] at hclose
      rw [abs_mul]
      exact mul_le_mul (hF _) hclose.le (abs_nonneg _) hBF
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hN0]
    calc
      _ ≤ (∑ _n ∈ Icc 1 N, BF * η) / N := div_le_div_of_nonneg_right
        ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hprod)) hN0.le
      _ = BF * η := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp
      _ < ε := by
        dsimp only [η]
        rw [mul_div_assoc', div_lt_iff₀ (by positivity : 0 < BF + 1)]
        nlinarith only [hε]
  have h := hz.add (hmean.const_mul b)
  simp only [zero_add] at h
  apply h.congr
  intro N
  rw [← mul_div_assoc, ← add_div, mul_sum, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun n _ => by ring

/-- The harmonic Ramanujan sum has its signed finite part on real cutoffs. -/
theorem tendsto_lagHarmonic_floor_finite_part {m : ℕ} (hm : 0 < m) :
    Tendsto (fun t : ℝ => lagHarmonic m ⌊t⌋₊ - (if m = 1 then Real.log t else 0))
      atTop (𝓝 (if m = 1 then Real.eulerMascheroniConstant else -vonMangoldt m)) := by
  by_cases hm1 : m = 1
  · subst m
    simp only [if_true, lagHarmonic_one]
    have hfloor : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop := tendsto_nat_floor_atTop
    have hratio : Tendsto (fun t : ℝ => (⌊t⌋₊ : ℝ) / t) atTop (𝓝 1) :=
      tendsto_nat_floor_div_atTop
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
    simp only [Real.log_one] at hlog
    have h := (Real.tendsto_harmonic_sub_log.comp hfloor).add hlog
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hq : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
    have hq0 : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by exact_mod_cast hq
    dsimp only [Function.comp_def]
    rw [Real.log_div hq0.ne' (by linarith : t ≠ 0)]
    ring
  · simpa only [if_neg hm1, sub_zero, Function.comp_def] using
      (tendsto_lagHarmonic (by omega : 2 ≤ m)).comp
        (tendsto_nat_floor_atTop : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop)

/-- A terminal profile retains the local logarithm at conductor one and the signed harmonic
charge at every other conductor. The cutoff scale may grow at any rate. -/
theorem tendsto_terminal_lagHarmonic_centered_mean
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m : ℕ} (hm : 0 < m) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) *
      (lagHarmonic m ⌊a N * ((n : ℝ) / N)⌋₊ -
        (if m = 1 then Real.log (a N) else 0))) / N) atTop
      (𝓝 (if m = 1 then
        Real.eulerMascheroniConstant * (∫ x in (0 : ℝ)..1, logProfile h x) +
          ∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x
        else -vonMangoldt m * ∫ x in (0 : ℝ)..1, logProfile h x)) := by
  obtain ⟨BF, _, hBF, _⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |logProfile h x - logProfile h y| ≤
        ((LF : ℝ) * Real.exp (2 * A)) * |x - y| :=
    fun x _ y _ => abs_logProfile_sub_le hh hsupp hA hBF hLF x y
  let δ : ℝ := Real.exp (-A) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hzero : ∀ x, 0 ≤ x → x ≤ δ → logProfile h x = 0 := by
    intro x _ hx
    apply logProfile_eq_zero_of_lt hsupp
    exact hx.trans_lt (by dsimp only [δ]; linarith [Real.exp_pos (-A)])
  have ht := tendsto_terminal_weighted_tail_mean (fun x => abs_logProfile_le hBF x) hFL
    hδ hzero (tendsto_lagHarmonic_floor_finite_part hm) ha
  by_cases hm1 : m = 1
  · subst m
    simp only [if_true] at ht ⊢
    let g : ℝ → ℝ := fun y => y * h y
    have hg : ContDiff ℝ 2 g := contDiff_id.mul hh
    have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0 := by
      intro y hy
      dsimp only [g]
      rw [hsupp y hy, mul_zero]
    obtain ⟨BG, _, hBG, _⟩ := exists_bound_lipschitz hg hgs
    obtain ⟨LG, hLG⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
      (hasCompactSupport_of_window hgs) hg (by norm_num)
    have hG := tendsto_weighted_riemannSum (w := fun _ : ℕ => (1 : ℝ))
      (M := 1) (W := 1) (by norm_num) (by intros; rfl) (by intros; norm_num)
      (fun x _ y _ => abs_logProfile_sub_le hg hgs hA hBG hLG x y)
      (fun x _ => abs_logProfile_le hBG x) 0
    simp only [Nat.sub_zero, one_mul, sum_range_one, Nat.cast_one, div_one] at hG
    apply (ht.add hG).congr'
    filter_upwards [eventually_ge_atTop 1, ha.eventually_gt_atTop 0] with N hN haN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← add_div, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hx : 0 < (n : ℝ) / N := div_pos hn0 hN0
    simp only [logProfile, if_pos hx, g]
    rw [Real.log_mul haN.ne' hx.ne']
    ring
  · simpa only [if_neg hm1, sub_zero] using ht

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_lagHarmonic_floor_finite_part
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_lagHarmonic_centered_mean
