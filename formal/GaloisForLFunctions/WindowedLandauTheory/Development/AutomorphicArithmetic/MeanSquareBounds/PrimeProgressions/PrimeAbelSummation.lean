import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.LogarithmicIntegral

/-! Partial summation transports the exceptional Chebyshev main term to its logarithmic integral. -/

open Complex Finset Classical ArithmeticFunction

noncomputable section

namespace QH.PrimeProgressions

theorem abel_log (c : ℕ → ℝ) (h0 : c 0 = 0) (h1 : c 1 = 0) {X : ℝ} (hX : 2 ≤ X) :
    ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n = (∑ n ∈ Icc 0 ⌊X⌋₊, c n) / Real.log X +
      ∫ t in (2 : ℝ)..X, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2) := by
  rw [sum_mul_eq_sub_integral_mul₁ c (f := fun n ↦ (Real.log n)⁻¹) h0 h1,
    ← intervalIntegral.integral_of_le hX]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in (2 : ℝ)..X, deriv (fun x ↦ (Real.log x)⁻¹) u * f u =
        ∫ u in (2 : ℝ)..X, -(f u / (u * Real.log u ^ 2)) :=
      intervalIntegral.integral_congr fun u _ ↦ by simp [field]
    rw [int_deriv, intervalIntegral.integral_neg]
    ring
  · intro z ⟨_, _⟩
    have : z ≠ 0 := by linarith
    have : Real.log z ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop

theorem intervalIntegrable_sum_div (c : ℕ → ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by
  have hmeas : Measurable (fun t : ℝ => ∑ n ∈ Icc 0 ⌊t⌋₊, c n) :=
    (measurable_from_nat (f := fun m => ∑ n ∈ Icc 0 m, c n)).comp Nat.measurable_floor
  set B : ℝ := ∑ n ∈ Icc 0 ⌊b⌋₊, |c n| with hB
  have hbound : IntervalIntegrable (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n)) MeasureTheory.volume a b := by
    refine IntervalIntegrable.mono_fun' (f := fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n)) (g := fun _ => B)
      intervalIntegrable_const hmeas.aestronglyMeasurable ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have htb : t ≤ b := by
      have := ht.2
      simpa [max_eq_right hab] using this
    show ‖∑ n ∈ Icc 0 ⌊t⌋₊, c n‖ ≤ B
    rw [Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono htb)) (fun _ _ _ => abs_nonneg _)
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Set.uIcc a b) := by
    have hpos : ∀ t ∈ Set.uIcc a b, 2 ≤ t := fun t ht => le_trans (le_trans ha (le_min le_rfl hab)) ht.1
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul continuousOn_id
      apply ContinuousOn.pow
      exact Real.continuousOn_log.mono (fun t ht => by simp; linarith [hpos t ht])
    · intro t ht
      have h2 := hpos t ht
      exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
  have he : (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) =
      fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) * (1 / (t * Real.log t ^ 2)) := by
    funext t
    ring
  rw [he]
  exact hbound.mul_continuousOn hc

theorem integral_rpow_div_log {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    ∫ t in (2 : ℝ)..X, t ^ (β - 1) / Real.log t = liX (X ^ β) - liX ((2 : ℝ) ^ β) := by
  have h1X : 1 < X ^ β := Real.one_lt_rpow (by linarith) hβ
  have h12 : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  have hsub : liX (X ^ β) - liX ((2 : ℝ) ^ β) = ∫ u in ((2 : ℝ) ^ β)..(X ^ β), 1 / Real.log u := by
    unfold liX
    exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log' (by norm_num) h1X)
      (intervalIntegrable_inv_log' (by norm_num) h12)
  rw [hsub]
  have key := intervalIntegral.integral_comp_mul_deriv' (a := 2) (b := X) (f := fun t : ℝ => t ^ β)
    (f' := fun t : ℝ => β * t ^ (β - 1)) (g := fun u : ℝ => 1 / Real.log u) ?_ ?_ ?_
  · rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only [Function.comp]
    rw [Real.log_rpow ht0]
    field_simp
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const t (β - 1) (Or.inl ht0))).continuousWithinAt
  · rintro u ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hX] at ht
    have h1 : 1 < t ^ β := Real.one_lt_rpow (by linarith [ht.1]) hβ
    exact ((continuousAt_const).div (Real.continuousAt_log (by linarith)) (Real.log_pos h1).ne').continuousWithinAt

def Fm (K θ β t : ℝ) : ℝ := K * (t - θ * t ^ β / β)

theorem continuousOn_Fm_div_mul_log_sq (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn (fun t => Fm K θ β t / (t * Real.log t ^ 2)) (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 2 ≤ t := fun t ht => le_trans ha ht.1
  apply ContinuousOn.div
  · unfold Fm
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub continuousOn_id
    apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (by simp; linarith [hpos t ht]))
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.pow
    exact Real.continuousOn_log.mono (fun t ht => by simp; linarith [hpos t ht])
  · intro t ht
    have h2 := hpos t ht
    exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')

theorem intervalIntegrable_Fm_div_mul_log_sq (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Fm K θ β t / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by
  exact (continuousOn_Fm_div_mul_log_sq K θ β ha).intervalIntegrable_of_Icc hab

theorem Fm_parts (K θ : ℝ) {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    Fm K θ β X / Real.log X + ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) =
      Fm K θ β 2 / Real.log 2 + K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) := by
  have hder : ∀ t ∈ Set.uIcc 2 X, HasDerivAt (fun t => Fm K θ β t / Real.log t)
      (K * (1 / Real.log t) - K * θ * (t ^ (β - 1) / Real.log t) - Fm K θ β t / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : Real.log t ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    have hp : HasDerivAt (fun t : ℝ => t ^ β) (β * t ^ (β - 1)) t := Real.hasDerivAt_rpow_const (Or.inl h0)
    have hF : HasDerivAt (fun t => Fm K θ β t) (K * (1 - θ * (β * t ^ (β - 1)) / β)) t := by
      unfold Fm
      exact (((hasDerivAt_id t).sub ((hp.const_mul θ).div_const β)).const_mul K)
    have := hF.div (Real.hasDerivAt_log h0) h1
    have hβ0 : β ≠ 0 := hβ.ne'
    refine HasDerivAt.congr_deriv (f := fun t => Fm K θ β t / Real.log t) this ?_
    generalize Fm K θ β t = F
    field_simp
  have hi1 : IntervalIntegrable (fun t => K * (1 / Real.log t)) MeasureTheory.volume 2 X :=
    (intervalIntegrable_inv_log le_rfl hX).const_mul K
  have hi2' : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t) MeasureTheory.volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : Real.log t ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    exact ((Real.continuousAt_rpow_const t (β - 1) (Or.inl h0)).div (Real.continuousAt_log h0) h1).continuousWithinAt
  have hi2 := hi2'.const_mul (K * θ)
  have hi3 := intervalIntegrable_Fm_div_mul_log_sq K θ β le_rfl hX
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder ((hi1.sub hi2).sub hi3)
  rw [intervalIntegral.integral_sub (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow_div_log hβ hX] at hftc
  have hli : ∫ t in (2 : ℝ)..X, 1 / Real.log t = liX X := rfl
  rw [hli] at hftc
  linarith

theorem Fm_abs_le {K θ β t : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (ht : 1 ≤ t) : |Fm K θ β t| ≤ 3 * t := by
  have hb : 0 < β := by linarith
  have htb : t ^ β ≤ t := by
    have := Real.rpow_le_rpow_of_exponent_le ht hβ1
    rwa [Real.rpow_one] at this
  have htpos : 0 ≤ t ^ β := Real.rpow_nonneg (by linarith) _
  unfold Fm
  rw [abs_mul, abs_of_nonneg hK0]
  have h3 : |θ * t ^ β / β| ≤ 2 * t := by
    rw [abs_div, abs_mul, abs_of_nonneg htpos, abs_of_pos hb, div_le_iff₀ hb]
    nlinarith [mul_le_mul_of_nonneg_right hθ htpos, abs_nonneg θ]
  have h2 : |t - θ * t ^ β / β| ≤ 3 * t := by
    calc |t - θ * t ^ β / β| ≤ |t| + |θ * t ^ β / β| := abs_sub _ _
      _ ≤ t + 2 * t := by rw [abs_of_nonneg (by linarith)]; linarith
      _ = 3 * t := by ring
  calc K * |t - θ * t ^ β / β| ≤ 1 * (3 * t) := mul_le_mul hK1 h2 (abs_nonneg _) (by norm_num)
    _ = 3 * t := one_mul _

theorem liX_two_rpow_abs {β : ℝ} (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) : |liX ((2 : ℝ) ^ β)| ≤ 4 := by
  unfold liX
  have h1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ β := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ
  have h2 : (2 : ℝ) ^ β ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
  have h3 : (1 : ℝ) < 2 ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 2) (b := (2 : ℝ) ^ β)
    (f := fun t => 1 / Real.log t) (C := 4) ?_
  · rw [Real.norm_eq_abs] at this
    calc _ ≤ 4 * |(2 : ℝ) ^ β - 2| := this
      _ ≤ 4 * 1 := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ = 4 := by norm_num
  · intro t ht
    rw [Set.uIoc_of_ge h2] at ht
    have hl : Real.log 2 / 2 ≤ Real.log t := by
      have : Real.log ((2 : ℝ) ^ (1 / 2 : ℝ)) ≤ Real.log t := Real.log_le_log (by positivity) (by linarith [ht.1])
      rw [Real.log_rpow (by norm_num)] at this; linarith
    have hl2 := Real.log_two_gt_d9
    have hl3 : 0 < Real.log t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hl3]
    linarith

private theorem prefix_mangoldt_bound (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hΛ : ∀ n, c n ≤ ArithmeticFunction.vonMangoldt n) {t : ℝ} (ht : 0 ≤ t) :
    |∑ n ∈ Icc 0 ⌊t⌋₊, c n| ≤ 6 * t := by
  rw [abs_of_nonneg (sum_nonneg fun n _ => hc n)]
  have hlog4 : Real.log 4 + 4 ≤ 6 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith only [Real.log_two_lt_d9]
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n := sum_le_sum fun n _ => hΛ n
    _ = Chebyshev.psi t := (Chebyshev.psi_eq_sum_Icc t).symm
    _ ≤ (Real.log 4 + 4) * t := Chebyshev.psi_le_const_mul_self ht
    _ ≤ 6 * t := mul_le_mul_of_nonneg_right hlog4 ht

private theorem integral_log_square_bound (d : ℝ → ℝ) {a b L C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 < L) (hla : L ≤ Real.log a) (hC : 0 ≤ C)
    (hd : ∀ t, a ≤ t → t ≤ b → |d t| ≤ C * t) :
    |∫ t in a..b, d t / (t * Real.log t ^ 2)| ≤ C / L ^ 2 * (b - a) := by
  rw [← Real.norm_eq_abs, ← abs_of_nonneg (sub_nonneg.mpr hab)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  rw [Set.uIoc_of_le hab] at ht
  have ht₀ := ha.trans ht.1
  have hLt := hla.trans (Real.log_le_log ha ht.1.le)
  have hlt := hL.trans_le hLt
  have hsq := pow_le_pow_left₀ hL.le hLt 2
  have hden := mul_pos ht₀ (pow_pos hlt 2)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
  calc
    _ ≤ C * t / (t * Real.log t ^ 2) :=
      div_le_div_of_nonneg_right (hd t ht.1.le ht.2) hden.le
    _ = C / Real.log t ^ 2 := by field_simp [ht₀.ne', hlt.ne']
    _ ≤ _ := div_le_div_of_nonneg_left hC (pow_pos hL 2) hsq

theorem abel_core (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcΛ : ∀ n, c n ≤ ArithmeticFunction.vonMangoldt n)
    {K θ β D X : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hD : 0 ≤ D)
    (h : ∀ t, √X ≤ t → t ≤ X → |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - Fm K θ β t| ≤ D * t) :
    |∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β))| ≤
      5 * D * X / Real.log X + 40 * √X := by
  have h0 : c 0 = 0 := le_antisymm (by simpa using hcΛ 0) (hc0 0)
  have h1 : c 1 = 0 := le_antisymm (by simpa using hcΛ 1) (hc0 1)
  have hX2 : 2 ≤ X := by linarith only [hX]
  have hX₀ : 0 < X := by linarith only [hX]
  have hs4 : 4 ≤ √X := by
    rw [Real.le_sqrt' (by norm_num)]
    linarith only [hX]
  have hs2 : 2 ≤ √X := by linarith only [hs4]
  have hsX : √X ≤ X := by
    have hs := le_self_pow₀ (by linarith only [hs4] : 1 ≤ √X) (by norm_num : (2 : ℕ) ≠ 0)
    simpa only [Real.sq_sqrt hX₀.le] using hs
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hL : 1 ≤ Real.log X := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hX
    linarith only [h16, hle, hl2]
  have hL₀ : 0 < Real.log X := zero_lt_one.trans_le hL
  let Ψ (t : ℝ) : ℝ := ∑ n ∈ Icc 0 ⌊t⌋₊, c n
  let g (t : ℝ) : ℝ := Ψ t / (t * Real.log t ^ 2) - Fm K θ β t / (t * Real.log t ^ 2)
  have hgi (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable g MeasureTheory.volume a b :=
    (intervalIntegrable_sum_div c ha hab).sub (intervalIntegrable_Fm_div_mul_log_sq K θ β ha hab)
  have hI : (∫ t in (2 : ℝ)..X, g t) = (∫ t in (2 : ℝ)..X, Ψ t / (t * Real.log t ^ 2)) -
      ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_sub (intervalIntegrable_sum_div c le_rfl hX2)
      (intervalIntegrable_Fm_div_mul_log_sq K θ β le_rfl hX2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgi 2 (√X) le_rfl hs2) (hgi (√X) X hs2 hsX)
  have hI1 : |∫ t in (2 : ℝ)..√X, g t| ≤ 36 * (√X - 2) := by
    have hlow (t : ℝ) (ht : 2 ≤ t) (_ : t ≤ √X) : |Ψ t - Fm K θ β t| ≤ 9 * t := by
      have ha := prefix_mangoldt_bound c hc0 hcΛ (by linarith only [ht] : 0 ≤ t)
      have hb := Fm_abs_le hK0 hK1 hθ hβ hβ1 (by linarith only [ht] : 1 ≤ t)
      exact (abs_sub _ _).trans (by linarith only [ha, hb])
    have hb := integral_log_square_bound (L := 1 / 2) (C := 9) (fun t => Ψ t - Fm K θ β t)
      (by norm_num) hs2 (by norm_num) hl2 (by norm_num) hlow
    simpa only [g, sub_div, show (9 : ℝ) / (1 / 2) ^ 2 = 36 by norm_num] using hb
  have hI2 : |∫ t in (√X)..X, g t| ≤ 4 * (D * X / Real.log X) := by
    have hlog : Real.log X / 2 ≤ Real.log (√X) := by rw [Real.log_sqrt hX₀.le]
    have hb := integral_log_square_bound (fun t => Ψ t - Fm K θ β t)
      (by linarith only [hs4]) hsX (half_pos hL₀) hlog hD h
    have hb' : |∫ t in (√X)..X, g t| ≤ D / (Real.log X / 2) ^ 2 * (X - √X) := by
      simpa only [g, sub_div] using hb
    calc
      _ ≤ D / (Real.log X / 2) ^ 2 * X :=
        hb'.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.sqrt_nonneg _)) (by positivity))
      _ = 4 * (D * X / Real.log X ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (mul_nonneg hD hX₀.le) hL₀ (le_self_pow₀ hL (by norm_num)))
        (by norm_num)
  have heq : ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β)) =
      (Ψ X - Fm K θ β X) / Real.log X + ((∫ t in (2 : ℝ)..√X, g t) + ∫ t in (√X)..X, g t) +
        Fm K θ β 2 / Real.log 2 + K * θ * liX ((2 : ℝ) ^ β) := by
    have habel := abel_log c h0 h1 hX2
    change _ = Ψ X / Real.log X + ∫ t in (2 : ℝ)..X, Ψ t / (t * Real.log t ^ 2) at habel
    have hparts := Fm_parts K θ (by linarith only [hβ] : 0 < β) hX2
    have e1 : K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) =
        K * (liX X - θ * liX (X ^ β)) + K * θ * liX ((2 : ℝ) ^ β) := by ring
    rw [e1] at hparts
    rw [sub_div]
    linarith only [habel, hparts, hI, hsplit]
  have b1 : |(Ψ X - Fm K θ β X) / Real.log X| ≤ D * X / Real.log X := by
    rw [abs_div, abs_of_pos hL₀]
    exact div_le_div_of_nonneg_right (h X hsX le_rfl) hL₀.le
  have b2 : |Fm K θ β 2 / Real.log 2| ≤ 12 := by
    have hFm := Fm_abs_le hK0 hK1 hθ hβ hβ1 (by norm_num : (1 : ℝ) ≤ 2)
    have hlog2 : 0 < Real.log 2 := by linarith only [hl2]
    rw [abs_div, abs_of_pos hlog2, div_le_iff₀ hlog2]
    linarith only [hFm, hl2]
  have b3 : |K * θ * liX ((2 : ℝ) ^ β)| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hK0]
    calc
      _ ≤ 1 * 4 := mul_le_mul (mul_le_one₀ hK1 (abs_nonneg θ) hθ)
        (liX_two_rpow_abs hβ hβ1) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [heq, abs_le, show 5 * D * X / Real.log X = 5 * (D * X / Real.log X) by ring]
  obtain ⟨hb1, hb1'⟩ := abs_le.mp b1
  obtain ⟨hb2, hb2'⟩ := abs_le.mp b2
  obtain ⟨hb3, hb3'⟩ := abs_le.mp b3
  obtain ⟨hi1, hi1'⟩ := abs_le.mp hI1
  obtain ⟨hi2, hi2'⟩ := abs_le.mp hI2
  constructor
  · linarith only [hb1, hb2, hb3, hi1, hi2, hs4]
  · linarith only [hb1', hb2', hb3', hi1', hi2', hs4]

end QH.PrimeProgressions
