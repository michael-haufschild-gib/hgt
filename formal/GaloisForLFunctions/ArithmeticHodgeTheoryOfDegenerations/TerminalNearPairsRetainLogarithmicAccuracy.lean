import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsReadEitherEndOfANearPair
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsPreserveHarmonicGapRows

/-!
# Terminal near-pair means retain logarithmic accuracy

The periodic row error, the variation of the exponential row integral,
and the terminal Riemann error retain explicit rates. Their sum still
vanishes after multiplication by log c when c log c / N tends to zero.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

/-- Periodic averaging and the terminal Riemann approximation have one uniform `1/N` error. -/
theorem abs_terminal_periodic_riemann_error_le
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    {B : ℝ} (hB : ∀ n, |p n| ≤ B) {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N, F (n / N) * p n) / N -
      periodicMean p q * ∫ x in (0 : ℝ)..1, F x| ≤
        (2 * q * B * (BF + LF) + |periodicMean p q| * LF) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := abs_sum_range_terminal_weight_sub_mean_le hF hLF hFL hq hp hB
    (a := 1) (M := N - 1) hN (by omega)
  rw [Nat.sub_add_cancel hN] at hb
  simp_rw [Nat.add_comm 1] at hb
  rw [sum_range_succ_eq_sum_Icc (fun n => F ((n : ℝ) / N) * p n),
    sum_range_succ_eq_sum_Icc (fun n => F ((n : ℝ) / N))] at hb
  have he : (∑ n ∈ Finset.Icc 1 N, F (n / N) * p n) / N -
      periodicMean p q * ∫ x in (0 : ℝ)..1, F x =
      ((∑ n ∈ Finset.Icc 1 N, F (n / N) * p n) -
        periodicMean p q * ∑ n ∈ Finset.Icc 1 N, F (n / N)) / N +
      periodicMean p q * ((∑ n ∈ Finset.Icc 1 N, F (n / N)) / N -
        ∫ x in (0 : ℝ)..1, F x) := by ring
  rw [he]
  calc
    _ ≤ |((∑ n ∈ Finset.Icc 1 N, F (n / N) * p n) -
          periodicMean p q * ∑ n ∈ Finset.Icc 1 N, F (n / N)) / N| +
        |periodicMean p q * ((∑ n ∈ Finset.Icc 1 N, F (n / N)) / N -
          ∫ x in (0 : ℝ)..1, F x)| := abs_add_le _ _
    _ ≤ (2 * q * B * (BF + LF)) / N + |periodicMean p q| * (LF / N) := by
      rw [abs_div, abs_of_pos hN0, abs_mul]
      exact add_le_add (div_le_div_of_nonneg_right hb hN0.le)
        (mul_le_mul_of_nonneg_left (abs_riemannSum_sub_integral_le hFL hN) (abs_nonneg _))
    _ = _ := by ring

/-- The exponential row integral differs from its limiting kernel integral by `O(w)`. -/
theorem abs_near_row_integral_sub_le
    {K : ℝ → ℝ} {α β A L w : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hw : 0 ≤ w) (hsmall : β * w ≤ 1)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|) :
    |(∫ s in α..β, K s * Real.exp (w * s / 2)) - ∫ s in α..β, K s| ≤
      (A * β * Real.exp 1 * (β - α)) * w := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  have hβ0 : 0 ≤ β := hα.trans hαβ
  have hK : ContinuousOn K (Icc α β) := continuousOn_of_abs_sub_le hL
  have hKint : IntervalIntegrable K volume α β := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hαβ] using hK
  have hE : Continuous (fun s : ℝ => Real.exp (w * s / 2)) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 2)
  have hKE : IntervalIntegrable (fun s => K s * Real.exp (w * s / 2)) volume α β := by
    have hcont : ContinuousOn (fun s : ℝ => K s * Real.exp (w * s / 2)) (Icc α β) :=
      fun s hs => (hK s hs).mul hE.continuousAt.continuousWithinAt
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hαβ] using hcont
  rw [← intervalIntegral.integral_sub hKE hKint]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := A * β * Real.exp 1 * w)
    (f := fun s => K s * Real.exp (w * s / 2) - K s) (a := α) (b := β) (fun s hs => by
      rw [Set.uIoc_of_le hαβ] at hs
      have hs0 : 0 ≤ s := hα.trans hs.1.le
      have ht0 : 0 ≤ w * s / 2 := by positivity
      have hts : w * s / 2 ≤ β * w := by
        have h := mul_le_mul_of_nonneg_left hs.2 hw
        nlinarith only [h, mul_nonneg hw hs0]
      have ht1 : w * s / 2 ≤ 1 := hts.trans hsmall
      have he : |Real.exp (w * s / 2) - 1| ≤ β * w * Real.exp 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht0))]
        exact SpacingScaleHarmonicAnalysis.exp_sub_one_le_mul_exp.trans
          (mul_le_mul hts (Real.exp_le_exp.mpr ht1) (Real.exp_pos _).le
            (mul_nonneg hβ0 hw))
      rw [Real.norm_eq_abs, show K s * Real.exp (w * s / 2) - K s =
        K s * (Real.exp (w * s / 2) - 1) by ring, abs_mul]
      exact (mul_le_mul (hA s ⟨hs.1.le, hs.2⟩) he (abs_nonneg _) hA0).trans_eq (by ring))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hαβ)] at hb
  exact hb.trans_eq (by ring)

/-- The exact periodic near-row estimate after overlap normalization. -/
theorem abs_nearPairSum_div_overlap_sub_weighted_row_le
    {K : ℝ → ℝ} {α β A L c : ℝ} {N : ℕ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β) (hc : 0 < c) (hN : 1 ≤ N)
    (hsmall : β * (c / N) ≤ 1) (hlarge : 1 ≤ 2 * β * c)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    {ρ : ℕ → ℝ} {R : ℝ} (hρ : ∀ n, |ρ n| ≤ R) :
    |nearPairSum K α β (c / N) N u v ρ / c -
      (∫ s in α..β, K s * Real.exp ((c / N) * s / 2)) *
        ((∑ n ∈ Finset.Icc 1 N,
          ρ n * (u n * periodicMean v q + v n * periodicMean u q)) / N)| ≤
      2 * R * B * (2 * B * A / c +
        ((2 * q + 1) * B * (4 * A + 2 * β * L)) *
          (1 / c + Real.log (2 * β * c) / c) +
        (4 * B * A * β) * (β * (c / N) + 1 / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hlarge' : 1 ≤ 2 * β * (c / N) * N := by
    rwa [show 2 * β * (c / N) * N = 2 * β * c by field_simp]
  have hb := abs_nearPairSum_sub_le hα hαβ hβ hw hsmall hA hL hL0 hq hu hv huB hvB
    hρ hN hlarge'
  have ei : (∫ s in α..β, K s * ((c / N) * Real.exp ((c / N) * s / 2))) =
      (c / N) * ∫ s in α..β, K s * Real.exp ((c / N) * s / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by ring
  have eMain : (∫ s in α..β, K s * ((c / N) * Real.exp ((c / N) * s / 2))) *
      (∑ n ∈ Finset.Icc 1 N, ρ n * (u n * periodicMean v q + v n * periodicMean u q)) / c =
      (∫ s in α..β, K s * Real.exp ((c / N) * s / 2)) *
        ((∑ n ∈ Finset.Icc 1 N, ρ n * (u n * periodicMean v q + v n * periodicMean u q)) / N) := by
    rw [ei]
    generalize (∫ s in α..β, K s * Real.exp ((c / N) * s / 2)) = z
    generalize (∑ n ∈ Finset.Icc 1 N, ρ n * (u n * periodicMean v q + v n * periodicMean u q)) = b
    field_simp [hc.ne']
  rw [← eMain, ← sub_div, abs_div, abs_of_pos hc]
  refine (div_le_div_of_nonneg_right hb hc.le).trans_eq ?_
  rw [show 2 * β * (c / N) * N = 2 * β * c by field_simp]
  field_simp [hN0.ne', hc.ne']

private theorem width_limits_of_log_error {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => Real.log (c N) / N) atTop (𝓝 0) := by
  constructor
  · have h := he.div_atTop (Real.tendsto_log_atTop.comp hcinf)
    apply h.congr'
    filter_upwards [(Real.tendsto_log_atTop.comp hcinf).eventually_gt_atTop 0] with N hN
    dsimp only [Function.comp_def] at hN ⊢
    field_simp [hN.ne']
  · have h := he.div_atTop hcinf
    exact h.congr fun N => by
      have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
      field_simp [hc0.ne']

private theorem tendsto_log_mul_terminal_riemann_error
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    {B : ℝ} (hB : ∀ n, |p n| ≤ B) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      ((∑ n ∈ Finset.Icc 1 N, F (n / N) * p n) / N -
        periodicMean p q * ∫ x in (0 : ℝ)..1, F x)) atTop (𝓝 0) := by
  have hlim := he.const_mul (2 * q * B * (BF + LF) + |periodicMean p q| * LF)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hlog : 0 ≤ Real.log (c N) := Real.log_nonneg (hc N)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog]
  exact (mul_le_mul_of_nonneg_left
    (abs_terminal_periodic_riemann_error_le hF hLF hFL hq hp hB hN) hlog).trans_eq (by ring)

private theorem tendsto_log_mul_near_row_integral_error
    {K : ℝ → ℝ} {α β A L : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      ((∫ s in α..β, K s * Real.exp ((c N / N) * s / 2)) - ∫ s in α..β, K s))
      atTop (𝓝 0) := by
  have hw := (width_limits_of_log_error hc hcinf he).1
  have hwβ := hw.const_mul β
  simp only [mul_zero] at hwβ
  have hlim := he.const_mul (A * β * Real.exp 1 * (β - α))
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hwβ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN
  have hlog : 0 ≤ Real.log (c N) := Real.log_nonneg (hc N)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog]
  have hc0 : 0 ≤ c N := zero_le_one.trans (hc N)
  exact (mul_le_mul_of_nonneg_left
    (abs_near_row_integral_sub_le hα hαβ (div_nonneg hc0 (Nat.cast_nonneg N)) hN.le hA hL)
    hlog).trans_eq (by ring)

private theorem tendsto_log_mul_nearPairSum_sub_weighted_row
    {K : ℝ → ℝ} {α β A L : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    {ρ : ℕ → ℕ → ℝ} {R : ℝ} (hρ : ∀ N n, |ρ N n| ≤ R)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      (nearPairSum K α β (c N / N) N u v (ρ N) / c N -
        (∫ s in α..β, K s * Real.exp ((c N / N) * s / 2)) *
          ((∑ n ∈ Finset.Icc 1 N,
            ρ N n * (u n * periodicMean v q + v n * periodicMean u q)) / N)))
      atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have hw := (width_limits_of_log_error hc hcinf he).1
  have hlogN := (width_limits_of_log_error hc hcinf he).2
  have hlog : Tendsto (fun N : ℕ => Real.log (c N) / c N) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcinf
  have hlog2 : Tendsto (fun N : ℕ => Real.log (c N) ^ 2 / c N) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hcinf
  have hcross : Tendsto (fun N : ℕ => Real.log (c N) * Real.log (2 * β * c N) / c N)
      atTop (𝓝 0) := by
    have h := (hlog.mul_const (Real.log (2 * β))).add hlog2
    simp only [zero_mul, zero_add] at h
    apply h.congr
    intro N
    rw [Real.log_mul (by positivity : (2 * β : ℝ) ≠ 0) (hc0 N).ne']
    ring
  let C : ℝ := (2 * q + 1) * B * (4 * A + 2 * β * L)
  let err : ℕ → ℝ := fun N => 2 * R * B *
    ((2 * B * A) * (Real.log (c N) / c N) +
      C * (Real.log (c N) / c N + Real.log (c N) * Real.log (2 * β * c N) / c N) +
      (4 * B * A * β) * (β * (c N * Real.log (c N) / N) + Real.log (c N) / N))
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := ((hlog.const_mul (2 * B * A)).add ((hlog.add hcross).const_mul C)).add
      (((he.const_mul β).add hlogN).const_mul (4 * B * A * β))
    simpa only [mul_zero, zero_mul, add_zero] using h.const_mul (2 * R * B)
  have hwβ := hw.const_mul β
  simp only [mul_zero] at hwβ
  apply squeeze_zero_norm' _ herr
  filter_upwards [eventually_ge_atTop 1,
    hwβ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hcinf.eventually_ge_atTop (1 / (2 * β))] with N hN hsmall hlarge
  have hlarge' : 1 ≤ 2 * β * c N := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * β)).mp hlarge
    nlinarith only [h]
  have hlog0 : 0 ≤ Real.log (c N) := Real.log_nonneg (hc N)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0]
  exact (mul_le_mul_of_nonneg_left
    (abs_nearPairSum_div_overlap_sub_weighted_row_le hα hαβ hβ (hc0 N) hN
      hsmall.le hlarge' hA hL hL0 hq hu hv huB hvB (hρ N)) hlog0).trans_eq
        (by dsimp only [err, C]; ring)

/-- The terminal periodic near mean keeps its limit after logarithmic magnification of the error. -/
theorem tendsto_log_mul_nearPairSum_terminal_relative_error
    {K F : ℝ → ℝ} {α β A L LF BF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      (nearPairSum K α β (c N / N) N u v (fun n => F (n / N)) / c N -
        2 * periodicMean u q * periodicMean v q *
          (∫ s in α..β, K s) * ∫ x in (0 : ℝ)..1, F x)) atTop (𝓝 0) := by
  let μu := periodicMean u q
  let μv := periodicMean v q
  let I := ∫ s in α..β, K s
  let J := ∫ x in (0 : ℝ)..1, F x
  let M : ℕ → ℝ := fun N =>
    (∑ n ∈ Finset.Icc 1 N, F (n / N) * (u n * μv + v n * μu)) / N
  have hM_eq (N : ℕ) : M N =
      ((∑ n ∈ Finset.Icc 1 N, F (n / N) * u n) / N) * μv +
        ((∑ n ∈ Finset.Icc 1 N, F (n / N) * v n) / N) * μu := by
    dsimp only [M]
    have hs : (∑ n ∈ Finset.Icc 1 N, F (n / N) * (u n * μv + v n * μu)) =
        (∑ n ∈ Finset.Icc 1 N, F (n / N) * u n) * μv +
          (∑ n ∈ Finset.Icc 1 N, F (n / N) * v n) * μu := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hs]
    ring
  have hlogN := (width_limits_of_log_error hc hcinf he).2
  have hU := tendsto_log_mul_terminal_riemann_error hF hLF hFL hq hu huB hc hlogN
  have hV := tendsto_log_mul_terminal_riemann_error hF hLF hFL hq hv hvB hc hlogN
  have hMlog : Tendsto (fun N => Real.log (c N) * (M N - 2 * μu * μv * J))
      atTop (𝓝 0) := by
    have h := (hU.mul_const μv).add (hV.mul_const μu)
    simp only [zero_mul, zero_add] at h
    apply h.congr
    intro N
    rw [hM_eq]
    dsimp only [μu, μv, J]
    ring
  have hMlim : Tendsto M atTop (𝓝 (2 * μu * μv * J)) := by
    have hz := hMlog.div_atTop (Real.tendsto_log_atTop.comp hcinf)
    have hz' : Tendsto (fun N => M N - 2 * μu * μv * J) atTop (𝓝 0) := by
      apply hz.congr'
      filter_upwards [(Real.tendsto_log_atTop.comp hcinf).eventually_gt_atTop 0] with N hN
      dsimp only [Function.comp_def] at hN ⊢
      field_simp [hN.ne']
    have h := hz'.add_const (2 * μu * μv * J)
    simpa only [zero_add, sub_add_cancel] using h
  have hIlog := tendsto_log_mul_near_row_integral_error hα hαβ hA hL hc hcinf he
  have hrow := tendsto_log_mul_nearPairSum_sub_weighted_row hα hαβ hβ hA hL hL0
    hq hu hv huB hvB (ρ := fun N n => F (n / N)) (fun _ _ => hF _) hc hcinf he
  have h := (hrow.add (hIlog.mul hMlim)).add (hMlog.const_mul I)
  simp only [zero_mul, mul_zero, add_zero] at h
  apply h.congr
  intro N
  dsimp only [μu, μv, I, J, M]
  ring

/-- Moving the terminal weight to one endpoint preserves logarithmic accuracy. -/
theorem tendsto_log_mul_endpointNearPairSum_relative_error
    {K F : ℝ → ℝ} {α β A L LF BF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      (endpointNearPairSum K F α β (c N / N) N u v / c N -
        2 * periodicMean u q * periodicMean v q *
          (∫ s in α..β, K s) * ∫ x in (0 : ℝ)..1, F x)) atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have hw := (width_limits_of_log_error hc hcinf he).1
  have hmass := tendsto_nearPairSum_div_overlap (K := fun _ => (1 : ℝ))
    (A := 1) (L := 0) hα hαβ hβ (by intros; norm_num) (by intros; simp) le_rfl
    (q := 1) (u := fun _ => 1) (v := fun _ => 1) (B := 1) one_pos
    (by intros; rfl) (by intros; rfl) (by intros; norm_num) (by intros; norm_num)
    hc0 hcinf hw
  have hcoeff := he.const_mul (LF * β * B ^ 2 * A)
  have hlim := hcoeff.mul hmass
  simp only [mul_zero, zero_mul] at hlim
  have hdiff : Tendsto (fun N : ℕ => Real.log (c N) *
      ((endpointNearPairSum K F α β (c N / N) N u v -
        nearPairSum K α β (c N / N) N u v (fun n => F (n / N))) / c N))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog : 0 ≤ Real.log (c N) := Real.log_nonneg (hc N)
    have hb := abs_endpointNearPairSum_sub_nearPairSum_le hαβ hβ
      (div_pos (hc0 N) hN0) hA hLF hFL huB hvB N
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog, abs_div, abs_of_pos (hc0 N)]
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (hc0 N).le) hlog).trans_eq
      (by ring)
  have hm := tendsto_log_mul_nearPairSum_terminal_relative_error hα hαβ hβ hA hL hL0
    hF hLF hFL hq hu hv huB hvB hc hcinf he
  have h := hdiff.add hm
  simp only [zero_add] at h
  exact h.congr fun N => by ring

/-- The logarithmically accurate terminal Ramanujan mean is supported at the polar pair. -/
theorem tendsto_log_mul_endpointNearPairSum_ramanujan_relative_error
    {K F : ℝ → ℝ} {α β A L LF BF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      (endpointNearPairSum K F α β (c N / N) N
        (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) / c N -
        (if m = 1 ∧ l = 1 then 2 * (∫ s in α..β, K s) * ∫ x in (0 : ℝ)..1, F x else 0)))
      atTop (𝓝 0) := by
  let B : ℝ := (∑ d ∈ m.divisors, (d : ℝ)) + ∑ d ∈ l.divisors, (d : ℝ)
  have hu : ∀ n, ramanujanLagCoefficient m (n + m * l) = ramanujanLagCoefficient m n :=
    fun n => ramanujanLagCoefficient_add_mul m n l
  have hv : ∀ n, ramanujanLagCoefficient l (n + m * l) = ramanujanLagCoefficient l n := by
    intro n
    rw [mul_comm m l]
    exact ramanujanLagCoefficient_add_mul l n m
  have huB : ∀ n, |ramanujanLagCoefficient m n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le m n).trans (le_add_of_nonneg_right (by positivity))
  have hvB : ∀ n, |ramanujanLagCoefficient l n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le l n).trans (le_add_of_nonneg_left (by positivity))
  have h := tendsto_log_mul_endpointNearPairSum_relative_error hα hαβ hβ hA hL hL0
    hF hLF hFL (Nat.mul_pos hm hl) hu hv huB hvB hc hcinf he
  rw [periodicMean_ramanujan_of_dvd hm (Nat.mul_pos hm hl) (dvd_mul_right m l),
    periodicMean_ramanujan_of_dvd hl (Nat.mul_pos hm hl) (dvd_mul_left l m)] at h
  have hconst : 2 * (if m = 1 then (1 : ℝ) else 0) * (if l = 1 then (1 : ℝ) else 0) *
      (∫ s in α..β, K s) * (∫ x in (0 : ℝ)..1, F x) =
      if m = 1 ∧ l = 1 then 2 * (∫ s in α..β, K s) * ∫ x in (0 : ℝ)..1, F x else 0 := by
    split_ifs <;> simp_all
  rwa [hconst] at h

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_log_mul_endpointNearPairSum_relative_error
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_log_mul_endpointNearPairSum_ramanujan_relative_error
