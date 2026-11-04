import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCenterPartOfTheBulkEntries
import GaloisForLFunctions.HTGeometry.BoundaryTraceRamification

/-!
# The harmonic finite part of the near center

The logarithmic window induces the exact linear gap cutoff
`H = N(1 - exp(-2c/N))`. Periodic Ramanujan correlation retains the
triangular harmonic sum with an error of order `harmonic N / N`.
Its finite part is `log 2 + γ - 1` at conductor one and `-Λ(m)` otherwise.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
open ArithmeticFunction (vonMangoldt)

/-- The mean of a Ramanujan gap row on an arbitrary integer interval. -/
theorem abs_gapRow_interval_sub_le {m l a b : ℕ} (hm : 0 < m) (hl : 0 < l)
    (ha : 1 ≤ a) (hab : a ≤ b + 1) (h : ℕ) :
    |(∑ n ∈ Icc a b, (ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
        ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n)) -
      ((b : ℝ) - a + 1) * (2 * (if m = l then ramanujanLagCoefficient m h else 0))| ≤
      4 * (l * m : ℕ) * (2 * (∑ d ∈ l.divisors, (d : ℝ)) * ∑ d ∈ m.divisors, (d : ℝ)) := by
  let f : ℕ → ℝ := fun n => ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
    ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n
  let A : ℝ := 2 * (if m = l then ramanujanLagCoefficient m h else 0)
  have hsplit : Icc 1 b = Icc 1 (a - 1) ∪ Icc a b := by
    ext n
    simp only [mem_Icc, mem_union]
    omega
  have hdisj : Disjoint (Icc 1 (a - 1)) (Icc a b) := by
    rw [disjoint_left]
    intro n hn hn'
    simp only [mem_Icc] at hn hn'
    omega
  have heq : (∑ n ∈ Icc a b, f n) - ((b : ℝ) - a + 1) * A =
      ((∑ n ∈ Icc 1 b, f n) - b * A) -
        ((∑ n ∈ Icc 1 (a - 1), f n) - (a - 1 : ℕ) * A) := by
    rw [hsplit, sum_union hdisj, Nat.cast_sub ha, Nat.cast_one]
    ring
  change |(∑ n ∈ Icc a b, f n) - ((b : ℝ) - a + 1) * A| ≤ _
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add (abs_gapRow_sub_le hm hl h b)
    (abs_gapRow_sub_le hm hl h (a - 1))).trans_eq (by ring))

/-- The linear gap cutoff corresponding to a logarithmic window of width `log (1+d)`. -/
def nearCenterGapCutoff (d : ℝ) (N : ℕ) : ℝ := N * d / (1 + d)

private theorem nearCenterGapCutoff_pos {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N) :
    0 < nearCenterGapCutoff d N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold nearCenterGapCutoff
  positivity

private theorem nearCenterGapCutoff_lt {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N) :
    nearCenterGapCutoff d N < N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold nearCenterGapCutoff
  rw [div_lt_iff₀ (by positivity)]
  nlinarith only [hN0]

private theorem ceil_gap_div_le_sub {d : ℝ} (hd : 0 < d) {N h : ℕ}
    (hh : (h : ℝ) ≤ nearCenterGapCutoff d N) : ⌈(h : ℝ) / d⌉₊ ≤ N - h := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hhN : (h : ℝ) ≤ N := by
    refine hh.trans ?_
    unfold nearCenterGapCutoff
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hN0]
  have hhN' : h ≤ N := by exact_mod_cast hhN
  rw [Nat.ceil_le, Nat.cast_sub hhN', div_le_iff₀ hd]
  have h := (le_div_iff₀ (by positivity : 0 < 1 + d)).mp hh
  nlinarith only [h]

/-- Near-center pair counts differ from their linear density by at most one. -/
theorem abs_nearCenterGap_count_sub_le {d : ℝ} (hd : 0 < d) {N h : ℕ}
    (hN : 1 ≤ N) (hh : 1 ≤ h) (hhH : (h : ℝ) ≤ nearCenterGapCutoff d N) :
    |((N - h : ℕ) : ℝ) - (⌈(h : ℝ) / d⌉₊ : ℕ) + 1 -
      N * (1 - h / nearCenterGapCutoff d N)| ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hhN : h ≤ N := by exact_mod_cast hhH.trans (nearCenterGapCutoff_lt hd hN).le
  have hlo := Nat.le_ceil ((h : ℝ) / d)
  have hhi := Nat.ceil_lt_add_one (div_nonneg hh0.le hd.le)
  have heq : ((N - h : ℕ) : ℝ) - (⌈(h : ℝ) / d⌉₊ : ℕ) + 1 -
      N * (1 - h / nearCenterGapCutoff d N) =
      h / d + 1 - (⌈(h : ℝ) / d⌉₊ : ℕ) := by
    rw [Nat.cast_sub hhN]
    unfold nearCenterGapCutoff
    field_simp [hN0.ne', hd.ne', (by positivity : (1 + d : ℝ) ≠ 0)]
    ring
  rw [heq]
  exact abs_le.mpr ⟨by linarith only [hhi], by linarith only [hlo]⟩

/-- Signed gap rows over the exact near-center cutoff. -/
def truncatedCenterDifference (m l : ℕ) (d : ℝ) (N : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊nearCenterGapCutoff d N⌋₊, (1 / (h : ℝ)) *
    ∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ (N - h),
      (ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
        ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n)

/-- The exact cutoff retains the signed harmonic Ramanujan sum, with only a harmonic error. -/
theorem abs_truncatedCenterDifference_sub_le {m l N : ℕ} (hm : 0 < m) (hl : 0 < l)
    {d : ℝ} (hd : 0 < d) (hN : 1 ≤ N) :
    |truncatedCenterDifference m l d N / (2 * N) -
      (if m = l then lagHarmonic m ⌊nearCenterGapCutoff d N⌋₊ -
        lagSum m ⌊nearCenterGapCutoff d N⌋₊ / nearCenterGapCutoff d N else 0)| ≤
      (4 * (l * m : ℕ) * (2 * (∑ t ∈ l.divisors, (t : ℝ)) * ∑ t ∈ m.divisors, (t : ℝ)) +
        2 * ∑ t ∈ m.divisors, (t : ℝ)) * harmonic N / (2 * N) := by
  let H : ℝ := nearCenterGapCutoff d N
  let Q : ℕ := ⌊H⌋₊
  let A : ℕ → ℝ := fun h => 2 * (if m = l then ramanujanLagCoefficient m h else 0)
  let K : ℝ := 4 * (l * m : ℕ) *
    (2 * (∑ t ∈ l.divisors, (t : ℝ)) * ∑ t ∈ m.divisors, (t : ℝ)) +
      2 * ∑ t ∈ m.divisors, (t : ℝ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hH : 0 < H := nearCenterGapCutoff_pos hd hN
  have hQN : Q ≤ N := by
    have hq : (Q : ℝ) ≤ H := Nat.floor_le hH.le
    exact_mod_cast hq.trans (nearCenterGapCutoff_lt hd hN).le
  let row : ℕ → ℝ := fun h => ∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ (N - h),
    (ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
      ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n)
  have hr : ∀ h ∈ Icc 1 Q, |row h - N * (1 - h / H) * A h| ≤ K := by
    intro h hh
    have hh1 := (mem_Icc.mp hh).1
    have hhH : (h : ℝ) ≤ H := (by exact_mod_cast (mem_Icc.mp hh).2 : (h : ℝ) ≤ Q).trans
      (Nat.floor_le hH.le)
    have ha1 : 1 ≤ ⌈(h : ℝ) / d⌉₊ := by
      have hh0 : (0 : ℝ) < h := by exact_mod_cast hh1
      have hhceil := Nat.le_ceil ((h : ℝ) / d)
      have hceil0 : (0 : ℝ) < (⌈(h : ℝ) / d⌉₊ : ℕ) := (div_pos hh0 hd).trans_le hhceil
      exact_mod_cast hceil0
    have hab := ceil_gap_div_le_sub hd hhH
    have hb := abs_gapRow_interval_sub_le hm hl ha1 (hab.trans (Nat.le_succ _)) h
    have hcount := abs_nearCenterGap_count_sub_le hd hN hh1 hhH
    have hA : |A h| ≤ 2 * ∑ t ∈ m.divisors, (t : ℝ) := by
      dsimp only [A]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply mul_le_mul_of_nonneg_left _ zero_le_two
      split_ifs
      · exact abs_ramanujanLagCoefficient_le m h
      · simp only [abs_zero]; positivity
    calc
      _ ≤ |row h - (((N - h : ℕ) : ℝ) - (⌈(h : ℝ) / d⌉₊ : ℕ) + 1) * A h| +
          |((((N - h : ℕ) : ℝ) - (⌈(h : ℝ) / d⌉₊ : ℕ) + 1) - N * (1 - h / H)) * A h| := by
        have he : row h - N * (1 - h / H) * A h =
            (row h - (((N - h : ℕ) : ℝ) - (⌈(h : ℝ) / d⌉₊ : ℕ) + 1) * A h) +
              (((((N - h : ℕ) : ℝ) - (⌈(h : ℝ) / d⌉₊ : ℕ) + 1) - N * (1 - h / H)) * A h) := by ring
        rw [he]
        exact abs_add_le _ _
      _ ≤ K := by
        rw [abs_mul]
        have hprod := mul_le_mul hcount hA (abs_nonneg _) zero_le_one
        dsimp only [K]
        linarith only [hb, hprod]
  have heq : (if m = l then lagHarmonic m Q - lagSum m Q / H else 0) =
      (∑ h ∈ Icc 1 Q, (1 / (h : ℝ)) * (N * (1 - h / H) * A h)) / (2 * N) := by
    by_cases hml : m = l
    · simp only [if_pos hml, lagHarmonic, lagSum, A]
      rw [sum_div, ← sum_sub_distrib, sum_div]
      apply sum_congr rfl
      intro h hh
      have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (mem_Icc.mp hh).1)
      field_simp [hN0.ne', hH.ne', hh0]
    · simp only [if_neg hml, A, mul_zero, sum_const_zero, zero_div]
  change |truncatedCenterDifference m l d N / (2 * N) -
    (if m = l then lagHarmonic m Q - lagSum m Q / H else 0)| ≤ _
  rw [heq, truncatedCenterDifference, ← sub_div, ← sum_sub_distrib,
    abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ h ∈ Icc 1 Q, (1 / (h : ℝ)) * K := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h hh => ?_)
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h)]
      exact mul_le_mul_of_nonneg_left (hr h hh) (by positivity)
    _ ≤ K * harmonic N := by
      rw [← sum_mul, harmonic_eq_sum_Icc_real, mul_comm K]
      apply mul_le_mul_of_nonneg_right _ hK
      simpa only [one_div] using sum_le_sum_of_subset_of_nonneg (f := fun h : ℕ => 1 / (h : ℝ))
        (show Icc 1 Q ⊆ Icc 1 N from fun h hh =>
          mem_Icc.mpr ⟨(mem_Icc.mp hh).1, (mem_Icc.mp hh).2.trans hQN⟩)
        (by intro h hh hh'; positivity)

/-- The triangular harmonic cutoff has an explicit signed finite part in every conductor. -/
theorem tendsto_triangular_lagHarmonic_finite_part {m : ℕ} (hm : 0 < m) :
    Tendsto (fun H : ℝ => lagHarmonic m ⌊H⌋₊ - lagSum m ⌊H⌋₊ / H -
      (if m = 1 then Real.log H else 0)) atTop
      (𝓝 (if m = 1 then Real.eulerMascheroniConstant - 1 else -vonMangoldt m)) := by
  have hfloor : Tendsto (fun H : ℝ => ⌊H⌋₊) atTop atTop := tendsto_nat_floor_atTop
  by_cases hm1 : m = 1
  · subst m
    simp only [if_true, lagHarmonic_one, lagSum_one]
    have hratio : Tendsto (fun H : ℝ => (⌊H⌋₊ : ℝ) / H) atTop (𝓝 1) :=
      tendsto_nat_floor_div_atTop
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
    simp only [Real.log_one] at hlog
    have hh := Real.tendsto_harmonic_sub_log.comp hfloor
    have h := (hh.add hlog).sub hratio
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    have hq : 1 ≤ ⌊H⌋₊ := (Nat.one_le_floor_iff H).mpr hH
    have hq0 : (0 : ℝ) < (⌊H⌋₊ : ℝ) := by exact_mod_cast hq
    simp only [Function.comp_def]
    rw [Real.log_div hq0.ne' (by linarith : H ≠ 0)]
    ring
  · simp only [if_neg hm1, sub_zero]
    have hm2 : 2 ≤ m := by omega
    let B : ℝ := (2 * m + 1) * ∑ t ∈ m.divisors, (t : ℝ)
    have hzero : Tendsto (fun H : ℝ => lagSum m ⌊H⌋₊ / H) atTop (𝓝 0) := by
      have hlim : Tendsto (fun H : ℝ => B / H) atTop (𝓝 0) := by
        simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul B
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < H)]
      exact div_le_div_of_nonneg_right (abs_lagSum_le hm2 ⌊H⌋₊) (by linarith)
    simpa only [Function.comp_def, sub_zero] using
      ((tendsto_lagHarmonic hm2).comp hfloor).sub hzero

/-- The exact near-center cutoff is asymptotic to twice the overlap. -/
theorem tendsto_nearCenterGapCutoff_div_overlap {c : ℕ → ℝ}
    (hc : ∀ N, 0 < c N) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearCenterGapCutoff (Real.exp (2 * c N / N) - 1) N / c N)
      atTop (𝓝 2) := by
  have hu : Tendsto (fun N : ℕ => 2 * c N / N) atTop (𝓝[>] 0) := by
    apply tendsto_inf.mpr
    constructor
    · simpa only [mul_zero, mul_div_assoc] using hcN.const_mul 2
    · apply tendsto_principal.mpr
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      exact div_pos (mul_pos zero_lt_two (hc N)) hN0
  have h := (HTGeometry.tendsto_one_sub_exp_neg_slope_nhdsGT_zero.comp hu).const_mul 2
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  dsimp only [Function.comp_def, nearCenterGapCutoff]
  rw [Real.exp_neg]
  field_simp [hN0.ne', (hc N).ne', Real.exp_ne_zero]
  ring

/-- The signed near-center harmonic finite part at a growing overlap. -/
theorem tendsto_triangular_lagHarmonic_at_overlap {m : ℕ} (hm : 0 < m)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    let H : ℕ → ℝ := fun N => nearCenterGapCutoff (Real.exp (2 * c N / N) - 1) N
    Tendsto (fun N : ℕ => lagHarmonic m ⌊H N⌋₊ - lagSum m ⌊H N⌋₊ / H N -
      (if m = 1 then Real.log (c N) else 0)) atTop
      (𝓝 (if m = 1 then Real.log 2 + Real.eulerMascheroniConstant - 1 else -vonMangoldt m)) := by
  intro H
  have hr := tendsto_nearCenterGapCutoff_div_overlap hc hcN
  have hHinf : Tendsto H atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hcinf.eventually_ge_atTop b,
      hr.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with N hNb hratio
    have hbound : c N ≤ H N := by
      simpa only [one_mul] using (le_div_iff₀ (hc N)).mp hratio.le
    exact hNb.trans hbound
  have hmain := (tendsto_triangular_lagHarmonic_finite_part hm).comp hHinf
  by_cases hm1 : m = 1
  · simp only [if_pos hm1] at hmain ⊢
    have hlog := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hr
    have h := hmain.add hlog
    have heq : Real.eulerMascheroniConstant - 1 + Real.log 2 =
        Real.log 2 + Real.eulerMascheroniConstant - 1 := by ring
    rw [heq] at h
    apply h.congr'
    filter_upwards [hHinf.eventually_ge_atTop 1] with N hHN
    have hH0 : 0 < H N := by linarith
    simp only [Function.comp_def]
    rw [Real.log_div hH0.ne' (hc N).ne']
    ring
  · simpa only [if_neg hm1, sub_zero, Function.comp_def] using hmain

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_truncatedCenterDifference_sub_le

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_triangular_lagHarmonic_at_overlap
