import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingNearPairMeanIsPolar

/-!
# Terminal weights preserve the polar near mean

A slowly varying function of the smaller index can be retained in the
growing-overlap pair average. The exact periodic row estimate and weighted
Riemann sums separate its integral from the two arithmetic period means.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

private theorem tendsto_nearPairSum_sub_weighted_row
    {K : ℝ → ℝ} {α β A L : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    {ρ : ℕ → ℕ → ℝ} {R : ℝ} (hρ : ∀ N n, |ρ N n| ≤ R)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearPairSum K α β (c N / N) N u v (ρ N) / c N -
      (∫ s in α..β, K s * Real.exp ((c N / N) * s / 2)) *
        ((∑ n ∈ Finset.Icc 1 N,
          ρ N n * (u n * periodicMean v q + v n * periodicMean u q)) / N))
      atTop (𝓝 0) := by
  let C : ℝ := (2 * q + 1) * B * (4 * A + 2 * β * L)
  have hinv : Tendsto (fun N : ℕ => 1 / c N) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hcinf
  have hlog : Tendsto (fun N : ℕ => Real.log (2 * β * c N) / c N) atTop (𝓝 0) := by
    have hg := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (hcinf.const_mul_atTop (by positivity : 0 < 2 * β))).mul_const (2 * β)
    simp only [zero_mul] at hg
    apply hg.congr
    intro N
    dsimp only [Function.comp_def, id_eq]
    field_simp [(hc N).ne', hβ.ne']
  have hNinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  let err : ℕ → ℝ := fun N => 2 * R * B *
    (2 * B * A * (1 / c N) + C * (1 / c N + Real.log (2 * β * c N) / c N) +
      (4 * B * A * β) * (β * (c N / N) + 1 / N))
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := ((hinv.const_mul (2 * B * A)).add ((hinv.add hlog).const_mul C)).add
      (((hcN.const_mul β).add hNinv).const_mul (4 * B * A * β))
    simpa only [zero_mul, mul_zero, add_zero] using h.const_mul (2 * R * B)
  apply squeeze_zero_norm' _ herr
  have hwlim : Tendsto (fun N : ℕ => β * (c N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcN.const_mul β
  filter_upwards [eventually_ge_atTop 1,
    hwlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hcinf.eventually_ge_atTop (1 / (2 * β))] with N hN hsmall hlarge
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c N / N := div_pos (hc N) hN0
  have hlarge' : 1 ≤ 2 * β * (c N / N) * N := by
    rw [show 2 * β * (c N / N) * N = (2 * β) * c N by field_simp]
    exact (div_le_iff₀ (by positivity : 0 < 2 * β)).mp hlarge |>.trans_eq (mul_comm _ _)
  have hb := abs_nearPairSum_sub_le hα hαβ hβ hw hsmall.le hA hL hL0 hq hu hv huB hvB
    (hρ N) hN hlarge'
  have ei : (∫ s in α..β, K s * ((c N / N) * Real.exp ((c N / N) * s / 2))) =
      (c N / N) * ∫ s in α..β, K s * Real.exp ((c N / N) * s / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by ring
  have eMain : (∫ s in α..β, K s * ((c N / N) * Real.exp ((c N / N) * s / 2))) *
      (∑ n ∈ Finset.Icc 1 N, ρ N n * (u n * periodicMean v q + v n * periodicMean u q)) /
        c N = (∫ s in α..β, K s * Real.exp ((c N / N) * s / 2)) *
          ((∑ n ∈ Finset.Icc 1 N,
            ρ N n * (u n * periodicMean v q + v n * periodicMean u q)) / N) := by
    rw [ei]
    generalize (∫ s in α..β, K s * Real.exp ((c N / N) * s / 2)) = z
    generalize (∑ n ∈ Finset.Icc 1 N,
      ρ N n * (u n * periodicMean v q + v n * periodicMean u q)) = b
    field_simp [(hc N).ne']
  rw [Real.norm_eq_abs, ← eMain, ← sub_div, abs_div, abs_of_pos (hc N)]
  calc
    _ ≤ (2 * R * B * (2 * B * A + C * (1 + Real.log (2 * β * (c N / N) * N)) +
        (β * (c N / N) * N + 1) * (4 * B * A * β * (c N / N)))) / c N :=
      div_le_div_of_nonneg_right hb (hc N).le
    _ = err N := by
      dsimp only [err]
      rw [show 2 * β * (c N / N) * N = 2 * β * c N by field_simp]
      field_simp [hN0.ne', (hc N).ne']

private theorem tendsto_near_row_integral
    {K : ℝ → ℝ} {α β A L : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ s in α..β, K s * Real.exp ((c N / N) * s / 2)) atTop
      (𝓝 (∫ s in α..β, K s)) := by
  have hz := tendsto_nearPairSum_sub_weighted_row hα hαβ hβ hA hL hL0
    (q := 1) (u := fun _ => 1) (v := fun _ => 1) (B := 1) one_pos
    (by intros; rfl) (by intros; rfl) (by intros; norm_num) (by intros; norm_num)
    (ρ := fun _ _ => 1) (R := 1) (by intros; norm_num) hc hcinf hcN
  have hm := tendsto_nearPairSum_div_overlap hα hαβ hβ hA hL hL0
    (q := 1) (u := fun _ => 1) (v := fun _ => 1) (B := 1) one_pos
    (by intros; rfl) (by intros; rfl) (by intros; norm_num) (by intros; norm_num)
    hc hcinf hcN
  have hone : periodicMean (fun _ : ℕ => (1 : ℝ)) 1 = 1 := by simp [periodicMean]
  simp only [hone, one_mul, mul_one] at hz hm
  have hlim := (hm.sub hz).div_const 2
  have htarget : (2 * (∫ s in α..β, K s) - 0) / 2 = ∫ s in α..β, K s := by ring
  rw [htarget] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  field_simp [hN0]
  ring

/-- A terminal weight contributes its integral to the signed periodic near-pair mean. -/
theorem tendsto_nearPairSum_terminal_weight_div_overlap
    {K F : ℝ → ℝ} {α β A L LF BF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) (hF : ∀ x, |F x| ≤ BF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearPairSum K α β (c N / N) N u v (fun n => F (n / N)) / c N)
      atTop (𝓝 (2 * periodicMean u q * periodicMean v q *
        (∫ s in α..β, K s) * ∫ x in (0 : ℝ)..1, F x)) := by
  have hz := tendsto_nearPairSum_sub_weighted_row hα hαβ hβ hA hL hL0 hq hu hv huB hvB
    (ρ := fun N n => F (n / N)) (fun _ _ => hF _) hc hcinf hcN
  have hI := tendsto_near_row_integral hα hαβ hβ hA hL hL0 hc hcinf hcN
  have hU := tendsto_weighted_riemannSum (Nat.succ_le_of_lt hq) hu huB hFL
    (fun x _ => hF x) 0
  have hV := tendsto_weighted_riemannSum (Nat.succ_le_of_lt hq) hv hvB hFL
    (fun x _ => hF x) 0
  simp only [Nat.sub_zero] at hU hV
  change Tendsto _ atTop (𝓝 (periodicMean u q * ∫ x in (0 : ℝ)..1, F x)) at hU
  change Tendsto _ atTop (𝓝 (periodicMean v q * ∫ x in (0 : ℝ)..1, F x)) at hV
  have hrow : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, F (n / N) *
        (u n * periodicMean v q + v n * periodicMean u q)) / N) atTop
      (𝓝 (2 * periodicMean u q * periodicMean v q * ∫ x in (0 : ℝ)..1, F x)) := by
    have h := (hU.mul_const (periodicMean v q)).add (hV.mul_const (periodicMean u q))
    have he : (periodicMean u q * ∫ x in (0 : ℝ)..1, F x) * periodicMean v q +
        (periodicMean v q * ∫ x in (0 : ℝ)..1, F x) * periodicMean u q =
        2 * periodicMean u q * periodicMean v q * ∫ x in (0 : ℝ)..1, F x := by ring
    rw [he] at h
    apply h.congr
    intro N
    have heSum : (∑ n ∈ Finset.Icc 1 N,
        F (n / N) * (u n * periodicMean v q + v n * periodicMean u q)) =
        (∑ n ∈ Finset.Icc 1 N, u n * F (n / N)) * periodicMean v q +
          (∑ n ∈ Finset.Icc 1 N, v n * F (n / N)) * periodicMean u q := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [heSum]
    ring
  have h := hz.add (hI.mul hrow)
  have he : 0 + (∫ s in α..β, K s) *
      (2 * periodicMean u q * periodicMean v q * ∫ x in (0 : ℝ)..1, F x) =
      2 * periodicMean u q * periodicMean v q *
        (∫ s in α..β, K s) * ∫ x in (0 : ℝ)..1, F x := by ring
  rw [he] at h
  exact h.congr fun N => by ring

/-- A terminally weighted Ramanujan pair retains only conductor one in both variables. -/
theorem tendsto_nearPairSum_ramanujan_terminal_weight_div_overlap
    {K F : ℝ → ℝ} {α β A L LF BF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) (hF : ∀ x, |F x| ≤ BF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearPairSum K α β (c N / N) N
      (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) (fun n => F (n / N)) / c N)
      atTop (𝓝 (if m = 1 ∧ l = 1 then
        2 * (∫ s in α..β, K s) * ∫ x in (0 : ℝ)..1, F x else 0)) := by
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
  have h := tendsto_nearPairSum_terminal_weight_div_overlap hα hαβ hβ hA hL hL0 hF hFL
    (Nat.mul_pos hm hl) hu hv huB hvB hc hcinf hcN
  rw [periodicMean_ramanujan_of_dvd hm (Nat.mul_pos hm hl) (dvd_mul_right m l),
    periodicMean_ramanujan_of_dvd hl (Nat.mul_pos hm hl) (dvd_mul_left l m)] at h
  convert h using 1
  by_cases hm1 : m = 1 <;> by_cases hl1 : l = 1 <;> simp [hm1, hl1]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_nearPairSum_terminal_weight_div_overlap
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_nearPairSum_ramanujan_terminal_weight_div_overlap
