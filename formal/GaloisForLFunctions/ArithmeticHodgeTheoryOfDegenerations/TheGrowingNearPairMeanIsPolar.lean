import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRowsOfANearPairSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The growing near-pair mean is polar

A bounded Lipschitz kernel of the scaled logarithmic gap averages against the
product of the two periodic means when the overlap grows and its horizon width
vanishes. Ramanujan pairs therefore retain only conductor one in both variables.
The quantitative row estimate pays the error before passage to the limit.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

private theorem tendsto_periodicMean_Icc {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hp : ∀ n, p (n + q) = p n) {B : ℝ} (hB : ∀ n, |p n| ≤ B) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, p n) / N) atTop
      (𝓝 (periodicMean p q)) := by
  have h := tendsto_weighted_riemannSum (G := fun _ : ℝ => (1 : ℝ))
    (L := 0) (B := 1) (Nat.succ_le_of_lt hq) hp hB
    (by intros; simp) (by intros; simp) 0
  simpa [periodicMean] using h

private theorem tendsto_integral_small_exp_kernel {K : ℝ → ℝ} {α β A L : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) {w : ℕ → ℝ} (hw : ∀ N, 0 ≤ w N)
    (hw0 : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ s in α..β, K s * Real.exp (w N * s / 2)) atTop
      (𝓝 (∫ s in α..β, K s)) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  have hK : ContinuousOn K (Icc α β) := by
    intro x hx
    refine Metric.continuousWithinAt_iff.mpr fun ε hε =>
      ⟨ε / (L + 1), by positivity, fun y hy hxy => ?_⟩
    rw [Real.dist_eq] at hxy ⊢
    calc
      _ ≤ L * |y - x| := hL y hy x hx
      _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hxy.le hL0
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  have hbound : ∀ N, |(∫ s in α..β, K s * Real.exp (w N * s / 2)) -
      ∫ s in α..β, K s| ≤ A * (Real.exp (w N * β / 2) - 1) * (β - α) := by
    intro N
    have hec : Continuous (fun s : ℝ => Real.exp (w N * s / 2)) :=
      Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 2)
    have hI : IntervalIntegrable (fun s : ℝ => K s * Real.exp (w N * s / 2)) volume α β :=
      (hK.mul hec.continuousOn).intervalIntegrable_of_Icc hαβ
    rw [← intervalIntegral.integral_sub hI (hK.intervalIntegrable_of_Icc hαβ)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s : ℝ => K s * Real.exp (w N * s / 2) - K s)
      (a := α) (b := β) (C := A * (Real.exp (w N * β / 2) - 1)) (fun s hs => by
        rw [uIoc_of_le hαβ] at hs
        have hs0 : 0 ≤ s := hα.trans hs.1.le
        have he1 : 1 ≤ Real.exp (w N * s / 2) :=
          Real.one_le_exp_iff.mpr (div_nonneg (mul_nonneg (hw N) hs0) (by norm_num))
        have heβ : Real.exp (w N * s / 2) ≤ Real.exp (w N * β / 2) :=
          Real.exp_le_exp.mpr (by nlinarith [hw N, hs.2])
        rw [Real.norm_eq_abs]
        rw [show K s * Real.exp (w N * s / 2) - K s =
          K s * (Real.exp (w N * s / 2) - 1) by ring,
          abs_mul, abs_of_nonneg (sub_nonneg.mpr he1)]
        exact mul_le_mul (hA s ⟨hs.1.le, hs.2⟩) (by linarith) (by linarith) hA0)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hαβ)] using hb
  have he : Tendsto (fun N => A * (Real.exp (w N * β / 2) - 1) * (β - α)) atTop (𝓝 0) := by
    have hwβ : Tendsto (fun N => w N * β / 2) atTop (𝓝 0) := by
      simpa only [zero_mul, zero_div] using (hw0.mul_const β).div_const 2
    have h := (((Real.continuous_exp.tendsto 0).comp hwβ).sub_const 1).const_mul A
    simpa only [zero_mul, zero_div, Real.exp_zero, sub_self, mul_zero, Function.comp_def] using
      h.mul_const (β - α)
  have hz : Tendsto (fun N : ℕ => (∫ s in α..β, K s * Real.exp (w N * s / 2)) -
      ∫ s in α..β, K s) atTop (𝓝 0) :=
    squeeze_zero_norm (fun N => by simpa only [Real.norm_eq_abs] using hbound N) he
  simpa only [zero_add, sub_add_cancel] using hz.add_const (∫ s in α..β, K s)

/-- Growing overlap averages a fixed Lipschitz gap kernel against the two period means. -/
theorem tendsto_nearPairSum_div_overlap {K : ℝ → ℝ} {α β A L : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearPairSum K α β (c N / N) N u v (fun _ => 1) / c N)
      atTop (𝓝 (2 * periodicMean u q * periodicMean v q * ∫ s in α..β, K s)) := by
  let C : ℝ := (2 * q + 1) * B * (4 * A + 2 * β * L)
  have hinv : Tendsto (fun N : ℕ => 1 / c N) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hcinf
  have hlog : Tendsto (fun N : ℕ => Real.log (2 * β * c N) / c N) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hg := (hsmall.comp (hcinf.const_mul_atTop (by positivity : 0 < 2 * β))).mul_const (2 * β)
    simp only [zero_mul] at hg
    apply hg.congr
    intro N
    dsimp only [Function.comp_def]
    field_simp [(hc N).ne', hβ.ne']
  have hNinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  let err : ℕ → ℝ := fun N => 2 * B *
    (2 * B * A * (1 / c N) + C * (1 / c N + Real.log (2 * β * c N) / c N) +
      (4 * B * A * β) * (β * (c N / N) + 1 / N))
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := ((hinv.const_mul (2 * B * A)).add ((hinv.add hlog).const_mul C)).add
      (((hcN.const_mul β).add hNinv).const_mul (4 * B * A * β))
    simpa only [zero_mul, mul_zero, add_zero] using h.const_mul (2 * B)
  let rowMean : ℕ → ℝ := fun N =>
    (∑ n ∈ Finset.Icc 1 N, (u n * periodicMean v q + v n * periodicMean u q)) / N
  have hrow : Tendsto rowMean atTop (𝓝 (2 * periodicMean u q * periodicMean v q)) := by
    have h := ((tendsto_periodicMean_Icc hq hu huB).mul_const (periodicMean v q)).add
      ((tendsto_periodicMean_Icc hq hv hvB).mul_const (periodicMean u q))
    have e : periodicMean u q * periodicMean v q + periodicMean v q * periodicMean u q =
      2 * periodicMean u q * periodicMean v q := by ring
    rw [e] at h
    apply h.congr
    intro N
    dsimp only [rowMean]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hI := tendsto_integral_small_exp_kernel hα hαβ hA hL hL0
    (fun N => div_nonneg (hc N).le (Nat.cast_nonneg N)) hcN
  have hprod := hI.mul hrow
  let main : ℕ → ℝ := fun N => (∫ s in α..β, K s * Real.exp ((c N / N) * s / 2)) * rowMean N
  have hz : Tendsto (fun N => nearPairSum K α β (c N / N) N u v (fun _ => 1) / c N -
      main N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ herr
    have hwlim : Tendsto (fun N : ℕ => β * (c N / N)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hcN.const_mul β
    have hwsmall : ∀ᶠ N in atTop, β * (c N / N) ≤ 1 :=
      (hwlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le
    filter_upwards [eventually_ge_atTop 1, hwsmall,
      hcinf.eventually_ge_atTop (1 / (2 * β))] with N hN hsmall hlarge
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hw : 0 < c N / N := div_pos (hc N) hN0
    have hlarge' : 1 ≤ 2 * β * (c N / N) * N := by
      rw [show 2 * β * (c N / N) * N = (2 * β) * c N by field_simp]
      exact (div_le_iff₀ (by positivity : 0 < 2 * β)).mp hlarge |>.trans_eq (mul_comm _ _)
    have hb := abs_nearPairSum_sub_le hα hαβ hβ hw hsmall hA hL hL0 hq hu hv huB hvB
      (ρ := fun _ => 1) (R := 1) (by intro n; norm_num) hN hlarge'
    have eMain : (∫ s in α..β, K s * ((c N / N) * Real.exp ((c N / N) * s / 2))) *
        (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) * (u n * periodicMean v q + v n * periodicMean u q)) /
        c N = main N := by
      simp only [one_mul]
      have ei : (∫ s in α..β, K s * ((c N / N) * Real.exp ((c N / N) * s / 2))) =
          (c N / N) * ∫ s in α..β, K s * Real.exp ((c N / N) * s / 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      rw [ei]
      dsimp only [main, rowMean]
      field_simp [(hc N).ne']
      simp only [mul_comm]
    rw [Real.norm_eq_abs, ← eMain, ← sub_div, abs_div, abs_of_pos (hc N)]
    calc
      _ ≤ (2 * 1 * B * (2 * B * A + C * (1 + Real.log (2 * β * (c N / N) * N)) +
          (β * (c N / N) * N + 1) * (4 * B * A * β * (c N / N)))) / c N :=
        div_le_div_of_nonneg_right hb (hc N).le
      _ = err N := by
        dsimp only [err]
        rw [show 2 * β * (c N / N) * N = 2 * β * c N by field_simp]
        field_simp [hN0.ne', (hc N).ne']
  have h := hz.add hprod
  have e : (∫ s in α..β, K s) * (2 * periodicMean u q * periodicMean v q) =
      2 * periodicMean u q * periodicMean v q * ∫ s in α..β, K s := mul_comm _ _
  simp only [zero_add] at h
  rw [e] at h
  apply h.congr
  intro N
  dsimp only [main]
  ring

/-- On any complete period, a Ramanujan mode has mean zero except at conductor one. -/
theorem periodicMean_ramanujan_of_dvd {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hmq : m ∣ q) :
    periodicMean (ramanujanLagCoefficient m) q = if m = 1 then 1 else 0 := by
  have h := sum_ramTwist_mul_ramTwist_add one_pos hm (one_dvd q) hmq 0
  simp only [ramTwist_eq_ramanujanLagCoefficient, ramanujanLagCoefficient_one,
    one_mul, add_zero] at h
  unfold periodicMean
  rw [h]
  by_cases hm1 : m = 1
  · subst m
    simp [Nat.ne_of_gt hq]
  · simp [hm1, Ne.symm hm1]

/-- A fixed scaled-gap kernel retains only the polar pair of Ramanujan conductors. -/
theorem tendsto_nearPairSum_ramanujan_div_overlap {K : ℝ → ℝ} {α β A L : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearPairSum K α β (c N / N) N
      (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) (fun _ => 1) / c N)
      atTop (𝓝 (if m = 1 ∧ l = 1 then 2 * ∫ s in α..β, K s else 0)) := by
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
  have h := tendsto_nearPairSum_div_overlap hα hαβ hβ hA hL hL0
    (Nat.mul_pos hm hl) hu hv huB hvB hc hcinf hcN
  rw [periodicMean_ramanujan_of_dvd hm (Nat.mul_pos hm hl) (dvd_mul_right m l),
    periodicMean_ramanujan_of_dvd hl (Nat.mul_pos hm hl) (dvd_mul_left l m)] at h
  convert h using 1
  by_cases hm1 : m = 1 <;> by_cases hl1 : l = 1 <;> simp [hm1, hl1]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_nearPairSum_div_overlap
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_nearPairSum_ramanujan_div_overlap
