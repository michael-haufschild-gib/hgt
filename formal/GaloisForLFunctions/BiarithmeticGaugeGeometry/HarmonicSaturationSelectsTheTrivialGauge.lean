import GaloisForLFunctions.BiarithmeticGaugeGeometry.PrimeGaugeTorusAndVacuumIntertwiners
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Harmonic saturation selects the trivial gauge

For a unitary prime gauge, the normalized harmonic mean tends to one exactly at the Euler
gauge. The finite obstruction is dilation: a nontrivial phase at `p` separates the values at
`n` and `pn`, forcing a positive harmonic deficit uniformly along multiples of `p`.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry.PrimeGauge

/-- The logarithmically weighted mean of the completely multiplicative character. -/
def harmonicAverage (ω : PrimeGauge) (N : ℕ) : ℂ :=
  (∑ n ∈ Icc 1 N, ω.gaugeChar n / (n : ℂ)) / ((harmonic N : ℝ) : ℂ)

/-- Deficit of the real harmonic correlation from its maximal value. -/
def harmonicDeficit (ω : PrimeGauge) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (1 - (ω.gaugeChar n).re) / n

private theorem harmonic_real_eq (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

private theorem harmonic_real_pos {N : ℕ} (hN : 1 ≤ N) : 0 < (harmonic N : ℝ) := by
  rw [harmonic_real_eq]
  exact sum_pos (fun n hn => by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
    positivity) ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩

private theorem harmonic_add_le (a b : ℕ) :
    (harmonic (a + b) : ℝ) ≤ (harmonic a : ℝ) + (harmonic b : ℝ) := by
  simp only [harmonic, sum_range_add, Rat.cast_add, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro n _
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.le_add_left (n + 1) a)

private theorem harmonic_mul_le (p N : ℕ) :
    (harmonic (p * N) : ℝ) ≤ (p : ℝ) * (harmonic N : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    calc
      (harmonic ((p + 1) * N) : ℝ) ≤
          (harmonic (p * N) : ℝ) + (harmonic N : ℝ) := by
        simpa only [Nat.add_mul, one_mul] using harmonic_add_le (p * N) N
      _ ≤ (p : ℝ) * (harmonic N : ℝ) + (harmonic N : ℝ) := add_le_add ih le_rfl
      _ = ((p + 1 : ℕ) : ℝ) * (harmonic N : ℝ) := by push_cast; ring

private theorem unit_norm_sub_one_sq {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, hz, one_pow, sq, one_mul] using Complex.normSq_eq_norm_sq z
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith only [hz2]

private theorem gauge_deficit_nonneg (ω : PrimeGauge) {n : ℕ} (hn : n ≠ 0) :
    0 ≤ 1 - (ω.gaugeChar n).re := by
  have h := sq_nonneg ‖ω.gaugeChar n - 1‖
  rw [unit_norm_sub_one_sq (ω.norm_gaugeChar hn)] at h
  linarith only [h]

/-- Dilation by `p` forces one of the two values away from one. -/
theorem dilation_deficit_le (ω : PrimeGauge) {p n : ℕ} (hp : p ≠ 0) (hn : n ≠ 0) :
    1 - (ω.gaugeChar p).re ≤
      2 * ((1 - (ω.gaugeChar n).re) + (1 - (ω.gaugeChar (p * n)).re)) := by
  have hdist : ‖ω.gaugeChar (p * n) - ω.gaugeChar n‖ = ‖ω.gaugeChar p - 1‖ := by
    rw [ω.gaugeChar_mul, ← sub_one_mul, norm_mul, ω.norm_gaugeChar hn, mul_one]
  have htri := norm_sub_le (ω.gaugeChar (p * n) - 1) (ω.gaugeChar n - 1)
  rw [sub_sub_sub_cancel_right, hdist] at htri
  have hs := mul_self_le_mul_self (norm_nonneg _) htri
  have hsq := sq_nonneg (‖ω.gaugeChar (p * n) - 1‖ - ‖ω.gaugeChar n - 1‖)
  have hp' := unit_norm_sub_one_sq (ω.norm_gaugeChar hp)
  have hn' := unit_norm_sub_one_sq (ω.norm_gaugeChar hn)
  have hpn := unit_norm_sub_one_sq (ω.norm_gaugeChar (mul_ne_zero hp hn))
  nlinarith only [hs, hsq, hp', hn', hpn]

theorem harmonicDeficit_nonneg (ω : PrimeGauge) (N : ℕ) : 0 ≤ ω.harmonicDeficit N := by
  refine sum_nonneg fun n hn => div_nonneg ?_ (Nat.cast_nonneg n)
  exact ω.gauge_deficit_nonneg (by have := (mem_Icc.mp hn).1; omega)

theorem harmonicDeficit_mono (ω : PrimeGauge) : Monotone ω.harmonicDeficit := by
  intro M N hMN
  refine sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) ?_
  intro n hn _
  exact div_nonneg (ω.gauge_deficit_nonneg (by have := (mem_Icc.mp hn).1; omega))
    (Nat.cast_nonneg n)

private theorem dilated_deficit_sum_le (ω : PrimeGauge) {p : ℕ} (hp : 1 ≤ p) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (1 - (ω.gaugeChar (p * n)).re) / n) ≤
      (p : ℝ) * ω.harmonicDeficit (p * N) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hp)
  have heq : (∑ n ∈ Icc 1 N, (1 - (ω.gaugeChar (p * n)).re) / n) =
      (p : ℝ) * ∑ n ∈ (Icc 1 N).image (p * ·), (1 - (ω.gaugeChar n).re) / n := by
    rw [sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab), mul_sum]
    refine sum_congr rfl fun n _ => ?_
    push_cast
    field_simp
  rw [heq]
  refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_ ?_) (Nat.cast_nonneg p)
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1.trans (Nat.le_mul_of_pos_left n hp),
      Nat.mul_le_mul_left p (mem_Icc.mp hn).2⟩
  · intro n hn _
    exact div_nonneg (ω.gauge_deficit_nonneg (by have := (mem_Icc.mp hn).1; omega))
      (Nat.cast_nonneg n)

/-- A fixed nontrivial phase costs a positive proportion of harmonic mass. -/
theorem harmonic_dilation_deficit (ω : PrimeGauge) {p : ℕ} (hp : 1 ≤ p) (N : ℕ) :
    (1 - (ω.gaugeChar p).re) * (harmonic N : ℝ) ≤
      2 * (1 + (p : ℝ)) * ω.harmonicDeficit (p * N) := by
  have hsum : (1 - (ω.gaugeChar p).re) * (harmonic N : ℝ) ≤
      2 * (ω.harmonicDeficit N +
        ∑ n ∈ Icc 1 N, (1 - (ω.gaugeChar (p * n)).re) / n) := by
    rw [harmonic_real_eq, mul_sum, harmonicDeficit, ← sum_add_distrib, mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have h := div_le_div_of_nonneg_right (ω.dilation_deficit_le (p := p) (n := n) (by omega) hn0)
      (Nat.cast_nonneg n)
    convert h using 1 <;> ring
  have hmono := ω.harmonicDeficit_mono (Nat.le_mul_of_pos_left N hp)
  have hdilate := ω.dilated_deficit_sum_le hp N
  nlinarith only [hsum, hmono, hdilate]

/-- The normalized defect has an explicit lower bound at every positive multiple of `p`. -/
theorem harmonic_dilation_deficit_ratio (ω : PrimeGauge) {p N : ℕ}
    (hp : 1 ≤ p) (hN : 1 ≤ N) :
    1 - (ω.gaugeChar p).re ≤
      (2 * (p : ℝ) * (1 + (p : ℝ))) *
        (ω.harmonicDeficit (p * N) / (harmonic (p * N) : ℝ)) := by
  have hH := harmonic_real_pos (hN.trans (Nat.le_mul_of_pos_left N hp))
  have hd := ω.gauge_deficit_nonneg (by omega : p ≠ 0)
  have hmass := mul_le_mul_of_nonneg_left (harmonic_mul_le p N) hd
  have hdef := mul_le_mul_of_nonneg_left (ω.harmonic_dilation_deficit hp N)
    (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  rw [← mul_div_assoc, le_div_iff₀ hH]
  nlinarith only [hmass, hdef]

private theorem re_div_nat (z : ℂ) (n : ℕ) : (z / (n : ℂ)).re = z.re / n := by
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, Complex.div_ofReal_re]

/-- The positive deficit is exactly one minus the real normalized correlation. -/
theorem harmonicDeficit_ratio (ω : PrimeGauge) {N : ℕ} (hN : 1 ≤ N) :
    ω.harmonicDeficit N / (harmonic N : ℝ) = 1 - (ω.harmonicAverage N).re := by
  have hsum : ω.harmonicDeficit N = (harmonic N : ℝ) -
      ∑ n ∈ Icc 1 N, (ω.gaugeChar n).re / n := by
    rw [harmonicDeficit, harmonic_real_eq, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => sub_div _ _ _
  have hre : (∑ n ∈ Icc 1 N, ω.gaugeChar n / (n : ℂ)).re =
      ∑ n ∈ Icc 1 N, (ω.gaugeChar n).re / n := by
    simp only [Complex.re_sum, re_div_nat]
  rw [hsum, sub_div, div_self (harmonic_real_pos hN).ne', harmonicAverage,
    Complex.div_ofReal_re, hre]

/-- Vanishing relative harmonic deficit forces the entire prime gauge to be trivial. -/
theorem eq_eulerGauge_of_harmonicDeficit_tendsto_zero (ω : PrimeGauge)
    (hlim : Tendsto (fun N => ω.harmonicDeficit N / (harmonic N : ℝ)) atTop (𝓝 0)) :
    ω = eulerGauge := by
  apply PrimeGauge.ext
  intro p
  change ω.val p = 1
  by_cases hp : p.Prime
  · have hdil := hlim.comp (tendsto_id.const_mul_atTop' hp.pos)
    have hupper := hdil.const_mul (2 * (p : ℝ) * (1 + (p : ℝ)))
    have hle : 1 - (ω.gaugeChar p).re ≤ 0 := by
      have h := tendsto_le_of_eventuallyLE tendsto_const_nhds hupper
        (by filter_upwards [eventually_ge_atTop 1] with N hN
            exact ω.harmonic_dilation_deficit_ratio hp.one_le hN)
      simpa only [mul_zero] using h
    have hsq := unit_norm_sub_one_sq (ω.norm_gaugeChar hp.ne_zero)
    have hz : ‖ω.gaugeChar p - 1‖ = 0 := by
      nlinarith only [hsq, hle, norm_nonneg (ω.gaugeChar p - 1)]
    have hchar : ω.gaugeChar p = 1 := sub_eq_zero.mp (norm_eq_zero.mp hz)
    rwa [ω.gaugeChar_prime hp] at hchar
  · exact ω.nonprime_eq_one hp

/-- Harmonic saturation characterizes the Euler point among all unitary prime gauges. -/
theorem harmonicAverage_tendsto_one_iff (ω : PrimeGauge) :
    Tendsto ω.harmonicAverage atTop (𝓝 1) ↔ ω = eulerGauge := by
  constructor
  · intro hlim
    apply ω.eq_eulerGauge_of_harmonicDeficit_tendsto_zero
    have hre := Complex.continuous_re.tendsto 1 |>.comp hlim
    have hd := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hre
    have hd' : Tendsto (fun N => 1 - (ω.harmonicAverage N).re) atTop (𝓝 0) := by
      simpa only [Complex.one_re, sub_self, Function.comp_apply] using hd
    refine hd'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (ω.harmonicDeficit_ratio hN).symm
  · rintro rfl
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have heq : (∑ n ∈ Icc 1 N, eulerGauge.gaugeChar n / (n : ℂ)) =
        ((harmonic N : ℝ) : ℂ) := by
      rw [harmonic_real_eq]
      push_cast
      refine sum_congr rfl fun n hn => ?_
      rw [gaugeChar_euler (by have := (mem_Icc.mp hn).1; omega)]
    rw [harmonicAverage, heq, div_self]
    exact_mod_cast (harmonic_real_pos hN).ne'

end GaloisForLFunctions.BiarithmeticGaugeGeometry.PrimeGauge

