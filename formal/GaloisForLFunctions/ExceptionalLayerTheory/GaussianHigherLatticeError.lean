import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherDerivatives
import GaloisForLFunctions.RHTower.DQPTEulerMaclaurin
import GaloisForLFunctions.HTGeometry.EulerMaclaurinSecondOrder

/-!
# Arbitrary even-order errors on complete Gaussian lattices

Bernoulli integration by parts is valid through the singular origin because
the last Gaussian derivative is integrable and all preceding ones are
continuous. Every endpoint correction vanishes on the complete lattice.
-/

open Complex MeasureTheory Filter Topology Finset
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def mellinBernoulliKernel (k : ℕ) (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((b ^ k * (bernoulliFun k (x / b - n) / (k.factorial : ℝ)) : ℝ) : ℂ)

private def mellinBernoulliRemainder (k : ℕ) (w ε : ℂ) (b : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, ∫ x in (b * n : ℝ)..(b * (n + 1)),
    mellinBernoulliKernel k b n x * gaussianMellinJet k w ε x

private theorem continuous_mellinBernoulliKernel (k : ℕ) (b : ℝ) (n : ℕ) :
    Continuous (mellinBernoulliKernel k b n) := by
  unfold mellinBernoulliKernel
  exact Complex.continuous_ofReal.comp
    (continuous_const.mul (((continuous_bernoulliFun k).comp
      ((continuous_id.div_const b).sub continuous_const)).div_const _))

private theorem hasDerivAt_mellinBernoulliKernel (k : ℕ) {b : ℝ}
    (hb : 0 < b) (n : ℕ) (x : ℝ) :
    HasDerivAt (mellinBernoulliKernel (k + 1) b n)
      (mellinBernoulliKernel k b n x) x := by
  have h := (RHTower.DQPT.dqpt_hasDerivAt_bernoulliQuot k 0 (x / b - n)).comp x
    (((hasDerivAt_id x).div_const b).sub_const (n : ℝ))
  have h' := (h.const_mul (b ^ (k + 1))).ofReal_comp
  simp only [sub_zero, Function.comp_def] at h'
  apply h'.congr_deriv
  dsimp only [mellinBernoulliKernel, Function.comp_def]
  congr 1
  rw [pow_succ]
  field_simp [hb.ne']

private theorem mellinBernoulliKernel_zero (b : ℝ) (n : ℕ) (x : ℝ) :
    mellinBernoulliKernel 0 b n x = 1 := by
  simp [mellinBernoulliKernel]

private theorem mellinBernoulliKernel_left (k : ℕ) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    mellinBernoulliKernel k b n (b * n) =
      ((b ^ k * (((bernoulli k : ℚ) : ℝ) / (k.factorial : ℝ)) : ℝ) : ℂ) := by
  simp only [mellinBernoulliKernel, mul_div_cancel_left₀ (n : ℝ) hb.ne', sub_self,
    bernoulliFun_eval_zero]

private theorem mellinBernoulliKernel_right (k : ℕ) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    mellinBernoulliKernel k b n (b * (n + 1)) =
      ((b ^ k * (bernoulliFun k 1 / (k.factorial : ℝ)) : ℝ) : ℂ) := by
  simp only [mellinBernoulliKernel, mul_div_cancel_left₀ ((n : ℝ) + 1) hb.ne',
    add_sub_cancel_left]

private theorem intervalIntegrable_mellinJet (k : ℕ) {w ε : ℂ}
    (hw : (k : ℝ) - 1 < w.re) (hε : 0 < ε.re) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) :
    IntervalIntegrable (gaussianMellinJet k w ε) volume a c := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mpr
  exact (integrableOn_gaussianMellinJet k hw hε).mono_set
    (fun x hx => lt_of_le_of_lt ha hx.1)

private theorem mellinBernoulli_cell (k : ℕ) {w ε : ℂ}
    (hw : (k : ℝ) < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (∫ x in (b * n : ℝ)..(b * (n + 1)),
        mellinBernoulliKernel (k + 1) b n x * gaussianMellinJet (k + 1) w ε x) =
      mellinBernoulliKernel (k + 1) b n (b * (n + 1)) *
        gaussianMellinJet k w ε (b * (n + 1)) -
      mellinBernoulliKernel (k + 1) b n (b * n) * gaussianMellinJet k w ε (b * n) -
      ∫ x in (b * n : ℝ)..(b * (n + 1)),
        mellinBernoulliKernel k b n x * gaussianMellinJet k w ε x := by
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (continuous_mellinBernoulliKernel _ _ _).continuousOn
    (continuous_gaussianMellinJet k hw ε).continuousOn
    (fun x _ => hasDerivAt_mellinBernoulliKernel k hb n x)
    (fun x hx => hasDerivAt_gaussianMellinJet k hw ε ?_)
    ((continuous_mellinBernoulliKernel _ _ _).intervalIntegrable _ _)
    (intervalIntegrable_mellinJet (k + 1) (by push_cast; linarith) hε
      (by positivity) (by nlinarith only [hb]))
  have hab : b * (n : ℝ) ≤ b * (n + 1) := by nlinarith only [hb]
  rw [min_eq_left hab, max_eq_right hab] at hx
  exact lt_of_le_of_lt (by positivity) hx.1

private theorem mellinBernoulliRemainder_succ {k : ℕ} (hk : 1 ≤ k) {w ε : ℂ}
    (hw : (k : ℝ) < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    mellinBernoulliRemainder (k + 1) w ε b N =
      ((b ^ (k + 1) * (((bernoulli (k + 1) : ℚ) : ℝ) /
        ((k + 1).factorial : ℝ)) : ℝ) : ℂ) * gaussianMellinJet k w ε (b * N) -
      mellinBernoulliRemainder k w ε b N := by
  unfold mellinBernoulliRemainder
  simp_rw [mellinBernoulli_cell k hw hε hb,
    mellinBernoulliKernel_left _ hb, mellinBernoulliKernel_right _ hb,
    bernoulliFun_endpoints_eq_of_ne_one (show k + 1 ≠ 1 by omega), bernoulliFun_eval_zero]
  rw [sum_sub_distrib]
  have ht : (∑ n ∈ range N,
      (gaussianMellinJet k w ε (b * (n + 1)) - gaussianMellinJet k w ε (b * n))) =
      gaussianMellinJet k w ε (b * N) := by
    have h := sum_range_sub (fun n : ℕ => gaussianMellinJet k w ε (b * n)) N
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero,
      gaussianMellinJet_zero k hw ε, sub_zero] using h
  simp_rw [← mul_sub]
  rw [← mul_sum, ht]

private theorem mellinBernoulliRemainder_one {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    mellinBernoulliRemainder 1 w ε b N =
      (b : ℂ) * ((∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
        gaussianMellinWeight w ε (b * N) / 2) -
      ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x := by
  have hw0 : ((0 : ℕ) : ℝ) < w.re := by simpa only [Nat.cast_zero] using hw
  have hc := continuous_gaussianMellinJet 0 hw0 ε
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := gaussianMellinWeight w ε)
    (fun _ _ => hc.intervalIntegrable (μ := volume) _ _)
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsplit
  have htrap := GaloisForLFunctions.HTGeometry.sum_trapezoid_complex
    (fun x => gaussianMellinWeight w ε (b * x)) N
  rw [sum_range_succ'] at htrap
  have hz : gaussianMellinWeight w ε 0 = 0 := gaussianMellinJet_zero 0 hw0 ε
  simp only [Nat.cast_zero, mul_zero, hz, add_zero, zero_add,
    Nat.cast_add, Nat.cast_one] at htrap
  unfold mellinBernoulliRemainder
  simp_rw [mellinBernoulli_cell 0 hw0 hε hb,
    mellinBernoulliKernel_left _ hb, mellinBernoulliKernel_right _ hb,
    mellinBernoulliKernel_zero, one_mul]
  simp only [gaussianMellinJet]
  rw [sum_sub_distrib, hsplit, ← htrap, mul_sum]
  congr 1
  apply sum_congr rfl
  intro n _
  norm_num [bernoulliFun_one]; ring

private theorem tendsto_mellinJet_lattice_zero (k : ℕ) (w : ℂ) {ε : ℂ}
    (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun N : ℕ => gaussianMellinJet k w ε (b * N)) atTop (𝓝 0) := by
  have hs : Summable (fun N : ℕ => gaussianMellinJet k w ε (b * N)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using summable_gaussianMellinJet_lattice k w hε hb
  exact hs.tendsto_atTop_zero

private theorem tendsto_mellinBernoulliRemainder (k : ℕ) {w ε : ℂ}
    (hw : (k : ℝ) < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    Tendsto (mellinBernoulliRemainder (k + 1) w ε b) atTop
      (𝓝 ((-1 : ℂ) ^ k * ((b : ℂ) *
        (∑' n : ℕ, gaussianMellinWeight w ε (b * (n + 1))) -
        ∫ x in Set.Ioi (0 : ℝ), gaussianMellinWeight w ε x))) := by
  induction k with
  | zero =>
    have hw0 : 0 < w.re := by simpa only [Nat.cast_zero] using hw
    have hs := (summable_gaussianMellinWeight_lattice_all (w := w) hε hb).hasSum.tendsto_sum_nat
    have hz := (tendsto_mellinJet_lattice_zero 0 w hε hb).div_const (2 : ℂ)
    have hN : Tendsto (fun N : ℕ => b * (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hb
    have hi := intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_gaussianMellinWeight hw0 hε) hN
    have h := ((hs.sub hz).const_mul (b : ℂ)).sub hi
    change Tendsto (fun N : ℕ => mellinBernoulliRemainder 1 w ε b N) _ _
    simp_rw [mellinBernoulliRemainder_one hw0 hε hb]
    simpa only [gaussianMellinJet, zero_div, sub_zero, pow_zero, one_mul] using h
  | succ k ih =>
    have hk : (k : ℝ) < w.re := by push_cast at hw; linarith
    have hprev := ih hk
    have hz := (tendsto_mellinJet_lattice_zero (k + 1) w hε hb).const_mul
      (((b ^ (k + 1 + 1) * (((bernoulli (k + 1 + 1) : ℚ) : ℝ) /
        ((k + 1 + 1).factorial : ℝ)) : ℝ) : ℂ))
    have h := hz.sub hprev
    change Tendsto (fun N : ℕ => mellinBernoulliRemainder (k + 1 + 1) w ε b N) _ _
    simp_rw [mellinBernoulliRemainder_succ (by omega : 1 ≤ k + 1) hw hε hb]
    simpa only [mul_zero, zero_sub, pow_succ, mul_neg_one, neg_mul] using h

private theorem norm_mellinBernoulliRemainder_le (r : ℕ) (hr : r ≠ 0) {w ε : ℂ}
    (hw : ((2 * r : ℕ) : ℝ) - 1 < w.re) (hε : 0 < ε.re)
    {b : ℝ} (hb : 0 < b) (N : ℕ) :
    ‖mellinBernoulliRemainder (2 * r) w ε b N‖ ≤
      b ^ (2 * r) * |((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ) *
        gaussianMellinJetVariation (2 * r) w ε := by
  let C : ℝ := b ^ (2 * r) * |((bernoulli (2 * r) : ℚ) : ℝ)| /
    ((2 * r).factorial : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcell (n : ℕ) :
      ‖∫ x in (b * n : ℝ)..(b * (n + 1)),
        mellinBernoulliKernel (2 * r) b n x * gaussianMellinJet (2 * r) w ε x‖ ≤
      C * ∫ x in (b * n : ℝ)..(b * (n + 1)), ‖gaussianMellinJet (2 * r) w ε x‖ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le
      (show b * (n : ℝ) ≤ b * (n + 1) by nlinarith only [hb])
      (Filter.Eventually.of_forall fun x hx => ?_)
      ((intervalIntegrable_mellinJet (2 * r) hw hε
        (by positivity) (by nlinarith only [hb])).norm.const_mul C)
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have harg : x / b - n ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · have h := (le_div_iff₀ hb).mpr (show (n : ℝ) * b ≤ x by nlinarith only [hx.1])
        linarith
      · have h := (div_le_iff₀ hb).mpr
          (show x ≤ ((n : ℝ) + 1) * b by nlinarith only [hx.2])
        linarith
    have hB := RHTower.DQPT.dqpt_abs_bernoulliFun_le hr harg
    change ‖((b ^ (2 * r) * (bernoulliFun (2 * r) (x / b - n) /
      ((2 * r).factorial : ℝ)) : ℝ) : ℂ)‖ ≤ C
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (by positivity : 0 ≤ b ^ (2 * r)),
      abs_of_nonneg (by positivity : 0 ≤ ((2 * r).factorial : ℝ))]
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hB (by positivity)) (by positivity)).trans_eq (by dsimp [C]; ring)
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N)
    (f := fun x => ‖gaussianMellinJet (2 * r) w ε x‖)
    (fun n _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (intervalIntegrable_mellinJet (2 * r) hw hε
          (show 0 ≤ b * n by positivity)
          (show b * (n : ℝ) ≤ b * (n + 1) by nlinarith only [hb])).norm)
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsplit
  have hi : (∫ x in (0 : ℝ)..(b * N), ‖gaussianMellinJet (2 * r) w ε x‖) ≤
      gaussianMellinJetVariation (2 * r) w ε := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine (setIntegral_mono_set (integrableOn_gaussianMellinJet (2 * r) hw hε).norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_).trans
      (integral_norm_gaussianMellinJet_le (2 * r) hw hε)
    exact Filter.Eventually.of_forall fun x hx => hx.1
  calc
    _ ≤ ∑ n ∈ range N, ‖∫ x in (b * n : ℝ)..(b * (n + 1)),
        mellinBernoulliKernel (2 * r) b n x * gaussianMellinJet (2 * r) w ε x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ range N, C * ∫ x in (b * n : ℝ)..(b * (n + 1)),
        ‖gaussianMellinJet (2 * r) w ε x‖ := sum_le_sum fun n _ => hcell n
    _ = C * ∫ x in (0 : ℝ)..(b * N), ‖gaussianMellinJet (2 * r) w ε x‖ := by
      rw [← mul_sum, hsplit]
    _ ≤ _ := mul_le_mul_of_nonneg_left hi hC

/-- Complete Gaussian divisor lattices have an error of order `b^(2r-1)`.
All boundary derivatives vanish; only the integrable final derivative is charged. -/
theorem norm_tsum_gaussianMellinWeight_sub_main_higher_le (r : ℕ) (hr : r ≠ 0)
    {w ε : ℂ} (hw : ((2 * r : ℕ) : ℝ) - 1 < w.re) (hε : 0 < ε.re)
    {b : ℝ} (hb : 0 < b) :
    ‖(∑' n : ℕ, gaussianMellinWeight w ε (b * (n + 1))) -
        (b : ℂ)⁻¹ * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) *
          ε ^ (-(w + 1) / 2))‖ ≤
      b ^ (2 * r - 1) * |((bernoulli (2 * r) : ℚ) : ℝ)| /
        ((2 * r).factorial : ℝ) * gaussianMellinJetVariation (2 * r) w ε := by
  have hp : 1 ≤ 2 * r := by omega
  have hpred : 2 * r - 1 + 1 = 2 * r := by omega
  have hcast : ((2 * r - 1 : ℕ) : ℝ) = ((2 * r : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hp, Nat.cast_one]
  have hw0 : 0 < w.re := by
    have hnonneg : (0 : ℝ) ≤ (2 * r - 1 : ℕ) := Nat.cast_nonneg _
    rw [hcast] at hnonneg
    linarith only [hw, hnonneg]
  have ht := tendsto_mellinBernoulliRemainder (2 * r - 1) (by rwa [hcast]) hε hb
  rw [hpred] at ht
  have hbound := le_of_tendsto ht.norm
    (Filter.Eventually.of_forall fun N => norm_mellinBernoulliRemainder_le r hr hw hε hb N)
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    integral_gaussianMellinWeight hw0 hε] at hbound
  have he (S P : ℂ) : (b : ℂ) * S - P = (b : ℂ) * (S - (b : ℂ)⁻¹ * P) := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne'), one_mul]
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at hbound
  apply le_of_mul_le_mul_left (a := b) _ hb
  apply hbound.trans_eq
  have hpow : b ^ (2 * r) = b ^ (2 * r - 1) * b := by
    calc
      _ = b ^ (2 * r - 1 + 1) := by rw [hpred]
      _ = _ := pow_succ _ _
  rw [hpow]
  ring

#print axioms norm_tsum_gaussianMellinWeight_sub_main_higher_le

end GaloisForLFunctions.ExceptionalLayerTheory
