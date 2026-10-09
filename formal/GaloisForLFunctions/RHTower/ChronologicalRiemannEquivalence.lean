import GaloisForLFunctions.RHTower.ChronologicalBudgetGapLaw
import GaloisForLFunctions.RHTower.ChronologicalBoseDilateCompleteness
import GaloisForLFunctions.RHTower.BaezDuarteCriterionHardDirection
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel

/-!
# RH is equivalent to bounded chronological approximation

For a finite row `a` the chronological heat error is
`r_a(t) = e^{-t} + Σ_{k ≤ N} a_k (1/(kt) - 1/(e^{kt} - 1))`.

**Plancherel form** (`chronologicalL2Norm_sq_eq_integral`).  On `0 < Re s < 1` the Mellin
transform of `r_a` is `Γ(s)(1 - ζ(s) A(s))`, `A(s) = Σ a_k k^{-s}`, and the Mellin unitary gives
`‖r_a‖²_{L²(0,∞)} = ∫ |Γ(s(ξ))(1 - ζ A)(s(ξ))|² dξ` on the line `s(ξ) = ½ - 2πiξ`.

**Converse** (`exists_chronologicalHeatError_lt_of_riemannHypothesis`).  Under RH the
Báez-Duarte Riesz rows `a_k = μ(k)(1 - k/X)k^{-δ}`, which are bounded by `1`, make `‖r_a‖`
arbitrarily small.  Since `|Γ(½ + it)|² ≤ π/(¼ + t²)` and
`1 - ζA = (1 + ζ P_c) + ζ Σ c_n/n`, the chronological error is controlled by the Báez-Duarte
distance plus `|Q_N(1 + δ)|²` times the finite constant `∫ |Γζ|²`.

**Dichotomy** (`riemannHypothesis_iff_chronological_unit_rows`,
`chronological_budget_dichotomy`).  RH holds iff rows bounded by `1` reach every accuracy.  If RH
fails, every coefficient budget `exp(ε^{-θ})` with `θ ≤ 2` fails at some accuracy.  The
coefficient price of chronological approximation is therefore either bounded or at least
`exp(ε^{-2})`, with nothing in between.
-/

open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The Dirichlet polynomial of a row. -/
def chronologicalRowPoly (a : ℕ → ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * (k : ℂ) ^ (-s)

/-- **Mellin transform of a chronological error** on the strip. -/
theorem mellin_chronologicalHeatError (a : ℕ → ℝ) (N : ℕ) {s : ℂ} (hs : s ∈ fusionMellinStrip) :
    mellin (fun t => (chronologicalHeatError a N t : ℂ)) s =
      Complex.Gamma s * (1 - riemannZeta s * chronologicalRowPoly a N s) := by
  have hx := chronologicalExponential_mellinConvergent hs.1
  have hm : ∀ k ∈ Finset.Ioc 0 N,
      MellinConvergent (fun t => (a k : ℂ) * fusionBoseKernel ((k : ℝ) * t)) s := by
    intro k hk
    have hd := (MellinConvergent.comp_mul_left
      (by exact_mod_cast (Finset.mem_Ioc.mp hk).1 : (0 : ℝ) < k)).mpr
        (fusionBoseKernel_converges s hs)
    simpa only [smul_eq_mul] using hd.const_smul (a k : ℂ)
  have he : (fun t => (chronologicalHeatError a N t : ℂ)) =
      (fun t => (Real.exp (-t) : ℂ) +
        ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * fusionBoseKernel ((k : ℝ) * t)) := by
    funext t
    simp [chronologicalHeatError, fusionBoseKernel]
  simp only [MellinConvergent, smul_eq_mul] at hx hm
  rw [he]
  unfold mellin
  simp only [smul_eq_mul, mul_add, Finset.mul_sum]
  rw [integral_add hx (integrable_finsetSum _ hm), integral_finsetSum _ hm]
  have hxv : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ)) = Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs.1, Complex.GammaIntegral]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [hxv]
  have hterm : ∀ k ∈ Finset.Ioc 0 N,
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * ((a k : ℂ) * fusionBoseKernel ((k : ℝ) * t))) =
        -(Complex.Gamma s * riemannZeta s * ((a k : ℂ) * (k : ℂ) ^ (-s))) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
    change mellin (fun t => (a k : ℂ) • fusionBoseKernel ((k : ℝ) * t)) s = _
    rw [mellin_const_smul, mellin_comp_mul_left _ _ hk0, fusionBoseKernel_mellin hs, smul_eq_mul,
      smul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  unfold chronologicalRowPoly
  rw [mul_sub, mul_one, Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Half-density bound for chronological errors: `|r(eˣ)| e^{x/2} ≤ A e^{-|x|/2}`. -/
theorem norm_halfDensityPullback_chronologicalHeatError_le (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) (x : ℝ) :
    ‖halfDensityPullback (fun t => (chronologicalHeatError a N t : ℂ)) x‖ ≤
      (1 + C * N) * Real.exp (-(1 / 2 * |x|)) := by
  have hb := chronologicalHeatError_bounds a N C ha (Real.exp_pos x)
  have hsq : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
  unfold halfDensityPullback
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), hsq]
  have hA : 0 ≤ 1 + C * N := by positivity
  rcases le_total x 0 with hx | hx
  · rw [abs_of_nonpos hx]
    calc Real.exp (x / 2) * |chronologicalHeatError a N (Real.exp x)|
        ≤ Real.exp (x / 2) * (1 + C * N) := mul_le_mul_of_nonneg_left hb.1 (Real.exp_pos _).le
      _ = (1 + C * N) * Real.exp (-(1 / 2 * -x)) := by ring_nf
  · rw [abs_of_nonneg hx]
    calc Real.exp (x / 2) * |chronologicalHeatError a N (Real.exp x)|
        ≤ Real.exp (x / 2) * ((1 + C * N) / Real.exp x) :=
          mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos _).le
      _ = (1 + C * N) * Real.exp (-(1 / 2 * x)) := by
          rw [mul_div_assoc', div_eq_mul_inv, ← Real.exp_neg]
          rw [mul_comm (Real.exp (x / 2)), mul_assoc, ← Real.exp_add]
          ring_nf

theorem integrable_halfDensityPullback_chronologicalHeatError (a : ℕ → ℝ) (N : ℕ) :
    Integrable (halfDensityPullback (fun t => (chronologicalHeatError a N t : ℂ))) := by
  set C := ∑ k ∈ Finset.Ioc 0 N, |a k| with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => abs_nonneg _
  have ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C := fun k hk =>
    Finset.single_le_sum (f := fun k => |a k|) (fun k _ => abs_nonneg _) hk
  have hexp : Integrable fun x : ℝ => Real.exp (-(1 / 2 * |x|)) := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
      (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * |x|)
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    have hpos : 0 < 1 + x ^ 2 := by positivity
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    rw [show 8 * (1 + x ^ 2)⁻¹ * Real.exp (1 / 2 * |x|) =
      8 * Real.exp (1 / 2 * |x|) / (1 + x ^ 2) by field_simp]
    rw [le_div_iff₀ hpos]
    nlinarith [abs_nonneg x]
  have hcont : ContinuousOn (fun t => (chronologicalHeatError a N t : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (chronologicalHeatError_continuousOn a N)
  have hm : AEStronglyMeasurable (halfDensityPullback
      (fun t => (chronologicalHeatError a N t : ℂ))) volume := by
    apply Continuous.aestronglyMeasurable
    unfold halfDensityPullback
    refine (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_exp)).mul ?_
    rw [continuous_iff_continuousAt]
    intro x
    exact (hcont.continuousAt (Ioi_mem_nhds (Real.exp_pos x))).comp
      Real.continuous_exp.continuousAt
  exact (hexp.const_mul (1 + C * N)).mono' hm
    (Eventually.of_forall (norm_halfDensityPullback_chronologicalHeatError_le a N C hC ha))

/-- **Plancherel form of the chronological error.** -/
theorem chronologicalL2Norm_sq_eq_integral (a : ℕ → ℝ) (N : ℕ) :
    chronologicalL2Norm (chronologicalHeatError a N) ^ 2 =
      ∫ ξ : ℝ, ‖Complex.Gamma (mellinLinePoint ξ) *
        (1 - riemannZeta (mellinLinePoint ξ) * chronologicalRowPoly a N (mellinLinePoint ξ))‖ ^ 2 := by
  set r := chronologicalHeatError a N with hr
  set g : ℝ → ℂ := fun t => (r t : ℂ) with hg
  have hrm : MemLp r 2 chronologicalPositiveVolume := chronologicalHeatError_memLp a N
  have hgm : MemLp g 2 (volume.restrict (Ioi (0 : ℝ))) := hrm.ofReal
  set f : HalfLineL2 := hgm.toLp g with hf
  have hnorm : chronologicalL2Norm r = ‖f‖ := by
    unfold chronologicalL2Norm
    rw [← toReal_eLpNorm hrm.1, hf, Lp.norm_toLp]
    congr 1
    exact (eLpNorm_congr_norm_ae (Eventually.of_forall fun t => by simp [hg])).symm
  rw [hnorm, ← halfLineMellinUnitary.norm_map, Lp_two_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [halfLineMellinUnitary_ae_eq_mellin f g (MemLp.coeFn_toLp hgm)
    (integrable_halfDensityPullback_chronologicalHeatError a N)] with ξ hξ
  rw [hξ]
  change ‖mellin g (mellinLinePoint ξ)‖ ^ 2 = _
  rw [mellin_chronologicalHeatError a N (mellinLinePoint_mem_strip ξ)]

/-- `|Γ(½ + it)|² ≤ π/(¼ + t²)`. -/
theorem norm_Gamma_half_sq_le (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 ≤ Real.pi / (1 / 4 + t ^ 2) := by
  rw [norm_Gamma_half_add_I_sq]
  have hcosh : 1 / 4 + t ^ 2 ≤ Real.cosh (Real.pi * t) := by
    set x := Real.pi * t with hx
    have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
    have h2 := Real.add_one_le_exp (-|x|)
    have hcx : Real.cosh x = Real.cosh |x| := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, Real.cosh_neg]
    rw [hcx, Real.cosh_eq]
    have hsq : |x| ^ 2 = Real.pi ^ 2 * t ^ 2 := by rw [sq_abs, hx]; ring
    have hpi : (1 : ℝ) ≤ Real.pi ^ 2 / 4 := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg t]
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hcosh

private theorem integrable_exp_neg_half_abs_chronological :
    Integrable fun x : ℝ => Real.exp (-(1 / 2 * |x|)) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * |x|)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  rw [show 8 * (1 + x ^ 2)⁻¹ * Real.exp (1 / 2 * |x|) =
    8 * Real.exp (1 / 2 * |x|) / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ hpos]
  nlinarith [abs_nonneg x]

/-- `ξ ↦ |Γζ(s(ξ))|²` is integrable on the Mellin line. -/
theorem integrable_norm_Gamma_mul_zeta_mellinLinePoint_sq :
    Integrable fun ξ : ℝ =>
      ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2 := by
  set K := 18 * Real.sqrt (2 * Real.pi) with hK
  refine (integrable_exp_neg_half_abs_chronological.const_mul (K ^ 2 * 11)).mono'
    ((continuous_Gamma_mul_zeta_mellinLinePoint.norm.pow 2).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mellinLinePoint_eq]
  set t := -(2 * Real.pi * ξ) with ht
  have hb := norm_Gamma_mul_zeta_half_le t
  have h0 : 0 ≤ ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I) *
      riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  have hsq := pow_le_pow_left₀ h0 hb 2
  have hcube := one_add_abs_pow_three_le_exp t
  have hsq3 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ 3 := by
    have : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    nlinarith
  have htξ : 1 / 2 * |ξ| ≤ Real.pi / 2 * |t| := by
    rw [ht, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hpi : (1 : ℝ) / 2 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    calc 1 / 2 * |ξ| ≤ Real.pi ^ 2 * |ξ| := mul_le_mul_of_nonneg_right hpi (abs_nonneg ξ)
      _ = Real.pi / 2 * (2 * Real.pi * |ξ|) := by ring
  have hexp1 : Real.exp (-(Real.pi / 2 * |t|)) ^ 2 * Real.exp (Real.pi / 2 * |t|) =
      Real.exp (-(Real.pi / 2 * |t|)) := by
    rw [sq, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I) *
        riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
      ≤ (K * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|))) ^ 2 := hsq
    _ = K ^ 2 * ((1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2 * |t|)) ^ 2) := by ring
    _ ≤ K ^ 2 * (11 * Real.exp (Real.pi / 2 * |t|) * Real.exp (-(Real.pi / 2 * |t|)) ^ 2) := by
        gcongr; linarith
    _ = K ^ 2 * 11 * (Real.exp (Real.pi / 2 * |t|) * Real.exp (-(Real.pi / 2 * |t|)) ^ 2) := by
        ring
    _ = K ^ 2 * 11 * Real.exp (-(Real.pi / 2 * |t|)) := by rw [mul_comm (Real.exp _), hexp1]
    _ ≤ K ^ 2 * 11 * Real.exp (-(1 / 2 * |ξ|)) := by
        gcongr

/-- `Σ_{n ≤ N} c_n/n = −Q_N(1 + δ)` for the Riesz coefficients. -/
theorem sum_bdRieszCoeff_div (N : ℕ) (δ : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, (bdRieszCoeff N δ n : ℂ) * (n : ℂ)⁻¹ = -moebiusRieszPoly N (1 + δ) := by
  unfold moebiusRieszPoly
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have h2 := natCast_rpow_neg_mul_cpow hn0 δ 1
  rw [Complex.cpow_neg_one] at h2
  unfold bdRieszCoeff
  push_cast
  rw [show (1 : ℂ) + δ = 1 + (δ : ℂ) from rfl, ← h2]
  ring

/-- For the negated Riesz row, `1 − ζA = (1 + ζP_c) − ζ Q_N(1 + δ)`. -/
theorem one_sub_riemannZeta_mul_chronologicalRowPoly_bdRiesz (N : ℕ) (δ : ℝ) (s : ℂ) :
    1 - riemannZeta s * chronologicalRowPoly (fun k => -bdRieszCoeff N δ k) N s =
      (1 + riemannZeta s * bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) s) -
        riemannZeta s * moebiusRieszPoly N (1 + δ) := by
  have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hK := sum_bdRieszCoeff_div N δ
  unfold chronologicalRowPoly bdMollPoly
  rw [hset, ← neg_neg (moebiusRieszPoly N (1 + δ)), ← hK]
  simp only [mul_sub, Finset.sum_sub_distrib, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Chronological error of the Riesz rows.**  For every row the squared chronological error is
at most the Báez-Duarte line integral plus `2‖Q_N(1+δ)‖² ∫|Γζ|²`. -/
theorem chronologicalL2Norm_sq_bdRiesz_le (N : ℕ) (δ : ℝ) :
    chronologicalL2Norm (chronologicalHeatError (fun k => -bdRieszCoeff N δ k) N) ^ 2 ≤
      (∫ t : ℝ, ‖1 + riemannZeta (1 / 2 + t * I) *
          bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) +
        2 * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2 * ∫ ξ : ℝ,
          ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2 := by
  set Q := moebiusRieszPoly N (1 + δ) with hQ
  set P := bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) with hP
  set H : ℝ → ℝ := fun t => ‖1 + riemannZeta (1 / 2 + t * I) * P (1 / 2 + t * I)‖ ^ 2 /
    (1 / 4 + t ^ 2) with hH
  have hS : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  obtain ⟨hHint, -⟩ := integrable_and_norm_sq_bdTarget_sub_sum_bdGen hS (bdRieszCoeff N δ)
  have hHint' : Integrable H := hHint
  have hGZ := integrable_norm_Gamma_mul_zeta_mellinLinePoint_sq
  -- change of variables `t = −2πξ`
  have hcov : (∫ ξ : ℝ, H (-(2 * Real.pi) * ξ)) = (2 * Real.pi)⁻¹ * ∫ t : ℝ, H t := by
    rw [Measure.integral_comp_mul_left H (-(2 * Real.pi))]
    rw [smul_eq_mul, inv_neg, abs_neg, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hHcomp : Integrable fun ξ : ℝ => H (-(2 * Real.pi) * ξ) :=
    hHint'.comp_mul_left' (neg_ne_zero.mpr (by positivity))
  rw [chronologicalL2Norm_sq_eq_integral]
  have hpt : ∀ ξ : ℝ, ‖Complex.Gamma (mellinLinePoint ξ) *
      (1 - riemannZeta (mellinLinePoint ξ) *
        chronologicalRowPoly (fun k => -bdRieszCoeff N δ k) N (mellinLinePoint ξ))‖ ^ 2 ≤
      2 * Real.pi * H (-(2 * Real.pi) * ξ) +
        2 * ‖Q‖ ^ 2 * ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2 := by
    intro ξ
    rw [one_sub_riemannZeta_mul_chronologicalRowPoly_bdRiesz]
    set s := mellinLinePoint ξ with hsdef
    have hs : s = 1 / 2 + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * I := by
      rw [hsdef, mellinLinePoint_eq]; push_cast; ring
    set u := 1 + riemannZeta s * P s with hu
    set v := riemannZeta s * Q with hv
    have hG := norm_Gamma_half_sq_le (-(2 * Real.pi) * ξ)
    rw [← hs] at hG
    have hHval : H (-(2 * Real.pi) * ξ) = ‖u‖ ^ 2 / (1 / 4 + (-(2 * Real.pi) * ξ) ^ 2) := by
      simp only [hH, hu, hP]
      rw [hs]
    have hden : 0 < 1 / 4 + (-(2 * Real.pi) * ξ) ^ 2 := by positivity
    calc ‖Complex.Gamma s * (u - v)‖ ^ 2
        = ‖Complex.Gamma s‖ ^ 2 * ‖u - v‖ ^ 2 := by rw [norm_mul, mul_pow]
      _ ≤ ‖Complex.Gamma s‖ ^ 2 * (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) := by
          gcongr
          have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le u v) 2
          nlinarith [norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]
      _ = 2 * (‖Complex.Gamma s‖ ^ 2 * ‖u‖ ^ 2) +
            2 * ‖Q‖ ^ 2 * ‖Complex.Gamma s * riemannZeta s‖ ^ 2 := by
          rw [hv, norm_mul, norm_mul, mul_pow, mul_pow]; ring
      _ ≤ 2 * (Real.pi / (1 / 4 + (-(2 * Real.pi) * ξ) ^ 2) * ‖u‖ ^ 2) +
            2 * ‖Q‖ ^ 2 * ‖Complex.Gamma s * riemannZeta s‖ ^ 2 := by
          gcongr
      _ = 2 * Real.pi * H (-(2 * Real.pi) * ξ) +
            2 * ‖Q‖ ^ 2 * ‖Complex.Gamma s * riemannZeta s‖ ^ 2 := by
          rw [hHval]; field_simp
  calc (∫ ξ : ℝ, ‖Complex.Gamma (mellinLinePoint ξ) *
        (1 - riemannZeta (mellinLinePoint ξ) *
          chronologicalRowPoly (fun k => -bdRieszCoeff N δ k) N (mellinLinePoint ξ))‖ ^ 2)
      ≤ ∫ ξ : ℝ, (2 * Real.pi * H (-(2 * Real.pi) * ξ) +
          2 * ‖Q‖ ^ 2 * ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity)
          ((hHcomp.const_mul _).add (hGZ.const_mul _)) (Eventually.of_forall hpt)
    _ = 2 * Real.pi * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, H t) +
          2 * ‖Q‖ ^ 2 * ∫ ξ : ℝ,
            ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2 := by
        rw [integral_add (hHcomp.const_mul _) (hGZ.const_mul _), integral_const_mul,
          integral_const_mul, hcov]
    _ = _ := by
        rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]

/-- The negated Riesz rows are bounded by `1`. -/
theorem abs_neg_bdRieszCoeff_le_one {N : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {k : ℕ}
    (hk : k ∈ Finset.Ioc 0 N) : |-bdRieszCoeff N δ k| ≤ 1 := by
  obtain ⟨hk1, hkN⟩ := Finset.mem_Ioc.mp hk
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hX : (k : ℝ) < perronLength N := by
    unfold perronLength; have : (k : ℝ) ≤ N := by exact_mod_cast hkN
    linarith
  have hX0 := perronLength_pos N
  have h1 : 0 ≤ 1 - (k : ℝ) / perronLength N := by
    rw [sub_nonneg, div_le_one hX0]; exact hX.le
  have h2 : 1 - (k : ℝ) / perronLength N ≤ 1 := by
    have : 0 ≤ (k : ℝ) / perronLength N := by positivity
    linarith
  have h3 : (k : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1' (by linarith)
  have h4 : 0 ≤ (k : ℝ) ^ (-δ) := Real.rpow_nonneg (by linarith) _
  have hmu : |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  unfold bdRieszCoeff
  rw [abs_neg, abs_mul, abs_mul, abs_neg, abs_of_nonneg h1, abs_of_nonneg h4]
  calc |((ArithmeticFunction.moebius k : ℤ) : ℝ)| * (1 - (k : ℝ) / perronLength N) * k ^ (-δ)
      ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- **Converse.**  Under RH, rows bounded by `1` reach every accuracy. -/
theorem exists_chronologicalHeatError_lt_of_riemannHypothesis (hRH : RiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ a : ℕ → ℝ, (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) ∧
      chronologicalL2Norm (chronologicalHeatError a N) < ε := by
  obtain ⟨B₂, hB₂0, hB⟩ := exists_norm_sq_bdTarget_sub_bdRiesz_le_of_rh hRH
  set M := ∫ ξ : ℝ, ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2
    with hMdef
  have hM0 : 0 ≤ M := integral_nonneg fun ξ => by positivity
  -- choose `δ`
  have hRlim : Tendsto (fun δ : ℝ => 3 * (zetaShiftDefect δ + B₂ * ‖invZetaCont (1 + δ)‖ ^ 2) +
      2 * ‖invZetaCont (1 + δ)‖ ^ 2 * M) (𝓝[>] 0) (𝓝 0) := by
    have hF : Tendsto zetaShiftDefect (𝓝[>] 0) (𝓝 0) :=
      tendsto_integral_one_sub_riemannZeta_ratio_of_rh hRH
    have hI := (tendsto_invZetaCont_one_add_of_rh hRH).norm.pow 2
    have := ((hF.add (hI.const_mul B₂)).const_mul 3).add ((hI.const_mul 2).mul_const M)
    simpa using this
  obtain ⟨δ, hδR, hδ0, hδ1⟩ :=
    ((hRlim.eventually (gt_mem_nhds (pow_pos hε 2))).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num))).exists
  obtain ⟨B₁, hB₁⟩ := hB δ hδ0 hδ1.le
  -- choose `N`
  have hG : Tendsto (fun N : ℕ => 3 * (zetaShiftDefect δ + B₁ * perronLength N ^ (-δ) +
      B₂ * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2) + 2 * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2 * M) atTop
      (𝓝 (3 * (zetaShiftDefect δ + B₂ * ‖invZetaCont (1 + δ)‖ ^ 2) +
        2 * ‖invZetaCont (1 + δ)‖ ^ 2 * M)) := by
    have h1 := (tendsto_perronLength_rpow_neg hδ0).const_mul B₁
    have h2 := (tendsto_moebiusRieszPoly_one_add_of_rh hRH hδ0 (by linarith)).norm.pow 2
    have := ((((tendsto_const_nhds (x := zetaShiftDefect δ)).add h1).add
      (h2.const_mul B₂)).const_mul 3).add ((h2.const_mul 2).mul_const M)
    simpa using this
  obtain ⟨N, hN⟩ := (hG.eventually (gt_mem_nhds hδR)).exists
  refine ⟨N, fun k => -bdRieszCoeff N δ k, fun k hk => abs_neg_bdRieszCoeff_le_one hδ0.le hk, ?_⟩
  have hS : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  obtain ⟨-, heq⟩ := integrable_and_norm_sq_bdTarget_sub_sum_bdGen hS (bdRieszCoeff N δ)
  have hle := chronologicalL2Norm_sq_bdRiesz_le N δ
  have hd := hB₁ N
  rw [heq] at hd
  have hπ : 0 < 2 * Real.pi := by positivity
  have hint_le : (∫ t : ℝ, ‖1 + riemannZeta (1 / 2 + t * I) *
      bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) ≤
      3 * (zetaShiftDefect δ + B₁ * perronLength N ^ (-δ) +
        B₂ * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hd hπ.le
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul, one_mul] at this
    exact this
  have hsq : chronologicalL2Norm (chronologicalHeatError (fun k => -bdRieszCoeff N δ k) N) ^ 2 <
      ε ^ 2 := by
    rw [← hMdef] at hle
    linarith
  exact (pow_lt_pow_iff_left₀ (chronologicalL2Norm_nonneg _) hε.le two_ne_zero).mp hsq

/-- **RH is bounded chronological approximation.** -/
theorem riemannHypothesis_iff_chronological_unit_rows :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : ℕ → ℝ,
      (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) ∧
        chronologicalL2Norm (chronologicalHeatError a N) < ε :=
  ⟨fun hRH _ hε => exists_chronologicalHeatError_lt_of_riemannHypothesis hRH hε,
    fun h => riemannHypothesis_of_forall_exists_chronologicalL2Norm_lt 1 zero_le_one h⟩

/-- **Budget dichotomy.**  Either RH holds and rows bounded by `1` reach every accuracy, or RH
fails and for every `0 < θ ≤ 2` some accuracy `ε` is out of reach for every row with
coefficients at most `exp(ε^{-θ})`. -/
theorem chronological_budget_dichotomy :
    (RiemannHypothesis ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : ℕ → ℝ,
        (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) ∧
          chronologicalL2Norm (chronologicalHeatError a N) < ε) ∨
      (¬ RiemannHypothesis ∧ ∀ θ : ℝ, 0 < θ → θ ≤ 2 → ∃ ε : ℝ, 0 < ε ∧
        ∀ N : ℕ, ∀ a : ℕ → ℝ, (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ Real.exp (ε ^ (-θ))) →
          ε < chronologicalL2Norm (chronologicalHeatError a N)) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ⟨hRH, riemannHypothesis_iff_chronological_unit_rows.mp hRH⟩
  · refine Or.inr ⟨hRH, fun θ hθ hθ2 => ?_⟩
    by_contra hcon
    push Not at hcon
    exact hRH (riemannHypothesis_of_chronological_budget_le_two hθ hθ2 fun ε hε => by
      obtain ⟨N, a, ha, hle⟩ := hcon ε hε
      exact ⟨N, a, ha, hle⟩)

end RHTower
