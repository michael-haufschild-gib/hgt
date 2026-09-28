import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryRateConstants
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicChebyshevOptimizer
import GaloisForLFunctions.HTGeometry.ArcsineLogIntegral

/-!
# The lower bound for the weighted Chebyshev norms

Let `T` be the monic degree-`m` weighted Chebyshev optimizer for the weight
`W(r)^m = (1 - √(1 - 4r))^m` on `[0, 1/4]`, with roots `r_i ∈ (0, 1/4)`, and put
`t_i = √(1 - 4 r_i)`.  Along the arcsine parametrization `r(φ) = (1 - b² cos² φ)/4` of
`[(1 - b²)/4, 1/4]`,

  `W(r(φ)) = 1 - b |cos φ|`,  `r(φ) - r_i = -(b cos φ - t_i)(b cos φ + t_i)/4`.

Averaging `log(W^m |T|) ≤ log t_m` over `φ ∈ [0, π]` and using that the arcsine potential is at
least `log(b/2)` gives, for **every** `b ∈ (0, 1)`,

  `t_m ≥ ρ(b)^m`,  `ρ(b) = (b²/16) exp((2/π) ∫_0^{π/2} log(1 - b cos s) ds)`.
-/

open MeasureTheory Set Filter intervalIntegral Polynomial
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The arcsine parametrization `r(φ) = (1 - b² cos² φ)/4`. -/
def arcsineRadius (b φ : ℝ) : ℝ := (1 - b ^ 2 * Real.cos φ ^ 2) / 4

theorem arcsineRadius_mem {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (φ : ℝ) :
    arcsineRadius b φ ∈ Icc (0 : ℝ) (1 / 4) := by
  have hc := Real.cos_sq_le_one φ
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
  constructor
  · unfold arcsineRadius; nlinarith [sq_nonneg (Real.cos φ), sq_nonneg b]
  · unfold arcsineRadius; nlinarith [sq_nonneg (Real.cos φ), sq_nonneg b]

theorem cubicRadialWeight_arcsineRadius {b : ℝ} (hb : 0 ≤ b) (φ : ℝ) :
    cubicRadialWeight (arcsineRadius b φ) = 1 - b * |Real.cos φ| := by
  unfold cubicRadialWeight arcsineRadius
  rw [show 1 - 4 * ((1 - b ^ 2 * Real.cos φ ^ 2) / 4) = (b * Real.cos φ) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hb]

theorem countable_cos_eq (c : ℝ) : {φ : ℝ | Real.cos φ = c}.Countable := by
  by_cases hc : c ∈ Icc (-1 : ℝ) 1
  · refine ((Set.countable_range fun k : ℤ => 2 * k * π + Real.arccos c).union
      (Set.countable_range fun k : ℤ => 2 * k * π - Real.arccos c)).mono fun φ hφ => ?_
    have h : Real.cos (Real.arccos c) = Real.cos φ := by
      rw [Real.cos_arccos hc.1 hc.2]; exact hφ.symm
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp h
    · exact Or.inl ⟨k, hk.symm⟩
    · exact Or.inr ⟨k, hk.symm⟩
  · convert Set.countable_empty
    ext φ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hc (h ▸ ⟨Real.neg_one_le_cos φ, Real.cos_le_one φ⟩)

/-- `∫_0^π f(|cos φ|) dφ = 2 ∫_0^{π/2} f(cos φ) dφ`. -/
theorem integral_abs_cos_symm (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    ∫ φ in (0 : ℝ)..π, f |Real.cos φ| = 2 * ∫ φ in (0 : ℝ)..π / 2, f (Real.cos φ) := by
  have hcont : ∀ a b : ℝ, IntervalIntegrable (fun φ => f |Real.cos φ|) volume a b := by
    intro a b
    refine ContinuousOn.intervalIntegrable (hf.comp (by fun_prop) fun φ _ =>
      ⟨abs_nonneg _, Real.abs_cos_le_one φ⟩)
  rw [← integral_add_adjacent_intervals (hcont 0 (π / 2)) (hcont (π / 2) π)]
  have h1 : ∫ φ in (0 : ℝ)..π / 2, f |Real.cos φ| = ∫ φ in (0 : ℝ)..π / 2, f (Real.cos φ) := by
    refine integral_congr fun φ hφ => ?_
    rw [uIcc_of_le (by positivity)] at hφ
    rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩)]
  have h2 : ∫ φ in π / 2..π, f |Real.cos φ| = ∫ φ in (0 : ℝ)..π / 2, f (Real.cos φ) := by
    have := integral_comp_sub_left (a := π / 2) (b := π) (fun φ => f |Real.cos φ|) π
    simp only [Real.cos_pi_sub, abs_neg] at this
    rw [show π - π = 0 by ring, show π - π / 2 = π / 2 by ring] at this
    rw [this, h1]
  rw [h1, h2]; ring

theorem arcsineRadius_sub_root {b φ r : ℝ} (hr : r ≤ 1 / 4) :
    arcsineRadius b φ - r = -((b * Real.cos φ - Real.sqrt (1 - 4 * r)) *
      (b * Real.cos φ - -Real.sqrt (1 - 4 * r))) / 4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 4 * r by linarith)
  unfold arcsineRadius
  nlinarith [hs]

/-- The Jensen integrand
`m log(1 - b|cos φ|) + Σ_{r ∈ s} (log(b cos φ - √(1-4r)) + log(b cos φ + √(1-4r)) - log 4)`,
equal to `log(W^m |T|)(r(φ))` for `T = ∏_{r ∈ s} (X - r)` off a countable set. -/
def jensenIntegrand (m : ℕ) (s : Finset ℝ) (b φ : ℝ) : ℝ :=
  (m : ℝ) * Real.log (1 - b * |Real.cos φ|) +
    ∑ r ∈ s, (Real.log (b * Real.cos φ - Real.sqrt (1 - 4 * r)) +
      Real.log (b * Real.cos φ - -Real.sqrt (1 - 4 * r)) - Real.log 4)

/-- **The pointwise Jensen bound.**  For `T = ∏_{r ∈ s} (X - r)` with roots in `(0, 1/4)`, off a
countable set of `φ` the Jensen integrand is at most `log ‖T‖_m`. -/
theorem ae_jensenIntegrand_le {m : ℕ} {T : Polynomial ℝ} {s : Finset ℝ}
    (hroots : ∀ r ∈ s, 0 < r ∧ r < 1 / 4) (hprod : T = ∏ r ∈ s, (X - C r)) {b : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ φ ∂(volume : Measure ℝ), jensenIntegrand m s b φ ≤
      Real.log (cubicWeightedIntervalNorm m T) := by
  classical
  set tm := cubicWeightedIntervalNorm m T with htm
  set t : ℝ → ℝ := fun r => Real.sqrt (1 - 4 * r) with ht
  set D : ℝ → ℝ := fun φ => jensenIntegrand m s b φ with hD
  have hW : ∀ φ, 0 < 1 - b * |Real.cos φ| := fun φ => by
    have := Real.abs_cos_le_one φ; nlinarith [hb.1, hb.2, abs_nonneg (Real.cos φ)]
  -- the pointwise bound on the arc
  have hbdd : BddAbove ((fun r : ℝ => cubicRadialWeight r ^ m * |T.eval r|) '' Icc 0 (1 / 4)) :=
    (isCompact_Icc.image_of_continuousOn ((cubicRadialWeight_continuous.pow m).mul
      (T.continuous.abs)).continuousOn).bddAbove
  have hpt : ∀ φ, cubicRadialWeight (arcsineRadius b φ) ^ m *
      |T.eval (arcsineRadius b φ)| ≤ tm := fun φ =>
    le_csSup hbdd ⟨_, arcsineRadius_mem hb φ, rfl⟩
  -- off a countable set, `D = log (W^m |T|) ≤ log t_m`
  have hE : ({φ : ℝ | ∃ r ∈ s, b * Real.cos φ - t r = 0 ∨ b * Real.cos φ - -t r = 0}).Countable := by
    have hsub : {φ : ℝ | ∃ r ∈ s, b * Real.cos φ - t r = 0 ∨ b * Real.cos φ - -t r = 0} ⊆
        ⋃ r ∈ s, ({φ | Real.cos φ = t r / b} ∪ {φ | Real.cos φ = -t r / b}) := by
      rintro φ ⟨r, hr, h | h⟩
      · refine Set.mem_biUnion hr (Or.inl ?_)
        simp only [Set.mem_setOf_eq]
        field_simp [hb.1.ne']; linarith
      · refine Set.mem_biUnion hr (Or.inr ?_)
        simp only [Set.mem_setOf_eq]
        field_simp [hb.1.ne']; linarith
    exact (s.countable_toSet.biUnion fun r _ =>
      (countable_cos_eq _).union (countable_cos_eq _)).mono hsub
  have hDle : ∀ᵐ φ ∂(volume : Measure ℝ), D φ ≤ Real.log tm := by
    refine ae_iff.mpr (measure_mono_null (fun φ hφ => ?_) (hE.measure_zero volume))
    simp only [Set.mem_setOf_eq, not_le] at hφ ⊢
    by_contra hne
    push Not at hne
    have hfac : ∀ r ∈ s, arcsineRadius b φ - r ≠ 0 := by
      intro r hr h0
      rw [arcsineRadius_sub_root (hroots r hr).2.le] at h0
      have := hne r hr
      apply mul_ne_zero this.1 this.2
      linarith
    have heval : T.eval (arcsineRadius b φ) = ∏ r ∈ s, (arcsineRadius b φ - r) := by
      rw [hprod, eval_prod]; simp
    have hTne : T.eval (arcsineRadius b φ) ≠ 0 := by
      rw [heval]; exact Finset.prod_ne_zero_iff.mpr hfac
    have hval : D φ = Real.log (cubicRadialWeight (arcsineRadius b φ) ^ m *
        |T.eval (arcsineRadius b φ)|) := by
      have hWm : cubicRadialWeight (arcsineRadius b φ) ^ m ≠ 0 := by
        rw [cubicRadialWeight_arcsineRadius hb.1.le]; exact pow_ne_zero _ (hW φ).ne'
      rw [Real.log_mul hWm (abs_ne_zero.mpr hTne), Real.log_pow, Real.log_abs,
        cubicRadialWeight_arcsineRadius hb.1.le, heval, Real.log_prod hfac]
      simp only [hD, jensenIntegrand]
      congr 1
      refine Finset.sum_congr rfl fun r hr => ?_
      have h1 := (hne r hr).1
      have h2 := (hne r hr).2
      rw [arcsineRadius_sub_root (hroots r hr).2.le, neg_div, Real.log_neg_eq_log,
        Real.log_div (mul_ne_zero h1 h2) (by norm_num), Real.log_mul h1 h2]
    rw [hval] at hφ
    exact absurd (Real.log_le_log (by
      rw [cubicRadialWeight_arcsineRadius hb.1.le]
      exact mul_pos (pow_pos (hW φ) _) (abs_pos.mpr hTne)) (hpt φ)) (not_le.mpr hφ)
  exact hDle

/-- **The Jensen lower bound.**  For every `b ∈ (0, 1)`, the optimizer norm satisfies
`t_m ≥ ρ(b)^m`. -/
theorem recoveryRateFun_pow_le {m : ℕ} (hm : 1 ≤ m) {T : Polynomial ℝ}
    (hT : IsCubicChebyshev m T) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    recoveryRateFun b ^ m ≤ cubicWeightedIntervalNorm m T := by
  classical
  obtain ⟨s, hcard, hroots, hprod, -, -⟩ := isCubicChebyshev_roots m hm hT
  obtain ⟨T₀, hT₀, hT₀pos⟩ := exists_isCubicChebyshev m
  have htpos : 0 < cubicWeightedIntervalNorm m T :=
    lt_of_lt_of_le hT₀pos (hT₀.2.2 T hT.1 hT.2.1)
  set tm := cubicWeightedIntervalNorm m T with htm
  set t : ℝ → ℝ := fun r => Real.sqrt (1 - 4 * r) with ht
  -- the logarithmic integrand
  set D : ℝ → ℝ := fun φ => (m : ℝ) * Real.log (1 - b * |Real.cos φ|) +
    ∑ r ∈ s, (Real.log (b * Real.cos φ - t r) + Real.log (b * Real.cos φ - -t r) - Real.log 4)
    with hD
  have hW : ∀ φ, 0 < 1 - b * |Real.cos φ| := fun φ => by
    have := Real.abs_cos_le_one φ; nlinarith [hb.1, hb.2, abs_nonneg (Real.cos φ)]
  have hDle : ∀ᵐ φ ∂(volume : Measure ℝ), D φ ≤ Real.log tm := ae_jensenIntegrand_le hroots hprod hb
  -- integrability of the pieces
  have hI1 : IntervalIntegrable (fun φ => (m : ℝ) * Real.log (1 - b * |Real.cos φ|))
      volume 0 π := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun φ _ => (hW φ).ne')
  have hI2 : ∀ r ∈ s, IntervalIntegrable (fun φ => Real.log (b * Real.cos φ - t r) +
      Real.log (b * Real.cos φ - -t r) - Real.log 4) volume 0 π := fun r _ =>
    ((intervalIntegrable_log_mul_cos_sub hb.1 _).add
      (intervalIntegrable_log_mul_cos_sub hb.1 _)).sub intervalIntegrable_const
  have hIsum : IntervalIntegrable (fun φ => ∑ r ∈ s, (Real.log (b * Real.cos φ - t r) +
      Real.log (b * Real.cos φ - -t r) - Real.log 4)) volume 0 π := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum s hI2
  have hDint : IntervalIntegrable D volume 0 π := hI1.add hIsum
  -- the integral of `D`
  have hJ : ∫ φ in (0 : ℝ)..π, (m : ℝ) * Real.log (1 - b * |Real.cos φ|) =
      (m : ℝ) * (2 * ∫ φ in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos φ)) := by
    rw [intervalIntegral.integral_const_mul, integral_abs_cos_symm (fun y => Real.log (1 - b * y))
      (ContinuousOn.log (by fun_prop) fun y hy => by nlinarith [hb.1, hb.2, hy.1, hy.2])]
  have hsumge : ((m : ℝ) * (2 * π * Real.log (b / 2) - π * Real.log 4)) ≤
      ∫ φ in (0 : ℝ)..π, ∑ r ∈ s, (Real.log (b * Real.cos φ - t r) +
        Real.log (b * Real.cos φ - -t r) - Real.log 4) := by
    rw [intervalIntegral.integral_finsetSum hI2]
    calc (m : ℝ) * (2 * π * Real.log (b / 2) - π * Real.log 4)
        = ∑ _r ∈ s, (2 * π * Real.log (b / 2) - π * Real.log 4) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [integral_sub ((intervalIntegrable_log_mul_cos_sub hb.1 _).add
            (intervalIntegrable_log_mul_cos_sub hb.1 _)) intervalIntegrable_const,
            integral_add (intervalIntegrable_log_mul_cos_sub hb.1 _)
              (intervalIntegrable_log_mul_cos_sub hb.1 _),
            intervalIntegral.integral_const, smul_eq_mul, sub_zero]
          have h1 := integral_log_mul_cos_sub_ge hb.1 (t r)
          have h2 := integral_log_mul_cos_sub_ge hb.1 (-t r)
          linarith
  have hmain : π * Real.log tm ≥ (m : ℝ) * (2 * ∫ φ in (0 : ℝ)..π / 2,
      Real.log (1 - b * Real.cos φ)) + (m : ℝ) * (2 * π * Real.log (b / 2) - π * Real.log 4) := by
    have hle := integral_mono_ae_restrict Real.pi_pos.le hDint intervalIntegrable_const
      (ae_restrict_of_ae hDle)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, hD,
      integral_add hI1 hIsum, hJ] at hle
    linarith
  -- conclude
  have hρ : recoveryRateFun b ^ m = Real.exp ((m : ℝ) * (Real.log (b ^ 2 / 16) +
      2 / π * ∫ φ in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos φ))) := by
    rw [recoveryRateFun, mul_pow, ← Real.exp_nat_mul, ← Real.exp_log (show 0 < (b ^ 2 / 16) ^ m by
      have := hb.1; positivity), ← Real.exp_add, Real.log_pow]
    congr 1; ring
  rw [hρ, ← Real.exp_log htpos]
  refine Real.exp_le_exp.mpr ?_
  have hlog : Real.log (b ^ 2 / 16) = 2 * Real.log (b / 2) - Real.log 4 := by
    rw [show b ^ 2 / 16 = (b / 2) ^ 2 / 4 by ring, Real.log_div (by have := hb.1; positivity)
      (by norm_num), Real.log_pow]; push_cast; ring
  rw [hlog]
  have hπ := Real.pi_pos
  rw [ge_iff_le, ← sub_nonneg] at hmain
  have : (m : ℝ) * (2 * Real.log (b / 2) - Real.log 4 +
      2 / π * ∫ φ in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos φ)) =
      ((m : ℝ) * (2 * ∫ φ in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos φ)) +
        (m : ℝ) * (2 * π * Real.log (b / 2) - π * Real.log 4)) / π := by
    field_simp; ring
  rw [this, div_le_iff₀ hπ]
  linarith

/-- **`t_m ≥ ρ^m`** at the recovery edge. -/
theorem recoveryRate_pow_le {m : ℕ} (hm : 1 ≤ m) {T : Polynomial ℝ}
    (hT : IsCubicChebyshev m T) : recoveryRate ^ m ≤ cubicWeightedIntervalNorm m T :=
  recoveryRateFun_pow_le hm hT recoveryEdge_mem

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
