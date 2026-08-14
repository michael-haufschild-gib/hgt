import GaloisForLFunctions.HTGeometry.ResolventSubordination

/-!
# The Gamma frequency symbol and its shifted numerical range

The literal Gamma jump has frequency symbol

`r(η) = 2 ∫₀^∞ (1 - cos (η s)) / (e^s - 1) ds`,

which is the classical combination `ψ(1+iη) + ψ(1-iη) + 2γ`.  Expanding `1/(e^s-1) = ∑ e^{-ns}`
and evaluating the elementary Laplace integrals turns it into the series

`r(η) = 2 ∑_{n ≥ 1} η² / (n (n² + η²))`,

from which nonnegativity, evenness, vanishing to second order at zero and monotonicity are
immediate.  Shifting the frequency into the strip costs exactly

`κ_σ = 2 ∫₀^∞ (cosh (σ s) - 1) / (e^s - 1) ds = 2 ∑_{n ≥ 1} σ² / (n (n² - σ²))`,

finite precisely for `|σ| < 1`, and the real part of the shifted symbol is bounded below by `-κ_σ`:
the first obstruction to shifting is the Gamma pole at height one.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The Laplace weight of the Gamma jump. -/
def gammaJumpWeight (s : ℝ) : ℝ := 1 / (Real.exp s - 1)

/-- The elementary Laplace transform of the cosine. -/
theorem gammaSymbol_integral_Ioi_exp_neg_mul_cos {n : ℝ} (hn : 0 < n) (η : ℝ) :
    (∫ s in Ioi (0:ℝ), Real.exp (-(n * s)) * Real.cos (η * s)) = n / (n ^ 2 + η ^ 2) := by
  have hc : ((n : ℂ) - η * Complex.I).re = n := by simp
  have hcpos : 0 < ((n : ℂ) - η * Complex.I).re := by rw [hc]; exact hn
  have hcomplex := GaloisForLFunctions.HTGeometry.integral_Ioi_cexp_neg hcpos
  have hre : ∀ s : ℝ, (Complex.exp (-(((n : ℂ) - η * Complex.I) * s))).re
      = Real.exp (-(n * s)) * Real.cos (η * s) := by
    intro s
    rw [Complex.exp_re]
    congr 1
    · congr 1
      simp [Complex.mul_re]
    · congr 1
      simp [Complex.mul_im]
  have hint : IntegrableOn (fun s : ℝ => Complex.exp (-(((n : ℂ) - η * Complex.I) * s)))
      (Ioi (0:ℝ)) volume := by
    have hnorm : ∀ s : ℝ, ‖Complex.exp (-(((n : ℂ) - η * Complex.I) * s))‖
        = Real.exp (-(n * s)) := by
      intro s
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.neg_re, Complex.mul_re, hc]
    refine Integrable.mono' (g := fun s : ℝ => Real.exp (-n * s))
      (exp_neg_integrableOn_Ioi 0 hn) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards with s
      rw [hnorm s]
      apply le_of_eq
      congr 1
      ring
  have hproj := (Complex.reCLM.integral_comp_comm hint)
  rw [hcomplex] at hproj
  simp only [Complex.reCLM_apply] at hproj
  have hval : (1 / ((n : ℂ) - η * Complex.I)).re = n / (n ^ 2 + η ^ 2) := by
    rw [one_div, Complex.inv_re]
    simp [Complex.normSq_apply, hc]
    ring
  rw [hval] at hproj
  rw [← hproj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  exact (hre s).symm

/-- The elementary Laplace transform of the exponential. -/
theorem gammaSymbol_integral_Ioi_exp_neg_mul {n : ℝ} (hn : 0 < n) :
    (∫ s in Ioi (0:ℝ), Real.exp (-(n * s))) = 1 / n := by
  have hderiv : ∀ s ∈ Ioi (0:ℝ),
      HasDerivAt (fun t : ℝ => -Real.exp (-(n * t)) / n) (Real.exp (-(n * s))) s := by
    intro s _
    have hinner0 : HasDerivAt (fun t : ℝ => -(n * t)) (-(n * 1)) s :=
      ((hasDerivAt_id' s).const_mul n).neg
    rw [mul_one] at hinner0
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(n * t))) (Real.exp (-(n * s)) * -n) s :=
      hinner0.exp
    have hscaled := (hexp.neg).div_const n
    have hval : -(Real.exp (-(n * s)) * -n) / n = Real.exp (-(n * s)) := by
      field_simp
    rw [← hval]
    exact hscaled
  have hcont : ContinuousWithinAt (fun t : ℝ => -Real.exp (-(n * t)) / n) (Ici (0:ℝ)) 0 := by
    apply Continuous.continuousWithinAt
    fun_prop
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-(n * s))) (Ioi (0:ℝ)) volume := by
    have hbase := exp_neg_integrableOn_Ioi (0:ℝ) hn
    refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show Real.exp (-n * x) = Real.exp (-(n * x))
    congr 1
    ring
  have hlim : Tendsto (fun t : ℝ => -Real.exp (-(n * t)) / n) atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(n * t))) atTop (𝓝 0) := by
      have hlin : Tendsto (fun t : ℝ => -(n * t)) atTop atBot := by
        have : Tendsto (fun t : ℝ => n * t) atTop atTop :=
          Filter.Tendsto.const_mul_atTop hn tendsto_id
        exact tendsto_neg_atTop_atBot.comp this
      exact Real.tendsto_exp_atBot.comp hlin
    have := (hexp.neg).div_const n
    simpa using this
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [hmain, mul_zero, neg_zero, Real.exp_zero]
  ring

/-! ## Elementary bounds on the Gamma jump weight -/

theorem one_le_cosh (u : ℝ) : 1 ≤ Real.cosh u := by
  rw [Real.cosh_eq]
  have hpos : 0 < Real.exp u := Real.exp_pos u
  have hinv : Real.exp (-u) = (Real.exp u)⁻¹ := Real.exp_neg u
  rw [hinv]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  have hsq : 0 ≤ (Real.exp u - 1) ^ 2 := sq_nonneg _
  have hne : Real.exp u ≠ 0 := ne_of_gt hpos
  have hmul : Real.exp u * (Real.exp u + (Real.exp u)⁻¹) = Real.exp u ^ 2 + 1 := by
    field_simp
  nlinarith [hsq, hpos, hmul]

theorem exp_sub_one_le_mul (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h1 : 1 - Real.exp (-t) ≤ t := by
    have := Real.add_one_le_exp (-t)
    linarith
  have h2 : Real.exp t * (1 - Real.exp (-t)) ≤ Real.exp t * t :=
    mul_le_mul_of_nonneg_left h1 (Real.exp_pos t).le
  have h3 : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [h2, h3]

theorem gammaJumpWeight_pos {s : ℝ} (hs : 0 < s) : 0 < gammaJumpWeight s := by
  have hexp : 1 < Real.exp s := by
    rw [show (1:ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr hs
  rw [gammaJumpWeight]
  apply div_pos one_pos
  linarith

theorem gammaJumpWeight_le_inv {s : ℝ} (hs : 0 < s) : gammaJumpWeight s ≤ 1 / s := by
  have hexp : s ≤ Real.exp s - 1 := by
    have := Real.add_one_le_exp s
    linarith
  rw [gammaJumpWeight]
  apply div_le_div_of_nonneg_left one_pos.le hs hexp

theorem gammaJumpWeight_le_two_exp {s : ℝ} (hs : 1 ≤ s) :
    gammaJumpWeight s ≤ 2 * Real.exp (-s) := by
  have hexp1 : Real.exp 1 ≤ Real.exp s := Real.exp_le_exp.mpr hs
  have he : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hpos : (0:ℝ) < Real.exp s := Real.exp_pos s
  have hhalf : Real.exp s / 2 ≤ Real.exp s - 1 := by
    nlinarith [hexp1, he, hpos]
  have hden : (0:ℝ) < Real.exp s - 1 := by
    nlinarith [hexp1, he]
  rw [gammaJumpWeight, div_le_iff₀ hden]
  have hinv : Real.exp (-s) = (Real.exp s)⁻¹ := Real.exp_neg s
  rw [hinv]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at hhalf
  field_simp
  nlinarith [hhalf, hpos]

/-! ## The shifted numerical range -/

/-- The exact cost of shifting the Gamma symbol into the strip. -/
def gammaShiftCost (σ s : ℝ) : ℝ := (Real.cosh (σ * s) - 1) * gammaJumpWeight s

theorem gammaShiftCost_nonneg {σ s : ℝ} (hs : 0 < s) : 0 ≤ gammaShiftCost σ s := by
  have h1 : 1 ≤ Real.cosh (σ * s) := one_le_cosh (σ * s)
  have h2 := gammaJumpWeight_pos hs
  rw [gammaShiftCost]
  nlinarith

/-- **`(17)`: the shift cost is integrable exactly inside the unit strip.** -/
theorem integrableOn_gammaShiftCost {σ : ℝ} (hσ : |σ| < 1) :
    IntegrableOn (gammaShiftCost σ) (Ioi (0:ℝ)) volume := by
  have hσ0 : 0 ≤ |σ| := abs_nonneg σ
  have hrate : 0 < 1 - |σ| := by linarith
  have hmeas : Measurable (gammaShiftCost σ) := by
    unfold gammaShiftCost gammaJumpWeight
    fun_prop
  have hnear : IntegrableOn (gammaShiftCost σ) (Ioc (0:ℝ) 1) volume := by
    refine Integrable.mono' (g := fun _ : ℝ => |σ| * Real.exp |σ|)
      (integrableOn_const (by simp)) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 < s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have hcosh : Real.cosh (σ * s) - 1 ≤ |σ| * s * Real.exp |σ| := by
      have habs : |σ * s| ≤ |σ| := by
        rw [abs_mul, abs_of_pos hs0]
        nlinarith [abs_nonneg σ]
      have hbound : Real.cosh (σ * s) ≤ Real.exp |σ * s| := by
        rw [Real.cosh_eq]
        have h1 : Real.exp (σ * s) ≤ Real.exp |σ * s| :=
          Real.exp_le_exp.mpr (le_abs_self _)
        have h2 : Real.exp (-(σ * s)) ≤ Real.exp |σ * s| :=
          Real.exp_le_exp.mpr (neg_le_abs _)
        linarith
      have hexp : Real.exp |σ * s| - 1 ≤ |σ * s| * Real.exp |σ * s| :=
        exp_sub_one_le_mul _
      have hmono : Real.exp |σ * s| ≤ Real.exp |σ| := Real.exp_le_exp.mpr habs
      have habs2 : |σ * s| = |σ| * s := by
        rw [abs_mul, abs_of_pos hs0]
      calc Real.cosh (σ * s) - 1
          ≤ Real.exp |σ * s| - 1 := by linarith
        _ ≤ |σ * s| * Real.exp |σ * s| := hexp
        _ = (|σ| * s) * Real.exp |σ * s| := by rw [habs2]
        _ ≤ (|σ| * s) * Real.exp |σ| := by
            apply mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = |σ| * s * Real.exp |σ| := by ring
    have hw := gammaJumpWeight_le_inv hs0
    have hwpos := gammaJumpWeight_pos hs0
    have hcosh0 : 0 ≤ Real.cosh (σ * s) - 1 := by
      have := one_le_cosh (σ * s)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (gammaShiftCost_nonneg hs0), gammaShiftCost]
    calc (Real.cosh (σ * s) - 1) * gammaJumpWeight s
        ≤ (|σ| * s * Real.exp |σ|) * (1 / s) := by
          apply mul_le_mul hcosh hw hwpos.le
          positivity
      _ = |σ| * Real.exp |σ| := by
          field_simp
  have hfar : IntegrableOn (gammaShiftCost σ) (Ioi (1:ℝ)) volume := by
    have hmajor : IntegrableOn (fun s : ℝ => 2 * Real.exp (-(1 - |σ|) * s)) (Ioi (1:ℝ)) volume :=
      (exp_neg_integrableOn_Ioi 1 hrate).const_mul 2
    refine Integrable.mono' hmajor hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs1 : (1:ℝ) ≤ s := le_of_lt hs
    have hs0 : (0:ℝ) < s := by linarith
    have hcosh : Real.cosh (σ * s) - 1 ≤ Real.exp (|σ| * s) := by
      have hbound : Real.cosh (σ * s) ≤ Real.exp |σ * s| := by
        rw [Real.cosh_eq]
        have h1 : Real.exp (σ * s) ≤ Real.exp |σ * s| :=
          Real.exp_le_exp.mpr (le_abs_self _)
        have h2 : Real.exp (-(σ * s)) ≤ Real.exp |σ * s| :=
          Real.exp_le_exp.mpr (neg_le_abs _)
        linarith
      have habs2 : |σ * s| = |σ| * s := by
        rw [abs_mul, abs_of_pos hs0]
      rw [habs2] at hbound
      linarith [Real.exp_pos (|σ| * s)]
    have hw := gammaJumpWeight_le_two_exp hs1
    have hcosh0 : 0 ≤ Real.cosh (σ * s) - 1 := by
      have := one_le_cosh (σ * s)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (gammaShiftCost_nonneg hs0), gammaShiftCost]
    calc (Real.cosh (σ * s) - 1) * gammaJumpWeight s
        ≤ Real.exp (|σ| * s) * (2 * Real.exp (-s)) := by
          apply mul_le_mul hcosh hw (gammaJumpWeight_pos hs0).le (Real.exp_pos _).le
      _ = 2 * Real.exp (-(1 - |σ|) * s) := by
          rw [show Real.exp (|σ| * s) * (2 * Real.exp (-s))
              = 2 * (Real.exp (|σ| * s) * Real.exp (-s)) by ring, ← Real.exp_add]
          congr 2
          ring
  have hunion : IntegrableOn (gammaShiftCost σ) (Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ)) volume :=
    hnear.union hfar
  rwa [Ioc_union_Ioi_eq_Ioi (le_of_lt one_pos)] at hunion

/-- The shifted symbol never costs more than the shift cost: the real part of the frequency
weight is bounded below by `-(cosh (σ s) - 1)` times the jump weight. -/
theorem re_shifted_weight_ge (x σ s : ℝ) (hs : 0 < s) :
    -gammaShiftCost σ s
      ≤ (1 - Real.cos (x * s) * Real.cosh (σ * s)) * gammaJumpWeight s := by
  have hw := gammaJumpWeight_pos hs
  have hcos : Real.cos (x * s) ≤ 1 := Real.cos_le_one _
  have hcosh : 1 ≤ Real.cosh (σ * s) := one_le_cosh _
  have hkey : 1 - Real.cosh (σ * s) ≤ 1 - Real.cos (x * s) * Real.cosh (σ * s) := by
    nlinarith [Real.neg_one_le_cos (x * s)]
  rw [gammaShiftCost]
  nlinarith [hw, hkey]

end

end RHTower
