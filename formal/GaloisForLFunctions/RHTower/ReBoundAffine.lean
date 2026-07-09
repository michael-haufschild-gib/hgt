import Mathlib

/-!
# A one-sided order-one growth bound forces an entire function to be affine

If `g : ℂ → ℂ` is entire and its **real part** obeys the order-one-with-logarithm bound
`Re (g z) ≤ B · (1 + ‖z‖) · log (2 + ‖z‖)` for some `B ≥ 0`, then `g` is a polynomial of
degree at most one:

`g z = g 0 + (deriv g 0) · z`.

This is the Borel–Carathéodory + Cauchy-estimate core of a Hadamard order argument.

## Mechanism

1. **Borel–Carathéodory** turns the one-sided real-part bound into a two-sided modulus bound.
   Applying `Complex.borelCaratheodory` on the disc of radius `R = 2(1 + ‖z‖)` with the majorant
   `M = (B+1)(1 + R) log (2 + R)` and simplifying `R - ‖z‖ = 2 + ‖z‖` yields the global envelope
   `‖g z‖ ≤ 2 (B+1)(3 + 2‖z‖) log (4 + 2‖z‖) + 3 ‖g 0‖`, an `O(‖z‖ log ‖z‖)` bound.

2. **Cauchy's estimate for the second derivative** at an arbitrary centre `c`
   (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) gives, for every radius `R`,
   `‖iteratedDeriv 2 g c‖ ≤ 2 · (envelope at ‖c‖ + R) / R²`.  Because the envelope grows like
   `R log R`, the right-hand side tends to `0` as `R → ∞`, so `iteratedDeriv 2 g c = 0`.

3. A vanishing second derivative everywhere means `deriv g` has zero derivative everywhere, hence
   `deriv g` is constant (`is_const_of_deriv_eq_zero`); a second application to
   `w ↦ g w - (deriv g 0) · w` shows that function is constant, which is exactly the affine
   conclusion.
-/

open Complex Metric Set Real Filter Topology MeasureTheory

namespace RHTower

/-- **A one-sided order-one growth bound forces an entire function to be affine.**

An entire `g : ℂ → ℂ` whose real part satisfies
`Re (g z) ≤ B · (1 + ‖z‖) · log (2 + ‖z‖)` (with `B ≥ 0`) is a degree `≤ 1` polynomial:
`g z = g 0 + (deriv g 0) · z`.

The proof upgrades the real-part bound to a modulus bound by Borel–Carathéodory, kills every
Taylor coefficient of degree `≥ 2` by the Cauchy estimate (the `R log R` envelope divided by `R²`
tends to `0`), and reads off the affine form from `deriv g` being constant. -/
theorem entire_reBound_imp_affine (g : ℂ → ℂ) (hg : Differentiable ℂ g) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, (g z).re ≤ B * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :
    ∀ z : ℂ, g z = g 0 + deriv g 0 * z := by
  -- A strictly positive majorant coefficient, so the Borel–Carathéodory bound `M` is positive.
  set B' : ℝ := B + 1 with hB'def
  have hB'pos : 0 < B' := by rw [hB'def]; linarith
  have hBB' : B ≤ B' := by rw [hB'def]; linarith
  -- Step 1: the global modulus envelope from Borel–Carathéodory.
  have hmod : ∀ z : ℂ,
      ‖g z‖ ≤ 2 * B' * (3 + 2 * ‖z‖) * Real.log (4 + 2 * ‖z‖) + 3 * ‖g 0‖ := by
    intro z
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    set R : ℝ := 2 * (1 + ‖z‖) with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    set M : ℝ := B' * (1 + R) * Real.log (2 + R) with hMdef
    have hlogRpos : 0 < Real.log (2 + R) := Real.log_pos (by rw [hRdef]; nlinarith)
    have hMpos : 0 < M := by rw [hMdef]; positivity
    have hzball : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hRdef]; nlinarith
    have hmaps : MapsTo g (ball (0 : ℂ) R) {w | (w : ℂ).re ≤ M} := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      have hwR : ‖w‖ ≤ R := le_of_lt hw
      simp only [mem_setOf_eq]
      have h1 : (g w).re ≤ B * (1 + ‖w‖) * Real.log (2 + ‖w‖) := hbound w
      have hXnn : 0 ≤ (1 + ‖w‖) * Real.log (2 + ‖w‖) := by
        have : 0 ≤ Real.log (2 + ‖w‖) :=
          Real.log_nonneg (by have := norm_nonneg w; linarith)
        positivity
      have h2 : B * ((1 + ‖w‖) * Real.log (2 + ‖w‖))
          ≤ B' * ((1 + ‖w‖) * Real.log (2 + ‖w‖)) :=
        mul_le_mul_of_nonneg_right hBB' hXnn
      have hXY : (1 + ‖w‖) * Real.log (2 + ‖w‖) ≤ (1 + R) * Real.log (2 + R) := by
        have hlw : Real.log (2 + ‖w‖) ≤ Real.log (2 + R) :=
          Real.log_le_log (by have := norm_nonneg w; linarith) (by linarith)
        have hlwnn : 0 ≤ Real.log (2 + ‖w‖) :=
          Real.log_nonneg (by have := norm_nonneg w; linarith)
        exact mul_le_mul (by linarith) hlw hlwnn (by linarith)
      have h3 : B' * ((1 + ‖w‖) * Real.log (2 + ‖w‖)) ≤ B' * ((1 + R) * Real.log (2 + R)) :=
        mul_le_mul_of_nonneg_left hXY (le_of_lt hB'pos)
      calc (g w).re ≤ B * (1 + ‖w‖) * Real.log (2 + ‖w‖) := h1
        _ = B * ((1 + ‖w‖) * Real.log (2 + ‖w‖)) := by ring
        _ ≤ B' * ((1 + R) * Real.log (2 + R)) := le_trans h2 h3
        _ = M := by rw [hMdef]; ring
    have hbc := Complex.borelCaratheodory hMpos hg.differentiableOn hmaps hRpos hzball
    have hRz : R - ‖z‖ = 2 + ‖z‖ := by rw [hRdef]; ring
    have ht1 : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
      rw [hRz, mul_div_assoc]
      apply mul_le_of_le_one_right (by positivity)
      rw [div_le_one (by positivity)]; linarith
    have ht2 : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
      rw [hRz, hRdef, mul_div_assoc]
      have hfrac : (2 * (1 + ‖z‖) + ‖z‖) / (2 + ‖z‖) ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      calc ‖g 0‖ * ((2 * (1 + ‖z‖) + ‖z‖) / (2 + ‖z‖)) ≤ ‖g 0‖ * 3 :=
            mul_le_mul_of_nonneg_left hfrac (norm_nonneg _)
        _ = 3 * ‖g 0‖ := by ring
    have hlogeq : Real.log (2 + R) = Real.log (4 + 2 * ‖z‖) := by rw [hRdef]; congr 1; ring
    have h2M : 2 * M = 2 * B' * (3 + 2 * ‖z‖) * Real.log (4 + 2 * ‖z‖) := by
      rw [hMdef, hlogeq, hRdef]; ring
    calc ‖g z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) := hbc
      _ ≤ 2 * M + 3 * ‖g 0‖ := by linarith
      _ = 2 * B' * (3 + 2 * ‖z‖) * Real.log (4 + 2 * ‖z‖) + 3 * ‖g 0‖ := by rw [h2M]
  -- The envelope `t ↦ 2 B' (3 + 2t) log (4 + 2t) + 3‖g 0‖` is nondecreasing on `[0, ∞)`.
  have hGmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      2 * B' * (3 + 2 * s) * Real.log (4 + 2 * s) + 3 * ‖g 0‖
        ≤ 2 * B' * (3 + 2 * t) * Real.log (4 + 2 * t) + 3 * ‖g 0‖ := by
    intro s t hs hst
    have hlog : Real.log (4 + 2 * s) ≤ Real.log (4 + 2 * t) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlognn : 0 ≤ Real.log (4 + 2 * s) := Real.log_nonneg (by linarith)
    have hprod : (3 + 2 * s) * Real.log (4 + 2 * s) ≤ (3 + 2 * t) * Real.log (4 + 2 * t) :=
      mul_le_mul (by linarith) hlog hlognn (by linarith)
    have := mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ) ≤ 2 * B')
    nlinarith [this]
  -- Step 2: the second derivative vanishes at every centre.
  have hsecond : ∀ c : ℂ, iteratedDeriv 2 g c = 0 := by
    intro c
    -- Cauchy's estimate at centre `c` for every radius `R`.
    have hcauchy : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv 2 g c‖
          ≤ 2 * (2 * B' * (3 + 2 * (‖c‖ + R)) * Real.log (4 + 2 * (‖c‖ + R)) + 3 * ‖g 0‖) / R ^ 2 := by
      intro R hR
      have hsph : ∀ w ∈ sphere c R,
          ‖g w‖ ≤ 2 * B' * (3 + 2 * (‖c‖ + R)) * Real.log (4 + 2 * (‖c‖ + R)) + 3 * ‖g 0‖ := by
        intro w hw
        have hwd : ‖w - c‖ = R := mem_sphere_iff_norm.1 hw
        have hwnorm : ‖w‖ ≤ ‖c‖ + R := by
          calc ‖w‖ = ‖c + (w - c)‖ := by rw [add_sub_cancel]
            _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
            _ = ‖c‖ + R := by rw [hwd]
        exact le_trans (hmod w) (hGmono _ _ (norm_nonneg w) hwnorm)
      have hcalc :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR hg.diffContOnCl hsph
      have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [hfac] at hcalc
      exact hcalc
    -- Let `R → ∞`: the right-hand side tends to `0`, so the fixed left-hand side is `≤ 0`.
    have htend :
        Tendsto
          (fun R : ℝ =>
            2 * (2 * B' * (3 + 2 * (‖c‖ + R)) * Real.log (4 + 2 * (‖c‖ + R)) + 3 * ‖g 0‖) / R ^ 2)
          atTop (𝓝 0) := by
      have hL : Tendsto (fun R : ℝ => Real.log (4 + 2 * (‖c‖ + R)) / R) atTop (𝓝 0) := by
        have hbase : Tendsto (fun u : ℝ => Real.log u / (1 * u + (-(4 + 2 * ‖c‖)))) atTop (𝓝 0) :=
          Real.tendsto_pow_log_div_mul_add_atTop 1 (-(4 + 2 * ‖c‖)) 1 one_ne_zero
            |>.congr (by intro u; simp)
        have hto : Tendsto (fun R : ℝ => 2 * R + (4 + 2 * ‖c‖)) atTop atTop :=
          Filter.tendsto_atTop_add_const_right _ (4 + 2 * ‖c‖)
            (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id)
        have hcomp2 : Tendsto (fun R : ℝ => Real.log (4 + 2 * (‖c‖ + R)) / (2 * R)) atTop (𝓝 0) := by
          refine (hbase.comp hto).congr ?_
          intro R
          simp only [Function.comp]
          rw [show (2 * R + (4 + 2 * ‖c‖)) = (4 + 2 * (‖c‖ + R)) from by ring]
          congr 1; ring
        have h2 := hcomp2.const_mul (2 : ℝ)
        simp only [mul_zero] at h2
        refine h2.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with R hR
        have : R ≠ 0 := ne_of_gt hR
        field_simp
      have hA : Tendsto (fun R : ℝ => (3 + 2 * (‖c‖ + R)) / R) atTop (𝓝 2) := by
        have hbase : Tendsto (fun R : ℝ => (3 + 2 * ‖c‖) / R + 2) atTop (𝓝 (0 + 2)) := by
          refine Tendsto.add ?_ tendsto_const_nhds
          simpa using
            (tendsto_const_nhds (x := (3 + 2 * ‖c‖)) (f := atTop)).div_atTop tendsto_id
        simp only [zero_add] at hbase
        refine hbase.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with R hR
        have : R ≠ 0 := ne_of_gt hR
        field_simp; ring
      have hAL :
          Tendsto (fun R : ℝ => (3 + 2 * (‖c‖ + R)) / R * (Real.log (4 + 2 * (‖c‖ + R)) / R))
            atTop (𝓝 0) := by
        have := hA.mul hL; simpa using this
      have hB1 :
          Tendsto
            (fun R : ℝ => 4 * B' * ((3 + 2 * (‖c‖ + R)) / R * (Real.log (4 + 2 * (‖c‖ + R)) / R)))
            atTop (𝓝 0) := by
        have := hAL.const_mul (4 * B'); simpa using this
      have hKt : Tendsto (fun R : ℝ => 6 * ‖g 0‖ / R ^ 2) atTop (𝓝 0) := by
        have hinv : Tendsto (fun R : ℝ => (R ^ 2)⁻¹) atTop (𝓝 0) :=
          Filter.Tendsto.comp tendsto_inv_atTop_zero (tendsto_pow_atTop (by norm_num))
        have := hinv.const_mul (6 * ‖g 0‖)
        simp only [mul_zero] at this
        refine this.congr ?_; intro R; ring
      have hsum := hB1.add hKt
      simp only [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with R hR
      have hRne : R ≠ 0 := ne_of_gt hR
      field_simp
      ring
    have hle : ‖iteratedDeriv 2 g c‖ ≤ 0 := by
      refine ge_of_tendsto htend ?_
      filter_upwards [eventually_gt_atTop 0] with R hR
      exact hcauchy R hR
    have : ‖iteratedDeriv 2 g c‖ = 0 := le_antisymm hle (norm_nonneg _)
    exact norm_eq_zero.1 this
  -- Step 3: vanishing second derivative ⟹ `deriv g` constant ⟹ `g` affine.
  have hid2 : ∀ c : ℂ, deriv (deriv g) c = 0 := by
    intro c
    have h := hsecond c
    rwa [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero] at h
  have hderiv_diff : Differentiable ℂ (deriv g) := fun z =>
    ((hg.analyticAt z).deriv).differentiableAt
  have hdg_const : ∀ x : ℂ, deriv g x = deriv g 0 :=
    fun x => is_const_of_deriv_eq_zero hderiv_diff hid2 x 0
  intro z
  set φ : ℂ → ℂ := fun w => g w - deriv g 0 * w with hφdef
  have hφdiff : Differentiable ℂ φ :=
    hg.sub ((differentiable_const _).mul differentiable_id)
  have hφderiv : ∀ w : ℂ, deriv φ w = 0 := by
    intro w
    have hsub : HasDerivAt φ (deriv g w - deriv g 0 * 1) w :=
      (hg w).hasDerivAt.sub (HasDerivAt.const_mul (deriv g 0) (hasDerivAt_id w))
    rw [hsub.deriv, hdg_const w]; ring
  have hφconst : φ z = φ 0 := is_const_of_deriv_eq_zero hφdiff hφderiv z 0
  have hφz : φ z = g z - deriv g 0 * z := rfl
  have hφ0 : φ 0 = g 0 := by rw [hφdef]; simp
  rw [hφz, hφ0] at hφconst
  linear_combination hφconst
