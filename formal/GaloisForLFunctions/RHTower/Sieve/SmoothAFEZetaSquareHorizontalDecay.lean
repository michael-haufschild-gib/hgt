import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquarePoleDecomposition
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound

/-!
# Horizontal Gaussian decay for the zeta-square contour

The additional zeta factor raises only the height polynomial from quadratic to quartic; the
single Gaussian still annihilates both horizontal interval integrals.
-/

noncomputable section

open Filter Topology Complex Set

namespace RHTower.Sieve

theorem tendsto_shifted_quartic_mul_exp_neg_sq (A C : ℝ) :
    Tendsto
      (fun T : ℝ =>
        C * ((1 + A + T) ^ (2 : ℕ) * (4 + A + T) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))))
      atTop (𝓝 0) := by
  let a : ℝ := 1 + A
  let b : ℝ := 4 + A
  have h0 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    0 (b := 1) (by norm_num)
  have h1 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    1 (b := 1) (by norm_num)
  have h2 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    2 (b := 1) (by norm_num)
  have h3 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    3 (b := 1) (by norm_num)
  have h4 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    4 (b := 1) (by norm_num)
  have hsum :=
    (((h4.add (h3.const_mul (2 * (a + b)))).add
      (h2.const_mul (a ^ (2 : ℕ) + 4 * a * b + b ^ (2 : ℕ)))).add
      (h1.const_mul (2 * a * b * (a + b)))).add
      (h0.const_mul (a ^ (2 : ℕ) * b ^ (2 : ℕ)))
  have hscaled := hsum.const_mul C
  simpa only [one_mul, zero_add, mul_zero, neg_one_mul] using hscaled.congr'
    (Filter.Eventually.of_forall fun T => by
      dsimp only [a, b]
      ring)


theorem exists_norm_smoothAFEZetaSquareMellinIntegrand_horizontal_le
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u T : ℝ},
      -1 ≤ u → u ≤ 1 → 1 ≤ |T| → 2 ≤ |tau + T| →
      ‖smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
        C * ((1 + |tau + T|) ^ (2 : ℕ) * (4 + |tau + T|) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))) := by
  let B : ℝ :=
    5 * Real.exp 2 * Real.exp |Real.log x| * Real.exp 1
  let Z : ℝ := 5 * Real.exp 2
  let C : ℝ := B * Z
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro u T huLow huHigh hT hheight
  have hsingle := norm_smoothAFEZetaMellinIntegrand_horizontal_le
    hx tau huLow huHigh hT hheight
  have hzeta :
      ‖riemannZeta
          (linePt tau + ((u : ℂ) + (T : ℂ) * I))‖ ≤
        Z * (1 + |tau + T|) * (4 + |tau + T|) := by
    rw [linePt_add_horizontal_eq]
    have hraw := norm_riemannZeta_le_smoothAFE_strip
      (σ := 1 / 2 + u) (t := tau + T)
      (by linarith) (by linarith) hheight
    simpa [Z] using hraw
  rw [smoothAFEZetaSquareMellinIntegrand_eq_single_mul_zeta, norm_mul]
  calc
    ‖smoothAFEZetaMellinIntegrand (linePt tau) x
          (↑u + ↑T * I)‖ *
        ‖riemannZeta (linePt tau + (↑u + ↑T * I))‖
      ≤ (B * ((1 + |tau + T|) * (4 + |tau + T|) *
          Real.exp (-(T ^ (2 : ℕ))))) *
        (Z * (1 + |tau + T|) * (4 + |tau + T|)) := by
          dsimp only [B]
          gcongr
    _ = C * ((1 + |tau + T|) ^ (2 : ℕ) * (4 + |tau + T|) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))) := by
      dsimp only [C]
      ring

theorem tendsto_smoothAFEZetaSquareMellinIntegrand_horizontal_top
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-1)..1,
          smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_norm_smoothAFEZetaSquareMellinIntegrand_horizontal_le hx tau
  have hmajor :
      Tendsto
        (fun T : ℝ =>
          (2 * C) * ((1 + |tau| + T) ^ (2 : ℕ) * (4 + |tau| + T) ^ (2 : ℕ) *
            Real.exp (-(T ^ (2 : ℕ)))))
        atTop (𝓝 0) :=
    tendsto_shifted_quartic_mul_exp_neg_sq |tau| (2 * C)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|tau| + 2))] with T hT
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTlarge : |tau| + 2 ≤ T := le_trans (le_max_right _ _) hT
  have hTabs : |T| = T := abs_of_nonneg (zero_le_one.trans hT1)
  have hheight : 2 ≤ |tau + T| := by
    have htri : |T| ≤ |tau + T| + |tau| := by
      have := abs_sub_le (tau + T) 0 tau
      simpa only [sub_zero, add_sub_cancel_left, zero_sub, abs_neg] using this
    rw [hTabs] at htri
    linarith
  have hheightUpper : |tau + T| ≤ |tau| + T := by
    calc
      |tau + T| ≤ |tau| + |T| := abs_add_le tau T
      _ = |tau| + T := by rw [hTabs]
  have hpoint : ∀ u ∈ uIoc (-1 : ℝ) 1,
      ‖smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
        C * ((1 + |tau| + T) ^ (2 : ℕ) * (4 + |tau| + T) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))) := by
    intro u hu
    have hu' : -1 ≤ u ∧ u ≤ 1 := by
      have h := (by simpa [mem_uIcc] using hu : -1 < u ∧ u ≤ 1)
      exact ⟨h.1.le, h.2⟩
    have hraw := hbase hu'.1 hu'.2 (by rw [hTabs]; exact hT1) hheight
    have hfirst : 1 + |tau + T| ≤ 1 + |tau| + T := by linarith
    have hsecond : 4 + |tau + T| ≤ 4 + |tau| + T := by linarith
    have hp1 : (1 + |tau + T|) ^ (2 : ℕ) ≤ (1 + |tau| + T) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (by positivity) hfirst 2
    have hp2 : (4 + |tau + T|) ^ (2 : ℕ) ≤ (4 + |tau| + T) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (by positivity) hsecond 2
    exact hraw.trans (by gcongr)
  calc
    ‖∫ u : ℝ in (-1)..1,
        smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) + (T : ℂ) * I)‖
      ≤ C * ((1 + |tau| + T) ^ (2 : ℕ) * (4 + |tau| + T) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))) * |(1 : ℝ) - (-1)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (2 * C) * ((1 + |tau| + T) ^ (2 : ℕ) * (4 + |tau| + T) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))) := by
      norm_num
      ring

theorem tendsto_smoothAFEZetaSquareMellinIntegrand_horizontal_bottom
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-1)..1,
          smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_norm_smoothAFEZetaSquareMellinIntegrand_horizontal_le hx tau
  have hmajor :
      Tendsto
        (fun T : ℝ =>
          (2 * C) * ((1 + |tau| + T) ^ (2 : ℕ) * (4 + |tau| + T) ^ (2 : ℕ) *
            Real.exp (-(T ^ (2 : ℕ)))))
        atTop (𝓝 0) :=
    tendsto_shifted_quartic_mul_exp_neg_sq |tau| (2 * C)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|tau| + 2))] with T hT
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTlarge : |tau| + 2 ≤ T := le_trans (le_max_right _ _) hT
  have hTabs : |T| = T := abs_of_nonneg (zero_le_one.trans hT1)
  have hheight : 2 ≤ |tau - T| := by
    have htri : |T| ≤ |tau - T| + |tau| := by
      have := abs_sub_le tau 0 (tau - T)
      simpa only [sub_zero, zero_sub, abs_neg, sub_sub_cancel, add_comm] using this
    rw [hTabs] at htri
    linarith
  have hheightUpper : |tau - T| ≤ |tau| + T := by
    calc
      |tau - T| = |tau + (-T)| := by rw [sub_eq_add_neg]
      _ ≤ |tau| + |-T| := abs_add_le tau (-T)
      _ = |tau| + T := by rw [abs_neg, hTabs]
  have hpoint : ∀ u ∈ uIoc (-1 : ℝ) 1,
      ‖smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) - (T : ℂ) * I)‖ ≤
        C * ((1 + |tau| + T) ^ (2 : ℕ) * (4 + |tau| + T) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))) := by
    intro u hu
    have hu' : -1 ≤ u ∧ u ≤ 1 := by
      have h := (by simpa [mem_uIcc] using hu : -1 < u ∧ u ≤ 1)
      exact ⟨h.1.le, h.2⟩
    have hraw := hbase hu'.1 hu'.2
      (T := -T) (by simpa [hTabs] using hT1)
      (by simpa only [sub_eq_add_neg] using hheight)
    have hraw' :
        ‖smoothAFEZetaSquareMellinIntegrand (linePt tau) x
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
          C * ((1 + |tau - T|) ^ (2 : ℕ) * (4 + |tau - T|) ^ (2 : ℕ) *
            Real.exp (-(T ^ (2 : ℕ)))) := by
      simpa [sub_eq_add_neg, ofReal_neg, neg_sq] using hraw
    have hfirst : 1 + |tau - T| ≤ 1 + |tau| + T := by linarith
    have hsecond : 4 + |tau - T| ≤ 4 + |tau| + T := by linarith
    have hp1 : (1 + |tau - T|) ^ (2 : ℕ) ≤ (1 + |tau| + T) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (by positivity) hfirst 2
    have hp2 : (4 + |tau - T|) ^ (2 : ℕ) ≤ (4 + |tau| + T) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (by positivity) hsecond 2
    exact hraw'.trans (by gcongr)
  calc
    ‖∫ u : ℝ in (-1)..1,
        smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          ((u : ℂ) - (T : ℂ) * I)‖
      ≤ C * ((1 + |tau| + T) ^ (2 : ℕ) * (4 + |tau| + T) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))) * |(1 : ℝ) - (-1)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (2 * C) * ((1 + |tau| + T) ^ (2 : ℕ) * (4 + |tau| + T) ^ (2 : ℕ) *
          Real.exp (-(T ^ (2 : ℕ)))) := by
      norm_num
      ring


end RHTower.Sieve
