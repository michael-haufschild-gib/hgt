import GaloisForLFunctions.HTGeometry.GammaCyclicSpectralMeasure

/-!
# Odd spectral synthesis

A synthesis `∑ c_d v_d` of vectors whose Gram matrix is the odd spectral kernel

```text
⟪v_d, v_e⟫ = 2 ∫ sin(h_d y) sin(h_e y) dν(y)
```

has squared norm equal to twice the `L²(ν)` energy of the associated sine series:

```text
‖∑ c_d v_d‖² = 2 ∫ (∑ c_d sin(h_d y))² dν(y) .
```

Both sides are computed from absolute summability of the coefficients: the Hilbert norm expands as a
double series of inner products, and the two interchanges of sum and integral are dominated by
`(∑ |c_d|)² ν(ℝ)`.
-/

open MeasureTheory

namespace HTGeometry

noncomputable section

/-! ### The Hilbert side -/

/-- The squared norm of an absolutely convergent synthesis is the double series of its Gram
entries. -/
theorem norm_sq_tsum_eq_tsum_inner {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] (y : ℕ → K) (hy : Summable y) :
    ‖∑' d, y d‖ ^ 2 = ∑' e, ∑' d, (inner ℝ (y e) (y d) : ℝ) := by
  have hS : ∀ w : K, (inner ℝ w (∑' e, y e) : ℝ) = ∑' e, (inner ℝ w (y e) : ℝ) :=
    fun w => (innerSL ℝ w).map_tsum hy
  calc ‖∑' d, y d‖ ^ 2 = (inner ℝ (∑' d, y d) (∑' e, y e) : ℝ) := by
        rw [real_inner_self_eq_norm_sq]
    _ = ∑' e, (inner ℝ (∑' d, y d) (y e) : ℝ) := hS _
    _ = ∑' e, ∑' d, (inner ℝ (y e) (y d) : ℝ) := by
        refine tsum_congr fun e => ?_
        rw [real_inner_comm]
        exact hS (y e)

/-! ### The sine series -/

variable (c h : ℕ → ℝ)

/-- The sine series attached to a summable coefficient family. -/
def sinSeries (y : ℝ) : ℝ := ∑' d, c d * Real.sin (h d * y)

theorem norm_sin_term_le (d : ℕ) (y : ℝ) : ‖c d * Real.sin (h d * y)‖ ≤ |c d| := by
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |Real.sin (h d * y)| ≤ 1 := Real.abs_sin_le_one _
  nlinarith [abs_nonneg (c d), abs_nonneg (Real.sin (h d * y))]

theorem summable_sin_term (hc : Summable fun d => |c d|) (y : ℝ) :
    Summable fun d => c d * Real.sin (h d * y) :=
  Summable.of_norm_bounded hc fun d => norm_sin_term_le c h d y

theorem continuous_sinSeries (hc : Summable fun d => |c d|) : Continuous (sinSeries c h) := by
  refine continuous_tsum (fun _ => by fun_prop) hc ?_
  intro d y
  exact norm_sin_term_le c h d y

theorem summable_norm_sin_term (hc : Summable fun d => |c d|) (y : ℝ) :
    Summable fun d => ‖c d * Real.sin (h d * y)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => norm_sin_term_le c h d y) hc

theorem abs_sinSeries_le (hc : Summable fun d => |c d|) (y : ℝ) :
    |sinSeries c h y| ≤ ∑' d, |c d| := by
  have hnorm := summable_norm_sin_term c h hc y
  calc |sinSeries c h y| = ‖∑' d, c d * Real.sin (h d * y)‖ := by
        rw [sinSeries, Real.norm_eq_abs]
    _ ≤ ∑' d, ‖c d * Real.sin (h d * y)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' d, |c d| := Summable.tsum_mono hnorm hc fun d => norm_sin_term_le c h d y

/-! ### Interchanging the sum and the integral -/

/-- Uniform domination lets the integral pass through an infinite sum. -/
theorem integral_tsum_of_bounded {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℕ → ℝ → ℝ} {u : ℕ → ℝ}
    (hmeas : ∀ d, AEStronglyMeasurable (f d) ν) (hu : Summable u)
    (hbound : ∀ d y, ‖f d y‖ ≤ u d) :
    (∫ y, (∑' d, f d y) ∂ν) = ∑' d, ∫ y, f d y ∂ν := by
  have hunn : ∀ d, (0 : ℝ) ≤ u d := fun d => le_trans (norm_nonneg _) (hbound d 0)
  refine integral_tsum hmeas ?_
  have hstep : ∀ d, (∫⁻ y, ‖f d y‖ₑ ∂ν) ≤ ENNReal.ofReal (u d) * ν Set.univ := by
    intro d
    calc (∫⁻ y, ‖f d y‖ₑ ∂ν) ≤ ∫⁻ _ : ℝ, ENNReal.ofReal (u d) ∂ν := by
          refine lintegral_mono fun y => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hbound d y)
      _ = ENNReal.ofReal (u d) * ν Set.univ := by rw [lintegral_const]
  have hsum : (∑' d, ∫⁻ y, ‖f d y‖ₑ ∂ν) ≤ (∑' d, ENNReal.ofReal (u d)) * ν Set.univ := by
    rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_le_tsum hstep
  refine ne_top_of_le_ne_top ?_ hsum
  refine ENNReal.mul_ne_top ?_ (measure_ne_top ν Set.univ)
  rw [← ENNReal.ofReal_tsum_of_nonneg hunn hu]
  exact ENNReal.ofReal_ne_top

/-! ### The energy of the sine series -/

variable (c h : ℕ → ℝ)

theorem integral_sinSeries_sq {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hc : Summable fun d => |c d|) :
    (∫ y, (sinSeries c h y) ^ 2 ∂ν)
      = ∑' d, ∑' e, c d * c e * ∫ y, Real.sin (h d * y) * Real.sin (h e * y) ∂ν := by
  have hcont := continuous_sinSeries c h hc
  set C : ℝ := ∑' d, |c d| with hC
  have hCnn : (0 : ℝ) ≤ C := tsum_nonneg fun d => abs_nonneg _
  have hsplit : ∀ y : ℝ, (sinSeries c h y) ^ 2
      = ∑' d, (c d * Real.sin (h d * y)) * sinSeries c h y := by
    intro y
    rw [tsum_mul_right, ← sinSeries, sq]
  have hstep1 : (∫ y, (sinSeries c h y) ^ 2 ∂ν)
      = ∑' d, ∫ y, (c d * Real.sin (h d * y)) * sinSeries c h y ∂ν := by
    rw [show (fun y => (sinSeries c h y) ^ 2)
        = fun y => ∑' d, (c d * Real.sin (h d * y)) * sinSeries c h y from funext hsplit]
    refine integral_tsum_of_bounded (u := fun d => |c d| * C) ?_ (hc.mul_right C) ?_
    · intro d
      exact (Continuous.aestronglyMeasurable (by fun_prop))
    · intro d y
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |c d * Real.sin (h d * y)| ≤ |c d| := norm_sin_term_le c h d y
      have h2 : |sinSeries c h y| ≤ C := abs_sinSeries_le c h hc y
      nlinarith [abs_nonneg (c d * Real.sin (h d * y)), abs_nonneg (sinSeries c h y),
        abs_nonneg (c d)]
  rw [hstep1]
  refine tsum_congr fun d => ?_
  have hinner : ∀ y : ℝ, (c d * Real.sin (h d * y)) * sinSeries c h y
      = ∑' e, (c d * Real.sin (h d * y)) * (c e * Real.sin (h e * y)) := by
    intro y
    rw [sinSeries, tsum_mul_left]
  rw [show (fun y => (c d * Real.sin (h d * y)) * sinSeries c h y)
      = fun y => ∑' e, (c d * Real.sin (h d * y)) * (c e * Real.sin (h e * y)) from funext hinner]
  rw [integral_tsum_of_bounded (u := fun e => |c d| * |c e|)
    (fun e => Continuous.aestronglyMeasurable (by fun_prop)) (hc.mul_left _) ?_]
  · refine tsum_congr fun e => ?_
    rw [show (fun y => (c d * Real.sin (h d * y)) * (c e * Real.sin (h e * y)))
        = fun y => (c d * c e) * (Real.sin (h d * y) * Real.sin (h e * y)) by
      funext y
      ring]
    rw [integral_const_mul]
  · intro e y
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |c d * Real.sin (h d * y)| ≤ |c d| := norm_sin_term_le c h d y
    have h2 : |c e * Real.sin (h e * y)| ≤ |c e| := norm_sin_term_le c h e y
    nlinarith [abs_nonneg (c d * Real.sin (h d * y)), abs_nonneg (c e * Real.sin (h e * y)),
      abs_nonneg (c d), abs_nonneg (c e)]

/-! ### The synthesis norm -/

/-- **Odd spectral synthesis.**  A synthesis whose Gram matrix is the odd spectral kernel has
squared norm twice the `L²(ν)` energy of its sine series. -/
theorem norm_sq_oddSynthesis {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] {ν : Measure ℝ} [IsFiniteMeasure ν] (v : ℕ → K)
    (hc : Summable fun d => |c d|)
    (hgram : ∀ d e, (inner ℝ (v d) (v e) : ℝ)
      = 2 * ∫ y, Real.sin (h d * y) * Real.sin (h e * y) ∂ν)
    (hsum : Summable fun d => c d • v d) :
    ‖∑' d, c d • v d‖ ^ 2 = 2 * ∫ y, (sinSeries c h y) ^ 2 ∂ν := by
  rw [norm_sq_tsum_eq_tsum_inner _ hsum, integral_sinSeries_sq c h hc]
  have hentry : ∀ e d : ℕ, (inner ℝ (c e • v e) (c d • v d) : ℝ)
      = 2 * (c e * c d * ∫ y, Real.sin (h e * y) * Real.sin (h d * y) ∂ν) := by
    intro e d
    rw [real_inner_smul_left, real_inner_smul_right, hgram e d]
    ring
  calc (∑' e, ∑' d, (inner ℝ (c e • v e) (c d • v d) : ℝ))
      = ∑' e, ∑' d, 2 * (c e * c d * ∫ y, Real.sin (h e * y) * Real.sin (h d * y) ∂ν) := by
        exact tsum_congr fun e => tsum_congr fun d => hentry e d
    _ = 2 * ∑' e, ∑' d, c e * c d * ∫ y, Real.sin (h e * y) * Real.sin (h d * y) ∂ν := by
        rw [← tsum_mul_left]
        exact tsum_congr fun e => tsum_mul_left

end

end HTGeometry
