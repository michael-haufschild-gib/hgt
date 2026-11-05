import GaloisForLFunctions.ArithmeticProduction.TheLengthPrecisionLaw
import GaloisForLFunctions.RHTower.Sieve.GallagherReverse

/-!
# The Selberg integral dictionary

Above the window a second moment stops being a sum over moduli and becomes a statement about short intervals.  For the weight `a` and the logarithmic
window of length `δ`, the **Selberg integral** is

  `S_a(N, δ) = ∫_ℝ |Σ_{n ≤ N, u < log n ≤ u+δ} a(n) n^{−½}|² du`.

* **Gallagher's direction** (`integral_norm_sq_linePoly_le_selbergIntegral`).  `∫_{−T}^{T}|P_a|² ≤ (5π/2) T² S_a(N, 1/T)`.
* **Resonance in short intervals** (`le_selbergIntegral_resonant`).  The resonant weight has `S_a(N, 1/T) ≥ ε²N^{1−2η}/(10π T² log N)`.

An upper bound for the second moment at length `T^θ`, `θ > 1`, is therefore a question about the variance of `a` in intervals of relative length `1/T`.  In this form the length–precision
threshold reads: the variance of primes in such intervals sees the term of a zero `1 − η + iγ`, `γ ≍ T`, at intervals located below `N`, once `N^{1−2η}` exceeds `T`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

/-- The coefficients `a(n) n^{−½}`. -/
def selbergCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ := a n * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- The Selberg integral: the mean square of `a(n) n^{−½}` in logarithmic windows of length `δ`. -/
def selbergIntegral (a : ℕ → ℂ) (N : ℕ) (δ : ℝ) : ℝ :=
  ∫ u : ℝ, ‖Sieve.logWindowSum (selbergCoeff a) (Finset.Icc 1 N) δ u‖ ^ (2 : ℕ)

/-- The line polynomial in the additive frequency variable. -/
theorem linePoly_eq_logPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    linePoly a N t = Sieve.logPoly (selbergCoeff a) (Finset.Icc 1 N) (-(1 / (2 * Real.pi)) * t) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold linePoly
  rw [edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1)]
  unfold cdpoly cdterm Sieve.logPoly selbergCoeff
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 3
  field_simp

/-- **Gallagher's direction of the dictionary.** -/
theorem integral_norm_sq_linePoly_le_selbergIntegral (a : ℕ → ℂ) (N : ℕ) {T T₁ T₂ : ℝ} (hT : 0 < T)
    (h1 : -T ≤ T₁) (h12 : T₁ ≤ T₂) (h2 : T₂ ≤ T) :
    (∫ t in T₁..T₂, ‖linePoly a N t‖ ^ 2) ≤ 5 * Real.pi / 2 * T ^ 2 * selbergIntegral a N (1 / T) := by
  have hπ := Real.pi_pos
  have hcont : Continuous fun t => ‖linePoly a N t‖ ^ 2 := (continuous_linePoly a N).norm.pow 2
  have hnonneg : ∀ t : ℝ, (0 : ℝ) ≤ ‖linePoly a N t‖ ^ 2 := fun t => by positivity
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) h1 h12 h2
    (Filter.Eventually.of_forall hnonneg) (hcont.intervalIntegrable (-T) T)
  refine hmono.trans ?_
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = T / (2 * Real.pi) := ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [hW]; positivity
  have hk : -(1 / (2 * Real.pi)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, one_div, inv_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact hπ.ne'
  have hchange : (∫ t in (-T)..T, ‖linePoly a N t‖ ^ 2) =
      2 * Real.pi * ∫ w in Set.Icc (-W) W,
        ‖Sieve.logPoly (selbergCoeff a) (Finset.Icc 1 N) w‖ ^ (2 : ℕ) := by
    simp_rw [linePoly_eq_logPoly]
    rw [intervalIntegral.integral_comp_mul_left
      (fun w => ‖Sieve.logPoly (selbergCoeff a) (Finset.Icc 1 N) w‖ ^ 2) hk]
    have hl : -(1 / (2 * Real.pi)) * -T = W := by
      rw [hW]
      field_simp
    have hr : -(1 / (2 * Real.pi)) * T = -W := by
      rw [hW]
      field_simp
    rw [hl, hr, intervalIntegral.integral_symm, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith), smul_eq_mul, inv_neg, one_div, inv_inv]
    ring
  rw [hchange]
  have hδ : (0 : ℝ) < 1 / T := by positivity
  have hb := Sieve.integral_Icc_normSq_logPoly_le_window (selbergCoeff a) (Finset.Icc 1 N) (W := W) hδ
    (by
      rw [hW]
      have : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 := by
        field_simp
      exact this.le)
  have h3 := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi)
  refine h3.trans (le_of_eq ?_)
  unfold selbergIntegral
  field_simp
  ring

/-- **The resonance in short intervals.** -/
theorem le_selbergIntegral_resonant {ε η γ T : ℝ} {N : ℕ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hN : 2 ≤ N) (hT : 0 < T)
    (h1 : 1 / (2 * Real.log N) - T ≤ γ) (h2 : γ + 1 / (2 * Real.log N) ≤ T) :
    ε ^ 2 * (N : ℝ) ^ (1 - 2 * η) / (4 * Real.log N) ≤
      5 * Real.pi / 2 * T ^ 2 * selbergIntegral (resonantWeight ε η γ) N (1 / T) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  have hδ : 0 < 1 / (2 * Real.log N) := by positivity
  have hres := resonant_second_moment_ge (T₁ := -T) (T₂ := T) hε hη hN (by linarith) h2
  exact hres.trans (integral_norm_sq_linePoly_le_selbergIntegral _ N hT le_rfl (by linarith) le_rfl)

end GaloisForLFunctions.ArithmeticProduction
