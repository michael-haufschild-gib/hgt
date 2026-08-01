import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Gamma on a vertical line, through the Beta integral

On a vertical line the Gamma values at conjugate points are conjugate, so the squared modulus of
`Γ(σ + it)` is `Γ(σ + it) Γ(σ − it)`, which the Beta identity turns into `Γ(2σ)` times a Beta
integral over the unit interval.  Substituting the logistic map turns that Beta integral into a
Fourier integral along the line — the substitution basics are established here — so the decay of
`Γ` on vertical lines becomes the Riemann–Lebesgue lemma.

This is the analytic input the monomial valuation theorem of eq. (3) consumes: `Γ(σ + it) → 0` as the
imaginary part grows.
-/

open Filter Topology MeasureTheory intervalIntegral

namespace GaloisForLFunctions

open Set

/-- **The Gamma function is dominated by its real part's Gamma value.** -/
theorem norm_Gamma_le_real_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
  have hx0 : (0:ℝ) < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]


/-- On a vertical line the Gamma values at conjugate points are conjugate. -/
theorem Gamma_conj_vertical (σ t : ℝ) :
    Complex.Gamma ((σ : ℂ) - (t : ℂ) * Complex.I)
      = (starRingEnd ℂ) (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hconj : (starRingEnd ℂ) ((σ : ℂ) + (t : ℂ) * Complex.I)
      = (σ : ℂ) - (t : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [← hconj, Complex.Gamma_conj]

/-- **The squared modulus of Gamma on a vertical line is a Beta integral.** -/
theorem normSq_Gamma_vertical {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ((‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)
      = Complex.Gamma ((2 * σ : ℝ) : ℂ)
        * Complex.betaIntegral ((σ : ℂ) + (t : ℂ) * Complex.I)
          ((σ : ℂ) - (t : ℂ) * Complex.I) := by
  have hre1 : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
  have hre2 : (((σ : ℂ) - (t : ℂ) * Complex.I)).re = σ := by simp
  have hsum : ((σ : ℂ) + (t : ℂ) * Complex.I) + ((σ : ℂ) - (t : ℂ) * Complex.I)
      = ((2 * σ : ℝ) : ℂ) := by
    push_cast
    ring
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (σ : ℂ) + (t : ℂ) * Complex.I)
    (t := (σ : ℂ) - (t : ℂ) * Complex.I) (by rw [hre1]; exact hσ) (by rw [hre2]; exact hσ)
  rw [hsum] at hbeta
  rw [← hbeta, Gamma_conj_vertical σ t, Complex.mul_conj']
  push_cast
  ring


section Logistic

open Real Set

/-- The logistic substitution carrying the line onto the unit interval. -/
noncomputable def sigmoid (v : ℝ) : ℝ := Real.exp v / (1 + Real.exp v)

theorem one_add_exp_pos (v : ℝ) : 0 < 1 + Real.exp v := by positivity

theorem sigmoid_pos (v : ℝ) : 0 < sigmoid v := by
  rw [sigmoid]
  positivity

theorem sigmoid_lt_one (v : ℝ) : sigmoid v < 1 := by
  rw [sigmoid, div_lt_one (one_add_exp_pos v)]
  linarith

theorem one_sub_sigmoid (v : ℝ) : 1 - sigmoid v = 1 / (1 + Real.exp v) := by
  rw [sigmoid]
  field_simp
  ring

theorem hasDerivAt_sigmoid (v : ℝ) :
    HasDerivAt sigmoid (Real.exp v / (1 + Real.exp v) ^ 2) v := by
  have hexp : HasDerivAt Real.exp (Real.exp v) v := Real.hasDerivAt_exp v
  have hden : HasDerivAt (fun u => 1 + Real.exp u) (Real.exp v) v := by
    simpa using hexp.const_add 1
  have h := hexp.div hden (one_add_exp_pos v).ne'
  refine h.congr_deriv ?_
  field_simp
  ring_nf

theorem sigmoid_strictMono : StrictMono sigmoid := by
  intro a b hab
  have h : ∀ v : ℝ, 0 < Real.exp v / (1 + Real.exp v) ^ 2 := by
    intro v
    positivity
  exact strictMono_of_deriv_pos (fun v => by
    rw [(hasDerivAt_sigmoid v).deriv]
    exact h v) hab

theorem sigmoid_range : Set.range sigmoid = Set.Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨sigmoid_pos v, sigmoid_lt_one v⟩
  · rintro ⟨hx0, hx1⟩
    refine ⟨Real.log (x / (1 - x)), ?_⟩
    have hpos : 0 < x / (1 - x) := by
      apply div_pos hx0
      linarith
    rw [sigmoid, Real.exp_log hpos]
    field_simp
    ring

end Logistic

end GaloisForLFunctions
