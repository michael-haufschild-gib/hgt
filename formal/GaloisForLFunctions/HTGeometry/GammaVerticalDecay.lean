import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Order.Compact
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

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
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re :=
  GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re hs


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
    ((‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ (2 : ℕ) : ℝ) : ℂ)
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
    HasDerivAt sigmoid (Real.exp v / (1 + Real.exp v) ^ (2 : ℕ)) v := by
  have hexp : HasDerivAt Real.exp (Real.exp v) v := Real.hasDerivAt_exp v
  have hden : HasDerivAt (fun u => 1 + Real.exp u) (Real.exp v) v := by
    simpa using hexp.const_add 1
  have h := hexp.div hden (one_add_exp_pos v).ne'
  refine h.congr_deriv ?_
  field_simp
  ring_nf

theorem sigmoid_strictMono : StrictMono sigmoid := by
  intro a b hab
  have h : ∀ v : ℝ, 0 < Real.exp v / (1 + Real.exp v) ^ (2 : ℕ) := by
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

section Decay

open MeasureTheory Set

theorem cpow_ofReal_exp (u : ℝ) (w : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ w = Complex.exp ((u : ℂ) * w) := by
  have hne : ((Real.exp u : ℝ) : ℂ) ≠ 0 := by
    simp
  rw [Complex.cpow_def_of_ne_zero hne]
  congr 1
  have hlog : Complex.log ((Real.exp u : ℝ) : ℂ) = ((Real.log (Real.exp u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Real.exp_pos u).le]
  rw [hlog, Real.log_exp]

/-- **Gamma on a vertical line is a Fourier integral.** -/
theorem Gamma_vertical_eq_fourier {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ∫ u : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)
          * ((Real.exp (σ * u - Real.exp u) : ℝ) : ℂ) := by
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  rw [Complex.Gamma_eq_integral (by rw [hre]; exact hσ), Complex.GammaIntegral]
  have himg : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [Set.image_univ, Real.range_exp]
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := (univ : Set ℝ)) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (Real.exp_injective.injOn)
    (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)
      * (x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))
  rw [himg] at hchange
  rw [hchange, MeasureTheory.setIntegral_univ]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show |Real.exp u| • (((Real.exp (-Real.exp u) : ℝ) : ℂ)
      * ((Real.exp u : ℝ) : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))
    = Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * ((Real.exp (σ * u - Real.exp u) : ℝ) : ℂ)
  rw [cpow_ofReal_exp u, abs_of_pos (Real.exp_pos u), Complex.real_smul]
  have h1 : ((Real.exp u : ℝ) : ℂ) = Complex.exp ((u : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
  have h2 : ((Real.exp (-Real.exp u) : ℝ) : ℂ) = Complex.exp (((-Real.exp u : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp]
  have h3 : ((Real.exp (σ * u - Real.exp u) : ℝ) : ℂ)
      = Complex.exp (((σ * u - Real.exp u : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp]
  rw [h1, h2, h3, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Gamma tends to zero along a vertical line.** -/
theorem Gamma_vertical_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
  set F : ℝ → ℂ := fun u => ((Real.exp (σ * u - Real.exp u) : ℝ) : ℂ) with hF
  have hRL := Real.tendsto_integral_exp_smul_cocompact (f := F)
  have hshift : Tendsto (fun t : ℝ => -t / (2 * Real.pi)) atTop atBot := by
    have hpi : 0 < 2 * Real.pi := by positivity
    have h1 : Tendsto (fun t : ℝ => -t) atTop atBot := tendsto_neg_atTop_atBot
    simp only [div_eq_mul_inv]
    exact h1.atBot_mul_const (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)
  have hco : Tendsto (fun t : ℝ => -t / (2 * Real.pi)) atTop (cocompact ℝ) :=
    hshift.mono_right (le_trans le_sup_left (le_of_eq cocompact_eq_atBot_atTop.symm))
  have hcomp := hRL.comp hco
  refine hcomp.congr fun t => ?_
  rw [Gamma_vertical_eq_fourier hσ t]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (Real.fourierChar (-(u * (-t / (2 * Real.pi)))) : Circle) • F u
    = Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * F u
  rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  congr 2
  push_cast
  field_simp

/-- **Gamma tends to zero along a vertical line, without vanishing.** -/
theorem Gamma_vertical_tendsto_nhdsWithin_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Gamma_vertical_tendsto_zero hσ) ?_
  filter_upwards with t
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  refine Complex.Gamma_ne_zero fun m => ?_
  intro hcon
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hre2 : ((-(m : ℂ)) : ℂ).re = -(m : ℝ) := by simp
  rw [hcon, hre2] at hre
  have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

end Decay

end GaloisForLFunctions
