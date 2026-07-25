/-
# Quantitative phase perturbations

Bourgain's proof says that a bounded Taylor-remainder multiplier can be
ignored.  Here that step is replaced by explicit norm inequalities: changing
every real phase by at most `η` changes a weighted finite exponential sum by
at most `η` times the coefficient `ℓ¹` norm, and changes an extension integral
by at most `η` times the amplitude `L¹` norm.
-/
import GaloisForLFunctions.RHTower.BourgainQuadraticTaylorControl
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Unit-circle oscillation with angular frequency normalized in radians. -/
def bourgainOscillation (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * x)

@[simp]
theorem norm_bourgainOscillation (x : ℝ) :
    ‖bourgainOscillation x‖ = 1 := by
  simp [bourgainOscillation, Complex.norm_exp_I_mul_ofReal]

/-- The unit-circle oscillation is one-Lipschitz in its real phase. -/
theorem norm_bourgainOscillation_sub_le (x y : ℝ) :
    ‖bourgainOscillation x - bourgainOscillation y‖ ≤ |x - y| := by
  rw [show bourgainOscillation x - bourgainOscillation y =
      bourgainOscillation y *
        (Complex.exp (Complex.I * (x - y)) - 1) by
    simp only [bourgainOscillation]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring]
  rw [norm_mul, norm_bourgainOscillation, one_mul]
  simpa only [Complex.ofReal_sub, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

/-- Explicit finite-sum version of the Taylor-remainder multiplier bound. -/
theorem norm_sum_weighted_bourgainOscillation_sub_le
    {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (θ ψ : ι → ℝ) {η : ℝ}
    (hphase : ∀ i ∈ s, |θ i - ψ i| ≤ η) :
    ‖(∑ i ∈ s, a i * bourgainOscillation (θ i)) -
        ∑ i ∈ s, a i * bourgainOscillation (ψ i)‖
      ≤ η * ∑ i ∈ s, ‖a i‖ := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ s,
        (a i * bourgainOscillation (θ i) -
          a i * bourgainOscillation (ψ i))‖
        ≤ ∑ i ∈ s,
            ‖a i * bourgainOscillation (θ i) -
              a i * bourgainOscillation (ψ i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖a i‖ * η := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((norm_bourgainOscillation_sub_le _ _).trans (hphase i hi))
        (norm_nonneg _)
    _ = η * ∑ i ∈ s, ‖a i‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- A phase perturbation contributes an explicit additive error to a finite
exponential sum. -/
theorem norm_sum_weighted_bourgainOscillation_le
    {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (θ ψ : ι → ℝ) {η : ℝ}
    (hphase : ∀ i ∈ s, |θ i - ψ i| ≤ η) :
    ‖∑ i ∈ s, a i * bourgainOscillation (θ i)‖
      ≤ ‖∑ i ∈ s, a i * bourgainOscillation (ψ i)‖ +
        η * ∑ i ∈ s, ‖a i‖ := by
  calc
    ‖∑ i ∈ s, a i * bourgainOscillation (θ i)‖
        ≤ ‖∑ i ∈ s, a i * bourgainOscillation (ψ i)‖ +
          ‖(∑ i ∈ s, a i * bourgainOscillation (θ i)) -
            ∑ i ∈ s, a i * bourgainOscillation (ψ i)‖ := by
      exact norm_le_norm_add_norm_sub' (E := ℂ)
        (∑ i ∈ s, a i * bourgainOscillation (θ i))
        (∑ i ∈ s, a i * bourgainOscillation (ψ i))
    _ ≤ ‖∑ i ∈ s, a i * bourgainOscillation (ψ i)‖ +
        η * ∑ i ∈ s, ‖a i‖ :=
      add_le_add le_rfl
        (norm_sum_weighted_bourgainOscillation_sub_le
          s a θ ψ hphase)

/-- Fully quantitative finite form of Bourgain's (1.21)--(1.22) multiplier
step.  A curve and its quadratic localization differ by the explicit
`N C K^{-3/2}/2` phase error. -/
theorem norm_sum_frequency_curve_le_quadraticTaylor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι)
    (aCoeff : ι → ℂ) (sample : ι → ℝ)
    (L : E →L[ℝ] ℝ)
    {f : ℝ → E} {a b C N K : ℝ}
    (hab : a ≤ b)
    (hf : ContDiffOn ℝ 3 f (Set.Icc a b))
    (hsample : ∀ i ∈ s, sample i ∈ Set.Icc a b)
    (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ Set.Icc a b,
      ‖iteratedDerivWithin 3 f (Set.Icc a b) y‖ ≤ C)
    (hN : ‖L‖ ≤ N)
    (hK : 0 ≤ K)
    (hδ : ∀ i ∈ s, sample i - a ≤ K ^ (-(1 : ℝ) / 2)) :
    ‖∑ i ∈ s,
        aCoeff i * bourgainOscillation (L (f (sample i)))‖
      ≤ ‖∑ i ∈ s,
          aCoeff i *
            bourgainOscillation
              (L (taylorWithinEval f 2 (Set.Icc a b) a (sample i)))‖ +
        (N * (C * K ^ (-(3 : ℝ) / 2) / 2)) *
          ∑ i ∈ s, ‖aCoeff i‖ := by
  apply norm_sum_weighted_bourgainOscillation_le
  intro i hi
  rw [← Real.norm_eq_abs, ← map_sub]
  exact bourgain_frequency_halfScale_quadraticTaylorWithin_remainder
    L hab hf (hsample i hi) hC0 hC hN hK (hδ i hi)

/-- Integral version of the phase-perturbation bound.  Integrability
hypotheses are stated explicitly; for Bourgain's compact intervals they
follow from continuity of the amplitude and phases. -/
theorem norm_integral_weighted_bourgainOscillation_sub_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℂ) (θ ψ : α → ℝ) {η : ℝ}
    (hg : Integrable g μ)
    (hθ : Integrable (fun t => g t * bourgainOscillation (θ t)) μ)
    (hψ : Integrable (fun t => g t * bourgainOscillation (ψ t)) μ)
    (hphase : ∀ᵐ t ∂μ, |θ t - ψ t| ≤ η) :
    ‖(∫ t, g t * bourgainOscillation (θ t) ∂μ) -
        ∫ t, g t * bourgainOscillation (ψ t) ∂μ‖
      ≤ η * ∫ t, ‖g t‖ ∂μ := by
  rw [← integral_sub hθ hψ]
  have hdom : ∀ᵐ t ∂μ,
      ‖g t * bourgainOscillation (θ t) -
          g t * bourgainOscillation (ψ t)‖ ≤ η * ‖g t‖ := by
    filter_upwards [hphase] with t ht
    rw [← mul_sub, norm_mul]
    calc
      ‖g t‖ * ‖bourgainOscillation (θ t) -
          bourgainOscillation (ψ t)‖
          ≤ ‖g t‖ * |θ t - ψ t| :=
        mul_le_mul_of_nonneg_left
          (norm_bourgainOscillation_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖g t‖ * η :=
        mul_le_mul_of_nonneg_left ht (norm_nonneg _)
      _ = η * ‖g t‖ := mul_comm _ _
  calc
    ‖∫ t,
        (g t * bourgainOscillation (θ t) -
          g t * bourgainOscillation (ψ t)) ∂μ‖
        ≤ ∫ t, η * ‖g t‖ ∂μ :=
      norm_integral_le_of_norm_le (hg.norm.const_mul η) hdom
    _ = η * ∫ t, ‖g t‖ ∂μ := by
      simpa using
        (MeasureTheory.integral_const_mul
          (μ := μ) η (fun t : α => ‖g t‖))

/-- Additive extension-integral comparison, making Bourgain's suppressed
multiplier loss explicit. -/
theorem norm_integral_weighted_bourgainOscillation_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℂ) (θ ψ : α → ℝ) {η : ℝ}
    (hg : Integrable g μ)
    (hθ : Integrable (fun t => g t * bourgainOscillation (θ t)) μ)
    (hψ : Integrable (fun t => g t * bourgainOscillation (ψ t)) μ)
    (hphase : ∀ᵐ t ∂μ, |θ t - ψ t| ≤ η) :
    ‖∫ t, g t * bourgainOscillation (θ t) ∂μ‖
      ≤ ‖∫ t, g t * bourgainOscillation (ψ t) ∂μ‖ +
        η * ∫ t, ‖g t‖ ∂μ := by
  calc
    ‖∫ t, g t * bourgainOscillation (θ t) ∂μ‖
        ≤ ‖∫ t, g t * bourgainOscillation (ψ t) ∂μ‖ +
          ‖(∫ t, g t * bourgainOscillation (θ t) ∂μ) -
            ∫ t, g t * bourgainOscillation (ψ t) ∂μ‖ := by
      exact norm_le_norm_add_norm_sub' (E := ℂ)
        (∫ t, g t * bourgainOscillation (θ t) ∂μ)
        (∫ t, g t * bourgainOscillation (ψ t) ∂μ)
    _ ≤ ‖∫ t, g t * bourgainOscillation (ψ t) ∂μ‖ +
        η * ∫ t, ‖g t‖ ∂μ :=
      add_le_add le_rfl
        (norm_integral_weighted_bourgainOscillation_sub_le
          μ g θ ψ hg hθ hψ hphase)

/-- A uniform additive phase error is harmless in every finite-measure
integer moment.  This is the explicit `Lᵖ` replacement for the smooth
multiplier suppression after Bourgain (1.23). -/
theorem integral_norm_pow_le_of_uniform_sub
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : Ω → ℂ) (p : ℕ) {E : ℝ}
    (hE : 0 ≤ E)
    (hF : Integrable (fun x => ‖F x‖ ^ p) μ)
    (hG : Integrable (fun x => ‖G x‖ ^ p) μ)
    (hsub : ∀ᵐ x ∂μ, ‖F x - G x‖ ≤ E) :
    (∫ x, ‖F x‖ ^ p ∂μ) ≤
      2 ^ (p - 1) *
        ((∫ x, ‖G x‖ ^ p ∂μ) + μ.real Set.univ * E ^ p) := by
  have hmajor :
      Integrable
        (fun x =>
          2 ^ (p - 1) * (‖G x‖ ^ p + E ^ p)) μ := by
    apply Integrable.const_mul
    exact hG.add (integrable_const (E ^ p))
  have hpoint : ∀ᵐ x ∂μ,
      ‖F x‖ ^ p ≤
        2 ^ (p - 1) * (‖G x‖ ^ p + E ^ p) := by
    filter_upwards [hsub] with x hx
    have hnorm : ‖F x‖ ≤ ‖G x‖ + E := by
      exact (norm_le_norm_add_norm_sub' (F x) (G x)).trans
        (add_le_add le_rfl hx)
    calc
      ‖F x‖ ^ p ≤ (‖G x‖ + E) ^ p :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm p
      _ ≤ 2 ^ (p - 1) * (‖G x‖ ^ p + E ^ p) :=
        add_pow_le (norm_nonneg _) hE p
  calc
    (∫ x, ‖F x‖ ^ p ∂μ) ≤
        ∫ x, 2 ^ (p - 1) * (‖G x‖ ^ p + E ^ p) ∂μ :=
      integral_mono_ae hF hmajor hpoint
    _ = 2 ^ (p - 1) *
        ((∫ x, ‖G x‖ ^ p ∂μ) + μ.real Set.univ * E ^ p) := by
      rw [integral_const_mul, integral_add hG (integrable_const (E ^ p)),
        integral_const]
      ring

end

end RHTower
