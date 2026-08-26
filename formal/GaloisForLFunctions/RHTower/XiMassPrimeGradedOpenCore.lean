import GaloisForLFunctions.RHTower.XiMassPrimeOpenCore
import GaloisForLFunctions.RHTower.XiMassGradedTraceZeroFreeDistortionUniversalityLaw

/-!
# Exact graded growth law for the mass--Xi prime source

The complete von-Mangoldt bottom integral carries the full exponential-type information of the
mass-shifted Xi divisor.  The archimedean channel is uniformly bounded, so it does not alter any
nonnegative exponential growth exponent.  Consequently prime-source growth
`O(exp (lam * |u|))` on any fixed positive complex-time line is equivalent to the pointwise mass
displacement bound `|Im p| <= lam`.

The contrapositive is quantitative: one mass displacement larger than `lam` forces the prime
integral above every proposed `C * exp (lam * |u|)` envelope somewhere on that line.  At `lam = 0`
this gives an exact source-side dichotomy between RH and cofinal unboundedness.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Growth of the literal von-Mangoldt integral at exponent `lam` on one fixed positive line. -/
def XiMassBottomPrimeLineGrowth (a c σ lam : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I)‖ ≤
      C * Real.exp (lam * |u|)

/-- Fixed-line exponential growth of the mass trace. -/
def XiMassTraceFixedLineGrowth (a σ lam : ℝ) (ha : 1 / 2 ≤ a) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖(xiMassFamily ha).traceC ((σ : ℂ) + u * I)‖ ≤
      C * Real.exp (lam * |u|)

/-- The bounded Gamma channel preserves every nonnegative exponential growth class exactly. -/
theorem xiMassBottomPrimeLineGrowth_iff_xiMassTraceFixedLineGrowth
    {a c σ lam : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hσ : 0 < σ) (hlam : 0 ≤ lam) :
    XiMassBottomPrimeLineGrowth a c σ lam ↔
      XiMassTraceFixedLineGrowth a σ lam (show 1 / 2 ≤ a by linarith) := by
  let B : ℝ := xiMassBottomArchUniformBound a σ
  have hB : 0 ≤ B := xiMassBottomArchUniformBound_nonneg
    (show 0 < a by linarith) hσ
  have hE : ∀ u : ℝ, 1 ≤ Real.exp (lam * |u|) :=
    fun u => Real.one_le_exp (mul_nonneg hlam (abs_nonneg u))
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖(2 * Real.pi * I : ℂ)⁻¹ * 2‖ * (C + B), fun u => ?_⟩
    let τ : ℂ := (σ : ℂ) + u * I
    let E : ℝ := Real.exp (lam * |u|)
    have hτ : 0 < τ.re := by
      dsimp only [τ]
      simp [Complex.mul_re]
      exact hσ
    have hBE : B ≤ B * E := by
      exact le_mul_of_one_le_right hB (hE u)
    have hsource : ‖∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x‖ ≤
        (C + B) * E := by
      rw [integral_xiMassBottomSourceIntegrand_eq_prime_add_arch hhalf hca hτ]
      calc
        ‖-I * xiMassBottomPrimeIntegral a c τ +
            I * xiMassBottomArchIntegral a c τ‖ ≤
          ‖-I * xiMassBottomPrimeIntegral a c τ‖ +
            ‖I * xiMassBottomArchIntegral a c τ‖ := norm_add_le _ _
        _ = ‖xiMassBottomPrimeIntegral a c τ‖ +
            ‖xiMassBottomArchIntegral a c τ‖ := by simp
        _ ≤ C * E + B := add_le_add (hC u)
          (norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hσ)
        _ ≤ C * E + B * E := add_le_add_right hBE _
        _ = (C + B) * E := by ring
    rw [xiMassTraceC_eq_normalizedBottomEulerContour hhalf hca hτ,
      normalizedXiMassBottomEulerContour]
    rw [show (2 * Real.pi * I : ℂ)⁻¹ *
        (2 * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x)) =
        ((2 * Real.pi * I : ℂ)⁻¹ * 2) *
          (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) by ring,
      norm_mul]
    calc
      ‖(2 * Real.pi * I : ℂ)⁻¹ * 2‖ *
          ‖∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x‖ ≤
        ‖(2 * Real.pi * I : ℂ)⁻¹ * 2‖ * ((C + B) * E) :=
          mul_le_mul_of_nonneg_left hsource (norm_nonneg _)
      _ = (‖(2 * Real.pi * I : ℂ)⁻¹ * 2‖ * (C + B)) * E := by ring
  · rintro ⟨C, hC⟩
    refine ⟨‖(Real.pi : ℂ) * I‖ * C + B, fun u => ?_⟩
    let τ : ℂ := (σ : ℂ) + u * I
    let E : ℝ := Real.exp (lam * |u|)
    have hτ : 0 < τ.re := by
      dsimp only [τ]
      simp [Complex.mul_re]
      exact hσ
    have hBE : B ≤ B * E := by
      exact le_mul_of_one_le_right hB (hE u)
    rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ]
    calc
      ‖I * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) +
          xiMassBottomArchIntegral a c τ‖ ≤
        ‖I * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x)‖ +
          ‖xiMassBottomArchIntegral a c τ‖ := norm_add_le _ _
      _ = ‖∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x‖ +
          ‖xiMassBottomArchIntegral a c τ‖ := by simp
      _ ≤ ‖(Real.pi : ℂ) * I‖ * (C * E) + B := by
        apply add_le_add
        · rw [integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hhalf hca hτ,
            norm_mul]
          exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _)
        · exact norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hσ
      _ ≤ ‖(Real.pi : ℂ) * I‖ * (C * E) + B * E := add_le_add_right hBE _
      _ = (‖(Real.pi : ℂ) * I‖ * C + B) * E := by ring

/-- **Exact source type law.**  Prime growth with exponent `lam` on a fixed positive line holds
exactly when every mass-shifted Xi point has transverse displacement at most `lam`. -/
theorem xiMassBottomPrimeLineGrowth_iff_mass_displacement_le
    {a c σ lam : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hσ : 0 < σ) (hlam : 0 ≤ lam) :
    XiMassBottomPrimeLineGrowth a c σ lam ↔
      ∀ q : XiZeroCopy, |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| ≤ lam := by
  have haHalf : 1 / 2 ≤ a := by linarith
  rw [xiMassBottomPrimeLineGrowth_iff_xiMassTraceFixedLineGrowth
    hhalf hca hσ hlam]
  constructor
  · rintro ⟨C, hC⟩
    exact (xiMassFamily haHalf).abs_im_le_of_line_growth_all hσ hlam hC
  · intro him
    refine ⟨(xiMassFamily haHalf).traceReal σ, fun u => ?_⟩
    have hτ : 0 < (((σ : ℂ) + u * I)).re := by
      simp [Complex.mul_re]
      exact hσ
    simpa [Complex.mul_re] using
      ((xiMassFamily haHalf).norm_traceC_le_of_abs_im_le him hτ)

/-- Fixed-line prime growth is equivalent to the existing existential-line mass growth class. -/
theorem xiMassBottomPrimeLineGrowth_iff_xiMassTraceLineGrowth
    {a c σ lam : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hσ : 0 < σ) (hlam : 0 ≤ lam) :
    XiMassBottomPrimeLineGrowth a c σ lam ↔
      xiMassTraceLineGrowth (show 1 / 2 ≤ a by linarith) lam := by
  have haHalf : 1 / 2 ≤ a := by linarith
  rw [xiMassBottomPrimeLineGrowth_iff_mass_displacement_le hhalf hca hσ hlam]
  exact (xiMassFamily haHalf).abs_im_le_iff_exists_line_growth hlam

/-- A displacement above `lam` defeats every proposed prime-source envelope of exponent `lam`. -/
theorem exists_xiMassBottomPrimeIntegral_norm_gt_exp_of_mass_displacement
    {a c σ lam : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hσ : 0 < σ) (hlam : 0 ≤ lam) (q : XiZeroCopy)
    (hq : lam < |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im|)
    (C : ℝ) :
    ∃ u : ℝ, C * Real.exp (lam * |u|) <
      ‖xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I)‖ := by
  by_contra h
  push Not at h
  have hall :=
    (xiMassBottomPrimeLineGrowth_iff_mass_displacement_le hhalf hca hσ hlam).mp ⟨C, h⟩ q
  exact (not_le_of_gt hq) hall

/-- At exponent zero, failure of RH is exactly cofinal unboundedness of the prime integral. -/
theorem not_riemannHypothesis_iff_xiMassBottomPrimeIntegral_norm_unbounded
    {a c σ : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    ¬ RiemannHypothesis ↔
      ∀ C : ℝ, ∃ u : ℝ,
        C < ‖xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I)‖ := by
  simpa only [XiMassBottomPrimeLineBound, not_exists, not_forall, not_le] using
    not_congr (riemannHypothesis_iff_xiMassBottomPrimeLineBound hhalf hca hσ)

/-- RH is exactly failure of unbounded escape for one canonical bottom prime integral. -/
theorem riemannHypothesis_iff_not_xiMassCanonicalBottomPrimeIntegral_norm_unbounded :
    RiemannHypothesis ↔
      ¬ ∀ C : ℝ, ∃ u : ℝ,
        C < ‖xiMassBottomPrimeIntegral 1 (3 / 4) (((1 : ℝ) : ℂ) + u * I)‖ := by
  rw [← not_riemannHypothesis_iff_xiMassBottomPrimeIntegral_norm_unbounded
    (a := 1) (c := 3 / 4) (σ := 1) (by norm_num) (by norm_num) (by norm_num)]
  tauto

end

end RHTower
