import GaloisForLFunctions.RHTower.XiMassPolynomialArchShift

/-!
# The filtered archimedean channel is uniformly bounded, and the filtered prime channel

On the centred line the filtered archimedean modulus is independent of the vertical time and the
crossed residue is a fixed real exponential, so the whole filtered archimedean contribution admits
one height-independent bound.  Splitting the filtered Euler-line source into its von-Mangoldt and
archimedean halves therefore isolates all RH-strength growth in the prime channel.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Centred-line filtered integral has one height-independent `L¹` bound. -/
theorem norm_integral_xiMassPolyCenteredArchIntegrand_le_baseNorm (P : Polynomial ℝ)
    {a σ u : ℝ} (ha : 0 < a) :
    ‖∫ x : ℝ, xiMassPolyCenteredArchIntegrand P a (σ + u * I) x‖ ≤
      ∫ x : ℝ, ‖xiMassPolyCenteredArchIntegrand P a (σ : ℂ) x‖ := by
  calc ‖∫ x : ℝ, xiMassPolyCenteredArchIntegrand P a (σ + u * I) x‖
      ≤ ∫ x : ℝ, ‖xiMassPolyCenteredArchIntegrand P a (σ + u * I) x‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖xiMassPolyCenteredArchIntegrand P a (σ : ℂ) x‖ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        exact norm_xiMassPolyCenteredArchIntegrand_verticalTime_eq P ha

/-- Explicit height-independent bound for the whole filtered archimedean channel. -/
def xiMassPolyBottomArchUniformBound (P : Polynomial ℝ) (a σ : ℝ) : ℝ :=
  (∫ x : ℝ, ‖xiMassPolyCenteredArchIntegrand P a (σ : ℂ) x‖) +
    2 * Real.pi * (‖evalRealPolynomial P (xiMassArchPole ^ 2) ^ 2‖ *
      Real.exp (-σ * xiMassArchPoleFrequency a))

theorem xiMassPolyBottomArchUniformBound_nonneg (P : Polynomial ℝ) {a σ : ℝ} :
    0 ≤ xiMassPolyBottomArchUniformBound P a σ := by
  rw [xiMassPolyBottomArchUniformBound]
  have hnorm : 0 ≤ ∫ x : ℝ, ‖xiMassPolyCenteredArchIntegrand P a (σ : ℂ) x‖ :=
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  positivity

/-- **The filtered archimedean bottom source is uniformly bounded on each positive vertical
line.** -/
theorem norm_integral_xiMassPolyBottomArchIntegrand_le_uniform (P : Polynomial ℝ)
    {a c σ u : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    ‖∫ x : ℝ, xiMassPolyBottomArchIntegrand P a c (σ + u * I) x‖ ≤
      xiMassPolyBottomArchUniformBound P a σ := by
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  have hahalf : 1 / 2 < a := lt_trans hhalf hca
  have hτ : (0 : ℝ) < ((σ : ℂ) + u * I).re := by simpa [Complex.mul_re] using hσ
  rw [integral_xiMassPolyBottomArch_eq_centered_add_residue P hhalf hca hτ]
  have hres : ‖2 * (Real.pi : ℂ) *
      xiMassPolyAnalyticTest P a ((σ : ℂ) + u * I) xiMassArchPole‖
      = 2 * Real.pi * (‖evalRealPolynomial P (xiMassArchPole ^ 2) ^ 2‖ *
        Real.exp (-σ * xiMassArchPoleFrequency a)) := by
    rw [xiMassPolyAnalyticTest, norm_mul, norm_mul, norm_mul,
      norm_xiMassAnalyticTest_archPole_eq hahalf, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  refine le_trans (norm_add_le _ _) ?_
  rw [xiMassPolyBottomArchUniformBound, hres]
  exact add_le_add
    (norm_integral_xiMassPolyCenteredArchIntegrand_le_baseNorm P ha) le_rfl

/-! ## The filtered prime channel -/

/-- Von-Mangoldt part of the filtered mass bottom edge. -/
def xiMassPolyBottomPrimeIntegrand (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  evalRealPolynomial P (((x : ℂ) - c * I) ^ 2) ^ 2 * xiMassBottomPrimeIntegrand a c τ x

theorem xiMassPolyBottomSourceIntegrand_split (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassPolyBottomSourceIntegrand P a c τ x =
      -I * xiMassPolyBottomPrimeIntegrand P a c τ x +
        I * xiMassPolyBottomArchIntegrand P a c τ x := by
  rw [xiMassPolyBottomSourceIntegrand, xiMassPolyBottomPrimeIntegrand,
    xiMassPolyBottomArchIntegrand, xiMassBottomSourceIntegrand_eq]
  ring

theorem xiMassPolyBottomPrimeIntegrand_eq (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassPolyBottomPrimeIntegrand P a c τ x =
      I * xiMassPolyBottomSourceIntegrand P a c τ x +
        xiMassPolyBottomArchIntegrand P a c τ x := by
  rw [xiMassPolyBottomSourceIntegrand_split]
  have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
  linear_combination (xiMassPolyBottomPrimeIntegrand P a c τ x
    - xiMassPolyBottomArchIntegrand P a c τ x) * hI

/-- The filtered von-Mangoldt bottom edge is absolutely integrable at every legal depth. -/
theorem integrable_xiMassPolyBottomPrimeIntegrand (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable (xiMassPolyBottomPrimeIntegrand P a c τ) := by
  have hs := (integrable_xiMassPolyBottomSourceIntegrand P hhalf hca hτ).const_mul I
  have ha := integrable_xiMassPolyBottomArchIntegrand P hhalf hca hτ
  exact (hs.add ha).congr (Filter.Eventually.of_forall fun x =>
    (xiMassPolyBottomPrimeIntegrand_eq P a c τ x).symm)

/-- **The filtered Euler-line source splits into its prime and archimedean channels.** -/
theorem integral_xiMassPolyBottomSourceIntegrand_split (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassPolyBottomSourceIntegrand P a c τ x) =
      -I * (∫ x : ℝ, xiMassPolyBottomPrimeIntegrand P a c τ x) +
        I * (∫ x : ℝ, xiMassPolyBottomArchIntegrand P a c τ x) := by
  have hp := integrable_xiMassPolyBottomPrimeIntegrand P hhalf hca hτ
  have haa := integrable_xiMassPolyBottomArchIntegrand P hhalf hca hτ
  have hsplit : (∫ x : ℝ, xiMassPolyBottomSourceIntegrand P a c τ x)
      = ∫ x : ℝ, (-I * xiMassPolyBottomPrimeIntegrand P a c τ x +
          I * xiMassPolyBottomArchIntegrand P a c τ x) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    exact xiMassPolyBottomSourceIntegrand_split P a c τ x
  rw [hsplit, MeasureTheory.integral_add (hp.const_mul (-I)) (haa.const_mul I),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end

end RHTower
