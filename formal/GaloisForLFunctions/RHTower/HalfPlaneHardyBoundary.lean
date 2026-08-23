import GaloisForLFunctions.RHTower.SuzukiModelSpaceConjugation
import GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane

noncomputable section

/-!
# From the analytic half-plane Hardy space to boundary values in `L²(ℝ)`

The corpus realizes the Hardy space of the right half-plane analytically: a function holomorphic
there with uniformly bounded mass on every vertical line is the half-line Laplace transform of a
square-integrable datum supported on `(0, ∞)`.  The model space `K(Θ)` and the de Branges space
`H(E)`, by contrast, live inside `L²(ℝ)` as boundary values.

This module connects the two.  The datum becomes an honest `L²(ℝ)` vector lying in the positive-ray
subspace `halfLineL2`, and the restriction of the Hardy function to the line `Re w = σ` is the
Fourier transform of the datum damped by `e^{-σx}`.  Letting `σ → 0` therefore identifies the
boundary values with the Fourier image of the datum itself.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem memLp_hardyDatum_volume {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) :
    MemLp (hardyDatum F hF) 2 (volume : Measure ℝ) := by
  have hind : (hardyDatum F hF) =ᵐ[volume] (Ioi (0 : ℝ)).indicator (hardyDatum F hF) := by
    filter_upwards [hardyDatum_ae_zero_of_neg hF,
      MeasureTheory.compl_mem_ae_iff.mpr (show volume ({0} : Set ℝ) = 0 by simp)] with x hx hx0
    rcases lt_trichotomy x 0 with h | h | h
    · rw [hx h, Set.indicator_of_notMem (by simp [Set.mem_Ioi]; linarith)]
    · exact absurd (by simp [h]) hx0
    · rw [Set.indicator_of_mem (by simpa [Set.mem_Ioi] using h)]
  have hbase : MemLp ((Ioi (0 : ℝ)).indicator (hardyDatum F hF)) 2 (volume : Measure ℝ) :=
    (memLp_indicator_iff_restrict measurableSet_Ioi).mpr (memLp_two_hardyDatum hF)
  exact hbase.ae_eq hind.symm

/-- The datum of a half-plane Hardy function, as an `L²(ℝ)` vector. -/
def hardyDatumLp (F : ℂ → ℂ) {M : ℝ} (hF : IsHalfPlaneHardy F M) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_hardyDatum_volume hF).toLp _

theorem hardyDatumLp_coeFn (F : ℂ → ℂ) {M : ℝ} (hF : IsHalfPlaneHardy F M) :
    ((hardyDatumLp F hF : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] hardyDatum F hF :=
  (memLp_hardyDatum_volume hF).coeFn_toLp

/-- **The datum lives on the positive ray.** -/
theorem hardyDatumLp_mem_halfLineL2 (F : ℂ → ℂ) {M : ℝ} (hF : IsHalfPlaneHardy F M) :
    hardyDatumLp F hF ∈ halfLineL2 := by
  rw [mem_halfLineL2_iff]
  filter_upwards [hardyDatumLp_coeFn F hF, hardyDatum_ae_zero_of_neg hF] with x h1 h2 hx
  rw [h1]
  exact h2 hx

/-- The datum damped by `e^{-σx}`, as an `L²(ℝ)` vector. -/
def dampedDatumLp (F : ℂ → ℂ) {M : ℝ} (hF : IsHalfPlaneHardy F M) {σ : ℝ} (hσ : 0 < σ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two_weighted_hardyDatum hF hσ).toLp _

theorem dampedDatumLp_eq_hardyPreimage (F : ℂ → ℂ) {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {σ : ℝ} (hσ : 0 < σ) :
    dampedDatumLp F hF hσ = hardyPreimage F σ (hF.memLp σ hσ) := by
  refine MeasureTheory.Lp.ext ?_
  simp only [dampedDatumLp]
  filter_upwards [(memLp_two_weighted_hardyDatum hF hσ).coeFn_toLp,
    hardyDatum_weight_ae hF hσ] with x h1 h2
  rw [h1, h2]

/-- **The boundary restriction on a line is the Fourier transform of the damped datum.**  This is
the bridge between the analytic realization of the half-plane Hardy space and its realization by
boundary values inside `L²(ℝ)`. -/
theorem lineRestriction_eq_fourier_dampedDatum (F : ℂ → ℂ) {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {σ : ℝ} (hσ : 0 < σ) :
    (hF.memLp σ hσ).toLp (fun ξ : ℝ => F (rayLine σ ξ))
      = (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (dampedDatumLp F hF hσ) := by
  rw [dampedDatumLp_eq_hardyPreimage]
  exact (fourier_hardyPreimage F σ (hF.memLp σ hσ)).symm


theorem norm_sq_lp_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 := by
  have hinner : (inner ℂ f f : ℂ) = ((∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (inner ℂ ((f : ℝ → ℂ) x) ((f : ℝ → ℂ) x) : ℂ) = ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ)
    rw [RCLike.inner_apply, Complex.mul_conj, Complex.sq_norm]
  have h := @inner_self_eq_norm_sq ℂ _ _ _ _ f
  rw [hinner] at h
  simpa using h.symm

/-- **The damped datum converges to the datum in `L²`.**  Hence the boundary values of a
half-plane Hardy function are the Fourier transform of its datum. -/
theorem tendsto_dampedDatumLp (F : ℂ → ℂ) {M : ℝ} (hF : IsHalfPlaneHardy F M)
    (σ : ℕ → ℝ) (hσpos : ∀ n, 0 < σ n) (hσ0 : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun n => dampedDatumLp F hF (hσpos n)) atTop (𝓝 (hardyDatumLp F hF)) := by
  have hdint : Integrable (fun x : ℝ => ‖hardyDatum F hF x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_hardyDatum hF)).mp
      (memLp_hardyDatum_volume hF)
  have hdiff : ∀ n : ℕ, ∀ᵐ x : ℝ,
      ‖((dampedDatumLp F hF (hσpos n) - hardyDatumLp F hF : Lp ℂ 2 (volume : Measure ℝ))
          : ℝ → ℂ) x‖ ^ 2
        = ‖((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1‖ ^ 2 * ‖hardyDatum F hF x‖ ^ 2 := by
    intro n
    filter_upwards [MeasureTheory.Lp.coeFn_sub (dampedDatumLp F hF (hσpos n)) (hardyDatumLp F hF),
      (memLp_two_weighted_hardyDatum hF (hσpos n)).coeFn_toLp,
      hardyDatumLp_coeFn F hF] with x h1 h2 h3
    rw [h1, Pi.sub_apply]
    show ‖((dampedDatumLp F hF (hσpos n) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
      - ((hardyDatumLp F hF : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ ^ 2 = _
    simp only [dampedDatumLp] at h2 ⊢
    rw [h2, h3, ← sub_one_mul, norm_mul, mul_pow]
  have hbnd : ∀ n : ℕ, ∀ᵐ x : ℝ,
      ‖‖((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1‖ ^ 2 * ‖hardyDatum F hF x‖ ^ 2‖
        ≤ ‖hardyDatum F hF x‖ ^ 2 := by
    intro n
    filter_upwards [hardyDatum_ae_zero_of_neg hF] with x hx
    rcases lt_or_ge x 0 with h | h
    · rw [hx h]
      simp
    · have he1 : Real.exp (-(σ n * x)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [(hσpos n).le])
      have he0 : (0 : ℝ) < Real.exp (-(σ n * x)) := Real.exp_pos _
      have hnb : ‖((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1‖ ≤ 1 := by
        rw [show ((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1
            = (((Real.exp (-(σ n * x)) - 1 : ℝ)) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        linarith [he0]
      have hsq1 : ‖((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg (((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1), hnb]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hsq1, sq_nonneg ‖hardyDatum F hF x‖]
  have hptw : ∀ᵐ x : ℝ, Tendsto
      (fun n => ‖((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1‖ ^ 2 * ‖hardyDatum F hF x‖ ^ 2)
      atTop (𝓝 0) := by
    filter_upwards with x
    have hexp : Tendsto (fun n => ((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => -(σ n * x)) atTop (𝓝 0) := by
        simpa using (hσ0.mul_const x).neg
      have h2 : Tendsto (fun n => Real.exp (-(σ n * x))) atTop (𝓝 1) := by
        have h2' := (Real.continuous_exp.tendsto 0).comp h1
        rw [Real.exp_zero] at h2'
        exact h2'
      have h3 : Tendsto (fun n => ((Real.exp (-(σ n * x)) : ℝ) : ℂ)) atTop (𝓝 1) := by
        have h3' := (Complex.continuous_ofReal.tendsto 1).comp h2
        rw [Complex.ofReal_one] at h3'
        exact h3'
      simpa using h3.sub_const 1
    have := ((hexp.norm).pow 2).mul_const (‖hardyDatum F hF x‖ ^ 2)
    simpa using this
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x : ℝ => ‖((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1‖ ^ 2 * ‖hardyDatum F hF x‖ ^ 2)
      volume := by
    intro n
    refine AEStronglyMeasurable.mul ?_ (hdint.aestronglyMeasurable)
    exact ((((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (by fun_prop))).sub continuous_const).norm).pow 2
      ).aestronglyMeasurable
  have hintTo : Tendsto (fun n => ∫ x : ℝ,
      ‖((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1‖ ^ 2 * ‖hardyDatum F hF x‖ ^ 2) atTop (𝓝 0) := by
    have := MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x : ℝ => ‖hardyDatum F hF x‖ ^ 2) hmeas hdint hbnd hptw
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n : ℕ,
      ‖dampedDatumLp F hF (hσpos n) - hardyDatumLp F hF‖ ^ 2
        = ∫ x : ℝ, ‖((Real.exp (-(σ n * x)) : ℝ) : ℂ) - 1‖ ^ 2 * ‖hardyDatum F hF x‖ ^ 2 := by
    intro n
    rw [norm_sq_lp_eq_integral]
    exact MeasureTheory.integral_congr_ae (hdiff n)
  have hsqTo : Tendsto
      (fun n => ‖dampedDatumLp F hF (hσpos n) - hardyDatumLp F hF‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hintTo
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsqTo
  simp only [Real.sqrt_zero] at hroot
  refine hroot.congr fun n => ?_
  exact Real.sqrt_sq (norm_nonneg _)


end RHTower
