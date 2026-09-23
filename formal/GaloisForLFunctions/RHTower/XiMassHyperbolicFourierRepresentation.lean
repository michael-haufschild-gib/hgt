import GaloisForLFunctions.RHTower.XiMassSpacelikeContourOptimality
import GaloisForLFunctions.RHTower.XiMassCriticalErrorFlux
import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence

/-!
# Hyperbolic representation of the Xi mass Fourier transform

The substitution `x = a sinh t` removes the square-root branch geometry from the real mass
Fourier kernel.  This module proves the exact Bochner-integral identity

`stripFourier = ∫₀∞ 2 a cosh(t) exp (-(sigma+i*u) a cosh(t)) cos (h a sinh(t)) dt`.

All change-of-variables hypotheses and improper integrability claims are discharged.  The
transformed majorant is exactly the real Schlaefli `K₁` kernel already constructed in
`BesselOrderRecurrence`.  This is the analytic entry point for curved hyperbolic contour
deformation; no asymptotic formula or unproved transform identity is assumed.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

def xiMassHyperbolicFourierKernel
    (a sigma u h t : ℝ) : ℂ :=
  ((a * Real.cosh t : ℝ) : ℂ) *
    Complex.exp (-((sigma : ℂ) + (u : ℂ) * I) *
      ((a * Real.cosh t : ℝ) : ℂ)) *
    Complex.exp (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ)))

def xiMassHyperbolicCosineKernel
    (a sigma u h t : ℝ) : ℂ :=
  (2 * a * Real.cosh t : ℝ) *
    Complex.exp (-((sigma : ℂ) + (u : ℂ) * I) *
      ((a * Real.cosh t : ℝ) : ℂ)) *
    Complex.cos ((h * a * Real.sinh t : ℝ) : ℂ)

theorem sqrt_sq_sinh_add_sq_eq_mul_cosh
    {a t : ℝ} (ha : 0 < a) :
    Real.sqrt ((a * Real.sinh t) ^ (2 : ℕ) + a ^ (2 : ℕ)) = a * Real.cosh t := by
  have hcosh : 0 < Real.cosh t := Real.cosh_pos t
  have hrhs : 0 ≤ a * Real.cosh t := (mul_pos ha hcosh).le
  have hsq : (a * Real.sinh t) ^ (2 : ℕ) + a ^ (2 : ℕ) = (a * Real.cosh t) ^ (2 : ℕ) := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  rw [hsq, Real.sqrt_sq hrhs]

theorem xiMassAnalyticSqrt_mul_sinh_eq_mul_cosh
    {a t : ℝ} (ha : 0 < a) :
    xiMassAnalyticSqrt a (((a * Real.sinh t : ℝ) : ℂ)) =
      ((a * Real.cosh t : ℝ) : ℂ) := by
  rw [xiMassAnalyticSqrt_ofReal_eq ha,
    sqrt_sq_sinh_add_sq_eq_mul_cosh ha]

theorem xiMassHyperbolicFourierKernel_eq_substitution
    {a sigma u h t : ℝ} (ha : 0 < a) :
    xiMassHyperbolicFourierKernel a sigma u h t =
      ((a * Real.cosh t : ℝ) : ℂ) *
        (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)
          ((a * Real.sinh t : ℝ) : ℂ) *
        Complex.exp (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ)))) := by
  rw [xiMassHyperbolicFourierKernel, xiMassAnalyticTest,
    xiMassAnalyticSqrt_mul_sinh_eq_mul_cosh ha]
  ring

theorem norm_xiMassHyperbolicFourierKernel
    {a sigma u h t : ℝ} (ha : 0 < a) :
    ‖xiMassHyperbolicFourierKernel a sigma u h t‖ =
      a * Real.exp (-(sigma * a) * Real.cosh t) * Real.cosh t := by
  rw [xiMassHyperbolicFourierKernel, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos ha (Real.cosh_pos t)),
    Complex.norm_exp, Complex.norm_exp]
  have hfirst :
      (-((sigma : ℂ) + (u : ℂ) * I) *
        ((a * Real.cosh t : ℝ) : ℂ)).re =
      -(sigma * a) * Real.cosh t := by
    simp [Complex.mul_re]
    ring
  have hphase :
      (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re]
  rw [hfirst, hphase, Real.exp_zero]
  ring

theorem integrableOn_xiMassHyperbolicFourierKernel
    {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    IntegrableOn (xiMassHyperbolicFourierKernel a sigma u h) (Ici 0) := by
  have hs : 0 < sigma * a := mul_pos hsigma ha
  have hB :=
    (GaloisForLFunctions.HTGeometry.integrableOn_realBesselOrderKernel hs 1).const_mul a
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply hB.mono'
  · unfold xiMassHyperbolicFourierKernel
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_xiMassHyperbolicFourierKernel ha]
    simp [GaloisForLFunctions.HTGeometry.realBesselOrderKernel]
    ring_nf
    exact le_rfl

private theorem integrable_xiMassRealFourierKernel
    {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Integrable (fun x : ℝ =>
      xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ) *
        Complex.exp (-(I * (h : ℂ) * (x : ℂ)))) := by
  apply (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hsigma).mono'
  · have hcont : Continuous (fun x : ℝ =>
        xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ) *
          Complex.exp (-(I * (h : ℂ) * (x : ℂ)))) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hmem : (x : ℂ) ∈ xiMassStrip a := by
        change |((x : ℂ)).im| < a
        simpa using ha
      exact (((hasDerivAt_xiMassAnalyticTest ha _ hmem).comp x
        Complex.ofRealCLM.hasDerivAt).continuousAt).mul (by fun_prop)
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, norm_xiMassAnalyticTest_ofReal_eq ha, Complex.norm_exp]
    have hphase : (-(I * (h : ℂ) * (x : ℂ))).re = 0 := by
      simp [Complex.mul_re]
    rw [hphase, Real.exp_zero, mul_one]
    apply Real.exp_le_exp.mpr
    have hsqrt := abs_re_le_xiMassAnalyticSqrt_re a (x : ℂ)
    rw [xiMassAnalyticSqrt_ofReal_eq ha] at hsqrt
    simp only [Complex.ofReal_re] at hsqrt
    nlinarith

private theorem continuous_xiMassRealFourierKernel
    {a sigma u h : ℝ} (ha : 0 < a) :
    Continuous (fun x : ℝ =>
      xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ) *
        Complex.exp (-(I * (h : ℂ) * (x : ℂ)))) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha
  exact (((hasDerivAt_xiMassAnalyticTest ha _ hmem).comp x
    Complex.ofRealCLM.hasDerivAt).continuousAt).mul (by fun_prop)

theorem integral_xiMassHyperbolicFourierKernel_Ioi_eq
    {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    (∫ t in Ioi (0 : ℝ), xiMassHyperbolicFourierKernel a sigma u h t) =
      ∫ x in Ioi (0 : ℝ),
        xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ) *
          Complex.exp (-(I * (h : ℂ) * (x : ℂ))) := by
  let f : ℝ → ℝ := fun t => a * Real.sinh t
  let f' : ℝ → ℝ := fun t => a * Real.cosh t
  let g : ℝ → ℂ := fun x =>
    xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ) *
      Complex.exp (-(I * (h : ℂ) * (x : ℂ)))
  have hf : ContinuousOn f (Ici 0) := by
    exact (continuous_const.mul Real.continuous_sinh).continuousOn
  have hsinhTop : Tendsto Real.sinh atTop atTop := by
    apply tendsto_atTop_atTop_of_monotone Real.sinh_strictMono.monotone
    intro b
    rcases Real.sinh_surjective b with ⟨t, ht⟩
    exact ⟨t, by rw [ht]⟩
  have hft : Tendsto f atTop atTop := by
    exact hsinhTop.const_mul_atTop ha
  have hff' : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f (f' t) (Ioi t) t := by
    intro t ht
    exact ((Real.hasDerivAt_sinh t).const_mul a).hasDerivWithinAt
  have hgcont : ContinuousOn g (f '' Ioi 0) :=
    (continuous_xiMassRealFourierKernel ha).continuousOn
  have hg1 : IntegrableOn g (f '' Ici 0) :=
    (integrable_xiMassRealFourierKernel ha hsigma).integrableOn
  have hg2 : IntegrableOn (fun t => f' t • (g ∘ f) t) (Ici 0) := by
    have hk := integrableOn_xiMassHyperbolicFourierKernel
      (u := u) (h := h) ha hsigma
    apply hk.congr_fun ?_ measurableSet_Ici
    intro t ht
    rw [xiMassHyperbolicFourierKernel_eq_substitution ha]
    rfl
  have hsub := MeasureTheory.integral_deriv_smul_comp_Ioi
    hf hft hff' hgcont hg1 hg2
  have hsub' :
      (∫ t in Ioi (0 : ℝ), f' t • (g ∘ f) t) =
        ∫ x in Ioi (0 : ℝ), g x := by
    simpa only [f, Real.sinh_zero, mul_zero] using hsub
  change (∫ t in Ioi (0 : ℝ), xiMassHyperbolicFourierKernel a sigma u h t) = _
  rw [← hsub']
  apply integral_congr_ae
  filter_upwards with t
  rw [xiMassHyperbolicFourierKernel_eq_substitution ha]
  rfl

theorem xiMassHyperbolicFourierKernel_add_neg_eq_cosine
    (a sigma u h t : ℝ) :
    xiMassHyperbolicFourierKernel a sigma u h t +
        xiMassHyperbolicFourierKernel a sigma u (-h) t =
      xiMassHyperbolicCosineKernel a sigma u h t := by
  rw [xiMassHyperbolicFourierKernel, xiMassHyperbolicFourierKernel,
    xiMassHyperbolicCosineKernel]
  rw [show (-(I * ((-h : ℝ) : ℂ) * ((a * Real.sinh t : ℝ) : ℂ))) =
      -(-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ))) by push_cast; ring]
  let z : ℂ := ((h * a * Real.sinh t : ℝ) : ℂ)
  have harg : I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ) = z * I := by
    dsimp only [z]
    push_cast
    ring
  rw [harg]
  have hpair : Complex.exp (-(z * I)) + Complex.exp (z * I) =
      2 * Complex.cos z := by
    rw [add_comm, ← Complex.two_cosh, Complex.cosh_mul_I]
  rw [show ((h * a * Real.sinh t : ℝ) : ℂ) = z by rfl]
  rw [neg_neg, ← mul_add, hpair]
  push_cast
  ring

theorem stripFourier_xiMass_eq_integral_hyperbolicCosine
    {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ) =
      ∫ t in Ioi (0 : ℝ), xiMassHyperbolicCosineKernel a sigma u h t := by
  let g : ℝ → ℂ := fun x =>
    xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ) *
      Complex.exp (-(I * (h : ℂ) * (x : ℂ)))
  have hg : Integrable g := integrable_xiMassRealFourierKernel ha hsigma
  rw [stripFourier]
  change (∫ x : ℝ, g x) = _
  rw [integral_eq_integral_Ioi_add_reflect hg]
  have hgpos : IntegrableOn g (Ioi 0) := hg.integrableOn
  have hgneg : IntegrableOn (fun x => g (-x)) (Ioi 0) :=
    hg.comp_neg.integrableOn
  rw [integral_add hgpos hgneg]
  have hpos :
      (∫ x in Ioi (0 : ℝ), g x) =
        ∫ t in Ioi (0 : ℝ), xiMassHyperbolicFourierKernel a sigma u h t := by
    simpa only [g] using
      (integral_xiMassHyperbolicFourierKernel_Ioi_eq ha hsigma).symm
  have hneg := integral_xiMassHyperbolicFourierKernel_Ioi_eq
    (a := a) (sigma := sigma) (u := u) (h := -h) ha hsigma
  have hreflect :
      (∫ x in Ioi (0 : ℝ), g (-x)) =
        ∫ x in Ioi (0 : ℝ),
          xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ) *
            Complex.exp (-(I * ((-h : ℝ) : ℂ) * (x : ℂ))) := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [g]
    push_cast
    rw [xiMassAnalyticTest_neg]
    congr 1
    ring
  rw [hpos, hreflect, ← hneg, ← integral_add]
  · apply integral_congr_ae
    filter_upwards with t
    exact xiMassHyperbolicFourierKernel_add_neg_eq_cosine a sigma u h t
  · exact (integrableOn_xiMassHyperbolicFourierKernel
      (u := u) (h := h) ha hsigma).mono_set Ioi_subset_Ici_self
  · exact (integrableOn_xiMassHyperbolicFourierKernel
      (u := u) (h := -h) ha hsigma).mono_set Ioi_subset_Ici_self

theorem xiMassHyperbolicFourierKernel_neg
    (a sigma u h t : ℝ) :
    xiMassHyperbolicFourierKernel a sigma u h (-t) =
      xiMassHyperbolicFourierKernel a sigma u (-h) t := by
  rw [xiMassHyperbolicFourierKernel, xiMassHyperbolicFourierKernel,
    Real.cosh_neg, Real.sinh_neg]
  push_cast
  congr 1
  ring

theorem integrable_xiMassHyperbolicFourierKernel
    {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Integrable (xiMassHyperbolicFourierKernel a sigma u h) := by
  let B : ℝ → ℝ := fun t =>
    a * Real.exp (-(sigma * a) * Real.cosh t) * Real.cosh t
  have hs : 0 < sigma * a := mul_pos hsigma ha
  have hpos : IntegrableOn B (Ioi 0) := by
    have hB :=
      (GaloisForLFunctions.HTGeometry.integrableOn_realBesselOrderKernel hs 1).const_mul a
    exact hB.congr (ae_of_all _ fun t => by
      simp [B, GaloisForLFunctions.HTGeometry.realBesselOrderKernel]
      ring_nf)
  have hposClosed : IntegrableOn B (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hpos
  have hneg : IntegrableOn B (Iic 0) := by
    have hposNeg : IntegrableOn B (Ici (-(0 : ℝ))) := by
      simpa only [neg_zero] using hposClosed
    have hcomp := hposNeg.comp_neg_Iic (c := (0 : ℝ))
    exact hcomp.congr (ae_of_all _ fun t => by
      simp only [B, Real.cosh_neg])
  have hB : Integrable B := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi]
    exact hneg.union hpos
  apply hB.mono'
  · unfold xiMassHyperbolicFourierKernel
    fun_prop
  · filter_upwards with t
    rw [norm_xiMassHyperbolicFourierKernel ha]

theorem stripFourier_xiMass_eq_integral_hyperbolicFourier
    {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ) =
      ∫ t : ℝ, xiMassHyperbolicFourierKernel a sigma u h t := by
  have hk : Integrable (xiMassHyperbolicFourierKernel a sigma u h) :=
    integrable_xiMassHyperbolicFourierKernel
      (u := u) (h := h) ha hsigma
  calc
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ) =
        ∫ t in Ioi (0 : ℝ), xiMassHyperbolicCosineKernel a sigma u h t :=
      stripFourier_xiMass_eq_integral_hyperbolicCosine ha hsigma
    _ = ∫ t in Ioi (0 : ℝ),
        (xiMassHyperbolicFourierKernel a sigma u h t +
          xiMassHyperbolicFourierKernel a sigma u h (-t)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [xiMassHyperbolicFourierKernel_neg,
        xiMassHyperbolicFourierKernel_add_neg_eq_cosine]
    _ = ∫ t : ℝ, xiMassHyperbolicFourierKernel a sigma u h t :=
      (integral_eq_integral_Ioi_add_reflect hk).symm

end

end RHTower
