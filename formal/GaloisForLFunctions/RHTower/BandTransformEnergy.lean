import GaloisForLFunctions.RHTower.BandLimitedExtension
import GaloisForLFunctions.RHTower.BandFormBridge
import GaloisForLFunctions.RHTower.BandLeakageSpectralTail

/-!
# The energy of the band transform, and the leakage as an outside mass

The band transform of a test function is the Fourier integral of its *windowed* spectrum: the change of
variables that turns the normalized window coordinate into the frequency has Jacobian `2 pi/c`, which
exactly cancels the prefactor of the window representation, leaving

```text
(B_c Phi)(x) = 𝓕 (1_([-k,k]) · 𝓕 (trunc Phi)) (-x),        k = c/(2 pi).
```

Plancherel then computes the *total* energy of the band transform on the whole line: it is the band
quadratic form,

```text
∫_ℝ (B_c Phi)² = ∫∫ sinc_c(x-y) Phi(x) Phi(y),
```

which is the projection identity `‖P f‖² = ⟪P f, f⟫` made explicit.

For an eigenfunction this converts the leakage into a statement about mass: with `B_c psi = nu psi`,
`nu² ∫_ℝ psi² = nu ‖psi‖²`, so the band-limited extension carries energy `‖psi‖²/nu` on the line and
`‖psi‖² (1 - nu)/nu` *outside* the band.  The leakage is exactly the mass that the eigenfunction's
entire extension is forced to spend outside `[-1, 1]` — the form in which a sharp lower envelope has to
be proved.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-! ## The windowed spectrum -/

/-- The spectrum of a test function, truncated to the frequency window. -/
def windowSpectrum (c : ℝ) (Φ : ℝ → ℝ) : ℝ → ℂ :=
  Set.indicator (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi))) (𝓕 (bandTrunc Φ))

theorem continuous_fourier_bandTrunc {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Continuous (𝓕 (bandTrunc Φ)) :=
  continuous_fourier_of_integrable (integrable_bandTrunc hΦ)

theorem integrable_windowSpectrum (c : ℝ) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Integrable (windowSpectrum c Φ) (volume : Measure ℝ) := by
  rw [windowSpectrum, integrable_indicator_iff measurableSet_Icc]
  exact (continuous_fourier_bandTrunc hΦ).continuousOn.integrableOn_compact isCompact_Icc

theorem memLp_windowSpectrum (c : ℝ) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    MemLp (windowSpectrum c Φ) 2 (volume : Measure ℝ) := by
  have hG := continuous_fourier_bandTrunc hΦ
  rw [windowSpectrum, memLp_indicator_iff_restrict measurableSet_Icc]
  haveI hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict
      (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(c / (2 * Real.pi))) (b := c / (2 * Real.pi))
    ).exists_bound_of_continuousOn hG.continuousOn
  refine MemLp.of_bound hG.aestronglyMeasurable.restrict C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-! ## The band transform is the transform of its windowed spectrum -/

/-- **The band transform is the Fourier integral of the windowed spectrum.**  The Jacobian of the
window change of variables cancels the prefactor of the window representation. -/
theorem bandTransform_eq_fourier_windowSpectrum {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (x : ℝ) :
    ((bandTransform c Φ x : ℝ) : ℂ) = 𝓕 (windowSpectrum c Φ) (-x) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  set k : ℝ := c / (2 * Real.pi) with hk
  have hkpos : 0 < k := by
    rw [hk]
    positivity
  have hkne : k ≠ 0 := ne_of_gt hkpos
  set g : ℝ → ℂ := fun u => 𝓕 (bandTrunc Φ) u * Complex.exp (((2 * Real.pi * u * x : ℝ) : ℂ)
    * Complex.I) with hg
  -- the right side is the window integral of the spectrum
  have hright : 𝓕 (windowSpectrum c Φ) (-x) = ∫ u in (-k)..k, g u := by
    rw [Real.fourier_eq']
    have hind : (∫ v : ℝ, Complex.exp ((↑(-2 * Real.pi * (inner ℝ v (-x))) : ℂ) * Complex.I)
          • windowSpectrum c Φ v)
        = ∫ v in Icc (-k) k, g v := by
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [windowSpectrum, hk, Set.indicator_apply]
      split_ifs with hv
      · have hinner : (inner ℝ v (-x) : ℝ) = -(v * x) := by
          simp
          ring
        rw [hinner, smul_eq_mul, hg]
        have hexp : ((-2 * Real.pi * -(v * x) : ℝ) : ℂ) = ((2 * Real.pi * v * x : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hexp]
        ring
      · rw [smul_zero]
    rw [hind, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -k ≤ k)]
  -- the left side is the window representation, rescaled
  have hleft : ((bandTransform c Φ x : ℝ) : ℂ) = ∫ u in (-k)..k, g u := by
    rw [bandTransform_eq_windowIntegral (ne_of_gt hc) hΦ x]
    have hspec : ∀ t : ℝ, bandSpectrum c Φ t
        * Complex.exp (Complex.I * (((c : ℂ) * (x : ℂ)) * (t : ℂ))) = g (k * t) := by
      intro t
      rw [bandSpectrum, bandFourier_eq_fourier, hg]
      have hfreq : -(-(c * t) / (2 * Real.pi)) = k * t := by
        rw [hk]
        field_simp
      rw [hfreq]
      congr 1
      have hphase : ((2 * Real.pi * (k * t) * x : ℝ) : ℂ) * Complex.I
          = Complex.I * (((c : ℂ) * (x : ℂ)) * (t : ℂ)) := by
        have hreal : (2 * Real.pi * (k * t) * x : ℝ) = c * x * t := by
          rw [hk]
          field_simp
        rw [hreal]
        push_cast
        ring
      rw [hphase]
    rw [intervalIntegral.integral_congr (g := fun t => g (k * t)) fun t _ => hspec t]
    rw [intervalIntegral.integral_comp_mul_left g hkne, Complex.real_smul]
    have hends : k * (-1) = -k ∧ k * 1 = k := by
      constructor <;> ring
    have hcast : ((c : ℂ) / (2 * (Real.pi : ℂ))) = ((k : ℝ) : ℂ) := by
      rw [hk]
      push_cast
      ring
    rw [hends.1, hends.2, hcast, ← mul_assoc]
    have hkk : ((k : ℝ) : ℂ) * (((k⁻¹ : ℝ)) : ℂ) = 1 := by
      have hne : ((k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hkne
      push_cast
      field_simp
    rw [hkk, one_mul]
  rw [hleft, hright]

/-! ## The total energy of the band transform -/

theorem integrable_sq_bandTransform {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Integrable (fun x : ℝ => (bandTransform c Φ x) ^ 2) (volume : Measure ℝ) := by
  have hint : Integrable (fun ξ : ℝ => ‖𝓕 (windowSpectrum c Φ) ξ‖ ^ 2) (volume : Measure ℝ) :=
    integrable_norm_sq_fourier (integrable_windowSpectrum c hΦ) (memLp_windowSpectrum c hΦ)
  have hneg : Integrable (fun x : ℝ => ‖𝓕 (windowSpectrum c Φ) (-x)‖ ^ 2)
      (volume : Measure ℝ) := hint.comp_neg
  refine hneg.congr ?_
  filter_upwards with x
  rw [← bandTransform_eq_fourier_windowSpectrum hc hΦ x, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- **The total energy of the band transform is the band quadratic form.**  This is the projection
identity `‖P f‖² = ⟪P f, f⟫` in explicit form. -/
theorem integral_sq_bandTransform_eq_form {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    (∫ x : ℝ, (bandTransform c Φ x) ^ 2)
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (Φ x * Φ y) := by
  have hle : -(c / (2 * Real.pi)) ≤ c / (2 * Real.pi) := by
    have : (0 : ℝ) < c / (2 * Real.pi) := by positivity
    linarith
  -- rewrite the space integral as the spectral integral of the windowed spectrum
  have hstep1 : (∫ x : ℝ, (bandTransform c Φ x) ^ 2)
      = ∫ x : ℝ, ‖𝓕 (windowSpectrum c Φ) (-x)‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (bandTransform c Φ x) ^ 2 = ‖𝓕 (windowSpectrum c Φ) (-x)‖ ^ 2
    rw [← bandTransform_eq_fourier_windowSpectrum hc hΦ x, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hstep2 : (∫ x : ℝ, ‖𝓕 (windowSpectrum c Φ) (-x)‖ ^ 2)
      = ∫ x : ℝ, ‖𝓕 (windowSpectrum c Φ) x‖ ^ 2 :=
    integral_neg_eq_self (fun x : ℝ => ‖𝓕 (windowSpectrum c Φ) x‖ ^ 2) volume
  have hstep3 : (∫ x : ℝ, ‖𝓕 (windowSpectrum c Φ) x‖ ^ 2)
      = ∫ v : ℝ, ‖windowSpectrum c Φ v‖ ^ 2 :=
    integral_norm_sq_fourier_eq (integrable_windowSpectrum c hΦ) (memLp_windowSpectrum c hΦ)
  have hstep4 : (∫ v : ℝ, ‖windowSpectrum c Φ v‖ ^ 2)
      = ∫ v in Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)), ‖𝓕 (bandTrunc Φ) v‖ ^ 2 := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [windowSpectrum, Set.indicator_apply]
    split_ifs with hv
    · rfl
    · simp
  have hstep5 : (∫ v in Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)), ‖𝓕 (bandTrunc Φ) v‖ ^ 2)
      = ∫ v in -(c / (2 * Real.pi))..(c / (2 * Real.pi)), ‖𝓕 (bandTrunc Φ) v‖ ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [hstep1, hstep2, hstep3, hstep4, hstep5,
    ← double_integral_sincKernel_eq_frequency_energy hc hΦ]

/-! ## The leakage as an outside mass -/

/-- The continuous representative of an eigenvector is its band class. -/
theorem bandClass_eigenExtension {c ν : ℝ} (hν : ν ≠ 0) {ψ : RealIntervalL2 (-1 : ℝ) 1}
    (heig : bandOperatorL2 c ψ = ν • ψ) :
    bandClass (eigenExtension c ν ψ) (continuous_eigenExtension c ν ψ) = ψ := by
  rw [Lp.ext_iff]
  exact (coeFn_bandClass (eigenExtension c ν ψ) (continuous_eigenExtension c ν ψ)).trans
    (eigenExtension_ae_eq hν heig).symm

/-- **The energy of the band-limited extension on the line.**  An eigenfunction at `nu` spreads its
band energy `‖psi‖²` into total energy `‖psi‖²/nu`. -/
theorem integral_sq_eigenExtension {c ν : ℝ} (hc : 0 < c) (hν : ν ≠ 0)
    {ψ : RealIntervalL2 (-1 : ℝ) 1} (heig : bandOperatorL2 c ψ = ν • ψ) :
    (∫ x : ℝ, (eigenExtension c ν ψ x) ^ 2) = ‖ψ‖ ^ 2 / ν := by
  have hΦ : Continuous (eigenExtension c ν ψ) := continuous_eigenExtension c ν ψ
  have hclass := bandClass_eigenExtension hν heig
  have hbt : ∀ x, bandTransform c (eigenExtension c ν ψ) x = ν * eigenExtension c ν ψ x :=
    bandTransform_eigenExtension hν heig
  have h1 : (∫ x : ℝ, (bandTransform c (eigenExtension c ν ψ) x) ^ 2)
      = ν ^ 2 * ∫ x : ℝ, (eigenExtension c ν ψ x) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (bandTransform c (eigenExtension c ν ψ) x) ^ 2
        = ν ^ 2 * (eigenExtension c ν ψ x) ^ 2
    rw [hbt x]
    ring
  have h2 := integral_sq_bandTransform_eq_form hc hΦ
  have h3 : (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      sincKernelSmooth c x y * (eigenExtension c ν ψ x * eigenExtension c ν ψ y))
      = (inner ℝ (bandOperatorL2 c ψ) ψ : ℝ) := by
    rw [← inner_bandOperatorL2_bandClass c (eigenExtension c ν ψ) hΦ, hclass]
  have h4 : (inner ℝ (bandOperatorL2 c ψ) ψ : ℝ) = ν * ‖ψ‖ ^ 2 := by
    rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [h2, h3, h4] at h1
  -- ν² E = ν ‖psi‖²
  have hνsq : (ν : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hν
  field_simp at h1 ⊢
  linarith [h1]

/-- **The leakage is the outside mass of the band-limited extension.**  The eigenfunction's entire
extension spends `‖psi‖² (1 - nu)/nu` of its energy outside the band. -/
theorem integral_outside_sq_eigenExtension {c ν : ℝ} (hc : 0 < c) (hν : ν ≠ 0)
    {ψ : RealIntervalL2 (-1 : ℝ) 1} (heig : bandOperatorL2 c ψ = ν • ψ) :
    (∫ x in (Icc (-1 : ℝ) 1)ᶜ, (eigenExtension c ν ψ x) ^ 2) = ‖ψ‖ ^ 2 * (1 - ν) / ν := by
  have hΦ : Continuous (eigenExtension c ν ψ) := continuous_eigenExtension c ν ψ
  have hclass := bandClass_eigenExtension hν heig
  have hbt : ∀ x, bandTransform c (eigenExtension c ν ψ) x = ν * eigenExtension c ν ψ x :=
    bandTransform_eigenExtension hν heig
  -- the square is integrable on the line
  have hint : Integrable (fun x : ℝ => (eigenExtension c ν ψ x) ^ 2) (volume : Measure ℝ) := by
    have h := integrable_sq_bandTransform hc hΦ
    have hsc : Integrable (fun x : ℝ => (ν ^ 2)⁻¹ * (bandTransform c (eigenExtension c ν ψ) x) ^ 2)
        (volume : Measure ℝ) := h.const_mul _
    refine hsc.congr ?_
    filter_upwards with x
    rw [hbt x]
    have hνsq : (ν : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hν
    field_simp
  -- the band part is the eigenvector's energy
  have hband : (∫ x in Icc (-1 : ℝ) 1, (eigenExtension c ν ψ x) ^ 2) = ‖ψ‖ ^ 2 := by
    have h := norm_sq_bandClass (eigenExtension c ν ψ) hΦ
    rw [hclass] at h
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact h.symm
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Icc (a := (-1 : ℝ)) (b := 1)) hint
  rw [hband, integral_sq_eigenExtension hc hν heig] at hsplit
  field_simp at hsplit ⊢
  linarith [hsplit]

end GaloisForLFunctions.RHTower

end
