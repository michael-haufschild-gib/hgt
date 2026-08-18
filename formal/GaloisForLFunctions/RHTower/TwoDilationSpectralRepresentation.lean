import GaloisForLFunctions.HTGeometry.SchwartzPositiveMeasureRepresentation
import GaloisForLFunctions.RHTower.HedenmalmUniversalPositiveFormClassification
import GaloisForLFunctions.RHTower.TwoDilationDivisorMetric

/-!
# Two prime dilations give the temperate spectral representation

`prime-modulated-weyl-idealizer-collapse-on-xi-sampling`, equations `(24)`–`(30)`.
-/

open MeasureTheory Filter Complex
open scoped SchwartzMap FourierTransform Topology

namespace RHTower

noncomputable section

open SchwartzMap

/-- `(25)`: invariance of a form under the translation by `log r`. -/
def DilationInvariant (Q : ContinuousSchwartzSesquilinearForm) (r : ℕ) : Prop :=
  ∀ u v : 𝓢(ℝ, ℂ),
    Q (translateCLM ℂ (Real.log r) u) (translateCLM ℂ (Real.log r) v) = Q u v

/-- **Two multiplicatively independent dilations force momentum symmetry.** -/
theorem momentumSymmetric_of_two_dilation_invariance
    (Q : ContinuousSchwartzSesquilinearForm) {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → r ^ m ≠ s ^ n)
    (hQr : DilationInvariant Q r) (hQs : DilationInvariant Q s) :
    Q.MomentumSymmetric := by
  rw [Q.momentumSymmetric_iff_derivativeSkew]
  intro u v
  set H : ℝ → ℂ := fun t => Q (translateCLM ℂ t u) (translateCLM ℂ t v) with hH
  have hderiv : ∀ a : ℝ, HasDerivAt H
      (Q (translateCLM ℂ a (derivCLM ℂ ℂ u)) (translateCLM ℂ a v) +
        Q (translateCLM ℂ a u) (translateCLM ℂ a (derivCLM ℂ ℂ v))) a :=
    fun a => Q.hasDerivAt_translate_pair u v a
  have hcont : Continuous H :=
    continuous_iff_continuousAt.mpr fun a => (hderiv a).continuousAt
  have hstep : ∀ (t : ℕ) (_ : 2 ≤ t), DilationInvariant Q t →
      ∀ x : ℝ, H (x + Real.log t) = H x := by
    intro t _ hQt x
    have hcomm : x + Real.log t = Real.log t + x := by ring
    simp only [hH, hcomm, ← translateCLM_add]
    exact hQt _ _
  have hconst : ∀ x y : ℝ, H x = H y :=
    eq_of_two_dilation_invariance hcont hr hs hind (hstep r hr hQr) (hstep s hs hQs)
  have h0 : HasDerivAt H (Q (derivCLM ℂ ℂ u) v + Q u (derivCLM ℂ ℂ v)) 0 := by
    simpa using hderiv 0
  have hzero : deriv H 0 = 0 := by
    have hfun : H = fun _ : ℝ => H 0 := funext fun x => hconst x 0
    rw [hfun]
    simp
  rw [← h0.deriv, hzero]

/-- **`(27)`: the two-dilation form has a unique positive temperate spectral measure.** -/
theorem existsUnique_temperateSpectralRepresentation_of_two_dilation
    (Q : ContinuousSchwartzSesquilinearForm) (hQnonneg : Q.IsNonnegative)
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → r ^ m ≠ s ^ n)
    (hQr : DilationInvariant Q r) (hQs : DilationInvariant Q s) :
    ∃! μ : Measure ℝ, TemperateSpectralRepresentation Q μ :=
  existsUnique_temperateSpectralRepresentation Q
    (momentumSymmetric_of_two_dilation_invariance Q hr hs hind hQr hQs) hQnonneg

/-- `(27)` in integral form. -/
theorem apply_eq_integral_of_temperateSpectralRepresentation
    {Q : ContinuousSchwartzSesquilinearForm} {μ : Measure ℝ}
    (h : TemperateSpectralRepresentation Q μ) (u v : 𝓢(ℝ, ℂ)) :
    Q u v = ∫ t : ℝ, (fourierTransformCLM ℂ u) t * (starRingEnd ℂ) ((fourierTransformCLM ℂ) v t)
      ∂μ := by
  obtain ⟨hμ, hQ⟩ := h
  letI := hμ
  rw [hQ]
  change (integralCLM ℂ μ) (pointwiseMulConj _ _) = _
  rw [integralCLM_apply]
  simp

/-- `(29)`: a null source has vanishing spectral mass. -/
theorem integral_normSq_eq_zero_of_null
    {Q : ContinuousSchwartzSesquilinearForm} {μ : Measure ℝ}
    (h : TemperateSpectralRepresentation Q μ) {k : 𝓢(ℝ, ℂ)} (hnull : Q k k = 0) :
    ∫ t : ℝ, Complex.normSq ((fourierTransformCLM ℂ) k t) ∂μ = 0 := by
  obtain ⟨hμ, hQ⟩ := h
  letI := hμ
  have hval := apply_eq_integral_of_temperateSpectralRepresentation ⟨hμ, hQ⟩ k k
  rw [hnull] at hval
  have hpt : ∀ t : ℝ, (fourierTransformCLM ℂ) k t *
      (starRingEnd ℂ) ((fourierTransformCLM ℂ) k t)
      = ((Complex.normSq ((fourierTransformCLM ℂ) k t) : ℝ) : ℂ) := fun t => Complex.mul_conj _
  rw [funext hpt] at hval
  rw [integral_complex_ofReal] at hval
  exact_mod_cast hval.symm

/-- **`(30)`: the spectral measure of a null-source two-dilation metric is carried by the real
Xi divisor.** -/
theorem measure_compl_xiRealDivisor_eq_zero_of_null_source
    {Q : ContinuousSchwartzSesquilinearForm} {μ : Measure ℝ}
    (h : TemperateSpectralRepresentation Q μ) {k : 𝓢(ℝ, ℂ)}
    (hk : ∀ t : ℝ, (fourierTransformCLM ℂ) k t = XiC (t : ℂ)) (hnull : Q k k = 0) :
    μ (xiRealDivisorᶜ) = 0 := by
  obtain ⟨hμ, hQ⟩ := h
  letI := hμ
  have hzero := integral_normSq_eq_zero_of_null ⟨hμ, hQ⟩ hnull
  have hintC : Integrable (fun t : ℝ => pointwiseMulConj
      ((fourierTransformCLM ℂ) k) ((fourierTransformCLM ℂ) k) t) μ :=
    (pointwiseMulConj ((fourierTransformCLM ℂ) k) ((fourierTransformCLM ℂ) k)).integrable
  have hintR : Integrable
      (fun t : ℝ => Complex.normSq ((fourierTransformCLM ℂ) k t)) μ := by
    refine hintC.norm.congr (Filter.Eventually.of_forall fun t => ?_)
    show ‖pointwiseMulConj ((fourierTransformCLM ℂ) k) ((fourierTransformCLM ℂ) k) t‖
        = Complex.normSq ((fourierTransformCLM ℂ) k t)
    rw [pointwiseMulConj_apply, Complex.mul_conj, Complex.norm_real,
      Real.norm_of_nonneg (Complex.normSq_nonneg _)]
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg
    (fun t => Complex.normSq_nonneg _) hintR).mp hzero
  have hsub : (xiRealDivisorᶜ : Set ℝ)
      ⊆ {t : ℝ | Complex.normSq ((fourierTransformCLM ℂ) k t) ≠ 0} := by
    intro t ht
    have htne : XiC (t : ℂ) ≠ 0 := ht
    rw [Set.mem_setOf_eq, Ne, Complex.normSq_eq_zero, hk t]
    exact htne
  refine measure_mono_null hsub ?_
  rw [← MeasureTheory.ae_iff]
  filter_upwards [hae] with t ht
  simpa using ht

/-- **The two-dilation divisor carrier law**, `(25)` → `(27)` → `(30)`. -/
theorem exists_temperateSpectralRepresentation_carried_by_xiRealDivisor
    (Q : ContinuousSchwartzSesquilinearForm) (hQnonneg : Q.IsNonnegative)
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → r ^ m ≠ s ^ n)
    (hQr : DilationInvariant Q r) (hQs : DilationInvariant Q s)
    {k : 𝓢(ℝ, ℂ)} (hk : ∀ t : ℝ, (fourierTransformCLM ℂ) k t = XiC (t : ℂ))
    (hnull : Q k k = 0) :
    ∃ μ : Measure ℝ, TemperateSpectralRepresentation Q μ ∧ μ (xiRealDivisorᶜ) = 0 := by
  obtain ⟨μ, hμ, -⟩ := existsUnique_temperateSpectralRepresentation_of_two_dilation Q hQnonneg
    hr hs hind hQr hQs
  exact ⟨μ, hμ, measure_compl_xiRealDivisor_eq_zero_of_null_source hμ hk hnull⟩

/-! ## `(28)`–`(30)` at the actual Hedenmalm theta source

The tree owns the theta source as a Schwartz function whose Fourier transform is the centered
`Xi`, together with the whole downstream classification of a theta-null spectral measure.  Two
prime dilations therefore suffice to trigger all of it.
-/

/-- **`(28)`–`(30)`: the two-dilation theta-null form has exactly one positive temperate spectral
measure, and it is supported on the real `Xi` divisor.** -/
theorem existsUnique_temperateSpectralRepresentation_supported_realDivisor_of_two_dilation
    (Q : ContinuousSchwartzSesquilinearForm) (hQnonneg : Q.IsNonnegative)
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → r ^ m ≠ s ^ n)
    (hQr : DilationInvariant Q r) (hQs : DilationInvariant Q s)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    ∃! μ : Measure ℝ,
      TemperateSpectralRepresentation Q μ ∧ μ.support ⊆ xiRealZeroSet :=
  existsUnique_temperateSpectralRepresentation_supported_realDivisor_of_thetaNull Q
    (momentumSymmetric_of_two_dilation_invariance Q hr hs hind hQr hQs) hQnonneg hnull

/-- **`(31)`: the two-dilation theta-null spectral measure is purely atomic on the real `Xi`
divisor.** -/
theorem canonicalMeasure_atomic_of_two_dilation
    (Q : ContinuousSchwartzSesquilinearForm) (hQnonneg : Q.IsNonnegative)
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → r ^ m ≠ s ^ n)
    (hQr : DilationInvariant Q r) (hQs : DilationInvariant Q s)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    Q.compactSpectralRieszMeasure
        (momentumSymmetric_of_two_dilation_invariance Q hr hs hind hQr hQs) hQnonneg
      = Measure.sum (fun t : xiRealZeroSet =>
          Q.compactSpectralRieszMeasure
            (momentumSymmetric_of_two_dilation_invariance Q hr hs hind hQr hQs)
            hQnonneg {(t : ℝ)} • Measure.dirac (t : ℝ)) :=
  universalPositiveForm_canonicalMeasure_atomic_of_thetaNull Q
    (momentumSymmetric_of_two_dilation_invariance Q hr hs hind hQr hQs) hQnonneg hnull

/-- **The theta source realises `(28)`.**  Its Fourier transform is the centered `Xi`. -/
theorem fourierTransformCLM_xiThetaSchwartzSource (t : ℝ) :
    (fourierTransformCLM ℂ) xiThetaSchwartzSource t = XiC (t : ℂ) :=
  fourier_xiThetaSchwartzSource t

/-- **The two-dilation divisor carrier law at the theta source.** -/
theorem exists_temperateSpectralRepresentation_theta_carried_by_xiRealDivisor
    (Q : ContinuousSchwartzSesquilinearForm) (hQnonneg : Q.IsNonnegative)
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → r ^ m ≠ s ^ n)
    (hQr : DilationInvariant Q r) (hQs : DilationInvariant Q s)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    ∃ μ : Measure ℝ, TemperateSpectralRepresentation Q μ ∧ μ (xiRealDivisorᶜ) = 0 :=
  exists_temperateSpectralRepresentation_carried_by_xiRealDivisor Q hQnonneg hr hs hind hQr hQs
    fourierTransformCLM_xiThetaSchwartzSource hnull

end

end RHTower
