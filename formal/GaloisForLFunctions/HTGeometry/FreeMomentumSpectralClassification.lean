import GaloisForLFunctions.RHTower.VectorL2WeakDerivativeFourier
import GaloisForLFunctions.HTGeometry.MultivariateAnalyticNullPreimage

/-!
# Free finite-channel momentum spectral classification

Vector-valued Plancherel sends `-ic d/du` to multiplication by `2πcξ`. For `c ≠ 0`, the associated
pushforward of Lebesgue measure is absolutely continuous and positive on every nonempty open
energy interval, its point spectrum is empty, and a fiber `ℂ^m` gives constant multiplicity `m`.
-/

noncomputable section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal SchwartzMap LineDeriv

namespace GaloisForLFunctions.HTGeometry

def freeMomentumEnergy (c ξ : ℝ) : ℝ := 2 * Real.pi * c * ξ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem l2_fourier_freeMomentum_ae
    (c : ℝ) (f g : Lp H 2 (volume : Measure ℝ))
    (hweak : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, H)) = (g : 𝓢'(ℝ, H))) :
    ((𝓕 ((-Complex.I * (c : ℂ)) • g) : Lp H 2 (volume : Measure ℝ)) : ℝ → H)
      =ᵐ[volume] fun ξ : ℝ =>
        ((freeMomentumEnergy c ξ : ℝ) : ℂ) •
          ((𝓕 f : Lp H 2 (volume : Measure ℝ)) : ℝ → H) ξ := by
  have hderiv := RHTower.l2_fourier_weakDerivative_ae f g hweak
  have hmap : (𝓕 ((-Complex.I * (c : ℂ)) • g) : Lp H 2 (volume : Measure ℝ)) =
      (-Complex.I * (c : ℂ)) • (𝓕 g : Lp H 2 (volume : Measure ℝ)) := by
    exact map_smul (Lp.fourierTransformₗᵢ ℝ H) _ _
  rw [hmap]
  filter_upwards [Lp.coeFn_smul (-Complex.I * (c : ℂ))
    (𝓕 g : Lp H 2 (volume : Measure ℝ)), hderiv] with ξ hsmul hξ
  rw [hsmul]
  change (-Complex.I * (c : ℂ)) •
      ((𝓕 g : Lp H 2 (volume : Measure ℝ)) : ℝ → H) ξ = _
  rw [hξ, smul_smul]
  congr 1
  simp only [freeMomentumEnergy]
  push_cast
  calc
    (-Complex.I * (c : ℂ)) *
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) =
        (-((2 : ℂ) * (Real.pi : ℂ) * (c : ℂ) * (ξ : ℂ))) *
          (Complex.I * Complex.I) := by ring
    _ = (2 : ℂ) * (Real.pi : ℂ) * (c : ℂ) * (ξ : ℂ) := by
      rw [Complex.I_mul_I]
      ring

def freeMomentumExceptionalFrequency (c : ℝ) (z : ℂ) : ℝ :=
  z.re / (2 * Real.pi * c)

theorem freeMomentumEnergy_ne_eigenvalue_of_ne_exception
    {c : ℝ} (hc : c ≠ 0) (z : ℂ) {ξ : ℝ}
    (hξ : ξ ≠ freeMomentumExceptionalFrequency c z) :
    ((freeMomentumEnergy c ξ : ℝ) : ℂ) ≠ z := by
  intro heq
  apply hξ
  have hden : 2 * Real.pi * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hc
  apply (eq_div_iff hden).2
  have hre := congrArg Complex.re heq
  simpa [freeMomentumEnergy, mul_assoc, mul_comm, mul_left_comm] using hre

omit [CompleteSpace H] in
theorem ae_eq_zero_of_freeMomentumEnergy_smul_eq
    {c : ℝ} (hc : c ≠ 0) (z : ℂ) {f : ℝ → H}
    (h : ∀ᵐ ξ : ℝ ∂volume,
      ((freeMomentumEnergy c ξ : ℝ) : ℂ) • f ξ = z • f ξ) :
    f =ᵐ[volume] (0 : ℝ → H) := by
  filter_upwards [h, (volume : Measure ℝ).ae_ne (freeMomentumExceptionalFrequency c z)]
    with ξ hξ hne
  have hcoef : ((freeMomentumEnergy c ξ : ℝ) : ℂ) - z ≠ 0 :=
    sub_ne_zero.mpr (freeMomentumEnergy_ne_eigenvalue_of_ne_exception hc z hne)
  have hz : (((freeMomentumEnergy c ξ : ℝ) : ℂ) - z) • f ξ = 0 := by
    rw [sub_smul, hξ, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left hcoef

omit [CompleteSpace H] in
theorem l2_freeMomentumMultiplier_has_no_eigenvector
    {c : ℝ} (hc : c ≠ 0) (z : ℂ) (f : Lp H 2 (volume : Measure ℝ))
    (h : ∀ᵐ ξ : ℝ ∂volume,
      ((freeMomentumEnergy c ξ : ℝ) : ℂ) • (f : ℝ → H) ξ =
        z • (f : ℝ → H) ξ) :
    f = 0 := by
  have hz := ae_eq_zero_of_freeMomentumEnergy_smul_eq hc z h
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero H 2 (volume : Measure ℝ)] with ξ hξ hzero
  rw [hξ, hzero]

theorem measurable_freeMomentumEnergy (c : ℝ) : Measurable (freeMomentumEnergy c) := by
  change Measurable (fun ξ : ℝ => (2 * Real.pi * c) * ξ)
  exact (continuous_const.mul continuous_id).measurable

theorem analyticOnNhd_freeMomentumEnergy (c : ℝ) :
    AnalyticOnNhd ℝ (freeMomentumEnergy c) univ := by
  change AnalyticOnNhd ℝ (fun ξ : ℝ => (2 * Real.pi * c) * ξ) univ
  exact analyticOnNhd_const.mul analyticOnNhd_id

theorem freeMomentumEnergy_nonconstant {c : ℝ} (hc : c ≠ 0) :
    ∃ x y : ℝ, freeMomentumEnergy c x ≠ freeMomentumEnergy c y := by
  refine ⟨0, 1, ?_⟩
  have hden : 2 * Real.pi * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hc
  simpa [freeMomentumEnergy] using hden

/-- The direct-integral spectral measure of nonzero free momentum is absolutely continuous with
respect to Lebesgue measure. -/
theorem freeMomentumSpectralMeasure_absolutelyContinuous
    {c : ℝ} (hc : c ≠ 0) :
    Measure.map (freeMomentumEnergy c) (volume : Measure ℝ) ≪ volume := by
  intro S hS
  obtain ⟨S', hSS', hS'meas, hS'null⟩ := exists_measurable_superset_of_null hS
  refine measure_mono_null hSS' ?_
  rw [Measure.map_apply (measurable_freeMomentumEnergy c) hS'meas]
  exact GaloisForLFunctions.HTGeometry.analytic_preimage_volume_eq_zero
    (analyticOnNhd_freeMomentumEnergy c) (freeMomentumEnergy_nonconstant hc) hS'null

/-- Every nonempty open energy interval has positive free-momentum spectral measure, so the
essential energy range is all of `ℝ`. -/
theorem freeMomentumSpectralMeasure_Ioo_ne_zero
    {c : ℝ} (hc : c ≠ 0) {a b : ℝ} (hab : a < b) :
    Measure.map (freeMomentumEnergy c) (volume : Measure ℝ) (Ioo a b) ≠ 0 := by
  rw [Measure.map_apply (measurable_freeMomentumEnergy c) measurableSet_Ioo]
  have hopen : IsOpen (freeMomentumEnergy c ⁻¹' Ioo a b) :=
    isOpen_Ioo.preimage (show Continuous (freeMomentumEnergy c) by
      change Continuous (fun ξ : ℝ => (2 * Real.pi * c) * ξ)
      exact continuous_const.mul continuous_id)
  apply hopen.measure_ne_zero (volume : Measure ℝ)
  have hden : 2 * Real.pi * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hc
  let x : ℝ := ((a + b) / 2) / (2 * Real.pi * c)
  refine ⟨x, ?_⟩
  change a < freeMomentumEnergy c x ∧ freeMomentumEnergy c x < b
  have hx : freeMomentumEnergy c x = (a + b) / 2 := by
    dsimp [x, freeMomentumEnergy]
    field_simp [hden]
  rw [hx]
  constructor <;> linarith

abbrev FiniteChannelFiber (m : ℕ) := EuclideanSpace ℂ (Fin m)

@[simp]
theorem finrank_finiteChannelFiber (m : ℕ) :
    Module.finrank ℂ (FiniteChannelFiber m) = m := by
  simp [FiniteChannelFiber]

/-- Exact free finite-channel classification: Lebesgue-absolutely-continuous spectral measure,
full real essential range, no point spectrum, and constant multiplicity `m`. -/
theorem finiteChannel_freeMomentum_spectral_classification
    (m : ℕ) {c : ℝ} (hc : c ≠ 0) :
    (Measure.map (freeMomentumEnergy c) (volume : Measure ℝ) ≪ volume) ∧
      (∀ ⦃a b : ℝ⦄, a < b →
        Measure.map (freeMomentumEnergy c) (volume : Measure ℝ) (Ioo a b) ≠ 0) ∧
      (∀ (z : ℂ) (f : Lp (FiniteChannelFiber m) 2 (volume : Measure ℝ)),
        (∀ᵐ ξ : ℝ ∂volume,
          ((freeMomentumEnergy c ξ : ℝ) : ℂ) • (f : ℝ → FiniteChannelFiber m) ξ =
            z • (f : ℝ → FiniteChannelFiber m) ξ) → f = 0) ∧
      Module.finrank ℂ (FiniteChannelFiber m) = m := by
  exact ⟨freeMomentumSpectralMeasure_absolutelyContinuous hc,
    fun {_a _b} hab => freeMomentumSpectralMeasure_Ioo_ne_zero hc hab,
    fun z f h => l2_freeMomentumMultiplier_has_no_eigenvector hc z f h,
    finrank_finiteChannelFiber m⟩

end GaloisForLFunctions.HTGeometry
