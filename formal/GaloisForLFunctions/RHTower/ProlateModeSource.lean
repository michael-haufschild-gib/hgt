import GaloisForLFunctions.RHTower.ProlateFourierBandEigen
import GaloisForLFunctions.RHTower.ConstrainedProlatePoissonMuntz

/-!
# The cut-off source of a prolate mode

The selected even mode, restricted to its aperture with the symmetric half-endpoint convention, is
an even, compactly supported, bounded, integrable real source.  Its Fourier transform is the mode
itself, rescaled: the aperture rescaling of the Fourier integral turns the transform into the
finite Fourier transform of the mode, which is a scalar multiple of the mode.

The half-endpoint convention is what makes the source's periodization continuous at the origin, so
the symmetric-Lebesgue boundary condition of the Poisson--Muntz law is automatic.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform Real Topology

namespace RHTower

/-- The cut-off source of a profile at aperture `a`. -/
def prolateModeSource (a : ℝ) (Φ : ℝ → ℝ) : ℝ → ℝ :=
  GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff a (fun y => Φ (y / a))

variable {a : ℝ} {Φ : ℝ → ℝ}

theorem prolateModeSource_eq_zero_of_not_mem (ha : 0 ≤ a) {y : ℝ}
    (hyn : y ∉ Icc (-a) a) : prolateModeSource a Φ y = 0 := by
  unfold prolateModeSource GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff
  rw [if_neg (fun h => hyn (Ioo_subset_Icc_self h)), if_neg]
  rintro (rfl | rfl)
  · exact hyn ⟨le_refl _, by linarith⟩
  · exact hyn ⟨by linarith, le_refl _⟩

theorem prolateModeSource_apply_of_mem_Ioo {y : ℝ} (hy : y ∈ Ioo (-a) a) :
    prolateModeSource a Φ y = Φ (y / a) := by
  unfold prolateModeSource GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff
  rw [if_pos hy]

theorem even_prolateModeSource (heven : Function.Even Φ) :
    Function.Even (prolateModeSource a Φ) := by
  intro y
  unfold prolateModeSource GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff
  have hmem : (-y ∈ Ioo (-a) a) ↔ (y ∈ Ioo (-a) a) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hend : (-y = -a ∨ -y = a) ↔ (y = -a ∨ y = a) := by
    constructor
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by rw [h]; ring)
      · exact Or.inl (by rw [h])
  have hval : Φ (-y / a) = Φ (y / a) := by
    rw [show -y / a = -(y / a) by ring, heven]
  by_cases h1 : y ∈ Ioo (-a) a
  · rw [if_pos (hmem.mpr h1), if_pos h1]
    show Φ (-y / a) = Φ (y / a)
    exact hval
  · rw [if_neg (fun h => h1 (hmem.mp h)), if_neg h1]
    by_cases h2 : y = -a ∨ y = a
    · rw [if_pos (hend.mpr h2), if_pos h2]
      show Φ (-y / a) / 2 = Φ (y / a) / 2
      rw [hval]
    · rw [if_neg (fun h => h2 (hend.mp h)), if_neg h2]

theorem measurable_prolateModeSource (hΦ : Continuous Φ) :
    Measurable (prolateModeSource a Φ) := by
  unfold prolateModeSource GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff
  have hG : Measurable fun y : ℝ => Φ (y / a) :=
    (hΦ.comp (continuous_id.div_const a)).measurable
  have hset : MeasurableSet {x : ℝ | x = -a ∨ x = a} := by
    have : {x : ℝ | x = -a ∨ x = a} = {-a} ∪ {a} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    rw [this]
    exact (measurableSet_singleton (-a)).union (measurableSet_singleton a)
  exact Measurable.ite measurableSet_Ioo hG (Measurable.ite hset (hG.div_const 2) measurable_const)

theorem abs_prolateModeSource_le {C : ℝ} (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C) (y : ℝ) :
    |prolateModeSource a Φ y| ≤ C := by
  unfold prolateModeSource GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff
  by_cases h1 : y ∈ Ioo (-a) a
  · rw [if_pos h1]
    exact hC _
  · rw [if_neg h1]
    by_cases h2 : y = -a ∨ y = a
    · rw [if_pos h2, abs_div]
      have := hC (y / a)
      have h2' : |(2 : ℝ)| = 2 := by norm_num
      rw [h2']
      linarith [abs_nonneg (Φ (y / a))]
    · rw [if_neg h2, abs_zero]
      exact hC0

theorem hasCompactSupport_prolateModeSource (ha : 0 < a) :
    HasCompactSupport (prolateModeSource a Φ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun y hy => ?_
  exact prolateModeSource_eq_zero_of_not_mem ha.le hy

theorem integrable_prolateModeSource (ha : 0 < a) (hΦ : Continuous Φ) {C : ℝ}
    (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C) :
    Integrable (prolateModeSource a Φ) := by
  have hmeas : AEStronglyMeasurable (prolateModeSource a Φ) volume :=
    (measurable_prolateModeSource hΦ).aestronglyMeasurable
  have hint : Integrable (Set.indicator (Icc (-a) a) (fun _ : ℝ => C)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const measure_Icc_lt_top.ne enorm_ne_top)
  refine Integrable.mono' hint hmeas (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hy, Real.norm_eq_abs]
    exact abs_prolateModeSource_le hC hC0 y
  · rw [Set.indicator_of_notMem hy, prolateModeSource_eq_zero_of_not_mem ha.le hy]
    simp

/-- **The Fourier transform of the cut-off source is the mode's finite Fourier transform.** -/
theorem fourier_prolateModeSource (ha : 0 < a) (hΦ : Continuous Φ)
    (heven : Function.Even Φ) (x : ℝ) :
    𝓕 (fun y => ((prolateModeSource a Φ y : ℝ) : ℂ)) (a * x)
      = (a : ℂ) * fourierBandTransform (2 * Real.pi * a ^ (2 : ℕ))
          (fun t => ((Φ t : ℝ) : ℂ)) x := by
  have hsupp : ∀ y : ℝ, y ∉ Icc (-a) a → ((prolateModeSource a Φ y : ℝ) : ℂ) = 0 := by
    intro y hy
    rw [prolateModeSource_eq_zero_of_not_mem ha.le hy, Complex.ofReal_zero]
  have hscale := fourier_compactSupport_unitScale ha hsupp x
  rw [← hscale]
  simp only [Circle.smul_def, Real.fourierChar_apply, Complex.real_smul, smul_eq_mul]
  rw [← setIntegral_scaledFourierChar_eq_fourierBandTransform
    (κ := a ^ (2 : ℕ)) (h := fun t : ℝ => ((Φ t : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hΦ) (fun t => by rw [heven t]) x]
  congr 1
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [Ioo_ae_eq_Icc] with t ht
  intro htcc
  have htoo : t ∈ Ioo (-1 : ℝ) 1 := ht.mpr htcc
  have hat : a * t ∈ Ioo (-a) a := by
    constructor <;> nlinarith [htoo.1, htoo.2]
  have hval : prolateModeSource a Φ (a * t) = Φ t := by
    rw [prolateModeSource_apply_of_mem_Ioo hat, mul_div_cancel_left₀ t ha.ne']
  rw [hval]
  congr 2
  push_cast
  ring

/-- **The symmetric-Lebesgue boundary condition holds for the cut-off source.** -/
theorem tendsto_symmetricLebesgue_prolateModeSource (ha : 0 < a) {b : ℝ} (hb : 0 < b)
    (hΦ : Continuous Φ) (heven : Function.Even Φ) {C : ℝ}
    (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C) :
    Tendsto (fun s : ℝ =>
      ((∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum (prolateModeSource a Φ) b t -
          poissonMuntzAngularDatum (prolateModeSource a Φ) b 0| +
        |poissonMuntzAngularDatum (prolateModeSource a Φ) b (-t) -
          poissonMuntzAngularDatum (prolateModeSource a Φ) b 0|) / s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_poissonMuntz_symmetricLebesgueAverage_of_continuousAt
    (integrable_prolateModeSource ha hΦ hC hC0) hb ?_
  unfold poissonMuntzScaledPeriodization prolateModeSource
  exact GaloisForLFunctions.HTGeometry.continuousAt_realL1Periodization_symmetricHalfEndpointCutoff_zero
    ha hb (hΦ.comp (continuous_id.div_const a)) (fun y => by
      show Φ (-y / a) = Φ (y / a)
      rw [show -y / a = -(y / a) by ring, heven])

end RHTower
