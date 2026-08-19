import GaloisForLFunctions.HTGeometry.CayleyOuterFamilyGauge
import GaloisForLFunctions.HTGeometry.ParabolicCayleyAutomorphism
import GaloisForLFunctions.HTGeometry.SpectralMobiusGauge

/-!
# Differential independence of the parabolic orbit of the bounded outer carrier

The bounded outer carrier of a finite positive measure is `O = exp ∘ c ∘ m ∘ φ` on the unit disc,
where `m` is the Cauchy transform of the measure, `c(z) = (z − i)/(z + i)` is the Cayley map of the
upper half plane into the disc, and `φ(w) = i(1 + w)/(1 − w)` is its inverse.  The parabolic disc
automorphisms are `τ_t = φ⁻¹ ∘ (z ↦ z + t) ∘ φ`, so `φ ∘ τ_t = φ + t`.

Freeness of the translated Cauchy family and its transport through the Cayley exponential are
already available.  The remaining transport is the rational change of variable `z = φ(w)`, which
turns the half-plane translation family into the parabolic orbit on the disc; the Mobius gauge
supplies it because `φ` is a Mobius map of nonzero determinant carrying the disc into the half
plane.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## Real translation configurations -/

/-- The shift configuration attached to an injective tuple of real translations. -/
def realShiftConfiguration {m : ℕ} (t : Fin m → ℝ) (ht : Function.Injective t) :
    InjectiveShiftConfiguration (Fin m) :=
  ⟨fun i => ((t i : ℝ) : ℂ), by
    intro i j hij
    exact ht (Complex.ofReal_inj.mp hij)⟩

/-- For real translations the common upper domain is the whole open upper half plane. -/
theorem mem_commonUpperTranslationDomain_of_im_pos {m : ℕ} {t : Fin m → ℝ}
    (ht : Function.Injective t) {z : ℂ} (hz : 0 < z.im) :
    z ∈ commonUpperTranslationDomain (realShiftConfiguration t ht) := by
  intro i
  simpa [realShiftConfiguration] using hz

/-! ## The inverse Cayley map in Mobius normal form -/

/-- `φ(w) = i(1 + w)/(1 − w)` is the Mobius map with coefficients `(i, i, −1, 1)`. -/
theorem cayleyToUpper_eq_mobius (v : ℂ) :
    (Complex.I * v + Complex.I) / ((-1 : ℂ) * v + 1) = cayleyToUpper v := by
  rw [cayleyToUpper]
  congr 1 <;> ring

/-! ## The parabolic orbit inherits the freeness of the translation family -/

/-- **Parabolic transport of translation freeness.**  If the translated Cauchy family carries no
differential relation on its common upper domain, then the family of parabolic translates of the
bounded outer carrier carries none on the disc. -/
theorem not_familyDifferentiallyAlgebraicOn_parabolicOrbit {m : ℕ}
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : Fin m → ℝ) (ht : Function.Injective t)
    (hfree : ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => cauchyTransform ν (z + (realShiftConfiguration t ht).1 i))
      (commonUpperTranslationDomain (realShiftConfiguration t ht))) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i w => outerCarrier ν (parabolicAut (t i) w)) openDisc := by
  set shift := realShiftConfiguration t ht with hshift
  set U := commonUpperTranslationDomain shift with hU
  have hUo : IsOpen U := isOpen_commonUpperTranslationDomain shift
  have hUc : IsPreconnected U := commonUpperTranslationDomain_isPreconnected shift
  have houter := not_familyDifferentiallyAlgebraicOn_outerCauchyTranslates ν shift hfree
  have hden : ∀ i, ∀ z ∈ U, cauchyTransform ν (z + shift.1 i) + Complex.I ≠ 0 := by
    intro i z hz
    exact add_I_ne_zero_of_im_nonneg (im_cauchyTransform_nonneg ν (hz i))
  have hga : ∀ i, AnalyticOnNhd ℂ
      (fun z => Complex.exp ((cauchyTransform ν (z + shift.1 i) - Complex.I)
        / (cauchyTransform ν (z + shift.1 i) + Complex.I))) U := by
    intro i z hz
    have hc := analyticOnNhd_cauchyTransform_translate ν shift i
    exact (((hc z hz).sub analyticAt_const).div ((hc z hz).add analyticAt_const)
      (hden i z hz)).cexp
  have hdet : (Complex.I * 1 - Complex.I * (-1 : ℂ)) ≠ 0 := by
    intro h
    have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination h
    simp [Complex.I_ne_zero] at h2
  have hVden : ∀ v ∈ openDisc, (-1 : ℂ) * v + 1 ≠ 0 := by
    intro v hv
    have hv1 : ‖v‖ < 1 := mem_openDisc_iff.mp hv
    intro h
    exact one_sub_ne_zero_of_norm_lt_one hv1 (by linear_combination h)
  have hVU : ∀ v ∈ openDisc,
      (Complex.I * v + Complex.I) / ((-1 : ℂ) * v + 1) ∈ U := by
    intro v hv
    rw [cayleyToUpper_eq_mobius, hU, hshift]
    exact mem_commonUpperTranslationDomain_of_im_pos ht
      (im_cayleyToUpper_pos (mem_openDisc_iff.mp hv))
  have hw₀ : (0 : ℂ) ∈ openDisc := by simp [mem_openDisc_iff]
  have hcomp := not_familyDifferentiallyAlgebraicOn_comp_mobius hUo hUc hga isOpen_openDisc
    hdet hVden hVU hw₀ houter
  intro hrel
  refine hcomp (familyDifferentiallyAlgebraicOn_congr_of_isOpen isOpen_openDisc
    (fun i v hv => ?_) hrel)
  have hv1 : ‖v‖ < 1 := mem_openDisc_iff.mp hv
  rw [outerCarrier, cayleyToUpper_parabolicAut hv1, cayleyToUpper_eq_mobius, cayleyToDisc]
  simp [hshift, realShiftConfiguration]

/-! ## The residual capstone -/

/-- **Maximal parabolic freeness of the bounded outer carrier.**  For every infinite-support base
measure and every strictly positive integrable density, one dense residual set of bounded
exponential parameters produces a bounded outer carrier on the disc whose entire real parabolic
orbit is differentially algebraically independent over the rational functions. -/
theorem outerCarrier_parabolicOrbitFreeness_denseResidual
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ x, 0 < w x) :
    ∃ Ufree : Set (Lp ℝ ⊤ μ), Dense Ufree ∧ Ufree ∈ residual (Lp ℝ ⊤ μ) ∧
      ∀ u ∈ Ufree, ∀ (m : ℕ) (t : Fin m → ℝ), Function.Injective t →
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i v => outerCarrier (expWeightedMeasure μ w u) (parabolicAut (t i) v))
          openDisc := by
  obtain ⟨hdense, hres, hfree⟩ :=
    herglotz_fullTranslationCauchyFamilyFreeness_denseResidual μ hμ w hw hwpos
  refine ⟨_, hdense, hres, ?_⟩
  intro u hu m t ht
  letI : IsFiniteMeasure (expWeightedMeasure μ w u) :=
    isFiniteMeasure_expWeightedMeasure μ w hw (fun x => (hwpos x).le) u
  exact not_familyDifferentiallyAlgebraicOn_parabolicOrbit _ t ht
    (hfree u hu m (realShiftConfiguration t ht))

end

end GaloisForLFunctions.HTGeometry
