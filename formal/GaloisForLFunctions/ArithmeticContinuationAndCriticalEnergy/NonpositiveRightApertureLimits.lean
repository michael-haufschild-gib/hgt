import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFlowIsAShellFlux
import GaloisForLFunctions.RHTower.PaperRestrictedWeilSource
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEnergyContinuity
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.UnitNonpositiveLimitsDoNotVanish
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Nonpositive limits on shrinking apertures

Unit form vectors of nonpositive shifted Weil energy cannot disappear
as apertures decrease. Compactness gives a nonzero weak limit, and strong
physical convergence places that limit in the limiting support interval.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil SignedArithmeticEnergyIncidence

/-- The weighted Fourier measure is sigma-finite, so its `L²` space and
each closed aperture form domain are separable. -/
instance separableSpace_weilFormDomain (a : SuzukiPositiveAperture) :
    TopologicalSpace.SeparableSpace (Space a) := by
  letI : MeasureTheory.SigmaFinite ccmArchimedeanFormMeasure := by
    unfold ccmArchimedeanFormMeasure
    infer_instance
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : SecondCountableTopology CCMArchimedeanFourierL2 := inferInstance
  infer_instance

theorem norm_apertureExt {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : Space a) : ‖apertureExt hab u‖ = ‖u‖ := by
  change ‖(apertureExt hab u).1‖ = ‖u.1‖
  rw [apertureExt_val]

theorem apertureExt_zero {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    apertureExt hab (0 : Space a) = 0 := by
  simpa only [zero_smul] using apertureExt_smul hab (0 : ℂ) (0 : Space a)

/-- All right-aperture vectors live isometrically in one fixed form domain. -/
def rightApertureExtension (a : SuzukiPositiveAperture) (n : ℕ)
    (u : Space (suzukiRightAperture a n)) : Space (suzukiRightAperture a 0) :=
  apertureExt (Subtype.coe_le_coe.mpr (antitone_suzukiRightAperture a (Nat.zero_le n))) u

/-- The literal energy shift is a compact perturbation of form-domain mass. -/
theorem operator_quadratic_eq_compactEnergy (a : SuzukiPositiveAperture)
    (E : ℝ) (u : Space a) :
    (inner ℂ (operator a E u) u).re =
      compactPerturbedEnergy (ccmArchimedeanFormToAperture a)
        (ccmRestrictedWeilBoundedRemainder a - (E : ℂ) • 1) u := by
  rw [operator_mixed]
  have hi : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have hscale := _root_.inner_smul_left (ccmArchimedeanFormToAperture a u)
    (ccmArchimedeanFormToAperture a u) (E : ℂ)
  simp only [ccmRestrictedWeilForm, compactPerturbedEnergy,
    sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, hscale,
    Complex.conj_ofReal, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hi]
  ring

private theorem operator_quadratic_extension {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) (E : ℝ) (u : Space a) :
    (inner ℂ (operator b E (apertureExt hab u)) (apertureExt hab u)).re =
      (inner ℂ (operator a E u) u).re := by
  rw [operator_quadratic, operator_quadratic,
    ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab (apertureExt_val hab u),
    norm_embedding_apertureExt]

theorem rightApertureExtension_norm (a : SuzukiPositiveAperture) (n : ℕ)
    (u : Space (suzukiRightAperture a n)) : ‖rightApertureExtension a n u‖ = ‖u‖ :=
  norm_apertureExt _ u

private theorem operator_quadratic_rightApertureExtension (a : SuzukiPositiveAperture)
    (E : ℝ) (n : ℕ) (u : Space (suzukiRightAperture a n)) :
    (inner ℂ (operator (suzukiRightAperture a 0) E (rightApertureExtension a n u))
      (rightApertureExtension a n u)).re =
        (inner ℂ (operator (suzukiRightAperture a n) E u) u).re :=
  operator_quadratic_extension _ E u

private theorem fixed_point_of_eq {H : Type*} (P : H → H) {x y : H}
    (h : x = y) (hy : P y = y) : P x = x :=
  (congrArg P h).trans (hy.trans h.symm)

private theorem rightApertureExtension_cutoff (a : SuzukiPositiveAperture) (n : ℕ)
    (u : Space (suzukiRightAperture a n)) :
    indicatorCutoff (centralInterval (suzukiRightAperture a n).1)
      (measurableSet_centralInterval (suzukiRightAperture a n).1)
      (ccmArchimedeanFormToAperture (suzukiRightAperture a 0)
        (rightApertureExtension a n u) : SoninL2) =
      (ccmArchimedeanFormToAperture (suzukiRightAperture a 0)
        (rightApertureExtension a n u) : SoninL2) := by
  exact fixed_point_of_eq _
    (ccmArchimedeanFormToAperture_coe_eq_of_val_eq (apertureExt_val _ u))
    (indicatorCutoff_ccmArchimedeanFormEmbedding _ u)

private theorem exists_nonpositive_rightAperture_ambient_limit
    (a : SuzukiPositiveAperture) (E : ℝ)
    (u : (n : ℕ) → Space (suzukiRightAperture a n))
    (hnorm : ∀ n, ‖u n‖ = 1)
    (hq : ∀ n, (inner ℂ (operator (suzukiRightAperture a n) E (u n)) (u n)).re ≤ 0) :
    ∃ v : Space (suzukiRightAperture a 0), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ v ≠ 0 ∧
      (inner ℂ (operator (suzukiRightAperture a 0) E v) v).re ≤ 0 ∧
      WeakConvC (fun n => rightApertureExtension a (φ n) (u (φ n))) v := by
  obtain ⟨v, φ, hφ, _, hw, hv, hqv⟩ := exists_unit_nonpositive_weakLimit
    (isCompactOperator_ccmArchimedeanFormToAperture (suzukiRightAperture a 0))
    (ccmRestrictedWeilBoundedRemainder (suzukiRightAperture a 0) - (E : ℂ) • 1)
    (fun n => rightApertureExtension a n (u n))
    (fun n => (rightApertureExtension_norm a n (u n)).trans (hnorm n))
    (fun n => by
      rw [← operator_quadratic_eq_compactEnergy, operator_quadratic_rightApertureExtension]
      exact hq n)
  exact ⟨v, φ, hφ, hv, (operator_quadratic_eq_compactEnergy _ E v).le.trans hqv, hw⟩

/-- A weak limit of bounded shrinking-aperture vectors has support in
its limiting aperture, by compact physical convergence. -/
private theorem exists_rightAperture_limit_descent (a : SuzukiPositiveAperture)
    (u : (n : ℕ) → Space (suzukiRightAperture a n)) (hnorm : ∀ n, ‖u n‖ = 1)
    (v : Space (suzukiRightAperture a 0)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hw : WeakConvC (fun n => rightApertureExtension a (φ n) (u (φ n))) v) :
    ∃ v₀ : Space a, apertureExt (suzukiRightAperture_gt a 0).le v₀ = v := by
  have hphys := tendsto_of_weakConvC
    (isCompactOperator_ccmArchimedeanFormToAperture (suzukiRightAperture a 0)) hw
    (fun n => ((rightApertureExtension_norm a (φ n) (u (φ n))).trans (hnorm (φ n))).le)
  have hphys' : Tendsto
      (fun n => (ccmArchimedeanFormToAperture (suzukiRightAperture a 0)
        (rightApertureExtension a (φ n) (u (φ n))) : SoninL2)) atTop
      (𝓝 (ccmArchimedeanFormToAperture (suzukiRightAperture a 0) v : SoninL2)) :=
    (continuous_subtype_val.tendsto _).comp hphys
  have hs := indicatorCutoff_limit_suzukiRightAperture a φ hφ.tendsto_atTop
    (fun n => (ccmArchimedeanFormToAperture (suzukiRightAperture a 0)
      (rightApertureExtension a (φ n) (u (φ n))) : SoninL2))
    (ccmArchimedeanFormToAperture (suzukiRightAperture a 0) v : SoninL2)
    (fun n => rightApertureExtension_cutoff a (φ n) (u (φ n))) hphys'
  obtain ⟨v₀, hvval, _⟩ := exists_ccmArchimedeanFormDomain_of_limit_support
    a (suzukiRightAperture a 0) v
    (ccmArchimedeanFormToAperture (suzukiRightAperture a 0) v) rfl hs
  exact ⟨v₀, Subtype.ext ((apertureExt_val _ v₀).trans hvval)⟩

/-- Shrinking apertures preserve a nonzero nonpositive weak limit at every
real energy, including the zero-energy endpoint. -/
theorem exists_nonpositive_rightAperture_limit (a : SuzukiPositiveAperture) (E : ℝ)
    (u : (n : ℕ) → Space (suzukiRightAperture a n))
    (hnorm : ∀ n, ‖u n‖ = 1)
    (hq : ∀ n, (inner ℂ (operator (suzukiRightAperture a n) E (u n)) (u n)).re ≤ 0) :
    ∃ v : Space a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ v ≠ 0 ∧
      (inner ℂ (operator a E v) v).re ≤ 0 ∧
      WeakConvC (fun n => rightApertureExtension a (φ n) (u (φ n)))
        (apertureExt (suzukiRightAperture_gt a 0).le v) := by
  obtain ⟨v, φ, hφ, hv0, hvq, hw⟩ := exists_nonpositive_rightAperture_ambient_limit a E u hnorm hq
  obtain ⟨v₀, hext⟩ := exists_rightAperture_limit_descent a u hnorm v φ hφ hw
  refine ⟨v₀, φ, hφ, ?_, ?_, ?_⟩
  · intro hz
    apply hv0
    rw [← hext, hz, apertureExt_zero]
  · rw [← operator_quadratic_extension (suzukiRightAperture_gt a 0).le, hext]
    exact hvq
  · rw [hext]
    exact hw

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
