import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFormTranslation
import GaloisForLFunctions.RHTower.CCM.CCMFirstContactSourceKernel

/-!
# Full completed-source translation and first-contact saturation

The literal Γ energy and prime autocorrelations are translation-invariant. The two polar
coordinates transform by opposite real characters, so their cross term is invariant too.
This removes the pole constraint from the existing translation law. Consequently a first-contact
null state cannot arise by translating any state from a narrower aperture. This is a necessary
source-geometry law, not RH or an exclusion of first contact.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct FourierTransform

noncomputable section
namespace RHTower

private theorem full_translation_pairing (t h : ℝ) (f : SoninL2) :
    inner ℂ (logTranslationCLM t (logTranslationCLM h f)) (logTranslationCLM h f) =
      inner ℂ (logTranslationCLM t f) f := by
  rw [logTranslationCLM_add_apply, add_comm t h, ← logTranslationCLM_add_apply]
  exact (MellinL2.additiveTranslationUnitary h).inner_map_map _ _

private theorem polar_translation_cross_cancel
    (h : ℝ) (m p : ℂ) :
    ((starRingEnd ℂ) ((Real.exp (h / 2) : ℂ) * m) *
        ((Real.exp (-h / 2) : ℂ) * p) +
      (starRingEnd ℂ) ((Real.exp (-h / 2) : ℂ) * p) *
        ((Real.exp (h / 2) : ℂ) * m)) =
      (starRingEnd ℂ) m * p + (starRingEnd ℂ) p * m := by
  have he : (Real.exp (h / 2) : ℂ) * (Real.exp (-h / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have : h / 2 + -h / 2 = 0 := by ring
    rw [this]
    simp
  rw [map_mul, map_mul]
  simp only [Complex.conj_ofReal]
  calc
    (Real.exp (h / 2) : ℂ) * (starRingEnd ℂ) m *
        ((Real.exp (-h / 2) : ℂ) * p) +
        (Real.exp (-h / 2) : ℂ) * (starRingEnd ℂ) p *
          ((Real.exp (h / 2) : ℂ) * m) =
        ((Real.exp (h / 2) : ℂ) * (Real.exp (-h / 2) : ℂ)) *
          ((starRingEnd ℂ) m * p + (starRingEnd ℂ) p * m) := by ring
    _ = _ := by rw [he, one_mul]

theorem ccmRestrictedWeilSourceQuadratic_translate_unconstrained
    {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic b
        (ccmArchimedeanFormTranslate h hab u) =
      ccmRestrictedWeilSourceQuadratic a u := by
  have hab' : a.1 ≤ b.1 := by linarith [abs_nonneg h]
  obtain ⟨w, hwval⟩ := exists_ccmArchimedeanFormDomain_extension hab' u
  let v := ccmArchimedeanFormTranslate h hab u
  have hgamma :
      (∫ x, 2 * gammaHardyPhaseRate (2 * Real.pi * x) *
          ‖(v.1 : ℝ → ℂ) x‖ ^ 2) =
      ∫ x, 2 * gammaHardyPhaseRate (2 * Real.pi * x) *
          ‖(w.1 : ℝ → ℂ) x‖ ^ 2 := by
    rw [hwval]
    apply integral_congr_ae
    have hp := (ccmArchimedeanPhaseMul_coeFn h u.1).filter_mono
      (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [hp] with x hx
    change _ * ‖ccmArchimedeanPhaseMul h u.1 x‖ ^ 2 = _
    rw [hx, norm_mul, MellinL2.norm_fourierPhase, one_mul]
  have hpair : ∀ t : ℝ,
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b v : SoninL2))
        (ccmArchimedeanFormToAperture b v : SoninL2) =
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b w : SoninL2))
        (ccmArchimedeanFormToAperture b w : SoninL2) := by
    intro t
    rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq hwval]
    change inner ℂ (logTranslationCLM t
      (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2))
        (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2) = _
    rw [ccmArchimedeanFormTranslate_physical]
    exact full_translation_pairing t h _
  have hpolar :
      ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (-1 / 2))
            (ccmArchimedeanFormToAperture b v)) *
          inner ℂ (ccmPolarApertureVector b (1 / 2))
            (ccmArchimedeanFormToAperture b v) +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (1 / 2))
            (ccmArchimedeanFormToAperture b v)) *
          inner ℂ (ccmPolarApertureVector b (-1 / 2))
            (ccmArchimedeanFormToAperture b v)) =
      ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (-1 / 2))
            (ccmArchimedeanFormToAperture b w)) *
          inner ℂ (ccmPolarApertureVector b (1 / 2))
            (ccmArchimedeanFormToAperture b w) +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (1 / 2))
            (ccmArchimedeanFormToAperture b w)) *
          inner ℂ (ccmPolarApertureVector b (-1 / 2))
            (ccmArchimedeanFormToAperture b w)) := by
    rw [show v = ccmArchimedeanFormTranslate h hab u by rfl,
      inner_polar_ccmArchimedeanFormTranslate,
      inner_polar_ccmArchimedeanFormTranslate]
    rw [← inner_ccmPolarApertureVector_eq_of_val_eq hab' (-1 / 2) hwval,
      ← inner_ccmPolarApertureVector_eq_of_val_eq hab' (1 / 2) hwval]
    have hm : -(-1 / 2 : ℝ) * h = h / 2 := by ring
    have hp : -(1 / 2 : ℝ) * h = -h / 2 := by ring
    rw [hm, hp]
    exact polar_translation_cross_cancel h _ _
  calc
    ccmRestrictedWeilSourceQuadratic b v =
        ccmRestrictedWeilSourceQuadratic b w := by
      unfold ccmRestrictedWeilSourceQuadratic
      dsimp only
      rw [hgamma, hpolar]
      simp_rw [hpair]
    _ = ccmRestrictedWeilSourceQuadratic a u :=
      ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab' hwval

/-- A zero-energy physical state at first contact cannot be a translation of a state
admitted at any strictly narrower aperture. -/
theorem ccmFirstContact_no_narrow_translate
    (a : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain a)
    (hbefore : ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
      0 < ccmRestrictedWeilGroundEnergy b)
    (hqphys : ccmArchimedeanFormToAperture a q ≠ 0)
    (hqzero : ccmRestrictedWeilSourceQuadratic a q = 0)
    (b : SuzukiPositiveAperture) (hba : b.1 < a.1)
    (h : ℝ) (hfit : b.1 + |h| ≤ a.1)
    (v : CCMArchimedeanFormDomain b) :
    q ≠ ccmArchimedeanFormTranslate h hfit v := by
  intro hq
  have hnorm : ‖ccmArchimedeanFormToAperture a q‖ =
      ‖ccmArchimedeanFormToAperture b v‖ := by
    rw [hq]
    exact norm_ccmArchimedeanFormTranslate_physical h hfit v
  have hvphys : ccmArchimedeanFormToAperture b v ≠ 0 := by
    intro hv
    apply hqphys
    apply norm_eq_zero.mp
    rw [hnorm, hv, norm_zero]
  have hsource : ccmRestrictedWeilSourceQuadratic b v = 0 := by
    rw [← ccmRestrictedWeilSourceQuadratic_translate_unconstrained h hfit v]
    rwa [← hq]
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source b v
  rw [hsource] at hfloor
  have hpos : 0 < ccmRestrictedWeilGroundEnergy b *
      ‖ccmArchimedeanFormToAperture b v‖ ^ 2 :=
    mul_pos (hbefore b hba) (pow_pos (norm_pos_iff.mpr hvphys) 2)
  exact (not_le_of_gt hpos) hfloor

/-- Source-level strengthening of the RH-or-first-contact alternative: a failure of RH
produces a physical exact-kernel state irreducible under translation from every narrower aperture.
This does not exclude such a state. -/
theorem riemannHypothesis_or_ccmFirstContactTranslationSaturation :
    RiemannHypothesis ∨
      ∃ (a : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain a),
        ccmRestrictedWeilGroundEnergy a = 0 ∧
        (∀ b : SuzukiPositiveAperture, b.1 < a.1 →
          0 < ccmRestrictedWeilGroundEnergy b) ∧
        ccmArchimedeanFormToAperture a q ≠ 0 ∧
        ccmRestrictedWeilZeroFormOperator a q = 0 ∧
        (∀ (b : SuzukiPositiveAperture) (h : ℝ)
            (hfit : b.1 + |h| ≤ a.1) (v : CCMArchimedeanFormDomain b),
          b.1 < a.1 → q ≠ ccmArchimedeanFormTranslate h hfit v) := by
  rcases riemannHypothesis_or_ccmFirstContactPhysicalSourceKernel with hRH | hcontact
  · exact Or.inl hRH
  · rcases hcontact with ⟨a, q, hground, hbefore, hqphys, hkernel, _⟩
    right
    have hqzero : ccmRestrictedWeilSourceQuadratic a q = 0 := by
      rw [← ccmRestrictedWeilForm_self_re_eq_source,
        ← inner_ccmRestrictedWeilZeroFormOperator, hkernel]
      simp
    exact ⟨a, q, hground, hbefore, hqphys, hkernel,
      fun b h hfit v hba =>
        ccmFirstContact_no_narrow_translate a q hbefore hqphys hqzero b hba h hfit v⟩

end RHTower
