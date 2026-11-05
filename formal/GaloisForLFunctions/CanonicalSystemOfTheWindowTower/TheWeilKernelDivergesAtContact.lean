import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLocalWeilKernelIsHermiteBiehler

/-!
# The exact Weil kernel diverges at finite contact

Isometric aperture inclusions make diagonal Fourier kernels monotone. A uniform bound up to
contact would extend from the strict smooth core to a null ground vector. Fourier uniqueness
excludes that bound at some fixed evaluation point. Thus finite contact is a singularity of
the actual reproducing-kernel chain, without a boundary-trace assumption.
-/

open Complex MeasureTheory Set Topology Zeta23
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower SquareRootThreshold WindowVisibilityLaw
open ArithmeticContinuationAndCriticalEnergy

namespace WeilHilbertBeforeContact

theorem norm_eval_sq_le (a : PrecontactAperture) (z : ℂ)
    (x : WeilHilbertBeforeContact a) :
    ‖eval a z x‖ ^ 2 ≤ ‖evalVector a z‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [← inner_evalVector]
  calc
    _ ≤ (‖evalVector a z‖ * ‖x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (norm_inner_le_norm (𝕜 := ℂ) (E := WeilHilbertBeforeContact a) _ _)
    _ = _ := mul_pow _ _ _

/-- Increasing the literal aperture increases every diagonal evaluation kernel. -/
theorem norm_evalVector_mono {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    ‖evalVector a z‖ ≤ ‖evalVector b z‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (E := WeilHilbertBeforeContact b)
    (evalVector b z) (inclusion hab (evalVector a z))
  rw [inner_evalVector, show eval b z (inclusion hab (evalVector a z)) =
      eval a z (evalVector a z) from fourier_inclusion hab _ z,
    evalVector_self, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), LinearIsometry.norm_map] at h
  have hp := norm_pos_iff.mpr (evalVector_ne_zero a z)
  apply (mul_le_mul_iff_right₀ hp).mp
  simpa only [pow_two, mul_comm] using h

theorem norm_evalVector_sq_mono {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    ‖evalVector a z‖ ^ 2 ≤ ‖evalVector b z‖ ^ 2 :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_evalVector_mono hab z)

end WeilHilbertBeforeContact

/-- Fourier evaluation in the original closed-form norm, including at contact. -/
def formEval (a : SuzukiPositiveAperture) (z : ℂ) : CCMArchimedeanFormDomain a →L[ℂ] ℂ :=
  (suzukiTaSpectralMoment a (star z)).comp (suzukiTaFromFormCLM a)

theorem formEval_smooth (a : SuzukiPositiveAperture) (z : ℂ)
    (u : CCMComplexSmoothInteriorSource a) :
    formEval a z u.toCCMFormVector = ∫ x : ℝ, Complex.exp (I * z * (x : ℂ)) * u x := by
  change suzukiTaSpectralMoment a (star z)
    (suzukiTaSmoothCoreToHilbert a (ccmComplexSmoothInteriorSourceToSuzukiTaSmoothCore a u)) = _
  rw [suzukiTaSpectralMoment_smoothCore_eq_integral, star_star]
  rfl

/-- A nonzero physical source has a nonzero entire Fourier value. -/
theorem exists_formEval_ne_zero (a : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain a)
    (hq : ccmArchimedeanFormToAperture a q ≠ 0) : ∃ z : ℂ, formEval a z q ≠ 0 := by
  by_contra! hz
  let y := suzukiTaFromFormCLM a q
  let g := suzukiApertureZeroExtendL2 (suzukiTaPhysicalEmbedding a y)
  have hg : g = 0 :=
    eq_zero_of_supported_fourier_constant_on_xiZeros a.2.le
      (suzukiApertureZeroExtendL2_cutoff _) (fun z _ => by
        exact (suzukiTaSpectralMoment_star_eq_physicalFourier a y z).symm.trans (hz z))
  have hphys : suzukiTaPhysicalEmbedding a y = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_suzukiApertureZeroExtendL2]
    change ‖g‖ = 0
    rw [hg, norm_zero]
  have hy : y = 0 := by
    apply suzukiTaPhysicalEmbedding_injective a
    simpa only [map_zero] using hphys
  have hq0 : q = 0 := by
    have h := congrArg (suzukiTaToFormCLM a) hy
    simpa only [y, suzukiTaToFormCLM_fromForm, map_zero] using h
  exact hq (by rw [hq0, map_zero])

open WeilHilbertBeforeContact

/-- A bound on all earlier kernels passes to every vector of the contact form domain. -/
theorem formEval_bound_of_earlier_kernel_bound (a : SuzukiPositiveAperture)
    (ha : (a.1 : EReal) = onsetAperture zetaZeroConfig) (z : ℂ) (C : ℝ)
    (hC : ∀ b : PrecontactAperture, ‖evalVector b z‖ ^ 2 ≤ C)
    (q : CCMArchimedeanFormDomain a) :
    ‖formEval a z q‖ ^ 2 ≤ C * ccmRestrictedWeilSourceQuadratic a q := by
  have hcore (u : CCMComplexSmoothInteriorSource a) :
      ‖formEval a z u.toCCMFormVector‖ ^ 2 ≤
        C * ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
    obtain ⟨b, hba, hsupp⟩ := exists_strict_smaller_aperture_of_compact_tsupport a u
    let B : PrecontactAperture :=
      ⟨b, (EReal.coe_lt_coe_iff.mpr hba).trans_eq ha⟩
    let ub := u.restrictAperture b hsupp
    let v : SuzukiTaSmoothCore b := ccmComplexSmoothInteriorSourceToSuzukiTaSmoothCore b ub
    let x : WeilHilbertBeforeContact B := smoothCore B v
    have he : eval B z x = formEval a z u.toCCMFormVector := by
      rw [formEval_smooth]
      exact eval_smoothCore_eq_integral B z v
    have hnorm : ‖x‖ ^ 2 = ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
      rw [norm_sq_eq_weil, ccmRestrictedWeilForm_self_re_eq_source]
      change ccmRestrictedWeilSourceQuadratic b ub.toCCMFormVector = _
      exact (ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hba.le
        (u.restrictAperture_toCCMFormVector_val b hsupp).symm).symm
    calc
      _ = ‖eval B z x‖ ^ 2 := by rw [he]
      _ ≤ ‖evalVector B z‖ ^ 2 * ‖x‖ ^ 2 := norm_eval_sq_le B z x
      _ ≤ C * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right (hC B) (sq_nonneg _)
      _ = _ := by rw [hnorm]
  have hclosed : IsClosed {q : CCMArchimedeanFormDomain a |
      ‖formEval a z q‖ ^ 2 ≤ C * ccmRestrictedWeilSourceQuadratic a q} :=
    isClosed_le ((formEval a z).continuous.norm.pow 2)
      (continuous_const.mul (continuous_suzukiWeilIntervalSourceQuadratic a))
  have hsub : Set.range (fun u : CCMComplexSmoothInteriorSource a => u.toCCMFormVector) ⊆
      {q | ‖formEval a z q‖ ^ 2 ≤ C * ccmRestrictedWeilSourceQuadratic a q} := by
    rintro _ ⟨u, rfl⟩
    exact hcore u
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [(denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).closure_eq] at hcl
  exact hcl (mem_univ q)

/-- Either the onset is infinite, or a fixed Fourier evaluation becomes unbounded below it. -/
theorem riemannHypothesis_or_kernel_unbounded_at_contact :
    RiemannHypothesis ∨ ∃ a : SuzukiPositiveAperture,
      (a.1 : EReal) = onsetAperture zetaZeroConfig ∧
      ccmRestrictedWeilGroundEnergy a = 0 ∧
      ∃ z : ℂ, ∀ C : ℝ, ∃ b : PrecontactAperture, C < ‖evalVector b z‖ ^ 2 := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  let a : SuzukiPositiveAperture := ⟨zetaContactAperture, zetaContactAperture_pos hRH⟩
  have ha : (a.1 : EReal) = onsetAperture zetaZeroConfig :=
    (onsetAperture_zeta_eq_contact_of_not_rh hRH).symm
  have hground : ccmRestrictedWeilGroundEnergy a = 0 :=
    ccmRestrictedWeilGroundEnergy_contact_eq_zero hRH
  obtain ⟨q, hq, hQ⟩ := ccmRestrictedWeilSource_exists_groundFormState a
  rw [hground, zero_mul] at hQ
  obtain ⟨z, hz⟩ := exists_formEval_ne_zero a q hq
  refine Or.inr ⟨a, ha, hground, z, ?_⟩
  intro C
  by_contra! hC
  have h := formEval_bound_of_earlier_kernel_bound a ha z C hC q
  rw [hQ, mul_zero] at h
  exact hz (norm_eq_zero.mp (by nlinarith only [h, norm_nonneg (formEval a z q)]))

/-- The singularity is approached monotonically in the original aperture coordinate. -/
theorem riemannHypothesis_or_kernel_tends_to_top_at_contact :
    RiemannHypothesis ∨ ∃ a : SuzukiPositiveAperture,
      (a.1 : EReal) = onsetAperture zetaZeroConfig ∧
      ccmRestrictedWeilGroundEnergy a = 0 ∧
      ∃ z : ℂ, ∀ C : ℝ, ∃ b₀ : PrecontactAperture,
        ∀ b : PrecontactAperture, b₀.1.1 ≤ b.1.1 → C < ‖evalVector b z‖ ^ 2 := by
  rcases riemannHypothesis_or_kernel_unbounded_at_contact with hRH | ⟨a, ha, hg, z, hz⟩
  · exact Or.inl hRH
  refine Or.inr ⟨a, ha, hg, z, fun C => ?_⟩
  obtain ⟨b₀, hb₀⟩ := hz C
  exact ⟨b₀, fun b hb => hb₀.trans_le (norm_evalVector_sq_mono hb z)⟩

/-- Finite contact retains window positivity while the earlier inverse kernels diverge. -/
theorem riemannHypothesis_or_positive_contact_with_unbounded_kernel :
    RiemannHypothesis ∨ ∃ a : SuzukiPositiveAperture,
      (a.1 : EReal) = onsetAperture zetaZeroConfig ∧
      WindowPositiveAt zetaZeroConfig a.1 ∧
      ∃ z : ℂ, ∀ C : ℝ, ∃ b : PrecontactAperture, C < ‖evalVector b z‖ ^ 2 := by
  rcases riemannHypothesis_or_kernel_unbounded_at_contact with hRH | ⟨a, ha, _, z, hz⟩
  · exact Or.inl hRH
  exact Or.inr ⟨a, ha,
    (windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig a.2.le).mpr ha.le,
    z, hz⟩

#print axioms WeilHilbertBeforeContact.norm_evalVector_sq_mono
#print axioms formEval_bound_of_earlier_kernel_bound
#print axioms riemannHypothesis_or_kernel_unbounded_at_contact
#print axioms riemannHypothesis_or_kernel_tends_to_top_at_contact
#print axioms riemannHypothesis_or_positive_contact_with_unbounded_kernel

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
