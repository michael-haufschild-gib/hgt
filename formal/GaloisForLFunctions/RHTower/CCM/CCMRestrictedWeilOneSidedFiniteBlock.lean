import GaloisForLFunctions.HTGeometry.HermitianOneSidedQuadratic
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilReducingFiniteBlock
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaSlepianDecomposition
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaSlepianStrictSource

/-!
# One-sided finite spectral obstruction for the literal CCM restricted-Weil form

The compact reducing-block theorem localizes every possible failure of restricted-Weil positivity
to a finite-dimensional exceptional space, but its operator-norm cutoff retains both signs of the
Birman--Schwinger spectrum.  Large negative eigenvalues are harmless for the form `I - K`.

This module performs the missing one-sided reduction inside the actual exceptional block.  The
dangerous subspace is the sum of eigenspaces of the literal zero-energy CCM Birman--Schwinger
operator with eigenvalue strictly greater than `1`.  The restricted-Weil form is strictly negative
on every nonzero vector in this subspace and nonnegative on its orthogonal complement.  Therefore
whole restricted-Weil positivity is equivalent to vanishing of precisely this one-sided subspace.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- At zero energy the Gamma--Slepian term vanishes identically: the actual Birman--Schwinger
pencil is exactly the negative compressed scalar--polar--prime remainder. -/
theorem ccmRestrictedWeilFormBirmanSchwinger_zero_eq_neg_remainder
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilFormBirmanSchwinger a 0 =
      -ccmRestrictedWeilFormRemainder a := by
  rw [ccmRestrictedWeilFormBirmanSchwinger_eq_gammaSlepian_sub_remainder]
  apply ContinuousLinearMap.ext
  intro u
  simp

/-- A reducing exceptional block for the zero-energy pencil is also invariant under the literal
compressed scalar--polar--prime remainder. -/
theorem ccmRestrictedWeilFormRemainder_exceptional_invariant
    (a : SuzukiPositiveAperture) (C : CCMRestrictedWeilReducingBlockCertificate a) :
    ∀ u ∈ C.exterior.orthogonal,
      ccmRestrictedWeilFormRemainder a u ∈ C.exterior.orthogonal := by
  intro u hu
  have h := C.exceptional_birmanSchwinger_invariant u hu
  rw [ccmRestrictedWeilFormBirmanSchwinger_zero_eq_neg_remainder] at h
  simpa using C.exterior.orthogonal.neg_mem h

/-- Below-minus-one spectral sector of the compressed scalar--polar--prime source remainder,
written as the above-one sector of its negative. -/
noncomputable def ccmRestrictedWeilNegativeSourceRemainderSubspace
    (a : SuzukiPositiveAperture) (C : CCMRestrictedWeilReducingBlockCertificate a) :
    Submodule ℂ C.exterior.orthogonal := by
  letI : InnerProductSpace ℂ C.exterior.orthogonal :=
    Submodule.innerProductSpace C.exterior.orthogonal
  exact @eigenSum C.exterior.orthogonal
    C.exterior.orthogonal.normedAddCommGroup
    (Submodule.innerProductSpace C.exterior.orthogonal)
    ((-ccmRestrictedWeilFormRemainder a).restrict (by
      intro u hu
      simpa using C.exterior.orthogonal.neg_mem
        (ccmRestrictedWeilFormRemainder_exceptional_invariant a C u hu))).toLinearMap 1

/-- Above-one spectral subspace of the literal CCM Birman--Schwinger operator inside a reducing
finite exceptional block. -/
noncomputable def ccmRestrictedWeilDangerousSubspace (a : SuzukiPositiveAperture)
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    Submodule ℂ C.exterior.orthogonal := by
  letI : InnerProductSpace ℂ C.exterior.orthogonal :=
    Submodule.innerProductSpace C.exterior.orthogonal
  exact @eigenSum C.exterior.orthogonal
    C.exterior.orthogonal.normedAddCommGroup
    (Submodule.innerProductSpace C.exterior.orthogonal)
    (((ccmRestrictedWeilFormBirmanSchwinger a 0).restrict
      C.exceptional_birmanSchwinger_invariant).toLinearMap) 1

/-- The operator-defined dangerous sector is exactly the below-minus-one spectral sector of the
literal compressed source remainder.  No Gamma--Slepian term remains. -/
theorem ccmRestrictedWeilDangerousSubspace_eq_negativeSourceRemainder
    (a : SuzukiPositiveAperture) (C : CCMRestrictedWeilReducingBlockCertificate a) :
    ccmRestrictedWeilDangerousSubspace a C =
      ccmRestrictedWeilNegativeSourceRemainderSubspace a C := by
  unfold ccmRestrictedWeilDangerousSubspace
    ccmRestrictedWeilNegativeSourceRemainderSubspace
  congr 1
  apply LinearMap.ext
  intro u
  have h := congrArg (fun T : CCMArchimedeanFormDomain a →L[ℂ]
      CCMArchimedeanFormDomain a => T (u : CCMArchimedeanFormDomain a))
    (ccmRestrictedWeilFormBirmanSchwinger_zero_eq_neg_remainder a)
  exact Subtype.ext h

/-- Exact one-sided sign classification of a literal CCM reducing block. -/
structure CCMRestrictedWeilOneSidedCertificate (a : SuzukiPositiveAperture)
    (C : CCMRestrictedWeilReducingBlockCertificate a) where
  dangerous : Submodule ℂ C.exterior.orthogonal
  dangerous_eq_upperSpectrum : dangerous = ccmRestrictedWeilDangerousSubspace a C
  dangerous_eq_negativeSourceRemainder : dangerous =
    ccmRestrictedWeilNegativeSourceRemainderSubspace a C
  dangerous_finiteDimensional : FiniteDimensional ℂ dangerous
  dangerous_strictly_negative : ∀ d : dangerous, d ≠ 0 →
    (ccmRestrictedWeilForm a
      (d : CCMArchimedeanFormDomain a) (d : CCMArchimedeanFormDomain a)).re < 0
  safe_exceptional_nonnegative : ∀ s : C.exterior.orthogonal,
    (∀ d : C.exterior.orthogonal, d ∈ dangerous →
      inner ℂ (d : CCMArchimedeanFormDomain a)
        (s : CCMArchimedeanFormDomain a) = 0) →
    0 ≤ (ccmRestrictedWeilForm a
      (s : CCMArchimedeanFormDomain a) (s : CCMArchimedeanFormDomain a)).re
  dangerous_source_remainder_debt : ∀ d : dangerous, d ≠ 0 →
    (inner ℂ
      (ccmRestrictedWeilFormRemainder a (d : CCMArchimedeanFormDomain a))
      (d : CCMArchimedeanFormDomain a)).re < -‖d‖ ^ 2
  safe_source_remainder_floor : ∀ s : C.exterior.orthogonal,
    (∀ d : C.exterior.orthogonal, d ∈ dangerous →
      inner ℂ (d : CCMArchimedeanFormDomain a)
        (s : CCMArchimedeanFormDomain a) = 0) →
    -‖s‖ ^ 2 ≤ (inner ℂ
      (ccmRestrictedWeilFormRemainder a (s : CCMArchimedeanFormDomain a))
      (s : CCMArchimedeanFormDomain a)).re
  dangerous_prime_overcompensation : ∀ d : dangerous, d ≠ 0 →
    ‖d‖ ^ 2 +
      (inner ℂ
        ((ccmArchimedeanRemainderScalar • ccmArchimedeanGammaSlepianGram a)
          (d : CCMArchimedeanFormDomain a))
        (d : CCMArchimedeanFormDomain a)).re +
      (inner ℂ
        (ccmRestrictedWeilFormPolarCompression a (d : CCMArchimedeanFormDomain a))
        (d : CCMArchimedeanFormDomain a)).re <
      (inner ℂ
        (ccmRestrictedWeilFormPrimeCompression a (d : CCMArchimedeanFormDomain a))
        (d : CCMArchimedeanFormDomain a)).re
  safe_prime_budget : ∀ s : C.exterior.orthogonal,
    (∀ d : C.exterior.orthogonal, d ∈ dangerous →
      inner ℂ (d : CCMArchimedeanFormDomain a)
        (s : CCMArchimedeanFormDomain a) = 0) →
    (inner ℂ
      (ccmRestrictedWeilFormPrimeCompression a (s : CCMArchimedeanFormDomain a))
      (s : CCMArchimedeanFormDomain a)).re ≤
      ‖s‖ ^ 2 +
        (inner ℂ
          ((ccmArchimedeanRemainderScalar • ccmArchimedeanGammaSlepianGram a)
            (s : CCMArchimedeanFormDomain a))
          (s : CCMArchimedeanFormDomain a)).re +
        (inner ℂ
          (ccmRestrictedWeilFormPolarCompression a (s : CCMArchimedeanFormDomain a))
          (s : CCMArchimedeanFormDomain a)).re
  positivity_iff_dangerous_vanishes :
    (∀ u : CCMArchimedeanFormDomain a, 0 ≤ (ccmRestrictedWeilForm a u u).re) ↔
      dangerous = ⊥

/-- For every positive aperture, the literal restricted-Weil problem has a finite-dimensional
one-sided obstruction: whole positivity holds exactly when the above-one Birman--Schwinger
spectral subspace vanishes. -/
theorem exists_ccmRestrictedWeil_oneSidedCertificate
    (a : SuzukiPositiveAperture) :
    ∃ C : CCMRestrictedWeilReducingBlockCertificate a,
      Nonempty (CCMRestrictedWeilOneSidedCertificate a C) := by
  obtain ⟨C⟩ := exists_ccmRestrictedWeil_reducingFiniteBlock a
  let K := ccmRestrictedWeilFormBirmanSchwinger a 0
  let F := C.exterior.orthogonal
  letI : InnerProductSpace ℂ F := Submodule.innerProductSpace C.exterior.orthogonal
  let T : F →ₗ[ℂ] F := (K.restrict C.exceptional_birmanSchwinger_invariant).toLinearMap
  let D : Submodule ℂ F := @eigenSum F F.normedAddCommGroup
    (Submodule.innerProductSpace C.exterior.orthogonal) T 1
  letI : FiniteDimensional ℂ F := C.exceptional_finiteDimensional
  letI : FiniteDimensional ℂ D := Submodule.finiteDimensional_of_le le_top
  have hKsymm : K.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a 0)
  have hTsymm : @LinearMap.IsSymmetric ℂ F inferInstance inferInstance
      (Submodule.innerProductSpace C.exterior.orthogonal) T :=
    hKsymm.restrict_invariant C.exceptional_birmanSchwinger_invariant
  have hform (f : F) :
      (ccmRestrictedWeilForm a
        (f : CCMArchimedeanFormDomain a) (f : CCMArchimedeanFormDomain a)).re =
        ‖f‖ ^ 2 - (inner ℂ f (T f)).re := by
    have hid := congrArg Complex.re
      (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a
        (f : CCMArchimedeanFormDomain a) (f : CCMArchimedeanFormDomain a))
    have hself : (inner ℂ (f : CCMArchimedeanFormDomain a)
        (f : CCMArchimedeanFormDomain a)).re = ‖f‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
        (f : CCMArchimedeanFormDomain a)).symm
    have hswitch : inner ℂ (K (f : CCMArchimedeanFormDomain a))
        (f : CCMArchimedeanFormDomain a) =
        inner ℂ (f : CCMArchimedeanFormDomain a)
          (K (f : CCMArchimedeanFormDomain a)) := hKsymm _ _
    change (ccmRestrictedWeilForm a
      (f : CCMArchimedeanFormDomain a) (f : CCMArchimedeanFormDomain a)).re =
      ‖f‖ ^ 2 - (inner ℂ (f : CCMArchimedeanFormDomain a)
        (K (f : CCMArchimedeanFormDomain a))).re
    simpa only [K, Complex.sub_re, hself, hswitch] using hid
  have hsourceform (f : F) :
      (ccmRestrictedWeilForm a
        (f : CCMArchimedeanFormDomain a) (f : CCMArchimedeanFormDomain a)).re =
        ‖f‖ ^ 2 + (inner ℂ
          (ccmRestrictedWeilFormRemainder a (f : CCMArchimedeanFormDomain a))
          (f : CCMArchimedeanFormDomain a)).re := by
    have hid := congrArg Complex.re
      (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a
        (f : CCMArchimedeanFormDomain a) (f : CCMArchimedeanFormDomain a))
    rw [ccmRestrictedWeilFormBirmanSchwinger_zero_eq_neg_remainder] at hid
    have hself : (inner ℂ (f : CCMArchimedeanFormDomain a)
        (f : CCMArchimedeanFormDomain a)).re = ‖f‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
        (f : CCMArchimedeanFormDomain a)).symm
    simpa only [neg_apply, inner_neg_left, Complex.sub_re, Complex.add_re,
      Complex.neg_re, sub_neg_eq_add, hself] using hid
  have hdanger : ∀ d : D, d ≠ 0 →
      (ccmRestrictedWeilForm a
        (d : CCMArchimedeanFormDomain a) (d : CCMArchimedeanFormDomain a)).re < 0 := by
    intro d hd0
    have hgt := @re_inner_apply_gt_of_mem_eigenSum (Module.finrank ℂ F) F
      F.normedAddCommGroup (Submodule.innerProductSpace C.exterior.orthogonal)
      C.exceptional_finiteDimensional T hTsymm rfl 1 (d : F) d.property
      (fun hz => hd0 (Subtype.ext hz))
    rw [one_mul] at hgt
    rw [hform]
    linarith
  have hsafe : ∀ s : F, (∀ d : F, d ∈ D →
      inner ℂ (d : CCMArchimedeanFormDomain a)
        (s : CCMArchimedeanFormDomain a) = 0) →
      0 ≤ (ccmRestrictedWeilForm a
        (s : CCMArchimedeanFormDomain a) (s : CCMArchimedeanFormDomain a)).re := by
    intro s hs
    have hsperp : s ∈ @Submodule.orthogonal ℂ F inferInstance F.normedAddCommGroup
        (Submodule.innerProductSpace C.exterior.orthogonal) D := by
      rw [Submodule.mem_orthogonal]
      exact hs
    have hle := @re_inner_apply_le_of_mem_eigenSum_orthogonal (Module.finrank ℂ F) F
      F.normedAddCommGroup (Submodule.innerProductSpace C.exterior.orthogonal)
      C.exceptional_finiteDimensional T hTsymm rfl 1 s hsperp
    rw [one_mul] at hle
    rw [hform]
    linarith
  have hsourceDebt : ∀ d : D, d ≠ 0 →
      (inner ℂ
        (ccmRestrictedWeilFormRemainder a (d : CCMArchimedeanFormDomain a))
        (d : CCMArchimedeanFormDomain a)).re < -‖d‖ ^ 2 := by
    intro d hd0
    have hneg := hdanger d hd0
    rw [hsourceform] at hneg
    change (inner ℂ
      (ccmRestrictedWeilFormRemainder a (d : CCMArchimedeanFormDomain a))
      (d : CCMArchimedeanFormDomain a)).re < -‖(d : F)‖ ^ 2
    linarith
  have hsourceFloor : ∀ s : F, (∀ d : F, d ∈ D →
      inner ℂ (d : CCMArchimedeanFormDomain a)
        (s : CCMArchimedeanFormDomain a) = 0) →
      -‖s‖ ^ 2 ≤ (inner ℂ
        (ccmRestrictedWeilFormRemainder a (s : CCMArchimedeanFormDomain a))
        (s : CCMArchimedeanFormDomain a)).re := by
    intro s hs
    have hnonneg := hsafe s hs
    rw [hsourceform] at hnonneg
    linarith
  have hprimeOvercompensation : ∀ d : D, d ≠ 0 →
      ‖d‖ ^ 2 +
        (inner ℂ
          ((ccmArchimedeanRemainderScalar • ccmArchimedeanGammaSlepianGram a)
            (d : CCMArchimedeanFormDomain a))
          (d : CCMArchimedeanFormDomain a)).re +
        (inner ℂ
          (ccmRestrictedWeilFormPolarCompression a (d : CCMArchimedeanFormDomain a))
          (d : CCMArchimedeanFormDomain a)).re <
        (inner ℂ
          (ccmRestrictedWeilFormPrimeCompression a (d : CCMArchimedeanFormDomain a))
          (d : CCMArchimedeanFormDomain a)).re := by
    intro d hd0
    have hdebt := hsourceDebt d hd0
    rw [ccmRestrictedWeilFormRemainder_eq_scalarGamma_add_polar_sub_prime] at hdebt
    simp only [add_apply, sub_apply, inner_add_left, inner_sub_left,
      Complex.add_re, Complex.sub_re] at hdebt
    have hnorm : ‖d‖ = ‖(d : F)‖ := rfl
    rw [hnorm] at hdebt
    change ‖(d : F)‖ ^ 2 + _ + _ < _
    linarith
  have hsafePrimeBudget : ∀ s : F, (∀ d : F, d ∈ D →
      inner ℂ (d : CCMArchimedeanFormDomain a)
        (s : CCMArchimedeanFormDomain a) = 0) →
      (inner ℂ
        (ccmRestrictedWeilFormPrimeCompression a (s : CCMArchimedeanFormDomain a))
        (s : CCMArchimedeanFormDomain a)).re ≤
        ‖s‖ ^ 2 +
          (inner ℂ
            ((ccmArchimedeanRemainderScalar • ccmArchimedeanGammaSlepianGram a)
              (s : CCMArchimedeanFormDomain a))
            (s : CCMArchimedeanFormDomain a)).re +
          (inner ℂ
            (ccmRestrictedWeilFormPolarCompression a (s : CCMArchimedeanFormDomain a))
            (s : CCMArchimedeanFormDomain a)).re := by
    intro s hs
    have hfloor := hsourceFloor s hs
    rw [ccmRestrictedWeilFormRemainder_eq_scalarGamma_add_polar_sub_prime] at hfloor
    simp only [add_apply, sub_apply, inner_add_left, inner_sub_left,
      Complex.add_re, Complex.sub_re] at hfloor
    linarith
  refine ⟨C, ⟨⟨D, ?_, ?_, inferInstance, hdanger, hsafe,
    hsourceDebt, hsourceFloor, hprimeOvercompensation, hsafePrimeBudget, ?_⟩⟩⟩
  · rfl
  · change ccmRestrictedWeilDangerousSubspace a C =
      ccmRestrictedWeilNegativeSourceRemainderSubspace a C
    exact ccmRestrictedWeilDangerousSubspace_eq_negativeSourceRemainder a C
  constructor
  · intro hpositive
    by_contra hne
    obtain ⟨d, hd0⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hne)
    have hneg := hdanger d hd0
    exact (not_lt_of_ge (hpositive (d : CCMArchimedeanFormDomain a))) hneg
  · intro hbot
    apply C.positivity_iff_exceptional.2
    intro f
    have hupper :=
      (@eigenSum_eq_bot_iff_global_quadratic_upper (Module.finrank ℂ F) F
        F.normedAddCommGroup (Submodule.innerProductSpace C.exterior.orthogonal)
        C.exceptional_finiteDimensional T hTsymm rfl 1).1 hbot f
    rw [one_mul] at hupper
    rw [hform]
    linarith

end RHTower
