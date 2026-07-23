import GaloisForLFunctions.HTGeometry.GammaPolePrincipalRemainderFreeness
import GaloisForLFunctions.HTGeometry.GammaInverseBranchLowerJetFreeness
import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalRelativeFreeness
import GaloisForLFunctions.HTGeometry.GammaPoleScaleDerivativeLaurentFreeness
import GaloisForLFunctions.HTGeometry.GammaPoleScaleUnitRelativeFreeness

/-!
# Joint freeness of the Gamma pole scale and principal remainders

The factorial pole scale and the analytic finite-part jets were previously controlled in separate
relative-freeness statements.  The exact finite-part/unit reflection makes the latter a nonzero
diagonal transform of the regular-unit coefficient frame, so the existing scale--unit theorem
closes to joint scale--remainder freeness over the moving-center field.
-/

open MvPolynomial Polynomial LaurentPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaPoleScaleFinitePartNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm := ratNatEval.toAlgebra

/-- Nonzero rational-base rescaling from regular-unit coefficients to finite-part jets. -/
def gammaPoleFinitePartRationalScale : Option ℕ → GammaPoleRationalBase
  | none => 1
  | some m => RatFunc.C (-(m.factorial : ℂ))

theorem gammaPoleFinitePartRationalScale_ne_zero (o : Option ℕ) :
    gammaPoleFinitePartRationalScale o ≠ 0 := by
  rcases o with (_ | m)
  · exact one_ne_zero
  · have hfac : ((m.factorial : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero m
    simpa [gammaPoleFinitePartRationalScale] using
      RatFunc.C_injective.ne (neg_ne_zero.mpr hfac)

/-- Distinguished reciprocal factorial scale followed by every analytic Gamma finite-part jet. -/
def gammaPoleScaleAndFinitePartJetFamily : Option ℕ → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some m => gammaPoleFinitePartJetGerm m

/-- Rational moving-center evaluation on the scale--finite-part frame. -/
def gammaPoleScaleAndFinitePartJetRationalEval :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval gammaPoleScaleAndFinitePartJetFamily

theorem gammaPoleScaleAndFinitePartJetRationalEval_eq_comp :
    gammaPoleScaleAndFinitePartJetRationalEval =
      gammaPoleScaleAndUnitPositiveCoefficientRationalEval.comp
        (mvPolynomialDiagonalScaleRing
          gammaPoleFinitePartRationalScale).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndFinitePartJetRationalEval,
      gammaPoleScaleAndUnitPositiveCoefficientRationalEval,
      mvPolynomialDiagonalScaleRing]
  · intro o
    rcases o with (_ | m)
    · simp [gammaPoleScaleAndFinitePartJetRationalEval,
        gammaPoleScaleAndFinitePartJetFamily,
        gammaPoleScaleAndUnitPositiveCoefficientRationalEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        gammaPoleFinitePartRationalScale,
        mvPolynomialDiagonalScaleRing]
    · simp [gammaPoleScaleAndFinitePartJetRationalEval,
        gammaPoleScaleAndFinitePartJetFamily,
        gammaPoleScaleAndUnitPositiveCoefficientRationalEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        gammaPoleFinitePartRationalScale,
        mvPolynomialDiagonalScaleRing,
        gammaPoleFinitePartJetGerm_eq_unitCoefficient]

theorem gammaPoleScaleAndFinitePartJetRationalEval_injective :
    Function.Injective gammaPoleScaleAndFinitePartJetRationalEval := by
  rw [gammaPoleScaleAndFinitePartJetRationalEval_eq_comp]
  exact gammaPoleScaleAndUnitPositiveCoefficientRationalEval_injective.comp
    (mvPolynomialDiagonalScaleRing_injective
      gammaPoleFinitePartRationalScale
      gammaPoleFinitePartRationalScale_ne_zero)

/-- **Scale--principal-remainder universality law.**  The reciprocal factorial pole scale and all
jets of the canonical analytic principal remainder are jointly algebraically independent over the
full rational moving-pole field `ℂ(N)`. -/
theorem algebraicIndependent_gammaPoleScaleAndFinitePartJet_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleScaleAndFinitePartJetFamily := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndFinitePartJetRationalEval,
    MvPolynomial.aeval_def] using
      gammaPoleScaleAndFinitePartJetRationalEval_injective

/-- Polynomial presentation after separating the factorial scale from the finite-part jets. -/
def gammaPoleScaleAndFinitePartJetPolynomialEval :
    Polynomial (MvPolynomial ℕ GammaPoleRationalBase) →+* NatGerm :=
  Polynomial.eval₂RingHom gammaPoleFinitePartJetRationalEval
    reciprocalSignedFactorialGerm

theorem gammaPoleScaleAndFinitePartJetPolynomialEval_eq_comp :
    gammaPoleScaleAndFinitePartJetPolynomialEval =
      gammaPoleScaleAndFinitePartJetRationalEval.comp
        (MvPolynomial.optionEquivLeft
          GammaPoleRationalBase ℕ).symm.toRingHom := by
  apply Polynomial.ringHom_ext
  · intro p
    let lhs : MvPolynomial ℕ GammaPoleRationalBase →+*
        MvPolynomial (Option ℕ) GammaPoleRationalBase :=
      (MvPolynomial.optionEquivLeft
        GammaPoleRationalBase ℕ).symm.toRingHom.comp Polynomial.C
    have hlhs : lhs = (MvPolynomial.rename some).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [lhs]
      · intro k
        simp [lhs, MvPolynomial.optionEquivLeft_symm_C_X]
    calc
      gammaPoleScaleAndFinitePartJetPolynomialEval (Polynomial.C p) =
          gammaPoleFinitePartJetRationalEval p := by
        simp [gammaPoleScaleAndFinitePartJetPolynomialEval]
      _ = gammaPoleScaleAndFinitePartJetRationalEval
          (MvPolynomial.rename some p) := by
        simp [gammaPoleFinitePartJetRationalEval,
          gammaPoleScaleAndFinitePartJetRationalEval,
          gammaPoleScaleAndFinitePartJetFamily,
          MvPolynomial.eval₂_rename, Function.comp_def]
      _ = gammaPoleScaleAndFinitePartJetRationalEval
          ((MvPolynomial.optionEquivLeft
            GammaPoleRationalBase ℕ).symm (Polynomial.C p)) := by
        have hp := RingHom.congr_fun hlhs p
        change (MvPolynomial.optionEquivLeft
            GammaPoleRationalBase ℕ).symm (Polynomial.C p) =
          MvPolynomial.rename some p at hp
        exact congrArg gammaPoleScaleAndFinitePartJetRationalEval hp.symm
  · simp [gammaPoleScaleAndFinitePartJetPolynomialEval,
      gammaPoleScaleAndFinitePartJetRationalEval,
      gammaPoleScaleAndFinitePartJetFamily]

theorem gammaPoleScaleAndFinitePartJetPolynomialEval_injective :
    Function.Injective gammaPoleScaleAndFinitePartJetPolynomialEval := by
  rw [gammaPoleScaleAndFinitePartJetPolynomialEval_eq_comp]
  exact gammaPoleScaleAndFinitePartJetRationalEval_injective.comp
    (MvPolynomial.optionEquivLeft
      GammaPoleRationalBase ℕ).symm.injective

/-- Laurent evaluation in the factorial scale with analytic finite-part jet coefficients. -/
def gammaPoleScaleAndFinitePartJetLaurentEval :
    LaurentPolynomial (MvPolynomial ℕ GammaPoleRationalBase) →+* NatGerm :=
  LaurentPolynomial.eval₂ gammaPoleFinitePartJetRationalEval
    reciprocalSignedFactorialGermUnit

/-- **Laurent scale--principal-remainder reflection.**  No nonzero finite Laurent relation in the
Gamma factorial scale with polynomial finite-part-jet coefficients can vanish across the pole
tower, even over the moving-center field `ℂ(N)`. -/
theorem gammaPoleScaleAndFinitePartJetLaurentEval_injective :
    Function.Injective gammaPoleScaleAndFinitePartJetLaurentEval := by
  apply laurentPolynomial_eval₂_injective_of_polynomial_eval₂_injective
  simpa [gammaPoleScaleAndFinitePartJetPolynomialEval,
    reciprocalSignedFactorialGermUnit_val] using
      gammaPoleScaleAndFinitePartJetPolynomialEval_injective

/-! ## Finite-part/covariant-residue coordinate tomography -/

/-- A tail coordinate map commutes with the canonical inclusion into an option-indexed frame. -/
theorem optionHeadLiftAlgHom_rename_some
    (f : MvPolynomial ℕ GammaPoleRationalBase →ₐ[GammaPoleRationalBase]
      MvPolynomial ℕ GammaPoleRationalBase)
    (P : MvPolynomial ℕ GammaPoleRationalBase) :
    optionHeadLiftAlgHom f (MvPolynomial.rename some P) =
      MvPolynomial.rename some (f P) := by
  let lhs : MvPolynomial ℕ GammaPoleRationalBase →+*
      MvPolynomial (Option ℕ) GammaPoleRationalBase :=
    (optionHeadLiftAlgHom f).toRingHom.comp
      (MvPolynomial.rename some).toRingHom
  let rhs : MvPolynomial ℕ GammaPoleRationalBase →+*
      MvPolynomial (Option ℕ) GammaPoleRationalBase :=
    (MvPolynomial.rename some).toRingHom.comp f.toRingHom
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs]
    · intro j
      simp [lhs, rhs, optionHeadLiftAlgHom_some]
  exact RingHom.congr_fun h P

/-- Formal inversion of the regular Gamma unit stays involutive after adjoining the pole scale. -/
theorem optionHeadLift_universalUnitInverseCoefficientRationalMap_involutive :
    (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap).comp
        (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap) =
      AlgHom.id GammaPoleRationalBase _ := by
  apply MvPolynomial.algHom_ext
  intro o
  rcases o with (_ | j)
  · simp [optionHeadLiftAlgHom_none]
  · simp only [AlgHom.comp_apply, optionHeadLiftAlgHom_some]
    rw [optionHeadLiftAlgHom_rename_some]
    have h := AlgHom.congr_fun
      universalUnitInverseCoefficientRationalMap_involutive
      (MvPolynomial.X j)
    simpa using congrArg (MvPolynomial.rename some) h

/-- Over the rational moving-center field, scaling by a nonzero diagonal after its reciprocal is
the identity. -/
theorem mvPolynomialDiagonalScaleRing_after_inverse
    {σ : Type*} (c : σ → GammaPoleRationalBase)
    (hc : ∀ i, c i ≠ 0) (P : MvPolynomial σ GammaPoleRationalBase) :
    mvPolynomialDiagonalScaleRing c
        (mvPolynomialDiagonalScaleRing (fun i => (c i)⁻¹) P) = P := by
  simpa only [inv_inv] using
    mvPolynomialDiagonalScaleRing_inv_apply
      (fun i => (c i)⁻¹) (fun i => inv_ne_zero (hc i)) P

/-- Rewrite a polynomial in the scale--covariant-residue frame as a polynomial in the
scale--finite-part frame. -/
def gammaPoleCovariantResidueToFinitePartRationalMap :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →ₐ[GammaPoleRationalBase]
      MvPolynomial (Option ℕ) GammaPoleRationalBase :=
  (mvPolynomialDiagonalScaleRing
      (fun o => (gammaPoleFinitePartRationalScale o)⁻¹)).comp
    ((optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap).comp
      (mvPolynomialDiagonalScaleRing gammaPoleCovariantResidueRationalScale))

/-- Rewrite a polynomial in the scale--finite-part frame as a polynomial in the
scale--covariant-residue frame. -/
def gammaPoleFinitePartToCovariantResidueRationalMap :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →ₐ[GammaPoleRationalBase]
      MvPolynomial (Option ℕ) GammaPoleRationalBase :=
  (mvPolynomialDiagonalScaleRing
      (fun o => (gammaPoleCovariantResidueRationalScale o)⁻¹)).comp
    ((optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap).comp
      (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale))

/-- The covariant-residue-to-finite-part coordinate rewrite preserves every evaluated polynomial. -/
theorem gammaPoleScaleAndFinitePartJetRationalEval_comp_residueToFinitePart :
    gammaPoleScaleAndFinitePartJetRationalEval.comp
        gammaPoleCovariantResidueToFinitePartRationalMap.toRingHom =
      gammaPoleScaleAndCovariantResidueRationalEval := by
  rw [gammaPoleScaleAndFinitePartJetRationalEval_eq_comp,
    gammaPoleScaleAndCovariantResidueRationalEval_eq_comp,
    gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_eq_comp]
  apply RingHom.ext
  intro P
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    gammaPoleCovariantResidueToFinitePartRationalMap]
  exact congrArg gammaPoleScaleAndUnitPositiveCoefficientRationalEval
    (mvPolynomialDiagonalScaleRing_after_inverse
      gammaPoleFinitePartRationalScale gammaPoleFinitePartRationalScale_ne_zero
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleCovariantResidueRationalScale P)))

/-- The finite-part-to-covariant-residue coordinate rewrite preserves every evaluated polynomial. -/
theorem gammaPoleScaleAndCovariantResidueRationalEval_comp_finitePartToResidue :
    gammaPoleScaleAndCovariantResidueRationalEval.comp
        gammaPoleFinitePartToCovariantResidueRationalMap.toRingHom =
      gammaPoleScaleAndFinitePartJetRationalEval := by
  rw [gammaPoleScaleAndFinitePartJetRationalEval_eq_comp,
    gammaPoleScaleAndCovariantResidueRationalEval_eq_comp,
    gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_eq_comp]
  apply RingHom.ext
  intro P
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    gammaPoleFinitePartToCovariantResidueRationalMap]
  apply congrArg gammaPoleScaleAndUnitPositiveCoefficientRationalEval
  change optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
      (mvPolynomialDiagonalScaleRing gammaPoleCovariantResidueRationalScale
        (mvPolynomialDiagonalScaleRing
          (fun o => (gammaPoleCovariantResidueRationalScale o)⁻¹)
          (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
            (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P)))) =
    mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P
  rw [mvPolynomialDiagonalScaleRing_after_inverse
    gammaPoleCovariantResidueRationalScale
    gammaPoleCovariantResidueRationalScale_ne_zero]
  have h := AlgHom.congr_fun
    optionHeadLift_universalUnitInverseCoefficientRationalMap_involutive
    (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P)
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h

/-- The two explicit coordinate rewrites are inverse in the residue-to-finite-part direction. -/
theorem gammaPoleFinitePartToCovariantResidue_leftInverse
    (P : MvPolynomial (Option ℕ) GammaPoleRationalBase) :
    gammaPoleFinitePartToCovariantResidueRationalMap
        (gammaPoleCovariantResidueToFinitePartRationalMap P) = P := by
  change mvPolynomialDiagonalScaleRing
      (fun o => (gammaPoleCovariantResidueRationalScale o)⁻¹)
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale
          (mvPolynomialDiagonalScaleRing
            (fun o => (gammaPoleFinitePartRationalScale o)⁻¹)
            (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
              (mvPolynomialDiagonalScaleRing
                gammaPoleCovariantResidueRationalScale P))))) = P
  rw [mvPolynomialDiagonalScaleRing_after_inverse
    gammaPoleFinitePartRationalScale gammaPoleFinitePartRationalScale_ne_zero]
  have h := AlgHom.congr_fun
    optionHeadLift_universalUnitInverseCoefficientRationalMap_involutive
    (mvPolynomialDiagonalScaleRing gammaPoleCovariantResidueRationalScale P)
  rw [show optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleCovariantResidueRationalScale P)) =
      mvPolynomialDiagonalScaleRing gammaPoleCovariantResidueRationalScale P by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h]
  exact mvPolynomialDiagonalScaleRing_inv_apply
    gammaPoleCovariantResidueRationalScale
    gammaPoleCovariantResidueRationalScale_ne_zero P

/-- The two explicit coordinate rewrites are inverse in the finite-part-to-residue direction. -/
theorem gammaPoleCovariantResidueToFinitePart_leftInverse
    (P : MvPolynomial (Option ℕ) GammaPoleRationalBase) :
    gammaPoleCovariantResidueToFinitePartRationalMap
        (gammaPoleFinitePartToCovariantResidueRationalMap P) = P := by
  change mvPolynomialDiagonalScaleRing
      (fun o => (gammaPoleFinitePartRationalScale o)⁻¹)
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleCovariantResidueRationalScale
          (mvPolynomialDiagonalScaleRing
            (fun o => (gammaPoleCovariantResidueRationalScale o)⁻¹)
            (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
              (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P))))) = P
  rw [mvPolynomialDiagonalScaleRing_after_inverse
    gammaPoleCovariantResidueRationalScale
    gammaPoleCovariantResidueRationalScale_ne_zero]
  have h := AlgHom.congr_fun
    optionHeadLift_universalUnitInverseCoefficientRationalMap_involutive
    (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P)
  rw [show optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P)) =
      mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h]
  exact mvPolynomialDiagonalScaleRing_inv_apply
    gammaPoleFinitePartRationalScale gammaPoleFinitePartRationalScale_ne_zero P

/-- **Finite-part/covariant-residue coordinate-field universality law.**  After adjoining the
reciprocal factorial pole scale over `ℂ(N)`, the analytic finite-part jets and covariant simple-zero
residues are two polynomial coordinate systems for exactly the same evaluated algebra.  Every
polynomial observable in either frame has a unique representative in the other. -/
theorem gammaPole_finitePart_covariantResidue_coordinateFieldUniversality :
    (∀ P, ∃! Q, gammaPoleScaleAndFinitePartJetRationalEval Q =
        gammaPoleScaleAndCovariantResidueRationalEval P) ∧
      (∀ Q, ∃! P, gammaPoleScaleAndCovariantResidueRationalEval P =
        gammaPoleScaleAndFinitePartJetRationalEval Q) := by
  constructor
  · intro P
    refine ⟨gammaPoleCovariantResidueToFinitePartRationalMap P, ?_, ?_⟩
    · exact RingHom.congr_fun
        gammaPoleScaleAndFinitePartJetRationalEval_comp_residueToFinitePart P
    · intro Q hQ
      apply gammaPoleScaleAndFinitePartJetRationalEval_injective
      exact hQ.trans (RingHom.congr_fun
        gammaPoleScaleAndFinitePartJetRationalEval_comp_residueToFinitePart P).symm
  · intro Q
    refine ⟨gammaPoleFinitePartToCovariantResidueRationalMap Q, ?_, ?_⟩
    · exact RingHom.congr_fun
        gammaPoleScaleAndCovariantResidueRationalEval_comp_finitePartToResidue Q
    · intro P hP
      apply gammaPoleScaleAndCovariantResidueRationalEval_injective
      exact hP.trans (RingHom.congr_fun
        gammaPoleScaleAndCovariantResidueRationalEval_comp_finitePartToResidue Q).symm

/-! ## Three-chart inverse-branch coordinate atlas -/

/-- Formal tangent-series inversion after extending coefficients to the moving-center field. -/
def universalTangentInverseCoefficientRationalMap :
    MvPolynomial ℕ GammaPoleRationalBase →ₐ[GammaPoleRationalBase]
      MvPolynomial ℕ GammaPoleRationalBase :=
  mvPolynomialAlgHomBaseChange
    (K := GammaPoleRationalBase) universalTangentInverseCoefficientMap

theorem universalTangentInverseCoefficientRationalMap_involutive :
    universalTangentInverseCoefficientRationalMap.comp
        universalTangentInverseCoefficientRationalMap =
      AlgHom.id GammaPoleRationalBase _ := by
  rw [universalTangentInverseCoefficientRationalMap,
    ← mvPolynomialAlgHomBaseChange_comp,
    universalTangentInverseCoefficientMap_involutive,
    mvPolynomialAlgHomBaseChange_id]

theorem universalTangentInverseCoefficientRationalMap_injective :
    Function.Injective universalTangentInverseCoefficientRationalMap := by
  apply Function.LeftInverse.injective
    (g := universalTangentInverseCoefficientRationalMap)
  intro P
  simpa using AlgHom.congr_fun
    universalTangentInverseCoefficientRationalMap_involutive P

@[simp] theorem universalTangentInverseCoefficientRationalMap_X (j : ℕ) :
    universalTangentInverseCoefficientRationalMap (MvPolynomial.X j) =
      MvPolynomial.map (algebraMap ℂ GammaPoleRationalBase)
        (universalTangentInverseCoefficient j) := by
  rw [universalTangentInverseCoefficientRationalMap,
    mvPolynomialAlgHomBaseChange_X]
  simp [universalTangentInverseCoefficientMap]

/-- Tangent compositional inversion stays involutive after adjoining the factorial scale. -/
theorem optionHeadLift_universalTangentInverseCoefficientRationalMap_involutive :
    (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap).comp
        (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap) =
      AlgHom.id GammaPoleRationalBase _ := by
  apply MvPolynomial.algHom_ext
  intro o
  rcases o with (_ | j)
  · simp [optionHeadLiftAlgHom_none]
  · simp only [AlgHom.comp_apply, optionHeadLiftAlgHom_some]
    rw [optionHeadLiftAlgHom_rename_some]
    have h := AlgHom.congr_fun
      universalTangentInverseCoefficientRationalMap_involutive
      (MvPolynomial.X j)
    simpa using congrArg (MvPolynomial.rename some) h

/-- Moving-center evaluation of the factorial scale and all nonlinear normalized inverse-Gamma
branch coefficients. -/
def gammaPoleScaleAndInverseBranchCoefficientRationalEval :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval
    gammaPoleScaleAndInverseBranchCoefficientFamily

theorem gammaPoleScaleAndInverseBranchCoefficientRationalEval_eq_comp :
    gammaPoleScaleAndInverseBranchCoefficientRationalEval =
      gammaPoleScaleAndReciprocalUnitCoefficientRationalEval.comp
        (optionHeadLiftAlgHom
          universalTangentInverseCoefficientRationalMap).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndInverseBranchCoefficientRationalEval,
      gammaPoleScaleAndReciprocalUnitCoefficientRationalEval]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndInverseBranchCoefficientRationalEval,
        gammaPoleScaleAndInverseBranchCoefficientFamily,
        gammaPoleScaleAndReciprocalUnitCoefficientRationalEval,
        gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        optionHeadLiftAlgHom_none]
    · rw [RingHom.comp_apply]
      simp only [gammaPoleScaleAndInverseBranchCoefficientRationalEval,
        MvPolynomial.eval₂Hom_X', gammaPoleScaleAndInverseBranchCoefficientFamily]
      change gammaInversePoleBranchCoefficientGerm j =
        gammaPoleScaleAndReciprocalUnitCoefficientRationalEval
          (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
            (MvPolynomial.X (some j)))
      rw [optionHeadLiftAlgHom_some,
        universalTangentInverseCoefficientRationalMap_X]
      simp [gammaInversePoleBranchCoefficientGerm,
        gammaPoleScaleAndReciprocalUnitCoefficientRationalEval,
        gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        tangentInverseCoefficientOfCoefficients_eq_aeval,
        MvPolynomial.aeval_def, MvPolynomial.eval₂_rename,
        Function.comp_def]
      have hbase : ratNatEval.comp RatFunc.C = complexNatGerm := rfl
      rw [hbase]
      rfl

theorem gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective :
    Function.Injective gammaPoleScaleAndInverseBranchCoefficientRationalEval := by
  rw [gammaPoleScaleAndInverseBranchCoefficientRationalEval_eq_comp]
  exact gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_injective.comp
    (optionHeadLiftAlgHom_injective
      universalTangentInverseCoefficientRationalMap_injective)

/-- Rewrite inverse-branch coordinates as finite-part coordinates. -/
def gammaPoleInverseBranchToFinitePartRationalMap :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →ₐ[GammaPoleRationalBase]
      MvPolynomial (Option ℕ) GammaPoleRationalBase :=
  (mvPolynomialDiagonalScaleRing
      (fun o => (gammaPoleFinitePartRationalScale o)⁻¹)).comp
    ((optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap).comp
      (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap))

/-- Rewrite finite-part coordinates as inverse-branch coordinates. -/
def gammaPoleFinitePartToInverseBranchRationalMap :
    MvPolynomial (Option ℕ) GammaPoleRationalBase →ₐ[GammaPoleRationalBase]
      MvPolynomial (Option ℕ) GammaPoleRationalBase :=
  (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap).comp
    ((optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap).comp
      (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale))

theorem gammaPoleScaleAndFinitePartJetRationalEval_comp_inverseBranchToFinitePart :
    gammaPoleScaleAndFinitePartJetRationalEval.comp
        gammaPoleInverseBranchToFinitePartRationalMap.toRingHom =
      gammaPoleScaleAndInverseBranchCoefficientRationalEval := by
  rw [gammaPoleScaleAndFinitePartJetRationalEval_eq_comp,
    gammaPoleScaleAndInverseBranchCoefficientRationalEval_eq_comp,
    gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_eq_comp]
  apply RingHom.ext
  intro P
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    gammaPoleInverseBranchToFinitePartRationalMap]
  exact congrArg gammaPoleScaleAndUnitPositiveCoefficientRationalEval
    (mvPolynomialDiagonalScaleRing_after_inverse
      gammaPoleFinitePartRationalScale gammaPoleFinitePartRationalScale_ne_zero
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap P)))

theorem gammaPoleScaleAndInverseBranchCoefficientRationalEval_comp_finitePartToInverseBranch :
    gammaPoleScaleAndInverseBranchCoefficientRationalEval.comp
        gammaPoleFinitePartToInverseBranchRationalMap.toRingHom =
      gammaPoleScaleAndFinitePartJetRationalEval := by
  rw [gammaPoleScaleAndFinitePartJetRationalEval_eq_comp,
    gammaPoleScaleAndInverseBranchCoefficientRationalEval_eq_comp,
    gammaPoleScaleAndReciprocalUnitCoefficientRationalEval_eq_comp]
  apply RingHom.ext
  intro P
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    gammaPoleFinitePartToInverseBranchRationalMap]
  apply congrArg gammaPoleScaleAndUnitPositiveCoefficientRationalEval
  change optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
      (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
        (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
          (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
            (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P)))) =
    mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P
  have hT := AlgHom.congr_fun
    optionHeadLift_universalTangentInverseCoefficientRationalMap_involutive
    (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
      (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P))
  rw [show optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
      (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
        (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
          (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P))) =
      optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P) by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hT]
  have hI := AlgHom.congr_fun
    optionHeadLift_universalUnitInverseCoefficientRationalMap_involutive
    (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P)
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hI

theorem gammaPoleFinitePartToInverseBranch_leftInverse
    (P : MvPolynomial (Option ℕ) GammaPoleRationalBase) :
    gammaPoleFinitePartToInverseBranchRationalMap
        (gammaPoleInverseBranchToFinitePartRationalMap P) = P := by
  change optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale
          (mvPolynomialDiagonalScaleRing
            (fun o => (gammaPoleFinitePartRationalScale o)⁻¹)
            (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
              (optionHeadLiftAlgHom
                universalTangentInverseCoefficientRationalMap P))))) = P
  rw [mvPolynomialDiagonalScaleRing_after_inverse
    gammaPoleFinitePartRationalScale gammaPoleFinitePartRationalScale_ne_zero]
  have hI := AlgHom.congr_fun
    optionHeadLift_universalUnitInverseCoefficientRationalMap_involutive
    (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap P)
  rw [show optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap P)) =
      optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap P by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hI]
  have hT := AlgHom.congr_fun
    optionHeadLift_universalTangentInverseCoefficientRationalMap_involutive P
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hT

theorem gammaPoleInverseBranchToFinitePart_leftInverse
    (P : MvPolynomial (Option ℕ) GammaPoleRationalBase) :
    gammaPoleInverseBranchToFinitePartRationalMap
        (gammaPoleFinitePartToInverseBranchRationalMap P) = P := by
  change mvPolynomialDiagonalScaleRing
      (fun o => (gammaPoleFinitePartRationalScale o)⁻¹)
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
          (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
            (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
              (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P))))) = P
  have hT := AlgHom.congr_fun
    optionHeadLift_universalTangentInverseCoefficientRationalMap_involutive
    (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
      (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P))
  rw [show optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
      (optionHeadLiftAlgHom universalTangentInverseCoefficientRationalMap
        (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
          (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P))) =
      optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P) by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hT]
  have hI := AlgHom.congr_fun
    optionHeadLift_universalUnitInverseCoefficientRationalMap_involutive
    (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P)
  rw [show optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
      (optionHeadLiftAlgHom universalUnitInverseCoefficientRationalMap
        (mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P)) =
      mvPolynomialDiagonalScaleRing gammaPoleFinitePartRationalScale P by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hI]
  exact mvPolynomialDiagonalScaleRing_inv_apply
    gammaPoleFinitePartRationalScale gammaPoleFinitePartRationalScale_ne_zero P

/-- Finite-part and inverse-branch frames are uniquely interchangeable over `ℂ(N)`. -/
theorem gammaPole_finitePart_inverseBranch_coordinateFieldUniversality :
    (∀ P, ∃! Q, gammaPoleScaleAndFinitePartJetRationalEval Q =
        gammaPoleScaleAndInverseBranchCoefficientRationalEval P) ∧
      (∀ Q, ∃! P, gammaPoleScaleAndInverseBranchCoefficientRationalEval P =
        gammaPoleScaleAndFinitePartJetRationalEval Q) := by
  constructor
  · intro P
    refine ⟨gammaPoleInverseBranchToFinitePartRationalMap P, ?_, ?_⟩
    · exact RingHom.congr_fun
        gammaPoleScaleAndFinitePartJetRationalEval_comp_inverseBranchToFinitePart P
    · intro Q hQ
      apply gammaPoleScaleAndFinitePartJetRationalEval_injective
      exact hQ.trans (RingHom.congr_fun
        gammaPoleScaleAndFinitePartJetRationalEval_comp_inverseBranchToFinitePart P).symm
  · intro Q
    refine ⟨gammaPoleFinitePartToInverseBranchRationalMap Q, ?_, ?_⟩
    · exact RingHom.congr_fun
        gammaPoleScaleAndInverseBranchCoefficientRationalEval_comp_finitePartToInverseBranch Q
    · intro P hP
      apply gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective
      exact hP.trans (RingHom.congr_fun
        gammaPoleScaleAndInverseBranchCoefficientRationalEval_comp_finitePartToInverseBranch Q).symm

/-- **Gamma pole three-chart coordinate-atlas universality law.**  Over the moving-center field
`ℂ(N)`, finite-part jets, covariant residues, and normalized nonlinear inverse-branch coefficients
are pairwise polynomial coordinate systems for the same evaluated algebra after adjoining the
factorial pole scale. -/
theorem gammaPole_finitePart_covariantResidue_inverseBranch_coordinateAtlasUniversality :
    ((∀ P, ∃! Q, gammaPoleScaleAndFinitePartJetRationalEval Q =
        gammaPoleScaleAndCovariantResidueRationalEval P) ∧
      (∀ Q, ∃! P, gammaPoleScaleAndCovariantResidueRationalEval P =
        gammaPoleScaleAndFinitePartJetRationalEval Q)) ∧
    ((∀ P, ∃! Q, gammaPoleScaleAndFinitePartJetRationalEval Q =
        gammaPoleScaleAndInverseBranchCoefficientRationalEval P) ∧
      (∀ Q, ∃! P, gammaPoleScaleAndInverseBranchCoefficientRationalEval P =
        gammaPoleScaleAndFinitePartJetRationalEval Q)) ∧
    ((∀ P, ∃! Q, gammaPoleScaleAndInverseBranchCoefficientRationalEval Q =
        gammaPoleScaleAndCovariantResidueRationalEval P) ∧
      (∀ Q, ∃! P, gammaPoleScaleAndCovariantResidueRationalEval P =
        gammaPoleScaleAndInverseBranchCoefficientRationalEval Q)) := by
  refine ⟨gammaPole_finitePart_covariantResidue_coordinateFieldUniversality,
    gammaPole_finitePart_inverseBranch_coordinateFieldUniversality, ?_⟩
  constructor
  · intro P
    let F := gammaPoleCovariantResidueToFinitePartRationalMap P
    let Q := gammaPoleFinitePartToInverseBranchRationalMap F
    refine ⟨Q, ?_, ?_⟩
    · calc
        gammaPoleScaleAndInverseBranchCoefficientRationalEval Q =
            gammaPoleScaleAndFinitePartJetRationalEval F :=
          RingHom.congr_fun
            gammaPoleScaleAndInverseBranchCoefficientRationalEval_comp_finitePartToInverseBranch F
        _ = gammaPoleScaleAndCovariantResidueRationalEval P :=
          RingHom.congr_fun
            gammaPoleScaleAndFinitePartJetRationalEval_comp_residueToFinitePart P
    · intro Q' hQ'
      apply gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective
      exact hQ'.trans (by
        calc
          gammaPoleScaleAndCovariantResidueRationalEval P =
              gammaPoleScaleAndFinitePartJetRationalEval F :=
            (RingHom.congr_fun
              gammaPoleScaleAndFinitePartJetRationalEval_comp_residueToFinitePart P).symm
          _ = gammaPoleScaleAndInverseBranchCoefficientRationalEval Q :=
            (RingHom.congr_fun
              gammaPoleScaleAndInverseBranchCoefficientRationalEval_comp_finitePartToInverseBranch
                F).symm)
  · intro Q
    let F := gammaPoleInverseBranchToFinitePartRationalMap Q
    let P := gammaPoleFinitePartToCovariantResidueRationalMap F
    refine ⟨P, ?_, ?_⟩
    · calc
        gammaPoleScaleAndCovariantResidueRationalEval P =
            gammaPoleScaleAndFinitePartJetRationalEval F :=
          RingHom.congr_fun
            gammaPoleScaleAndCovariantResidueRationalEval_comp_finitePartToResidue F
        _ = gammaPoleScaleAndInverseBranchCoefficientRationalEval Q :=
          RingHom.congr_fun
            gammaPoleScaleAndFinitePartJetRationalEval_comp_inverseBranchToFinitePart Q
    · intro P' hP'
      apply gammaPoleScaleAndCovariantResidueRationalEval_injective
      exact hP'.trans (by
        calc
          gammaPoleScaleAndInverseBranchCoefficientRationalEval Q =
              gammaPoleScaleAndFinitePartJetRationalEval F :=
            (RingHom.congr_fun
              gammaPoleScaleAndFinitePartJetRationalEval_comp_inverseBranchToFinitePart Q).symm
          _ = gammaPoleScaleAndCovariantResidueRationalEval P :=
            (RingHom.congr_fun
              gammaPoleScaleAndCovariantResidueRationalEval_comp_finitePartToResidue F).symm)

/-- An arbitrary formal lower-depth jet frame adjoined to one Gamma pole coordinate chart. -/
abbrev GammaPoleThreeChartLowerJetDomain (κ : Type*) :=
  MvPolynomial κ (MvPolynomial (Option ℕ) GammaPoleRationalBase)

/-- Lower-jet extension of the moving-center finite-part evaluation. -/
def gammaPoleScaleAndFinitePartLowerJetRationalEval (κ : Type*) :
    GammaPoleThreeChartLowerJetDomain κ →+* GammaInverseBranchLowerJetRing κ :=
  MvPolynomial.map gammaPoleScaleAndFinitePartJetRationalEval

/-- Lower-jet extension of the moving-center covariant-residue evaluation. -/
def gammaPoleScaleAndCovariantResidueLowerJetRationalEval (κ : Type*) :
    GammaPoleThreeChartLowerJetDomain κ →+* GammaInverseBranchLowerJetRing κ :=
  MvPolynomial.map gammaPoleScaleAndCovariantResidueRationalEval

/-- Lower-jet extension of the moving-center normalized inverse-branch evaluation. -/
def gammaPoleScaleAndInverseBranchLowerJetRationalEval (κ : Type*) :
    GammaPoleThreeChartLowerJetDomain κ →+* GammaInverseBranchLowerJetRing κ :=
  MvPolynomial.map gammaPoleScaleAndInverseBranchCoefficientRationalEval

/-- **Gamma three-chart lower-jet extension universality.**  After adjoining an arbitrary formal
lower-depth jet frame, finite-part, covariant-residue, and inverse-branch coordinates all remain
injective.  Thus no nonzero mixed lower-jet polynomial can disappear in any chart. -/
theorem gammaPole_threeChart_lowerJetExtension_injective (κ : Type*) :
    Function.Injective (gammaPoleScaleAndFinitePartLowerJetRationalEval κ) ∧
      Function.Injective (gammaPoleScaleAndCovariantResidueLowerJetRationalEval κ) ∧
      Function.Injective (gammaPoleScaleAndInverseBranchLowerJetRationalEval κ) := by
  exact ⟨MvPolynomial.map_injective _
      gammaPoleScaleAndFinitePartJetRationalEval_injective,
    MvPolynomial.map_injective _
      gammaPoleScaleAndCovariantResidueRationalEval_injective,
    MvPolynomial.map_injective _
      gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective⟩

/-- Evaluation form of the lower-jet extension law: every nonzero mixed polynomial survives in
all three Gamma pole charts. -/
theorem gammaPole_threeChart_lowerJetExtension_ne_zero
    {κ : Type*} {P : GammaPoleThreeChartLowerJetDomain κ} (hP : P ≠ 0) :
    gammaPoleScaleAndFinitePartLowerJetRationalEval κ P ≠ 0 ∧
      gammaPoleScaleAndCovariantResidueLowerJetRationalEval κ P ≠ 0 ∧
      gammaPoleScaleAndInverseBranchLowerJetRationalEval κ P ≠ 0 := by
  obtain ⟨hfinitePart, hresidue, hinverse⟩ :=
    gammaPole_threeChart_lowerJetExtension_injective κ
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hP
    apply hfinitePart
    simpa using hzero
  · intro hzero
    apply hP
    apply hresidue
    simpa using hzero
  · intro hzero
    apply hP
    apply hinverse
    simpa using hzero

end

end GaloisForLFunctions
