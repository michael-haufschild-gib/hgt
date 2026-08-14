import GaloisForLFunctions.HTGeometry.DerivationPrescription
import GaloisForLFunctions.HTGeometry.FreeCoordinateExponentialObstruction

/-!
# Exact differentials cannot be nonconstant logarithmic differentials

In a characteristic-zero field extension, an identity `dw = w ds` with `w ≠ 0` in universal
Kähler differentials forces both `s` and `w` to be algebraic over the base field.  A hypothetical
transcendental `s` is extended to a transcendence basis.  The coordinate derivation with
`s' = 1` and all other basis coordinates constant extends through the algebraic remainder; the
differential identity would then make the algebraic element `w` solve `w' = w`, contradicting the
free-coordinate exponential obstruction.
-/

open Set IntermediateField MvPolynomial TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- If `dw = w ds` in relative Kähler differentials and `w` is nonzero, then `s` is algebraic over
the base field. -/
theorem isAlgebraic_left_of_kaehlerD_eq_smul
    {C L : Type*} [Field C] [Field L] [Algebra C L] [CharZero C]
    {s w : L} (hw : w ≠ 0)
    (hlog : KaehlerDifferential.D C L w =
      w • KaehlerDifferential.D C L s) :
    IsAlgebraic C s := by
  classical
  by_contra hsalg
  have hstrans : Transcendental C s := hsalg
  have hsingle : AlgebraicIndepOn C id ({s} : Set L) := by
    change AlgebraicIndependent C (fun z : ({s} : Set L) ↦ z.1)
    rw [algebraicIndependent_singleton_iff
      (⟨s, Set.mem_singleton s⟩ : ({s} : Set L))]
    exact hstrans
  have hI : (AlgebraicIndependent.matroid C L).Indep ({s} : Set L) :=
    AlgebraicIndependent.matroid_indep_iff.mpr hsingle
  obtain ⟨B, hBbase, hsB⟩ := hI.exists_isBase_superset
  have hB : IsTranscendenceBasis C ((↑) : B → L) :=
    AlgebraicIndependent.matroid_isBase_iff.mp hBbase
  let F := IntermediateField.adjoin C (Set.range ((↑) : B → L))
  let Q := FreeCoordinateRationalField C B
  let b : B := ⟨s, hsB (Set.mem_singleton s)⟩
  let sb : F :=
    ⟨s, IntermediateField.subset_adjoin C (Set.range ((↑) : B → L))
      ⟨b, rfl⟩⟩
  let e : Q ≃ₐ[C] F := hB.1.aevalEquivField
  let dQ : Derivation C Q Q := freeCoordinateDerivation C B b
  let dF : Derivation C F F := GaloisForLFunctions.transportDerivation e dQ
  have heX : e.symm sb = freeCoordinate C B b := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change s = (hB.1.aevalEquivField
      (algebraMap (MvPolynomial B C) Q (MvPolynomial.X b)) : F)
    rw [hB.1.aevalEquivField_algebraMap_apply_coe]
    simp [b]
  have hdFs : dF sb = 1 := by
    rw [GaloisForLFunctions.transportDerivation_apply, heX,
      freeCoordinateDerivation_freeCoordinate_self, map_one]
  letI : Algebra.IsAlgebraic F L := hB.isAlgebraic_field
  letI : Algebra.IsIntegral F L := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable F L := by infer_instance
  obtain ⟨D, hD⟩ := exists_derivation_extension (K := C) (F := F) (L := L) dF
  have hDs : D s = 1 := by
    have hs := hD sb
    rw [show (algebraMap F L sb : L) = s from rfl, hdFs, map_one] at hs
    exact hs
  have hDw : D w = w := by
    have hmap := congrArg D.liftKaehlerDifferential hlog
    rw [Derivation.liftKaehlerDifferential_comp_D,
      map_smul, Derivation.liftKaehlerDifferential_comp_D, hDs, smul_eq_mul,
      mul_one] at hmap
    exact hmap
  let φ : Q →ₐ[C] L := (IsScalarTower.toAlgHom C F L).comp e.toAlgHom
  letI : Algebra Q L := φ.toAlgebra
  have hCQ : algebraMap C L =
      (algebraMap Q L).comp (algebraMap C Q) := by
    ext c
    change algebraMap C L c = algebraMap F L (e (algebraMap C Q c))
    rw [e.commutes]
    exact (IsScalarTower.algebraMap_apply C F L c).symm
  letI : IsScalarTower C Q L :=
    IsScalarTower.of_algebraMap_eq' hCQ
  have hDQ : ∀ a : Q,
      D (algebraMap Q L a) =
        algebraMap Q L (freeCoordinateDerivation C B b a) := by
    intro a
    change D (algebraMap F L (e a)) =
      algebraMap F L (e (freeCoordinateDerivation C B b a))
    rw [hD]
    simp only [dF, GaloisForLFunctions.transportDerivation_apply,
      e.symm_apply_apply, dQ]
  have hcomp :
      RingHom.comp (algebraMap F L) e.toRingEquiv.toRingHom =
        RingHom.comp (RingHom.id L) (algebraMap Q L) := by
    ext a
    rfl
  letI : Algebra.IsAlgebraic Q L :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq
      e.toRingEquiv (RingHom.id L) e.surjective Function.injective_id hcomp
  have hwalg : IsAlgebraic Q w := Algebra.IsAlgebraic.isAlgebraic w
  exact (ne_self_of_isAlgebraic_freeCoordinateDerivation b D hDQ hwalg hw) hDw

/-- **Logarithmic-differential algebraicity.** In characteristic zero, `dw = w ds` with `w ≠ 0`
forces both entries to be algebraic over the base field. -/
theorem algebraic_of_kaehlerD_eq_smul
    {C L : Type*} [Field C] [Field L] [Algebra C L] [CharZero C]
    {s w : L} (hw : w ≠ 0)
    (hlog : KaehlerDifferential.D C L w =
      w • KaehlerDifferential.D C L s) :
    IsAlgebraic C s ∧ IsAlgebraic C w := by
  have hs : IsAlgebraic C s :=
    isAlgebraic_left_of_kaehlerD_eq_smul hw hlog
  have hds : KaehlerDifferential.D C L s = 0 :=
    GaloisForLFunctions.kaehlerD_eq_zero_of_isAlgebraic hs
  have hdw : KaehlerDifferential.D C L w = 0 := by
    rw [hlog, hds, smul_zero]
  exact ⟨hs, GaloisForLFunctions.isAlgebraic_of_kaehlerD_eq_zero hdw⟩

end

end GaloisForLFunctions.HTGeometry
