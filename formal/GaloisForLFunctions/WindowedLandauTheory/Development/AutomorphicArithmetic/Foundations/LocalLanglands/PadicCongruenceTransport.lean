import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicIntegralReduction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicCompletionNormalization
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionReduction

/-! A continuous p-adic identification takes the integral group and
first principal congruence subgroup to their completion counterparts.
The associated residue field isomorphism commutes with reduction. -/

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.Reciprocity

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- Principal congruence defined using the rings of integers and reduction at a finite place. -/
def completionPrincipalCongruenceOne (v : HeightOneSpectrum (𝓞 F)) (n : Type*)
    [Fintype n] [DecidableEq n] : Subgroup (GL n (v.adicCompletion F)) :=
  (GeneralLinearGroup.map (n := n) (completionReduction v)).ker.map
    (GeneralLinearGroup.map (algebraMap (CompletedIntegers v) (v.adicCompletion F)))

theorem generalLinearGroup_map_ringEquiv_surjective {R S : Type*}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    Function.Surjective (GeneralLinearGroup.map (n := n) e.toRingHom) := by
  intro x
  refine ⟨GeneralLinearGroup.map e.symm.toRingHom x, Units.ext (Matrix.ext fun i j => ?_)⟩
  exact e.apply_symm_apply (x.val i j)

theorem principalCongruenceOne_map_along_padicIso (v : HeightOneSpectrum (𝓞 F))
    (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i) :
    (principalCongruenceOne p n).map (GeneralLinearGroup.map i.toRingHom) =
      completionPrincipalCongruenceOne v n := by
  obtain ⟨w, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := F)).surjective v
  let v := w.maximalIdeal
  let e := padicCompletionIntegersEquiv w i hi
  letI : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  let f := (PadicInt.residueField.symm.trans (IsLocalRing.ResidueField.mapEquiv e)).trans (completedResidueEquiv v).symm
  have hred : (completionReduction v).comp e.toRingHom = f.toRingHom.comp PadicInt.toZMod := by
    apply RingHom.ext
    intro x
    change completionReduction v (e x) =
      (completedResidueEquiv v).symm ((IsLocalRing.ResidueField.mapEquiv e)
        (PadicInt.residueField.symm (PadicInt.toZMod x)))
    have hx : PadicInt.toZMod x = PadicInt.residueField (IsLocalRing.residue _ x) :=
      DFunLike.congr_fun PadicInt.toZMod_eq_residueField_comp_residue x
    rw [hx, RingEquiv.symm_apply_apply]
    rfl
  have hker (k : GL n ℤ_[p]) :
      GeneralLinearGroup.map (n := n) (completionReduction v) (GeneralLinearGroup.map e.toRingHom k) = 1 ↔
        integralReduction p n k = 1 := by
    change GeneralLinearGroup.map ((completionReduction v).comp e.toRingHom) k = 1 ↔ _
    rw [hred, GeneralLinearGroup.map_comp, MonoidHom.comp_apply, ← map_one (GeneralLinearGroup.map f.toRingHom)]
    constructor
    · intro h
      refine Units.ext (Matrix.ext fun i j => f.injective ?_)
      exact congrArg (fun u : GL n (𝓞 F ⧸ v.asIdeal) => u.val i j) h
    · intro h
      exact congrArg (GeneralLinearGroup.map f.toRingHom) h
  have hinc (k : GL n ℤ_[p]) :
      GeneralLinearGroup.map i.toRingHom (integralInclusion p n k) =
        GeneralLinearGroup.map (algebraMap (CompletedIntegers v) (v.adicCompletion F))
          (GeneralLinearGroup.map e.toRingHom k) := by
    apply Units.ext
    ext i j
    rfl
  rw [principalCongruenceOne, Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, (hker k).mpr hk, (hinc k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨l, rfl⟩ := generalLinearGroup_map_ringEquiv_surjective e k
    exact ⟨l, (hker l).mp hk, hinc l⟩

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.principalCongruenceOne_map_along_padicIso
