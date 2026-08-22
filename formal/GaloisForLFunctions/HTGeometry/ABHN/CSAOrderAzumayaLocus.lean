import GaloisForLFunctions.HTGeometry.ABHN.CSAFractionFieldOrder
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaEnvelopeBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.CentralSimpleAzumaya
import GaloisForLFunctions.HTGeometry.ABHN.GenericLocalizationBijection

/-!
# Generic Azumaya property of a fraction-field CSA order

An order whose fraction-field scalar extension is a central simple algebra has
a bijective left-right action at its generic fiber.  This is the generic point
input for spreading the Azumaya condition to a principal open subset.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w z

/-- A fraction-field order in a central simple algebra has bijective left-right action after
passing to the fraction field. -/
theorem mulLeftRight_bijective_of_fractionFieldOrder
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (A : CSA.{v, w} K) [Algebra R A.carrier] [IsScalarTower R K A.carrier]
    (O : Subalgebra R A.carrier) (e : K ⊗[R] O ≃ₐ[K] A.carrier) :
    Function.Bijective (AlgHom.mulLeftRight K (K ⊗[R] O)) := by
  exact mulLeftRight_bijective_of_csa (csaOfAlgEquiv A (K ⊗[R] O) e.symm)

/-- If an order is finite free, its fraction-field left-right isomorphism is the scalar extension
of its integral left-right map. -/
theorem mulLeftRight_baseChange_bijective_of_fractionFieldOrder_of_free
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (A : CSA.{v, w} K) [Algebra R A.carrier] [IsScalarTower R K A.carrier]
    (O : Subalgebra R A.carrier) (e : K ⊗[R] O ≃ₐ[K] A.carrier)
    [Module.Finite R O] [Module.Free R O] :
    Function.Bijective ((AlgHom.mulLeftRight R O).toLinearMap.baseChange K) := by
  let C := K ⊗[R] O
  let f := (AlgHom.mulLeftRight R O).toLinearMap.baseChange K
  let g := LinearMap.tensorProductEnd R K O
  let h := AlgHom.mulLeftRight K C
  let q := AzumayaScalarExtension.envelopeBaseChangeMap (R := R) (S := K) (A := O)
  have hleft : Function.Bijective (h ∘ q) := by
    exact (mulLeftRight_bijective_of_fractionFieldOrder R K A O e).comp
      (AzumayaScalarExtension.envelopeBaseChangeMap_bijective (R := R) (S := K) (A := O))
  have hcomp : Function.Bijective (g ∘ f) := by
    rw [← show h ∘ q = g ∘ f from funext fun t =>
      AzumayaScalarExtension.mulLeftRight_envelopeBaseChangeMap (R := R) (S := K) (A := O) t]
    exact hleft
  have hg : Function.Bijective g :=
    tensorProductEnd_bijective_of_projective (R := R) (S := K) (M := O)
  constructor
  · intro x y hxy
    apply hcomp.1
    exact congrArg g hxy
  · intro y
    obtain ⟨x, hx⟩ := hcomp.2 (g y)
    exact ⟨x, hg.1 (by simpa [Function.comp_apply] using hx)⟩

/-- A finite free order in a fraction-field CSA has bijective left-right action after inverting
one nonzero base element. -/
theorem exists_nonzero_away_mulLeftRight_bijective_of_fractionFieldOrder_of_free
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : CSA.{v, w} K) [Algebra R A.carrier] [IsScalarTower R K A.carrier]
    (O : Subalgebra R A.carrier) (e : K ⊗[R] O ≃ₐ[K] A.carrier)
    [Module.Finite R O] [Module.Free R O] :
    ∃ r : R, r ≠ 0 ∧ Function.Bijective
      (LocalizedModule.map (Submonoid.powers r) (AlgHom.mulLeftRight R O).toLinearMap) := by
  letI : Module.Finite R (O ⊗[R] Oᵐᵒᵖ) := inferInstance
  letI : Module.Finite R (Module.End R O) := inferInstance
  letI : Module.FinitePresentation R (Module.End R O) :=
    Module.finitePresentation_of_finite R (Module.End R O)
  exact exists_nonzero_away_bijective_of_fractionField_baseChange_bijective R K
    (O ⊗[R] Oᵐᵒᵖ) (Module.End R O) (AlgHom.mulLeftRight R O).toLinearMap
    (mulLeftRight_baseChange_bijective_of_fractionFieldOrder_of_free R K A O e)

/-- A finite free faithful algebra whose localized left-right map is bijective becomes Azumaya
after the corresponding principal localization. -/
theorem isAzumaya_away_of_localized_mulLeftRight_bijective
    (R : Type u) [CommRing R] (r : R)
    (A : Type w) [Ring A] [Algebra R A]
    [Module.Finite R A] [Module.Free R A] [FaithfulSMul R A]
    (hlocal : Function.Bijective
      (LocalizedModule.map (Submonoid.powers r) (AlgHom.mulLeftRight R A).toLinearMap)) :
    IsAzumaya (Localization (Submonoid.powers r)) (Localization (Submonoid.powers r) ⊗[R] A) := by
  apply AzumayaScalarExtension.isAzumaya_scalarExtension_of_mulLeftRight_baseChange_bijective
  exact baseChange_bijective_of_localized_bijective R (Submonoid.powers r)
    (Localization (Submonoid.powers r)) (A ⊗[R] Aᵐᵒᵖ) (Module.End R A)
    (AlgHom.mulLeftRight R A).toLinearMap hlocal

/-- A finite free faithful order in a fraction-field CSA becomes Azumaya after inverting one
nonzero base element. -/
theorem exists_nonzero_away_isAzumaya_of_fractionFieldOrder_of_free
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : CSA.{v, w} K) [Algebra R A.carrier] [IsScalarTower R K A.carrier]
    (O : Subalgebra R A.carrier) (e : K ⊗[R] O ≃ₐ[K] A.carrier)
    [Module.Finite R O] [Module.Free R O] [FaithfulSMul R O] :
    ∃ r : R, r ≠ 0 ∧ IsAzumaya (Localization (Submonoid.powers r))
      (Localization (Submonoid.powers r) ⊗[R] O) := by
  obtain ⟨r, hr, hlocal⟩ :=
    exists_nonzero_away_mulLeftRight_bijective_of_fractionFieldOrder_of_free R K A O e
  exact ⟨r, hr, isAzumaya_away_of_localized_mulLeftRight_bijective R r O hlocal⟩

/-- A finite `R`-algebra with central-simple fraction-field fibre has a bijective left-right
action at that fibre.  Unlike the order-specialized result above, this formulation does not
require the algebra to be presented as a subalgebra of the generic fibre. -/
theorem mulLeftRight_bijective_of_fractionFieldModel
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (A : CSA.{v, w} K)
    (B : Type z) [Ring B] [Algebra R B] (e : K ⊗[R] B ≃ₐ[K] A.carrier) :
    Function.Bijective (AlgHom.mulLeftRight K (K ⊗[R] B)) := by
  exact mulLeftRight_bijective_of_csa (csaOfAlgEquiv A (K ⊗[R] B) e.symm)

/-- For a finite free fraction-field model, the generic left-right isomorphism is induced by
the scalar extension of its integral left-right map. -/
theorem mulLeftRight_baseChange_bijective_of_fractionFieldModel_of_free
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (A : CSA.{v, w} K)
    (B : Type z) [Ring B] [Algebra R B] (e : K ⊗[R] B ≃ₐ[K] A.carrier)
    [Module.Finite R B] [Module.Free R B] :
    Function.Bijective ((AlgHom.mulLeftRight R B).toLinearMap.baseChange K) := by
  let C := K ⊗[R] B
  let f := (AlgHom.mulLeftRight R B).toLinearMap.baseChange K
  let g := LinearMap.tensorProductEnd R K B
  let h := AlgHom.mulLeftRight K C
  let q := AzumayaScalarExtension.envelopeBaseChangeMap (R := R) (S := K) (A := B)
  have hleft : Function.Bijective (h ∘ q) := by
    exact (mulLeftRight_bijective_of_fractionFieldModel R K A B e).comp
      (AzumayaScalarExtension.envelopeBaseChangeMap_bijective (R := R) (S := K) (A := B))
  have hcomp : Function.Bijective (g ∘ f) := by
    rw [← show h ∘ q = g ∘ f from funext fun t =>
      AzumayaScalarExtension.mulLeftRight_envelopeBaseChangeMap (R := R) (S := K) (A := B) t]
    exact hleft
  have hg : Function.Bijective g :=
    tensorProductEnd_bijective_of_projective (R := R) (S := K) (M := B)
  constructor
  · intro x y hxy
    apply hcomp.1
    exact congrArg g hxy
  · intro y
    obtain ⟨x, hx⟩ := hcomp.2 (g y)
    exact ⟨x, hg.1 (by simpa [Function.comp_apply] using hx)⟩

/-- A finite free fraction-field model of a central simple algebra has bijective left-right
action after inverting one nonzero element. -/
theorem exists_nonzero_away_mulLeftRight_bijective_of_fractionFieldModel_of_free
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : CSA.{v, w} K)
    (B : Type z) [Ring B] [Algebra R B] (e : K ⊗[R] B ≃ₐ[K] A.carrier)
    [Module.Finite R B] [Module.Free R B] :
    ∃ r : R, r ≠ 0 ∧ Function.Bijective
      (LocalizedModule.map (Submonoid.powers r) (AlgHom.mulLeftRight R B).toLinearMap) := by
  letI : Module.Finite R (B ⊗[R] Bᵐᵒᵖ) := inferInstance
  letI : Module.Finite R (Module.End R B) := inferInstance
  letI : Module.FinitePresentation R (Module.End R B) :=
    Module.finitePresentation_of_finite R (Module.End R B)
  exact exists_nonzero_away_bijective_of_fractionField_baseChange_bijective R K
    (B ⊗[R] Bᵐᵒᵖ) (Module.End R B) (AlgHom.mulLeftRight R B).toLinearMap
    (mulLeftRight_baseChange_bijective_of_fractionFieldModel_of_free R K A B e)

/-- A model with nontrivial fraction-field fibre is itself nontrivial. -/
theorem nontrivial_of_fractionFieldModel
    (R : Type u) [CommRing R] (K : Type v) [Field K] [Algebra R K]
    (A : CSA.{v, w} K)
    (B : Type z) [Ring B] [Algebra R B] (e : K ⊗[R] B ≃ₐ[K] A.carrier) :
    Nontrivial B := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · letI : Subsingleton B := hB
    have hsub : Subsingleton (K ⊗[R] B) := by
      have hzero : ∀ x : K ⊗[R] B, x = 0 := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => rfl
        | add x y hx hy => rw [hx, hy, add_zero]
        | tmul k b =>
          rw [show b = 0 from Subsingleton.elim _ _, TensorProduct.tmul_zero]
      exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
    have hzero : (0 : A.carrier) = 1 := by
      simpa using congrArg e (hsub.elim (0 : K ⊗[R] B) 1)
    exact (zero_ne_one hzero).elim
  · exact hB

/-- Every finite free fraction-field model of a central simple algebra is Azumaya on some
principal open subset. -/
theorem exists_nonzero_away_isAzumaya_of_fractionFieldModel_of_free
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : CSA.{v, w} K)
    (B : Type z) [Ring B] [Algebra R B] (e : K ⊗[R] B ≃ₐ[K] A.carrier)
    [Module.Finite R B] [Module.Free R B] :
    ∃ r : R, r ≠ 0 ∧ IsAzumaya (Localization (Submonoid.powers r))
      (Localization (Submonoid.powers r) ⊗[R] B) := by
  letI : Nontrivial B := nontrivial_of_fractionFieldModel R K A B e
  letI : FaithfulSMul R B := inferInstance
  obtain ⟨r, hr, hlocal⟩ :=
    exists_nonzero_away_mulLeftRight_bijective_of_fractionFieldModel_of_free R K A B e
  exact ⟨r, hr, isAzumaya_away_of_localized_mulLeftRight_bijective R r B hlocal⟩

/-- A central simple algebra over a fraction field has an Azumaya model after first making a
finite order free and then passing to a further principal open.  This is the algebraic core of
the finite-ramification step in the Hasse-principle infrastructure. -/
theorem exists_iterated_principalOpen_isAzumayaModel_of_csa
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : CSA.{v, w} K) [Algebra R A.carrier] [IsScalarTower R K A.carrier] :
    ∃ (O : Subalgebra R A.carrier) (_ : K ⊗[R] O ≃ₐ[K] A.carrier) (r : R), r ≠ 0 ∧
      Module.Finite R O ∧ ∃ s : Localization (Submonoid.powers r), s ≠ 0 ∧
        IsAzumaya (Localization (Submonoid.powers s))
          (Localization (Submonoid.powers s) ⊗[Localization (Submonoid.powers r)]
            (Localization (Submonoid.powers r) ⊗[R] O)) := by
  obtain ⟨O, e, hfinite⟩ := exists_fractionFieldOrder_of_csa R K A
  letI : Module.Finite R O := hfinite
  letI : Module.FinitePresentation R O := Module.finitePresentation_of_finite R O
  obtain ⟨r, hr, hfree⟩ := exists_nonzero_away_free_of_fractionField_baseChange R K O
  let S := Localization (Submonoid.powers r)
  have hpow : Submonoid.powers r ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hpow
  letI : Algebra S K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S K (Submonoid.powers r)
      (nonZeroDivisors R) hpow
  letI : IsScalarTower R S K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S K (Submonoid.powers r)
      (nonZeroDivisors R) hpow
  letI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) S K
  letI : Module.Free S (LocalizedModule.Away r O) := hfree
  letI : Module.Free S (S ⊗[R] O) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) O)
  letI : Module.Finite S (S ⊗[R] O) := inferInstance
  have e' : K ⊗[S] (S ⊗[R] O) ≃ₐ[K] A.carrier :=
    (AzumayaScalarExtension.cancelBaseChangeNoncommutative
      (R := R) (S := S) (A := O) (T := K)).trans e
  obtain ⟨s, hs, has⟩ :=
    exists_nonzero_away_isAzumaya_of_fractionFieldModel_of_free S K A (S ⊗[R] O) e'
  exact ⟨O, e, r, hr, hfinite, s, hs, has⟩

end GaloisForLFunctions.HTGeometry.ABHN
