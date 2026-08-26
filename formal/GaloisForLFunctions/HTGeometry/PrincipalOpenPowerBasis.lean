import GaloisForLFunctions.HTGeometry.ABHN.GenericLocalizationBijection

/-!
# Spreading a localized power basis to a principal open

For a finite presented algebra, a global element whose powers form a basis after localization at
a prime already has power-basis coordinates after inverting one element outside that prime.  This
is the finite-presentation step that spreads a local monogenic presentation to an affine
principal-open chart.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalizedModule
open scoped TensorProduct

universe u v w

/-- A finite module over a Noetherian commutative ring is finitely presented. -/
theorem moduleFinitePresentation_of_isNoetherianRing_of_finite
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.FinitePresentation R M := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let s : Finset M := Finset.univ.image g
  refine Module.FinitePresentation.mk ⟨s, ?_, ?_⟩
  · rw [← hg]
    congr 1
    ext x
    simp [s]
  · letI : IsNoetherian R (↑s →₀ R) := by infer_instance
    exact IsNoetherian.noetherian _

/-- The coefficient map for the first `d` powers of an algebra element. -/
noncomputable def powerCombination
    {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
    (theta : B) (d : Nat) : (Fin d →₀ R) →ₗ[R] B :=
  Finsupp.linearCombination R (fun i : Fin d => theta ^ (i : Nat))

@[simp]
theorem powerCombination_basisSingleOne
    {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
    (theta : B) (d : Nat) (i : Fin d) :
    powerCombination (R := R) theta d (Finsupp.single i 1) = theta ^ (i : Nat) := by
  classical
  rw [powerCombination, Finsupp.linearCombination_single, one_smul]

/-- The localized coefficient map is bijective when the localized powers are a basis. -/
theorem localized_powerCombination_bijective_of_basis
    (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type w) [CommRing T] [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N]
    (fN : B →ₗ[R] N) [IsLocalizedModule p.primeCompl fN]
    (theta : B) (d : Nat) (b : Module.Basis (Fin d) T N)
    (hb : ∀ i : Fin d, b i = fN (theta ^ (i : Nat))) :
    Function.Bijective (IsLocalizedModule.map p.primeCompl
      (TensorProduct.mk R T (Fin d →₀ R) 1) fN (powerCombination (R := R) theta d)) := by
  classical
  let M := Fin d →₀ R
  let fM : M →ₗ[R] TensorProduct R T M := TensorProduct.mk R T M 1
  let localMap := IsLocalizedModule.map p.primeCompl fM fN
    (powerCombination (R := R) theta d)
  let sourceBasis : Module.Basis (Fin d) T (TensorProduct R T M) :=
    (Finsupp.basisSingleOne (R := R) (ι := Fin d)).baseChange T
  let e : TensorProduct R T M ≃ₗ[T] N := sourceBasis.equivFun.trans b.equivFun.symm
  have he_basis (i : Fin d) : e (sourceBasis i) = b i := by
    apply b.equivFun.injective
    ext j
    simp [e, Module.Basis.equivFun_apply, Finsupp.single_apply]
  have hlocal_eq : localMap = e.toLinearMap.restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext p.primeCompl fM fN
    apply Module.Basis.ext (Finsupp.basisSingleOne (R := R) (ι := Fin d))
    intro i
    change localMap (fM (Finsupp.single i 1)) = e (fM (Finsupp.single i 1))
    dsimp only [localMap]
    rw [IsLocalizedModule.map_apply]
    change fN (powerCombination (R := R) theta d (Finsupp.single i 1)) =
      e (fM (Finsupp.single i 1))
    rw [powerCombination_basisSingleOne, ← hb]
    have hsource : fM (Finsupp.single i 1) = sourceBasis i := by
      dsimp only [fM, sourceBasis]
      rw [Module.Basis.baseChange_apply]
      exact TensorProduct.mk_apply _ _
    rw [hsource, he_basis]
  change Function.Bijective localMap
  rw [hlocal_eq]
  exact e.bijective

/-- A power basis visible at a prime spreads to one principal open containing that prime. -/
theorem exists_notMem_powerCombination_bijective_of_localized_basis
    (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type w) [CommRing T] [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N]
    (fN : B →ₗ[R] N) [IsLocalizedModule p.primeCompl fN]
    (theta : B) (d : Nat) (b : Module.Basis (Fin d) T N)
    (hb : ∀ i : Fin d, b i = fN (theta ^ (i : Nat))) :
    ∃ g ∉ p, Function.Bijective
      (LocalizedModule.map (Submonoid.powers g) (powerCombination (R := R) theta d)) := by
  letI : Module.FinitePresentation R B :=
    moduleFinitePresentation_of_isNoetherianRing_of_finite R B
  letI : Module.Finite R (Fin d →₀ R) :=
    Module.Finite.of_basis (Finsupp.basisSingleOne (R := R) (ι := Fin d))
  have hlocal := localized_powerCombination_bijective_of_basis
    R B p T N fN theta d b hb
  exact Module.FinitePresentation.exists_notMem_bijective
    (powerCombination (R := R) theta d) p (TensorProduct.mk R T (Fin d →₀ R) 1) fN
    hlocal

end GaloisForLFunctions.HTGeometry
