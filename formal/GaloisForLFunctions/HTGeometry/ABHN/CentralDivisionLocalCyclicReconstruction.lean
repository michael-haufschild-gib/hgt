import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionLocalCyclicNormalizer
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionRepresentative
import GaloisForLFunctions.HTGeometry.ABHN.CyclicAlgebraLiftGenerator
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisBrauerSubgroup
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerAdditive

/-!
# Cyclic reconstruction of local central division algebras

A maximal cyclic Galois subfield and its Skolem--Noether normalizer give the defining relations
of a cyclic algebra. Mapping the formal cyclic generator to the inverse normalizer is injective by
cyclic-algebra simplicity and surjective by the exact dimension formula. Consequently every
Brauer class over a nonarchimedean local field has a cyclic Galois representative.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

section Reconstruction

variable (F T A : Type) [Field F] [Field T] [DivisionRing A]
  [Algebra F T] [Algebra F A] [IsCyclic Gal(T / F)]
  [FiniteDimensional F T] [IsGalois F T]

/-- Universal cyclic-algebra map induced by a normalizer whose degree-th power is central. The
inverse normalizer matches the convention `X * C(t) = C(σ(t)) * X` of `cyclicGaloisAlgebra`. -/
noncomputable def cyclicGaloisAlgebraNormalizerRingHom
    (iota : T →ₐ[F] A) (u : Aˣ) (a : Fˣ)
    (hcomm : ∀ t : T, iota t * (u : A) =
      (u : A) * iota (cyclicGaloisGenerator F T t))
    (hpow : (u : A) ^ Module.finrank F T = algebraMap F A (a : F)) :
    cyclicGaloisAlgebra F T ((a⁻¹ : Fˣ) : F) →+* A := by
  let y : A := (u⁻¹ : Aˣ)
  have hone : ∀ t : T,
      iota (cyclicGaloisGenerator F T t) * y = y * iota t := by
    intro t
    change iota (cyclicGaloisGenerator F T t) * (u⁻¹ : Aˣ) =
      (u⁻¹ : Aˣ) * iota t
    calc
      iota (cyclicGaloisGenerator F T t) * (u⁻¹ : Aˣ) =
          (u⁻¹ : Aˣ) *
            ((u : A) * (iota (cyclicGaloisGenerator F T t) * (u⁻¹ : Aˣ))) := by
        simp
      _ = (u⁻¹ : Aˣ) *
            (((u : A) * iota (cyclicGaloisGenerator F T t)) * (u⁻¹ : Aˣ)) := by
        rw [mul_assoc]
      _ = (u⁻¹ : Aˣ) * ((iota t * (u : A)) * (u⁻¹ : Aˣ)) := by
        rw [hcomm]
      _ = (u⁻¹ : Aˣ) * iota t := by
        simp
  have hall := cyclicAlgebraLift_comm_of_generator
    (cyclicGaloisGenerator F T).toRingEquiv iota.toRingHom y hone
  have hrel : y ^ Module.finrank F T =
      iota (algebraMap F T ((a⁻¹ : Fˣ) : F)) := by
    simpa [y] using congrArg Inv.inv hpow
  exact cyclicAlgebraLift (cyclicGaloisGenerator F T).toRingEquiv
    (Module.finrank F T) (algebraMap F T ((a⁻¹ : Fˣ) : F))
    iota.toRingHom y hall hrel

omit [FiniteDimensional F T] [IsGalois F T] in
/-- The reconstruction map restricts to the prescribed embedding of the cyclic subfield. -/
theorem cyclicGaloisAlgebraNormalizerRingHom_C
    (iota : T →ₐ[F] A) (u : Aˣ) (a : Fˣ)
    (hcomm : ∀ t : T, iota t * (u : A) =
      (u : A) * iota (cyclicGaloisGenerator F T t))
    (hpow : (u : A) ^ Module.finrank F T = algebraMap F A (a : F))
    (t : T) :
    cyclicGaloisAlgebraNormalizerRingHom F T A iota u a hcomm hpow
        (cyclicGaloisAlgebraC F T ((a⁻¹ : Fˣ) : F) t) = iota t := by
  simp only [cyclicGaloisAlgebraNormalizerRingHom]
  apply cyclicAlgebraLift_C

/-- Simplicity of the nonzero cyclic algebra makes the reconstruction map injective. -/
theorem cyclicGaloisAlgebraNormalizerRingHom_injective
    (iota : T →ₐ[F] A) (u : Aˣ) (a : Fˣ)
    (hcomm : ∀ t : T, iota t * (u : A) =
      (u : A) * iota (cyclicGaloisGenerator F T t))
    (hpow : (u : A) ^ Module.finrank F T = algebraMap F A (a : F)) :
    Function.Injective (cyclicGaloisAlgebraNormalizerRingHom F T A iota u a hcomm hpow) := by
  letI : IsSimpleRing (cyclicGaloisAlgebra F T ((a⁻¹ : Fˣ) : F)) :=
    isSimpleRing_cyclicGaloisAlgebra_of_nonzero F T _ (Units.ne_zero (a⁻¹))
  exact RingHom.injective _

/-- The reconstruction map as a homomorphism of base-field algebras. -/
noncomputable def cyclicGaloisAlgebraNormalizerAlgHom
    (iota : T →ₐ[F] A) (u : Aˣ) (a : Fˣ)
    (hcomm : ∀ t : T, iota t * (u : A) =
      (u : A) * iota (cyclicGaloisGenerator F T t))
    (hpow : (u : A) ^ Module.finrank F T = algebraMap F A (a : F)) :
    cyclicGaloisAlgebra F T ((a⁻¹ : Fˣ) : F) →ₐ[F] A :=
  { cyclicGaloisAlgebraNormalizerRingHom F T A iota u a hcomm hpow with
    commutes' := by
      intro r
      rw [cyclicGaloisAlgebra_algebraMap_apply]
      exact (cyclicGaloisAlgebraNormalizerRingHom_C
        F T A iota u a hcomm hpow (algebraMap F T r)).trans (iota.commutes r) }

/-- Exact equality of dimensions upgrades injectivity of the reconstruction map to surjectivity. -/
theorem cyclicGaloisAlgebraNormalizerAlgHom_surjective
    [Module.Finite F A] [Algebra.IsCentral F A]
    (iota : T →ₐ[F] A) (u : Aˣ) (a : Fˣ)
    (hcomm : ∀ t : T, iota t * (u : A) =
      (u : A) * iota (cyclicGaloisGenerator F T t))
    (hpow : (u : A) ^ Module.finrank F T = algebraMap F A (a : F))
    (hdegree : Module.finrank F T = divisionAlgebraDegree (F := F) (A := A)) :
    Function.Surjective
      (cyclicGaloisAlgebraNormalizerAlgHom F T A iota u a hcomm hpow) := by
  have hinj : Function.Injective
      (cyclicGaloisAlgebraNormalizerAlgHom F T A iota u a hcomm hpow) :=
    cyclicGaloisAlgebraNormalizerRingHom_injective F T A iota u a hcomm hpow
  have hfin :
      Module.finrank F (cyclicGaloisAlgebra F T ((a⁻¹ : Fˣ) : F)) =
        Module.finrank F A := by
    rw [cyclicGaloisAlgebra_finrank_eq_square, hdegree]
    simpa [pow_two] using
      (divisionAlgebraDegree_mul_self (F := F) (A := A))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (cyclicGaloisAlgebraNormalizerAlgHom F T A iota u a hcomm hpow).toLinearMap)
    hfin).mp hinj

/-- A normalizing unit with a central degree-th power reconstructs the central division algebra
as the corresponding cyclic Galois algebra. -/
noncomputable def cyclicGaloisAlgebraNormalizerAlgEquiv
    [Module.Finite F A] [Algebra.IsCentral F A]
    (iota : T →ₐ[F] A) (u : Aˣ) (a : Fˣ)
    (hcomm : ∀ t : T, iota t * (u : A) =
      (u : A) * iota (cyclicGaloisGenerator F T t))
    (hpow : (u : A) ^ Module.finrank F T = algebraMap F A (a : F))
    (hdegree : Module.finrank F T = divisionAlgebraDegree (F := F) (A := A)) :
    cyclicGaloisAlgebra F T ((a⁻¹ : Fˣ) : F) ≃ₐ[F] A :=
  AlgEquiv.ofBijective
    (cyclicGaloisAlgebraNormalizerAlgHom F T A iota u a hcomm hpow)
    ⟨cyclicGaloisAlgebraNormalizerRingHom_injective F T A iota u a hcomm hpow,
      cyclicGaloisAlgebraNormalizerAlgHom_surjective F T A iota u a hcomm hpow hdegree⟩

end Reconstruction

section LocalReconstruction

open scoped NormedField ValuativeRel Valued

variable {F A : Type} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F] [DivisionRing A] [Algebra F A]
  [Module.Finite F A] [Algebra.IsCentral F A]

/-- Every finite-dimensional central division algebra over a nonarchimedean local field is a
cyclic algebra, reconstructed from its residue-exhausting unramified maximal subfield. -/
theorem exists_residueExhausting_cyclicGaloisAlgebraAlgEquiv :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      let T := Algebra.adjoin F ({(x : A)} : Set A)
      ∃ hT : IsField T,
        letI : Field T := hT.toField
        letI : Algebra F T := Subalgebra.algebra T
        Module.finrank F T = divisionAlgebraDegree (F := F) (A := A) ∧
          (letI : NormedDivisionRing A :=
              divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A);
            letI : NontriviallyNormedField T :=
              divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
                (F := F) (A := A) T hT;
            letI : NormedSpace F T :=
              divisionAlgebraRestrictedRootDeterminantNormedSpace
                (F := F) (A := A) T hT;
            letI : IsUltrametricDist T :=
              divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
                (F := F) (A := A) T hT;
            Nonempty (NormValuationResidue (F := T) ≃ₐ[NormValuationResidue (F := F)]
              DivisionAlgebraDeterminantResidue (F := F) (A := A))) ∧
          ∃ hGalois : IsGalois F T,
            letI : IsGalois F T := hGalois
            ∃ hCyclic : IsCyclic Gal(T / F),
              letI : IsCyclic Gal(T / F) := hCyclic
              ∃ u : Aˣ, ∃ a : Fˣ,
                (∀ t : T, (t : A) * (u : A) =
                  (u : A) * (cyclicGaloisGenerator F T t : T)) ∧
                (u : A) ^ Module.finrank F T = algebraMap F A (a : F) ∧
                Nonempty
                  (cyclicGaloisAlgebra F T ((a⁻¹ : Fˣ) : F) ≃ₐ[F] A) := by
  obtain ⟨x, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, u, a, hcomm, hpow⟩ :=
    exists_residueExhausting_cyclicNormalizer_baseParameter (F := F) (A := A)
  let T := Algebra.adjoin F ({((x :
    divisionAlgebraDeterminantValuationSubring (F := F) (A := A)) : A)} : Set A)
  letI : Field T := hT.toField
  letI : Algebra F T := Subalgebra.algebra T
  letI : FiniteDimensional F T := by infer_instance
  letI : IsGalois F T := hGalois
  letI : IsCyclic Gal(T / F) := hCyclic
  have hcomm' : ∀ t : T, (t : A) * (u : A) =
      (u : A) * (cyclicGaloisGenerator F T t : T) := by
    simpa only [cyclicGaloisGeneratorAnyUniverse, cyclicGaloisGenerator] using hcomm
  refine ⟨x, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, u, a, hcomm', hpow, ?_⟩
  exact ⟨cyclicGaloisAlgebraNormalizerAlgEquiv F T A (Subalgebra.val T)
    u a hcomm' hpow hdegree⟩

/-- Every Brauer class over a nonarchimedean local field is represented by a cyclic Galois
algebra. This is local cyclic exhaustion, the crossed-product input to the local invariant. -/
theorem nonarchimedeanLocal_brauerGroup_exists_cyclicGaloisRepresentative
    (x : BrauerGroup F) :
    ∃ (T : Type) (_ : Field T) (_ : Algebra F T) (_ : FiniteDimensional F T)
      (_ : IsGalois F T) (_ : IsCyclic Gal(T / F)) (a : Fˣ),
      x = brauerClass
        (cyclicGaloisAlgebraCSA F T ((a⁻¹ : Fˣ) : F) (Units.ne_zero (a⁻¹))) := by
  obtain ⟨D, hD, aD, finD, centralD, hx⟩ :=
    brauerGroup_exists_centralDivisionRepresentative F x
  letI : DivisionRing D := hD
  letI : Algebra F D := aD
  letI : Module.Finite F D := finD
  letI : Algebra.IsCentral F D := centralD
  obtain ⟨z, hT, hdegree, hres, hGalois, hCyclic, u, a, hcomm, hpow, ⟨e⟩⟩ :=
    exists_residueExhausting_cyclicGaloisAlgebraAlgEquiv (F := F) (A := D)
  let T := Algebra.adjoin F ({((z :
    divisionAlgebraDeterminantValuationSubring (F := F) (A := D)) : D)} : Set D)
  letI : Field T := hT.toField
  letI : Algebra F T := Subalgebra.algebra T
  letI : FiniteDimensional F T := by infer_instance
  letI : IsGalois F T := hGalois
  letI : IsCyclic Gal(T / F) := hCyclic
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, a, ?_⟩
  exact hx.trans (brauerClass_eq_of_algEquiv
    (cyclicGaloisAlgebraCSA F T ((a⁻¹ : Fˣ) : F) (Units.ne_zero (a⁻¹)))
    (centralDivisionCSA F D) e).symm

/-- Every local Brauer class occurs in one finite cyclic Galois Brauer slice. -/
theorem nonarchimedeanLocal_brauerGroup_cyclicSlice_exhaustion
    (x : BrauerGroup F) :
    ∃ (T : Type) (_ : Field T) (_ : Algebra F T) (_ : FiniteDimensional F T)
      (_ : IsGalois F T) (_ : IsCyclic Gal(T / F)),
      ∃ y : cyclicGaloisBrauerSubgroup F T, (y : BrauerGroup F) = x := by
  obtain ⟨T, hT, aT, finT, galT, cycT, a, hx⟩ :=
    nonarchimedeanLocal_brauerGroup_exists_cyclicGaloisRepresentative (F := F) x
  letI : Field T := hT
  letI : Algebra F T := aT
  letI : FiniteDimensional F T := finT
  letI : IsGalois F T := galT
  letI : IsCyclic Gal(T / F) := cycT
  let y : cyclicGaloisBrauerSubgroup F T :=
    ⟨brauerClass
        (cyclicGaloisAlgebraCSA F T ((a⁻¹ : Fˣ) : F) (Units.ne_zero (a⁻¹))),
      cyclicGaloisAlgebra_brauerClass_mem_cyclicGaloisBrauerSubgroup F T (a⁻¹)⟩
  exact ⟨T, hT, aT, finT, galT, cycT, y, hx.symm⟩

/-- The Brauer group of a nonarchimedean local field is torsion. More precisely, every class is
killed by the degree of a cyclic Galois field occurring in its reconstruction. -/
theorem nonarchimedeanLocal_brauerGroup_isTorsion :
    AddMonoid.IsTorsion (BrauerGroup F) := by
  intro x
  obtain ⟨T, hT, aT, finT, galT, cycT, a, hx⟩ :=
    nonarchimedeanLocal_brauerGroup_exists_cyclicGaloisRepresentative (F := F) x
  letI : Field T := hT
  letI : Algebra F T := aT
  letI : FiniteDimensional F T := finT
  letI : IsGalois F T := galT
  letI : IsCyclic Gal(T / F) := cycT
  let b : Additive Fˣ := Additive.ofMul (a⁻¹)
  let z : cyclicGaloisH2 F T := cyclicGaloisH2BaseProjection F T b
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨Module.finrank F T, Module.finrank_pos, ?_⟩
  rw [hx]
  have hclass :
      brauerClass (cyclicGaloisAlgebraCSA F T ((a⁻¹ : Fˣ) : F) (Units.ne_zero (a⁻¹))) =
        cyclicGaloisH2BrauerMap F T z := by
    exact cyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection
      F T b z rfl
  rw [hclass]
  change Module.finrank F T • cyclicGaloisH2BrauerAddHom F T z = 0
  rw [← map_nsmul, cyclicGaloisH2_finrank_nsmul_eq_zero, map_zero]

end LocalReconstruction

end GaloisForLFunctions.HTGeometry.ABHN
