import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbelianDescentFromInvariantFactor
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RelativeFrobeniusConjugation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ConjugatePrimeNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RayClassNorm
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteDegreeOneFrobenius

/-! A faithful relative Artin character induced by the ideal norm is
conjugation invariant, so its extension descends abelianity across a cyclic base change. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions GlobalTheory.DegreeOneFrobenius
open scoped Pointwise IsMulCommutative nonZeroDivisors

namespace GlobalTheory.Reciprocity

variable (K E M T : Type) [Field K] [Field E] [Field M] [Field T]
  [NumberField K] [NumberField E] [NumberField M] [nT : NumberField T]
  [Algebra K E] [Algebra E M] [Algebra M T] [Algebra K M] [Algebra K T] [Algebra E T]
  [IsScalarTower K E M] [hKET : IsScalarTower K E T]
  [hKMT : IsScalarTower K M T] [hEMT : IsScalarTower E M T]
  [IsGalois K E] [IsCyclic (E ≃ₐ[K] E)] [IsAbelianGalois E M]
  [hfin : FiniteDimensional K T] [hgal : IsGalois K T]

local notation "Γ" => (T ≃ₐ[K] T)
local notation "G" => (E ≃ₐ[K] E)
local notation "H" => (M ≃ₐ[E] M)
local notation "res" => (AlgEquiv.restrictNormalHom E : Γ →* G)
local notation "resM" => (AlgEquiv.restrictNormalHom M : (T ≃ₐ[E] T) →* H)

local instance : CommGroup G := IsCyclic.commGroup
local instance : CommGroup H :=
  { (inferInstance : Group H) with mul_comm := IsMulCommutative.is_comm.comm }
local instance : Fintype G := Fintype.ofFinite _
local instance : Fintype H := Fintype.ofFinite _

local instance : SMulCommClass (T ≃ₐ[E] T) (𝓞 E) (𝓞 T) :=
  ⟨fun s a x => RingOfIntegers.ext (by
    change s (algebraMap E T (a : E) * (x : T)) = algebraMap E T (a : E) * s (x : T)
    rw [map_mul, s.commutes])⟩

attribute [local instance] primeMulAction

omit [NumberField K] [NumberField E] nT [IsCyclic (E ≃ₐ[K] E)] hfin hgal in
private theorem smul_algebraMap_ringOfIntegers (t : Γ) (x : 𝓞 E) :
    t • algebraMap (𝓞 E) (𝓞 T) x = algebraMap (𝓞 E) (𝓞 T) (res t • x) :=
  RingOfIntegers.ext (t.restrictNormal_commutes E (x : E)).symm

omit nT in
private theorem restriction_frob_of_unramified
    {w : HeightOneSpectrum (𝓞 E)} (hu : IsUnramifiedPrime E M H w)
    (P : Ideal (𝓞 T)) [P.IsMaximal] [P.LiesOver w.asIdeal]
    {s : T ≃ₐ[E] T} (hs : IsArithFrobAt (𝓞 E) s P) :
    resM s = frobeniusElement E M H w := by
  let Q := P.under (𝓞 M)
  letI : Q.IsMaximal := inferInstance
  letI : Q.LiesOver w.asIdeal := Ideal.under_liesOver_of_liesOver (𝓞 M) P w.asIdeal
  have hπ (z : T ≃ₐ[E] T) (x : 𝓞 M) :
      algebraMap (𝓞 M) (𝓞 T) (resM z • x) = z • algebraMap (𝓞 M) (𝓞 T) x :=
    RingOfIntegers.ext (z.restrictNormal_commutes M (x : M))
  have hQ : IsArithFrobAt (𝓞 E) (resM s) Q := isArithFrobAt_map_under resM hπ hs
  have hd := hQ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 E) H Q)
  rw [hu Q inferInstance inferInstance, Subgroup.mem_bot,
    arithFrobAt_eq_frobeniusElement hu Q] at hd
  exact mul_inv_eq_one.mp hd

omit [NumberField K] [NumberField E] nT [IsCyclic (E ≃ₐ[K] E)] hfin hgal in
private theorem isArithFrobAt_conjugate_restriction
    {P : Ideal (𝓞 T)} {s : (res).ker}
    (hs : IsArithFrobAt (𝓞 E) (restrictionKernelEquiv K E T s) P) (t : Γ) :
    IsArithFrobAt (𝓞 E) (restrictionKernelEquiv K E T (conjugateIn (res).ker t s)) (t • P) := by
  letI : SMulCommClass (res).ker (𝓞 E) (𝓞 T) :=
    ⟨fun z a x => smul_comm (restrictionKernelEquiv K E T z) a x⟩
  have hs' : IsArithFrobAt (𝓞 E) s P := fun x => hs x
  have ht := conjugateIn_isArithFrobAt res (smul_algebraMap_ringOfIntegers K E T) hs' t
  exact fun x => ht x

omit [NumberField K] [NumberField E] nT hfin hgal in
private theorem prime_liesOver_conjugate (t : Γ) (w : HeightOneSpectrum (𝓞 E))
    (P : Ideal (𝓞 T)) [P.LiesOver w.asIdeal] :
    (t • P : Ideal (𝓞 T)).LiesOver (res t • w).asIdeal := by
  constructor
  rw [under_smul_eq_map_smul_under res
    (fun z x => (smul_algebraMap_ringOfIntegers K E T z x).symm), ← Ideal.over_def P w.asIdeal]
  exact asIdeal_prime_smul E G (res t) w

omit [IsScalarTower K E M] in
include nT hKET hKMT hEMT hfin hgal in
/-- Relative Frobenius values of a norm pullback force abelianity over the lower field. -/
theorem isAbelianGalois_of_norm_frobenius {A : Type*} [Group A]
    (c : ℕ) [NeZero c] (χ : RayClassGroup (normModulus K c) →* A) (ψ : H →* A)
    (hinj : Function.Injective ψ)
    (hu : ∀ w, ¬ w.asIdeal ∣ (normModulus E c).fin → IsUnramifiedPrime E M H w)
    (hχ : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ w.asIdeal ∣ (normModulus E c).fin),
      ψ (frobeniusElement E M H w) =
        χ (rayClassNorm K E c (rayClass (normModulus E c) ⟨idealUnit w.ne_bot,
          idealUnit_prime_mem_idealGroup _ hw⟩))) : IsAbelianGalois K M := by
  letI : IsGalois E T := IsGalois.tower_top_of_isGalois K E T
  apply isAbelianGalois_of_invariant_factor K E T ψ hinj
  intro t s
  obtain ⟨w, hw, -, P, hP, hPw, hs⟩ := exists_arithmeticFrobenius_away E T
    (restrictionKernelEquiv K E T s) _ (finite_primes_dvd (normModulus E c))
  letI := hP
  letI := hPw
  let w' := res t • w
  have hw' : ¬ w'.asIdeal ∣ (normModulus E c).fin :=
    (prime_dvd_normModulus_smul_iff E G c (res t) w).not.mpr hw
  let Q : Ideal (𝓞 T) := t • P
  letI : Q.IsMaximal := by
    rw [show Q = t • P from rfl, Ideal.pointwise_smul_def]
    exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv Γ (𝓞 T) t)
  letI : Q.LiesOver w'.asIdeal := prime_liesOver_conjugate K E T t w P
  rw [restriction_frob_of_unramified E M T (hu _ hw) P hs,
    restriction_frob_of_unramified E M T (hu _ hw') Q
      (isArithFrobAt_conjugate_restriction K E T hs t), hχ _ hw, hχ _ hw']
  apply congrArg (χ ∘ rayClass (normModulus K c))
  apply Subtype.ext
  exact idealNormHom_idealUnit_smul K E G (res t) w

end GlobalTheory.Reciprocity
