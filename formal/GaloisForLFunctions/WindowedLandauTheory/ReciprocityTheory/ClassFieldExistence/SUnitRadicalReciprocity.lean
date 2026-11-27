import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SUnitRadicalUnramified
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.PowerCongruenceArtinKernel
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The Artin map of the S-unit radical extension kills the diagonal
and the n-th-power congruences at S and at infinity. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Kummer

open GlobalTheory.Reciprocity GlobalTheory.Reciprocity.IdeleGroup GlobalTheory.Reciprocity.IdeleRay

universe u

variable (K : Type u) [Field K] [NumberField K]
attribute [local instance] primeMulAction

/-- A finite set of primes is stable under the trivial Galois group of K/K. -/
def sUnitPrimeSet (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SubMulAction Gal(K/K) (HeightOneSpectrum (𝓞 K)) where
  carrier := S
  smul_mem' g v hv := by
    rw [Subsingleton.elim g (1 : Gal(K/K)), one_smul]
    exact hv

instance (S : Finset (HeightOneSpectrum (𝓞 K))) : Fintype (sUnitPrimeSet K S) := by
  change Fintype (S : Set (HeightOneSpectrum (𝓞 K)))
  infer_instance

omit [NumberField K] in
theorem card_sUnitPrimeSet (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Fintype.card (sUnitPrimeSet K S) = S.card := by
  have e : sUnitPrimeSet K S ≃ S := Equiv.refl _
  exact (Fintype.card_congr e).trans (Fintype.card_coe S)

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]

/-- The S-unit radical extension inside a fixed algebraic closure. -/
def sUnitRadicalExtension : IntermediateField K (AlgebraicClosure K) :=
  radicalField (sUnitRadicalClasses K Gal(K/K) (sUnitPrimeSet K S) n)

local notation "M" => sUnitRadicalExtension K S n

instance : FiniteDimensional K M :=
  radicalField_finiteDimensional (AlgebraicClosure K) (sUnitRadicalClasses K Gal(K/K) (sUnitPrimeSet K S) n)

instance : IsAbelianGalois K M :=
  radicalField_isAbelianGalois _

theorem finrank_sUnitRadicalExtension :
    Module.finrank K M = n ^ (Fintype.card (InfinitePlace K) + S.card) := by
  rw [sUnitRadicalExtension, finrank_sUnitRadicalField, card_sUnitPrimeSet]

theorem exists_sUnitRadical_artin
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    letI : Fintype Gal(M/K) := Fintype.ofFinite _
    letI : NumberField M := NumberField.of_module_finite K M
    letI : CommGroup Gal(M/K) :=
      { (inferInstance : Group Gal(M/K)) with mul_comm := IsMulCommutative.is_comm.comm }
    ∃ (m : Modulus K) (φ : IdeleGroup K →* Gal(M/K)),
      Continuous φ ∧ Function.Surjective φ ∧
      (diagonal K).range ⊔ powerCongruence n S ≤ φ.ker ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.fin ↔ ¬ IsUnramifiedPrime K M Gal(M/K) v) ∧
      ∀ x : idelesOneMod m, φ x.val = artinMap K M Gal(M/K) (toFractionalIdeal x.val) := by
  letI : Fintype Gal(M/K) := Fintype.ofFinite _
  letI : NumberField M := NumberField.of_module_finite K M
  letI : CommGroup Gal(M/K) :=
    { (inferInstance : Group Gal(M/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  letI : DiscreteTopology Gal(M/K) := krullTopology_discreteTopology_of_finiteDimensional K M
  obtain ⟨m, φ, hc, hsurj, hd, hram, hφ⟩ := exists_finite_idelic_artin K M Gal(M/K)
  have hexp (g : Gal(M/K)) : g ^ n = 1 :=
    radicalField_pow_eq_one (sUnitRadicalClasses K Gal(K/K) (sUnitPrimeSet K S) n) g
  have hm (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ m.fin) : v ∈ S := by
    by_contra hvS
    exact (hram v).mp hv (sUnitRadicalField_unramified (Ω := AlgebraicClosure K)
      (sUnitPrimeSet K S) v (show v ∉ sUnitPrimeSet K S from hvS) (fun h => hvS (hnS v h)))
  have hd' : (diagonal K).range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    exact MonoidHom.mem_ker.mpr (hd x)
  exact ⟨m, φ, hc, hsurj,
    sup_le hd' (powerCongruence_le_ker_finite_idelic_artin hexp S m hm φ hφ), hram, hφ⟩

end GlobalTheory.Kummer
