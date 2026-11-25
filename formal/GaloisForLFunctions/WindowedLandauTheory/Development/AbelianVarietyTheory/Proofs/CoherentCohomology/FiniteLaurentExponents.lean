import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PolynomialLocalizationCoefficients
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Noetherian.Basic

/-! Fixed total degree bounds all exponents when their signs are the same. -/

open MvPolynomial

namespace GlobalTheory

variable {ι : Type} [Fintype ι]

def fullyNegativeExponents (ι : Type) [Fintype ι] (n : ℤ) : Set (ι → ℤ) :=
  {a | (∑ i, a i) = n ∧ ∀ i, a i < 0}

theorem finite_fullyNegativeExponents (n : ℤ) : (fullyNegativeExponents ι n).Finite := by
  classical
  refine (Set.Finite.pi' fun _ : ι => Set.finite_Icc n (0 : ℤ)).subset ?_
  intro a ha i
  have hneg : ∀ i, a i ≤ 0 := fun i => (ha.2 i).le
  refine ⟨?_, hneg i⟩
  have h := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
  have hrest : ∑ j ∈ Finset.univ.erase i, a j ≤ 0 := Finset.sum_nonpos fun j _ => hneg j
  rw [ha.1] at h
  omega

theorem finite_localizedExponents_empty (n : ℤ) : (localizedExponents (∅ : Finset ι) n).Finite := by
  classical
  refine (Set.Finite.pi' fun _ : ι => Set.finite_Icc (0 : ℤ) n).subset ?_
  intro a ha i
  have hpos : ∀ i, 0 ≤ a i := fun i => ha.2 i (Finset.notMem_empty _)
  refine ⟨hpos i, ?_⟩
  rw [← ha.1]
  exact Finset.single_le_sum (f := a) (fun j _ => hpos j) (Finset.mem_univ i)

theorem finite_homLoc_of_finite_exponents {R : Type} [CommRing R] [IsNoetherianRing R]
    {s : Finset ι} {n : ℤ} (hs : (localizedExponents s n).Finite) :
    Module.Finite R (homLoc (polyGrading ι R) s n) := by
  letI := hs.fintype
  let K := Finsupp.supported R R (localizedExponents s n)
  let e : K ≃ₗ[R] (localizedExponents s n) →₀ R := Finsupp.supportedEquivFinsupp _
  let f : homLoc (polyGrading ι R) s n →ₗ[R] K :=
    (localizedCoefficients R s n).codRestrict K fun z =>
      (Finsupp.mem_supported R _).2 (localizedCoefficients_support s n z)
  apply Module.Finite.of_injective (e.toLinearMap.comp f)
  exact e.injective.comp (fun _ _ h => localizedCoefficients_injective s n (congrArg Subtype.val h))

end GlobalTheory
