import GaloisForLFunctions.HTGeometry.PaperNativeReesQuotient

/-!
# Homogeneous independence in native Rees coordinates

Transport the paper's coefficient-kernel mechanism to the existing natural
grading of the native Rees algebra. No cancellation between distinct
homogeneous degrees can hide a nonzero initial class.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Polynomial evaluation in the special fibre, with the coefficient map made explicit. -/
def paperNativeReesPolynomialMap {S : Type*} [CommRing S] (f : S →+* R)
    (x : PaperIdealAssociatedGraded I) : Polynomial S →+* PaperIdealAssociatedGraded I :=
  Polynomial.eval₂RingHom ((algebraMap R (PaperIdealAssociatedGraded I)).comp f) x

/-- A finite sum of native initial classes vanishes exactly one coefficient at a time. -/
theorem paperNativeRees_sum_mono_eq_zero_iff (s : Finset ℕ) (a : (n : ℕ) → (I ^ n : Ideal R)) :
    (∑ n ∈ s, paperNativeReesSpecialization I (ReesGrading.mono I n (a n) (a n).property)) = 0 ↔
      ∀ n ∈ s, (a n : R) ∈ I ^ (n + 1) := by
  classical
  have hcoeff (n : ℕ) :
      ((∑ i ∈ s, ReesGrading.mono I i (a i) (a i).property : reesAlgebra I) : Polynomial R).coeff n =
        if n ∈ s then (a n : R) else 0 := by
    change ((reesAlgebra I).val (∑ i ∈ s, ReesGrading.mono I i (a i) (a i).property)).coeff n = _
    rw [map_sum]
    change (∑ i ∈ s, Polynomial.monomial i (a i : R) : Polynomial R).coeff n = _
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    exact Finset.sum_ite_eq' s n (fun i => (a i : R))
  rw [← map_sum, paperNativeReesSpecialization_eq_zero_iff_coeff]
  constructor
  · intro h n hn
    simpa only [hcoeff, if_pos hn] using h n
  · intro h n
    rw [hcoeff]
    split_ifs with hn
    · exact h n hn
    · exact (I ^ (n + 1)).zero_mem

/-- Homogeneous initial classes have no cross-degree cancellation in the native quotient. -/
theorem paperNativeRees_sum_mono_eq_zero_iff_individual
    (s : Finset ℕ) (a : (n : ℕ) → (I ^ n : Ideal R)) :
    (∑ n ∈ s, paperNativeReesSpecialization I (ReesGrading.mono I n (a n) (a n).property)) = 0 ↔
      ∀ n ∈ s, paperNativeReesSpecialization I (ReesGrading.mono I n (a n) (a n).property) = 0 := by
  simp only [paperNativeRees_sum_mono_eq_zero_iff, paperNativeReesSpecialization_mono_eq_zero_iff]

end

end GaloisForLFunctions.HTGeometry
