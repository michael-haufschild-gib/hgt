import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealACC
import GaloisForLFunctions.HTGeometry.DifferentialKolchinClosure

/-!
# The Kolchin topology of one differential coordinate is Noetherian

Vanishing ideals of sets of points are radical (the target is reduced) and differential, and a
Kolchin closed set is recovered from its vanishing ideal.  The ascending chain condition on radical
differential ideals therefore becomes the descending chain condition on Kolchin closed sets.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K L : Type*} [Field K] [CharZero K] [Differential K]
  [CommRing L] [IsReduced L] [Algebra K L] [Differential L] [DifferentialAlgebra K L]

attribute [local instance] differentialPolynomialDifferential

omit [CharZero K] [Differential K] [DifferentialAlgebra K L] in
theorem isRadical_differentialVanishingIdealOver (X : Set (Unit → L)) :
    (differentialVanishingIdealOver (K := K) (L := L) X).IsRadical := by
  intro P hP
  obtain ⟨n, hn⟩ := hP
  intro x hx
  have hzero : (differentialPolynomialEvalOver (K := K) x P) ^ n = 0 := by
    rw [← map_pow]
    exact hn x hx
  exact IsReduced.eq_zero _ ⟨n, hzero⟩

/-- **The descending chain condition on Kolchin closed sets.** -/
theorem dcc_isKolchinClosedOver (X : ℕ → Set (Unit → L)) (hanti : Antitone X)
    (hclosed : ∀ n, IsKolchinClosedOver K (X n)) :
    ∃ N : ℕ, ∀ n, N ≤ n → X n = X N := by
  classical
  set I : ℕ → Ideal (DifferentialPolynomial Unit K) :=
    fun n => differentialVanishingIdealOver (K := K) (L := L) (X n) with hI
  have hmono : Monotone I := by
    intro m n hmn P hP x hx
    exact hP x (hanti hmn hx)
  obtain ⟨N, hN⟩ := acc_radicalDifferentialIdeal I hmono
    (fun n => isRadical_differentialVanishingIdealOver (K := K) (X n))
    (fun n P hP => differentialPolynomialOverDerivation_mem_differentialVanishingIdealOver
      (X n) hP)
  refine ⟨N, fun n hn => ?_⟩
  have hXn : kolchinClosureOver K (X n) = X n :=
    isKolchinClosedOver_iff_kolchinClosureOver_eq.mp (hclosed n)
  have hXN : kolchinClosureOver K (X N) = X N :=
    isKolchinClosedOver_iff_kolchinClosureOver_eq.mp (hclosed N)
  rw [← hXn, ← hXN, kolchinClosureOver, kolchinClosureOver]
  congr 1
  exact congrArg
    (fun J : Ideal (DifferentialPolynomial Unit K) =>
      (J : Set (DifferentialPolynomial Unit K))) (hN n hn)

end

end GaloisForLFunctions.HTGeometry
