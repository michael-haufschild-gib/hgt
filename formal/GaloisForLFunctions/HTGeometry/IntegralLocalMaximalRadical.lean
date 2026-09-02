import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The maximal ideal under an integral local map

For an integral map between local rings, the radical of the extended maximal ideal is the maximal
ideal upstairs.  This is the algebraic form of saying that an integral local fibre is
zero-dimensional.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing

universe u v

/-- **The extended maximal ideal under an integral map of local rings is maximal-primary.** -/
theorem radical_map_maximalIdeal_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] [IsLocalRing A] [IsLocalRing B] :
    (Ideal.map (algebraMap A B) (maximalIdeal A)).radical = maximalIdeal B := by
  have hcomapMax :
      Ideal.comap (algebraMap A B) (maximalIdeal B) = maximalIdeal A := by
    apply IsLocalRing.eq_maximalIdeal
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B)
  apply le_antisymm
  · rw [Ideal.IsPrime.radical_le_iff (I := Ideal.map _ _) (J := maximalIdeal B)
      (by infer_instance)]
    rw [Ideal.map_le_iff_le_comap, hcomapMax]
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro J hJ
    rcases hJ with ⟨hmap, hprime⟩
    letI : J.IsPrime := hprime
    have hcomap : Ideal.comap (algebraMap A B) J = maximalIdeal A := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal
          (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ J))
      · exact Ideal.map_le_iff_le_comap.mp hmap
    have hmax : J.IsMaximal := by
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (S := B) J
      rw [hcomap]
      infer_instance
    rw [IsLocalRing.eq_maximalIdeal hmax]

/-- **After localizing a finite integral algebra at one of its maximal ideals, the extended
maximal ideal of the local base still has maximal radical.**  The localized algebra need not itself
be integral over the base; the proof contracts primes through the finite integral algebra first. -/
theorem radical_map_maximalIdeal_localizationAtMaximal_eq
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.IsIntegral A D] [IsLocalRing A]
    (q : Ideal D) [q.IsMaximal] :
    (Ideal.map (algebraMap A (Localization.AtPrime q)) (maximalIdeal A)).radical =
      maximalIdeal (Localization.AtPrime q) := by
  let B := Localization.AtPrime q
  have hqcomap : Ideal.comap (algebraMap A D) q = maximalIdeal A := by
    apply IsLocalRing.eq_maximalIdeal
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
  apply le_antisymm
  · rw [Ideal.IsPrime.radical_le_iff
      (I := Ideal.map (algebraMap A B) (maximalIdeal A))
      (J := maximalIdeal B) (by infer_instance)]
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap A B a ∈ maximalIdeal B
    rw [IsScalarTower.algebraMap_apply A D B]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff B q (algebraMap A D a)).2
    change a ∈ Ideal.comap (algebraMap A D) q
    rw [hqcomap]
    exact ha
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro J hJ
    rcases hJ with ⟨hmap, hprime⟩
    letI : J.IsPrime := hprime
    let P : Ideal D := Ideal.comap (algebraMap D B) J
    have hPprime : P.IsPrime := Ideal.comap_isPrime _ J
    letI : P.IsPrime := hPprime
    have hmle : maximalIdeal A ≤ Ideal.comap (algebraMap A D) P := by
      intro a ha
      change algebraMap D B (algebraMap A D a) ∈ J
      rw [← IsScalarTower.algebraMap_apply A D B]
      exact hmap (Ideal.mem_map_of_mem _ ha)
    have hPcomap : Ideal.comap (algebraMap A D) P = maximalIdeal A := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal
          (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ P))
      · exact hmle
    have hPmax : P.IsMaximal := by
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (S := D) P
      rw [hPcomap]
      infer_instance
    have hPle : P ≤ q :=
      (IsLocalization.AtPrime.orderIsoOfPrime B q ⟨J, hprime⟩).2.2
    have hPeq : P = q := hPmax.eq_of_le (Ideal.IsPrime.ne_top (by infer_instance)) hPle
    have hJeq : J = maximalIdeal B :=
      (Localization.AtPrime.eq_maximalIdeal_iff_under_eq (I := q) (J := J)).mp hPeq
    exact hJeq.symm.le

end GaloisForLFunctions.HTGeometry
