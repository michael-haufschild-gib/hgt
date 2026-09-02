import GaloisForLFunctions.HTGeometry.GradeGeneratorsRegular
import GaloisForLFunctions.HTGeometry.IntegralRegularLocalGrade
import GaloisForLFunctions.HTGeometry.RegularSequenceLocalization

/-!
# Miracle freeness for finite integral regular algebras

Let `A` be regular local and let `D` be a finite integral regular `A`-algebra satisfying going
down.  A regular system of parameters of `A` maps to a regular sequence in every maximal
localization of `D`: the extended parameter ideal is maximal-primary, the dimensions agree, and
the localized ring is Cohen--Macaulay.  Ring-regularity is local at maximal ideals, so the mapped
sequence is regular on `D`; restriction of scalars then makes `D` free over `A`.

This is the finite integral form of miracle flatness needed by the critical-source chart.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing RingTheory.Sequence

universe u

/-- **A finite integral regular going-down algebra over a regular local ring is free.** -/
theorem free_of_finite_integral_regular_of_goingDown
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    [IsRegularLocalRing A] [IsRegularRing D] [Nontrivial D]
    [Module.Finite A D] [Algebra.IsIntegral A D] [Algebra.HasGoingDown A D] :
    Module.Free A D := by
  obtain ⟨rs, hlen, hspan, hrs⟩ := exists_isRingRegularSeq_maximalIdeal A
  have hregD : IsRingRegularSeq (rs.map (algebraMap A D)) := by
    apply isRingRegularSeq_of_localizationAtMaximal
    intro q hq
    let B := Localization.AtPrime q
    have hrad :
        (Ideal.map (algebraMap A B) (maximalIdeal A)).radical =
          maximalIdeal B :=
      radical_map_maximalIdeal_localizationAtMaximal_eq q
    have hgrade : HasGradeGE (maximalIdeal B) (ModuleCat.of B B)
        (maximalIdeal A).spanFinrank :=
      hasGradeGE_maximalIdeal_localizationAtMaximal q
    have hmem : ∀ r ∈ rs.map (algebraMap A B), r ∈ maximalIdeal B := by
      intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      rw [← hrad]
      exact Ideal.le_radical (Ideal.mem_map_of_mem _ (by
        rw [← hspan]
        exact Ideal.subset_span hs))
    have hspanRad : maximalIdeal B ≤
        (Ideal.ofList (rs.map (algebraMap A B)) ⊔
          Module.annihilator B B).radical := by
      rw [← hrad, ← hspan, Ideal.map_ofList]
      exact Ideal.radical_mono le_sup_left
    have hweak : IsWeaklyRegular B (rs.map (algebraMap A B)) :=
      isWeaklyRegular_of_hasGradeGE_of_maximalIdeal_le_radical_sup_annihilator
        (maximalIdeal A).spanFinrank (A := B) (rs := rs.map (algebraMap A B))
          (M := B) (by simpa using hlen) hmem hspanRad hgrade
    have hregular : IsRegular B (rs.map (algebraMap A B)) :=
      (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hweak
    have hdirect : IsRingRegularSeq (rs.map (algebraMap A B)) :=
      (isRingRegularSeq_iff_isRegular _).mpr hregular
    have heq :
        (rs.map (algebraMap A D)).map (algebraMap D B) =
          rs.map (algebraMap A B) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      exact (IsScalarTower.algebraMap_apply A D B x).symm
    rw [heq]
    exact hdirect
  have hweakD : IsWeaklyRegular D (rs.map (algebraMap A D)) :=
    (isRingRegularSeq_iff_isRegular _).mp hregD |>.toIsWeaklyRegular
  exact free_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
    (maximalIdeal A).spanFinrank hlen hspan
      ((isWeaklyRegular_map_algebraMap_iff (R := A) (S := D) (M := D) rs).mp hweakD)

end

end GaloisForLFunctions.HTGeometry
