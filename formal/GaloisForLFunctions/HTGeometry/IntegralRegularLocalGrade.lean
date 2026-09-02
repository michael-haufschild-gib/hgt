import GaloisForLFunctions.HTGeometry.CohenMacaulayPrimaryGrade
import GaloisForLFunctions.HTGeometry.IntegralLocalKrullDim
import GaloisForLFunctions.HTGeometry.RegularLocalDomain
import GaloisForLFunctions.HTGeometry.ReesDepth

/-!
# Full local grade in an integral regular extension

Let `A` be regular local and let `D` be a regular integral `A`-algebra satisfying going down.
At every maximal ideal `q` of `D`, the extension of the maximal ideal of `A` to `D_q` has
radical the maximal ideal of `D_q`.  The two rings have the same dimension, and regularity makes
`D_q` Cohen--Macaulay.  Rees's radical-invariance theorem therefore gives this extended ideal
the full grade of `A`.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing
open scoped Pointwise

universe u v

/-- **The extended base maximal ideal has full grade at every maximal localization of a regular
integral going-down algebra.** -/
theorem hasGradeGE_map_maximalIdeal_localizationAtMaximal
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.IsIntegral A D] [Algebra.HasGoingDown A D]
    [IsRegularLocalRing A] [IsRegularRing D]
    (q : Ideal D) [q.IsMaximal] :
    HasGradeGE
      (Ideal.map (algebraMap A (Localization.AtPrime q)) (maximalIdeal A))
      (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))
      (maximalIdeal A).spanFinrank := by
  let B := Localization.AtPrime q
  let I : Ideal B := Ideal.map (algebraMap A B) (maximalIdeal A)
  have hrad : I.radical = maximalIdeal B :=
    radical_map_maximalIdeal_localizationAtMaximal_eq q
  have hIne : I ≠ ⊤ := by
    intro htop
    have : I.radical = ⊤ := by rw [htop, Ideal.radical_top]
    rw [hrad] at this
    exact Ideal.IsMaximal.ne_top (by infer_instance : (maximalIdeal B).IsMaximal) this
  have hIlt : I • (⊤ : Submodule B B) < ⊤ :=
    smul_top_lt_top_of_ne_top hIne
  have hdimA : ringKrullDim A =
      ((((maximalIdeal A).spanFinrank : ℕ∞)) : WithBot ℕ∞) := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  have hdimB : ringKrullDim B =
      ((((maximalIdeal A).spanFinrank : ℕ∞)) : WithBot ℕ∞) := by
    rw [ringKrullDim_localizationAtMaximal_eq_of_isIntegral_of_hasGoingDown
        (A := A) (D := D) q,
      hdimA]
  exact hasGradeGE_of_isCohenMacaulay_of_radical_eq_maximalIdeal
    I (maximalIdeal A).spanFinrank hIlt hrad
    (isCohenMacaulayRing_of_isRegularLocalRing B) hdimB

/-- **Every maximal localization of a regular integral going-down algebra has maximal-ideal grade
equal to the dimension of the regular local base.** -/
theorem hasGradeGE_maximalIdeal_localizationAtMaximal
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.IsIntegral A D] [Algebra.HasGoingDown A D]
    [IsRegularLocalRing A] [IsRegularRing D]
    (q : Ideal D) [q.IsMaximal] :
    HasGradeGE
      (maximalIdeal (Localization.AtPrime q))
      (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))
      (maximalIdeal A).spanFinrank := by
  let B := Localization.AtPrime q
  have hdimA : ringKrullDim A =
      ((((maximalIdeal A).spanFinrank : ℕ∞)) : WithBot ℕ∞) := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  have hdimB : ringKrullDim B =
      ((((maximalIdeal A).spanFinrank : ℕ∞)) : WithBot ℕ∞) := by
    rw [ringKrullDim_localizationAtMaximal_eq_of_isIntegral_of_hasGoingDown
        (A := A) (D := D) q,
      hdimA]
  exact hasGradeGE_of_isCohenMacaulay_of_radical_eq_maximalIdeal
    (maximalIdeal B) (maximalIdeal A).spanFinrank
    (maximalIdeal_smul_top_lt_top B)
    (by exact (by infer_instance : (maximalIdeal B).IsPrime).radical)
    (isCohenMacaulayRing_of_isRegularLocalRing B) hdimB

end GaloisForLFunctions.HTGeometry
