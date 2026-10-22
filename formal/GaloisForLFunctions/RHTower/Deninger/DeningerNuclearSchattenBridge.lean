import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearOperator
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten

/-!
# Nuclear operators on a Hilbert space are trace class

A rank-one map has rank at most one in the approximation-number sense, and a nuclear operator is
the operator-norm sum of such maps with absolutely summable norms.  On a Hilbert space that is
exactly the hypothesis of the absolute nuclear-series criterion, so every nuclear operator lies in
the Schatten 1-class.

This identifies the general normed-space notion of nuclearity with the Hilbert-space trace class
on the intersection of their domains, so the trace norm, the ideal bounds and the additivity of
the Schatten 1-class all apply to nuclear operators.

* `deningerSmulRight_hasRankLE_one` : a rank-one map has rank at most one.
* `DeningerIsNuclear.memSchattenClass_one` : a nuclear operator is trace class.
-/

namespace RHTower

section Bridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A rank-one map has rank at most one**: its image lies in the line spanned by its vector. -/
theorem deningerSmulRight_hasRankLE_one (φ : H →L[ℂ] ℂ) (y : H) :
    HasRankLE ((φ.smulRight y : H →L[ℂ] H)) 1 := by
  classical
  refine ⟨Submodule.span ℂ ({y} : Set H), ?_, ?_, ?_⟩
  · exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton y)
  · have h := finrank_span_le_card (R := ℂ) ({y} : Set H)
    simpa using h
  · intro x
    rw [ContinuousLinearMap.smulRight_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)

/-- **A nuclear operator on a Hilbert space is trace class.** -/
theorem DeningerIsNuclear.memSchattenClass_one {T : H →L[ℂ] H} (hT : DeningerIsNuclear T) :
    MemSchattenClass 1 T := by
  obtain ⟨ι, φ, y, hsum, hS⟩ := hT.hasSum_smulRight
  have hnorm : Summable fun i => ‖(φ i).smulRight (y i)‖ := by
    have heq : (fun i => ‖(φ i).smulRight (y i)‖) = fun i => ‖φ i‖ * ‖y i‖ := by
      funext i
      exact ContinuousLinearMap.norm_smulRight_apply (φ i) (y i)
    rw [heq]
    exact hsum
  have hmem := memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    (fun i => (φ i).smulRight (y i)) (fun i => deningerSmulRight_hasRankLE_one (φ i) (y i)) hnorm
  rwa [hS.tsum_eq] at hmem

end Bridge

end RHTower

