import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLocalFields

/-!
# Constant residues in the completed infinity field

Density first approximates a completed integer by an integer in the actual
function field. Leading-term cancellation there supplies a constant with the
same residue. This gives the explicit residue step used in pole reduction.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

open scoped WithZero WithZeroMulInt

noncomputable section

theorem infinityEmbedding_dense : DenseRange infinityEmbedding :=
  UniformSpace.Completion.denseRange_coe.comp
    (WithVal.equiv infinityValuation).symm.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- Every completed integer has the residue of an actual constant of the curve. -/
theorem completedInfinity_sub_constant (z : InfinityCompletion) (hz : Valued.v z ≤ 1) :
    ∃ c : Constants, Valued.v (z - infinityEmbedding (algebraMap Constants K c)) < 1 := by
  have hball : IsOpen {w : InfinityCompletion | Valued.v.restrict w < 1} :=
    Valued.isOpen_ball InfinityCompletion 1
  have hopen : IsOpen {w : InfinityCompletion | Valued.v.restrict (w - z) < 1} :=
    hball.preimage (continuous_id.sub continuous_const)
  obtain ⟨a, ha⟩ := infinityEmbedding_dense.mem_nhds
    (hopen.mem_nhds (show Valued.v.restrict (z - z) < 1 by simp))
  have hadiff : Valued.v (infinityEmbedding a - z) < 1 :=
    (Valued.v : Valuation InfinityCompletion ℤᵐ⁰).restrict_lt_one_iff.mp ha
  have hav : Valued.v (infinityEmbedding a) ≤ 1 := by
    calc
      Valued.v (infinityEmbedding a) = Valued.v (z + (infinityEmbedding a - z)) := by
        congr 1
        abel
      _ ≤ max (Valued.v z) (Valued.v (infinityEmbedding a - z)) := Valued.v.map_add _ _
      _ ≤ 1 := max_le hz hadiff.le
  rw [infinityEmbedding_valuation] at hav
  obtain ⟨c, hc⟩ := infinity_regular_sub_constant (⟨a, hav⟩ : InfinityRing)
  refine ⟨c, ?_⟩
  have hfirst : Valued.v (z - infinityEmbedding a) < 1 := by
    rw [Valuation.map_sub_swap]
    exact hadiff
  have hsecond : Valued.v (infinityEmbedding a - infinityEmbedding (algebraMap Constants K c)) < 1 := by
    rw [← map_sub, infinityEmbedding_valuation]
    exact hc
  calc
    Valued.v (z - infinityEmbedding (algebraMap Constants K c)) =
        Valued.v ((z - infinityEmbedding a) +
          (infinityEmbedding a - infinityEmbedding (algebraMap Constants K c))) := by
      congr 1
      abel
    _ ≤ max (Valued.v (z - infinityEmbedding a))
        (Valued.v (infinityEmbedding a - infinityEmbedding (algebraMap Constants K c))) :=
      Valued.v.map_add _ _
    _ < 1 := max_lt hfirst hsecond

/-- Nonzero constants have value one at the actual infinity place. -/
theorem infinityValuation_constant (c : Constants) (hc : c ≠ 0) :
    infinityValuation (algebraMap Constants K c) = 1 := by
  exact Valuation.Integers.one_of_isUnit' (v := infinityValuation)
    (isUnit_iff_ne_zero.mpr hc) (fun a => (infinityConstants a).property)

theorem completedInfinity_constant_valuation (c : Constants) (hc : c ≠ 0) :
    Valued.v (infinityEmbedding (algebraMap Constants K c)) = 1 := by
  rw [infinityEmbedding_valuation, infinityValuation_constant c hc]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
