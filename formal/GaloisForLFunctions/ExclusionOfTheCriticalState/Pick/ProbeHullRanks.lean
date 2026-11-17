import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeReflectionHull
import GaloisForLFunctions.HilbertMetric.NegativeHeightGrams

/-!
# Gram ranks reconstruct the finite reflection representation

The ranges of the two character averages on the reflection hull are exactly
the spans of the corresponding projected probes. Their dimensions therefore
match the positive and negative sector Gram ranks. This reconstructs both the
minimal invariant-space dimension and its reflection character directly from
finite probe matrices, including redundant probe families.

Equality between the sector-rank sum and the ordinary Gram rank is equivalent
to reflection invariance of the original probe span. These formulas refine the
order-two character average from Aoki, *Distribution of Primes in Galois
Extensions of Global Fields with Explicit Constant Terms*, Lemma 3.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk

private def positiveMap : Module.End ℂ ZeroSpace :=
  (1 / 2 : ℂ) • (1 + zeroReflection.toLinearMap)
private def negativeMap : Module.End ℂ ZeroSpace :=
  (1 / 2 : ℂ) • (1 - zeroReflection.toLinearMap)

private theorem positiveMap_reflection :
    positiveMap.comp zeroReflection.toLinearMap = positiveMap := by
  apply LinearMap.ext
  intro x
  change (1 / 2 : ℂ) • (zeroReflection x + zeroReflection (zeroReflection x)) =
    (1 / 2 : ℂ) • (x + zeroReflection x)
  rw [zeroReflection_involutive, add_comm]

private theorem negativeMap_reflection :
    negativeMap.comp zeroReflection.toLinearMap = -negativeMap := by
  apply LinearMap.ext
  intro x
  change (1 / 2 : ℂ) • (zeroReflection x - zeroReflection (zeroReflection x)) =
    -((1 / 2 : ℂ) • (x - zeroReflection x))
  rw [zeroReflection_involutive]
  module

variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

private theorem positive_range_image :
    (LinearMap.range (hullPositive p)).map (reflectionHull p).subtype =
      (probeSpace p).map positiveMap := by
  rw [← LinearMap.range_comp]
  have he : (reflectionHull p).subtype.comp (hullPositive p) =
      positiveMap.comp (reflectionHull p).subtype := by
    apply LinearMap.ext
    intro x
    rfl
  rw [he, LinearMap.range_comp, Submodule.range_subtype, reflectionHull,
    Submodule.map_sup, ← Submodule.map_comp, positiveMap_reflection, sup_idem]

private theorem negative_range_image :
    (LinearMap.range (hullNegative p)).map (reflectionHull p).subtype =
      (probeSpace p).map negativeMap := by
  rw [← LinearMap.range_comp]
  have he : (reflectionHull p).subtype.comp (hullNegative p) =
      negativeMap.comp (reflectionHull p).subtype := by
    apply LinearMap.ext
    intro x
    rfl
  rw [he, LinearMap.range_comp, Submodule.range_subtype, reflectionHull,
    Submodule.map_sup, ← Submodule.map_comp, negativeMap_reflection, Submodule.map_neg, sup_idem]

private theorem rank_neg (A : Matrix (Fin N) (Fin N) ℂ) : (-A).rank = A.rank := by
  have h : (-A).mulVecLin = -A.mulVecLin := by
    apply LinearMap.ext
    intro x
    exact Matrix.neg_mulVec x A
  change Module.finrank ℂ ((-A).mulVecLin.range) = Module.finrank ℂ (A.mulVecLin.range)
  rw [h, LinearMap.range_neg]

private theorem reverseGram_rank (v : Fin N → ZeroSpace) :
    Matrix.rank (fun i j => inner ℂ (v j) (v i)) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) := by
  have h : (fun i j => inner ℂ (v j) (v i)) = -(HilbertMetric.negativeHeightGram v).transpose := by
    ext i j
    simp [HilbertMetric.negativeHeightGram, Matrix.gram]
  rw [h, rank_neg, Matrix.rank_transpose]
  exact HilbertMetric.negativeHeightGram_rank v

/-- Positive Gram rank counts the actual fixed-sector dimension in the reflection hull. -/
theorem positiveProbeGram_rank_hull :
    (positiveProbeGram p).rank = Module.finrank ℂ (LinearMap.range (hullPositive p)) := by
  change Matrix.rank (fun i j => inner ℂ (positivePart (probeVec (p j).property))
    (positivePart (probeVec (p i).property))) = _
  rw [reverseGram_rank,
    ← Submodule.finrank_map_subtype_eq (reflectionHull p) (LinearMap.range (hullPositive p)),
    positive_range_image, probeSpace, Submodule.map_span, ← Set.range_comp]
  rfl

/-- Negative Gram rank counts the actual odd-sector dimension in the reflection hull. -/
theorem negativeProbeGram_rank_hull :
    (negativeProbeGram p).rank = Module.finrank ℂ (LinearMap.range (hullNegative p)) := by
  change Matrix.rank (fun i j => inner ℂ (negativePart (probeVec (p j).property))
    (negativePart (probeVec (p i).property))) = _
  rw [reverseGram_rank,
    ← Submodule.finrank_map_subtype_eq (reflectionHull p) (LinearMap.range (hullNegative p)),
    negative_range_image, probeSpace, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The minimal reflection-stable extension has dimension determined by two observable Gram ranks. -/
theorem reflectionHull_finrank_eq_sector_ranks :
    Module.finrank ℂ (reflectionHull p) = (positiveProbeGram p).rank + (negativeProbeGram p).rank := by
  have h : (Module.finrank ℂ (reflectionHull p) : ℂ) =
      ((positiveProbeGram p).rank : ℂ) + ((negativeProbeGram p).rank : ℂ) := by
    rw [positiveProbeGram_rank_hull, negativeProbeGram_rank_hull,
      hullPositive_dimension, hullNegative_dimension]
    ring
  exact_mod_cast h

/-- The character of the zero reflection is recovered from the signed Gram-rank difference. -/
theorem hullReflection_trace_eq_sector_ranks :
    LinearMap.trace ℂ (reflectionHull p) (hullReflection p) =
      ((positiveProbeGram p).rank : ℂ) - ((negativeProbeGram p).rank : ℂ) := by
  rw [positiveProbeGram_rank_hull, negativeProbeGram_rank_hull, hullReflection_trace]

/-- Ordinary Gram rank counts the original probe span. -/
theorem hilbertProbeGram_rank_space :
    (hilbertProbeGram p).rank = Module.finrank ℂ (probeSpace p) :=
  reverseGram_rank _

/-- Rank equality detects reflection invariance of a possibly redundant probe family. -/
theorem sector_rank_sum_eq_iff_reflection_invariant :
    (positiveProbeGram p).rank + (negativeProbeGram p).rank = (hilbertProbeGram p).rank ↔
      (probeSpace p).map zeroReflection.toLinearMap ≤ probeSpace p := by
  rw [← reflectionHull_finrank_eq_sector_ranks, hilbertProbeGram_rank_space]
  constructor
  · intro h
    have he := Submodule.eq_of_le_of_finrank_eq (probeSpace_le_reflectionHull p) h.symm
    have hr : (probeSpace p).map zeroReflection.toLinearMap ≤ reflectionHull p := le_sup_right
    rwa [← he] at hr
  · intro h
    have he : reflectionHull p = probeSpace p := sup_eq_left.mpr h
    rw [he]

#print axioms hilbertProbeGram_rank_space
#print axioms sector_rank_sum_eq_iff_reflection_invariant
#print axioms positiveProbeGram_rank_hull
#print axioms negativeProbeGram_rank_hull
#print axioms reflectionHull_finrank_eq_sector_ranks
#print axioms hullReflection_trace_eq_sector_ranks
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
