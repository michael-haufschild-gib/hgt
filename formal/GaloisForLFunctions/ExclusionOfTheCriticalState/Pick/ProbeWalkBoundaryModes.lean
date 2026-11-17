import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeHullRanks

/-!
# Endpoint modes of the active probe walk

Inside the reflection hull, stationary and alternating walk vectors are exactly
the positive and negative reflection sectors already lying in the probe span.
No reflection eigenvector in that hull can be orthogonal to every probe.

Rank-nullity for the two character averages gives exact endpoint multiplicities
from the ordinary and sector Gram ranks. This uses the order-two averaging
mechanism of Aoki, arXiv:2611.20592, Lemma 3.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

/-- A reflection eigenvector in the active hull cannot be invisible to every probe. -/
theorem hull_eigen_eq_zero_of_orthogonal {x : ZeroSpace} (hx : x ∈ reflectionHull p)
    (ho : x ∈ (probeSpace p)ᗮ) {c : ℂ} (hc : zeroReflection x = c • x) : x = 0 := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  have hinner : inner ℂ (u + zeroReflection w) x = 0 := by
    rw [inner_add_left, zeroReflection_inner_left, hc, inner_smul_right,
      (Submodule.mem_orthogonal _ _).mp ho u hu,
      (Submodule.mem_orthogonal _ _).mp ho w hw, mul_zero, add_zero]
  change u + zeroReflection w = x at huv
  rw [huv] at hinner
  exact inner_self_eq_zero.mp hinner

/-- Stationary vectors of the active walk are exactly the reflection-positive vectors in the original probe span. -/
theorem walk_fixed_iff_of_mem_hull {x : ZeroSpace} (hx : x ∈ reflectionHull p) :
    walk p x = x ↔ x ∈ probeSpace p ∧ zeroReflection x = x := by
  constructor
  · intro hw
    have hr : zeroReflection x = probeProjection p x + probeProjection p x - x := by
      have h := congrArg zeroReflection hw
      change zeroReflection (zeroReflection (probeProjection p x + probeProjection p x - x)) =
        zeroReflection x at h
      rw [zeroReflection_involutive] at h
      exact h.symm
    have hq : probeProjection p x = positivePart x := by
      rw [positivePart, hr]
      module
    have hy : zeroReflection (x - probeProjection p x) = -(x - probeProjection p x) := by
      rw [map_sub, hq, zeroReflection_positivePart, ← hq, hr]
      abel
    have hqh : probeProjection p x ∈ reflectionHull p :=
      probeSpace_le_reflectionHull p ((probeSpace p).starProjection_apply_mem x)
    have hz := hull_eigen_eq_zero_of_orthogonal p ((reflectionHull p).sub_mem hx hqh)
      ((probeSpace p).sub_starProjection_mem_orthogonal x) (c := -1)
      (by simpa only [neg_one_smul] using hy)
    have he : x = probeProjection p x := sub_eq_zero.mp hz
    refine ⟨?_, ?_⟩
    · rw [he]
      exact (probeSpace p).starProjection_apply_mem x
    · rw [hr, ← he]
      abel
  · rintro ⟨hxU, hxR⟩
    have hq : probeProjection p x = x := Submodule.starProjection_eq_self_iff.mpr hxU
    change zeroReflection (probeProjection p x + probeProjection p x - x) = x
    rw [hq, add_sub_cancel_left, hxR]

/-- Alternating vectors of the active walk are exactly the reflection-negative vectors in the original probe span. -/
theorem walk_neg_fixed_iff_of_mem_hull {x : ZeroSpace} (hx : x ∈ reflectionHull p) :
    walk p x = -x ↔ x ∈ probeSpace p ∧ zeroReflection x = -x := by
  constructor
  · intro hw
    have hr : zeroReflection x = x - (probeProjection p x + probeProjection p x) := by
      have h := congrArg zeroReflection hw
      change zeroReflection (zeroReflection (probeProjection p x + probeProjection p x - x)) =
        zeroReflection (-x) at h
      rw [zeroReflection_involutive, map_neg] at h
      calc
        zeroReflection x = -(probeProjection p x + probeProjection p x - x) := by
          rw [h, neg_neg]
        _ = x - (probeProjection p x + probeProjection p x) := neg_sub _ _
    have hq : probeProjection p x = negativePart x := by
      rw [negativePart, hr]
      module
    have hy : zeroReflection (x - probeProjection p x) = x - probeProjection p x := by
      rw [map_sub, hq, zeroReflection_negativePart, ← hq, hr]
      abel
    have hqh : probeProjection p x ∈ reflectionHull p :=
      probeSpace_le_reflectionHull p ((probeSpace p).starProjection_apply_mem x)
    have hz := hull_eigen_eq_zero_of_orthogonal p ((reflectionHull p).sub_mem hx hqh)
      ((probeSpace p).sub_starProjection_mem_orthogonal x) (c := 1)
      (by simpa only [one_smul] using hy)
    have he : x = probeProjection p x := sub_eq_zero.mp hz
    refine ⟨?_, ?_⟩
    · rw [he]
      exact (probeSpace p).starProjection_apply_mem x
    · rw [hr, ← he]
      abel
  · rintro ⟨hxU, hxR⟩
    have hq : probeProjection p x = x := Submodule.starProjection_eq_self_iff.mpr hxU
    change zeroReflection (probeProjection p x + probeProjection p x - x) = -x
    rw [hq, add_sub_cancel_left, hxR]

/-- Restriction of the negative character average to the original probe span. -/
def negativeFromProbe : (probeSpace p) →ₗ[ℂ] (reflectionHull p) :=
  (hullNegative p).comp (Submodule.inclusion (probeSpace_le_reflectionHull p))

/-- Restriction of the positive character average to the original probe span. -/
def positiveFromProbe : (probeSpace p) →ₗ[ℂ] (reflectionHull p) :=
  (hullPositive p).comp (Submodule.inclusion (probeSpace_le_reflectionHull p))

/-- Original probes generate the entire negative hull sector after averaging. -/
theorem range_negativeFromProbe :
    LinearMap.range (negativeFromProbe p) = LinearMap.range (hullNegative p) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨Submodule.inclusion (probeSpace_le_reflectionHull p) x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp x.property
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨⟨u - w, (probeSpace p).sub_mem hu hw⟩, ?_⟩
    apply Subtype.ext
    change (1 / 2 : ℂ) • ((u - w) - zeroReflection (u - w)) =
      (1 / 2 : ℂ) • ((x : ZeroSpace) - zeroReflection x)
    change u + zeroReflection w = (x : ZeroSpace) at huv
    rw [← huv, map_sub, map_add, zeroReflection_involutive]
    module

/-- Original probes generate the entire positive hull sector after averaging. -/
theorem range_positiveFromProbe :
    LinearMap.range (positiveFromProbe p) = LinearMap.range (hullPositive p) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨Submodule.inclusion (probeSpace_le_reflectionHull p) x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp x.property
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨⟨u + w, (probeSpace p).add_mem hu hw⟩, ?_⟩
    apply Subtype.ext
    change (1 / 2 : ℂ) • ((u + w) + zeroReflection (u + w)) =
      (1 / 2 : ℂ) • ((x : ZeroSpace) + zeroReflection x)
    change u + zeroReflection w = (x : ZeroSpace) at huv
    rw [← huv, map_add, map_add, zeroReflection_involutive]
    module

/-- The negative average detects exactly the stationary walk modes on the original probe span. -/
theorem mem_ker_negativeFromProbe_iff (x : probeSpace p) :
    x ∈ LinearMap.ker (negativeFromProbe p) ↔ walk p (x : ZeroSpace) = x := by
  rw [walk_fixed_iff_of_mem_hull p (probeSpace_le_reflectionHull p x.property)]
  simp only [x.property, true_and, LinearMap.mem_ker]
  have he : negativeFromProbe p x = 0 ↔ (1 / 2 : ℂ) •
      ((x : ZeroSpace) - zeroReflection x) = 0 := Subtype.ext_iff
  rw [he, smul_eq_zero, or_iff_right (by norm_num : (1 / 2 : ℂ) ≠ 0), sub_eq_zero, eq_comm]

/-- The positive average detects exactly the alternating walk modes on the original probe span. -/
theorem mem_ker_positiveFromProbe_iff (x : probeSpace p) :
    x ∈ LinearMap.ker (positiveFromProbe p) ↔ walk p (x : ZeroSpace) = -x := by
  rw [walk_neg_fixed_iff_of_mem_hull p (probeSpace_le_reflectionHull p x.property)]
  simp only [x.property, true_and, LinearMap.mem_ker]
  have he : positiveFromProbe p x = 0 ↔ (1 / 2 : ℂ) •
      ((x : ZeroSpace) + zeroReflection x) = 0 := Subtype.ext_iff
  rw [he, smul_eq_zero, or_iff_right (by norm_num : (1 / 2 : ℂ) ≠ 0)]
  constructor
  · intro h
    calc
      zeroReflection x = ((x : ZeroSpace) + zeroReflection x) - x := by abel
      _ = -x := by rw [h, zero_sub]
  · intro h
    rw [h, add_neg_cancel]

/-- Rank-nullity computes the stationary multiplicity from the negative Gram rank. -/
theorem stationary_dimension_add_negative_rank :
    Module.finrank ℂ (LinearMap.ker (negativeFromProbe p)) +
      (negativeProbeGram p).rank = (hilbertProbeGram p).rank := by
  rw [negativeProbeGram_rank_hull, ← range_negativeFromProbe, hilbertProbeGram_rank_space]
  exact (Nat.add_comm _ _).trans (LinearMap.finrank_range_add_finrank_ker (negativeFromProbe p))

/-- Rank-nullity computes the alternating multiplicity from the positive Gram rank. -/
theorem alternating_dimension_add_positive_rank :
    Module.finrank ℂ (LinearMap.ker (positiveFromProbe p)) +
      (positiveProbeGram p).rank = (hilbertProbeGram p).rank := by
  rw [positiveProbeGram_rank_hull, ← range_positiveFromProbe, hilbertProbeGram_rank_space]
  exact (Nat.add_comm _ _).trans (LinearMap.finrank_range_add_finrank_ker (positiveFromProbe p))

#print axioms stationary_dimension_add_negative_rank
#print axioms alternating_dimension_add_positive_rank

#print axioms hull_eigen_eq_zero_of_orthogonal
#print axioms walk_fixed_iff_of_mem_hull
#print axioms walk_neg_fixed_iff_of_mem_hull
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
