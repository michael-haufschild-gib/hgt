import GaloisForLFunctions.AdelicKreinGeometry.Haar.SubgroupOrbits
import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicHecke
import GaloisForLFunctions.AdelicKreinGeometry.Haar.TranslationProjections

/-!
# Moving correlations for subgroup-indicator successors

Nested cyclic projections preserve the smaller moving space. Projecting one
column onto a translation that fixes the other bounds their squared pairing by
the reciprocal quotient order of the slope ratio.
-/

open Complex Module
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- Removing a nonnegative fixed component leaves each moving column with norm at most one. -/
theorem subgroup_successor_movingDilationColumn_pairing_le_one {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) :
    (kernelColumnPairing k (movingDilationColumn k hp b a)
      (movingDilationColumn k hp b a)).re ≤ 1 := by
  let v := kernelColumnPoint k (dilation a)
  have hv : kernelColumnPairing k v v = 1 := by
    rw [kernelColumnPairing_point_left hk]
    change k ((dilation a)⁻¹ * dilation a) = 1
    rw [inv_mul_cancel, hasSubgroupSuccessor_one hs]
  have hsplit := kernelColumnPairing_projection_decomposition hk (translation b)
    (kernel_translation_locally_periodic hp b) v v
  have he := congrArg Complex.re hsplit
  rw [hv, Complex.one_re, Complex.add_re] at he
  have hnonneg := subgroup_successor_projection_pairing_nonneg h1 hk hi hs hp b (dilation a)
  simp only [movingDilationColumn_eq_sub, translationFixedProjection]
  dsimp only [v, translationFixedProjection] at he hnonneg
  linarith only [he, hnonneg]

/-- A cyclic fixed projection bounds moving correlations by the reciprocal subgroup orbit order. -/
theorem normSq_movingDilationColumn_pairing_le_inv_subgroupOrder {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a c : ℚˣ)
    {n : ℕ} (hc : (c : ℚ) = (n : ℚ) * b) :
    normSq (kernelColumnPairing k (movingDilationColumn k hp b a)
      (movingDilationColumn k hp b c)) ≤
      (rationalSubgroupOrder H ((c : ℚ) / (a : ℚ)) : ℝ)⁻¹ := by
  let P := translationFixedProjection k hp b
  let Q := translationFixedProjection k hp (c : ℚ)
  let v := kernelColumnPoint k (dilation a)
  let u := movingDilationColumn k hp b a
  let w := movingDilationColumn k hp b c
  let W := LinearMap.range (kernelColumnRepresentation k (translation b) + (-1 : ℂ) • 1)
  have hcomm : Commute P Q := locallyPeriodicProjection_commute_pair
    (kernelColumnRepresentation k (translation b)) (kernelColumnRepresentation k (translation (c : ℚ)))
    (kernel_translation_locally_periodic hp b) (kernel_translation_locally_periodic hp (c : ℚ))
    (kernelColumnRepresentation_translation_commute k b (c : ℚ))
  have hQP : Q (P v) = P v := by
    apply locallyPeriodicProjection_apply_of_fixed
    change kernelColumnRepresentation k (translation (c : ℚ)) (P v) = P v
    rw [hc]
    exact translationFixedProjection_fixed_nat_multiple k hp b n v
  have hPQ : P (Q v) = P v := by
    have h := LinearMap.congr_fun hcomm.eq v
    simpa only [Module.End.mul_apply, hQP] using h
  have huP : P u = 0 := (locallyPeriodicProjection_apply_eq_zero_iff _
    (kernel_translation_locally_periodic hp b) u).mpr (movingDilationColumn_mem_range k hp b a)
  have hQumem : Q u ∈ W := by
    apply (locallyPeriodicProjection_apply_eq_zero_iff _
      (kernel_translation_locally_periodic hp b) (Q u)).mp
    change P (Q u) = 0
    have h := LinearMap.congr_fun hcomm.eq u
    simpa only [Module.End.mul_apply, huP, map_zero] using h
  have hwmem : w ∈ W := movingDilationColumn_mem_range k hp b c
  have hW : ∀ x ∈ W, 0 ≤ (kernelColumnPairing k x x).re :=
    fun x hx => translation_moving_subspace_nonnegative hk hi hp b x hx
  have hQu : Q u = Q v - P v := by
    change Q (movingDilationColumn k hp b a) = _
    rw [movingDilationColumn_eq_sub, map_sub, hQP]
  have hQnorm : (kernelColumnPairing k (Q u) (Q u)).re ≤
      (rationalSubgroupOrder H ((c : ℚ) / (a : ℚ)) : ℝ)⁻¹ := by
    have hsplit := kernelColumnPairing_projection_decomposition hk (translation b)
      (kernel_translation_locally_periodic hp b) (Q v) (Q v)
    change kernelColumnPairing k (Q v) (Q v) =
      kernelColumnPairing k (P (Q v)) (P (Q v)) +
        kernelColumnPairing k (Q v - P (Q v)) (Q v - P (Q v)) at hsplit
    rw [hPQ, ← hQu] at hsplit
    have he := congrArg Complex.re hsplit
    rw [Complex.add_re] at he
    have hfixed : (kernelColumnPairing k (Q v) (Q v)).re =
        (rationalSubgroupOrder H ((c : ℚ) / (a : ℚ)) : ℝ)⁻¹ := by
      simpa only [affSlope_dilation] using
        subgroup_successor_projection_pairing_re h1 hk hi hs hp (c : ℚ) (dilation a)
    rw [hfixed] at he
    have hnonneg := subgroup_successor_projection_pairing_nonneg h1 hk hi hs hp b (dilation a)
    linarith only [he, hnonneg]
  have hQw : Q w = w := locallyPeriodicProjection_apply_of_fixed _
    (kernel_translation_locally_periodic hp (c : ℚ)) (movingDilationColumn_fixed k hp b c hc)
  have hpair : kernelColumnPairing k (Q u) w = kernelColumnPairing k u w := by
    have h := kernelColumnPairing_projection_selfadjoint hk (translation (c : ℚ))
      (kernel_translation_locally_periodic hp (c : ℚ)) u w
    change kernelColumnPairing k (Q u) w = kernelColumnPairing k u (Q w) at h
    rwa [hQw] at h
  have hCS := kernelColumnPairing_normSq_le_on_subspace hk W hW (Q u) w hQumem hwmem
  rw [hpair] at hCS
  have hwbound := subgroup_successor_movingDilationColumn_pairing_le_one h1 hk hi hs hp b c
  have hprod : (kernelColumnPairing k (Q u) (Q u)).re * (kernelColumnPairing k w w).re ≤
      (kernelColumnPairing k (Q u) (Q u)).re := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hwbound (hW (Q u) hQumem)
  exact hCS.trans (hprod.trans hQnorm)

#print axioms subgroup_successor_movingDilationColumn_pairing_le_one
#print axioms normSq_movingDilationColumn_pairing_le_inv_subgroupOrder
end GaloisForLFunctions.AdelicKreinGeometry
