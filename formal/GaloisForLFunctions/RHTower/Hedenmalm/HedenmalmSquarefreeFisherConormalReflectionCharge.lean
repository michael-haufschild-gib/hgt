import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnSquarefreeFisherConormalResidue
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSoninWeylDefectQuantizationWall

/-!
# Squarefree Fisher conormal reflection charge

The continuous Hedenmalm--Sonin Weyl defect cannot retain integer divisor charge near the critical
wall.  This module realizes the positive survivor: a fixed affine squarefree source chart carries
the complete strict-right `xi` divisor order, while its Fisher conormal quotient has residue twice
that source order.  Squared source orders reproduce the canonical reflection self-intersection
charge coefficient-for-coefficient on every finite strip window.

This crosses the quantization wall without dividing a continuous defect by horizontal distance.
It does not bound the resulting charge and therefore does not prove RH.
-/

open Complex Set Metric Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Complete divisor multiplicity carried by the fixed squarefree source chart
`(sigma, epsilon, u) = (2, 1, rho - 2)`. -/
def hedenmalmSquarefreeConormalMultiplicity (rho : ℂ) : ℕ :=
  (analyticOrderAt
    (GaloisForLFunctions.squarefreeBoundaryOverlap 2 1) (rho - 2)).toNat

/-- In the strict-right open strip, fixed-chart squarefree source multiplicity is exactly Xi
multiplicity. -/
theorem hedenmalmSquarefreeConormalMultiplicity_eq_xi
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1) :
    hedenmalmSquarefreeConormalMultiplicity rho =
      (analyticOrderAt xi rho).toNat := by
  unfold hedenmalmSquarefreeConormalMultiplicity
  congr 1
  exact analyticOrderAt_squarefreeBoundaryOverlap_eq_xi_of_strictRightStrip
    (sigma := 2) (epsilon := 1) (u := rho - 2) (rho := rho)
    (by norm_num) (by norm_num) (by ring) hhalf hone

/-- Strict-right finite-window zero support defined entirely by the squarefree partition. -/
def hedenmalmSquarefreeRightSourceZeros (T : ℝ) : Set ℂ :=
  {rho | 1 / 2 < rho.re ∧ rho.re < 1 ∧ 0 ≤ rho.im ∧ rho.im < T ∧
    GaloisForLFunctions.squarefreePartition rho = 0}

/-- Squarefree source support is exactly strict-right Xi support. -/
theorem hedenmalmSquarefreeRightSourceZeros_eq (T : ℝ) :
    hedenmalmSquarefreeRightSourceZeros T =
      {rho | rho ∈ stripZeros T ∧ 1 / 2 < rho.re} := by
  ext rho
  constructor
  · intro h
    change 1 / 2 < rho.re ∧ rho.re < 1 ∧ 0 ≤ rho.im ∧ rho.im < T ∧
      GaloisForLFunctions.squarefreePartition rho = 0 at h
    rcases h with ⟨hhalf, hone, him0, himT, hsq⟩
    have hzero :=
      (squarefreePartition_eq_zero_iff_xi_eq_zero_of_strictRightStrip hhalf hone).mp hsq
    exact ⟨⟨⟨by linarith, hone, him0, himT⟩, hzero⟩, hhalf⟩
  · intro h
    rcases h with ⟨hstrip, hhalf⟩
    change 1 / 2 < rho.re ∧ rho.re < 1 ∧ 0 ≤ rho.im ∧ rho.im < T ∧
      GaloisForLFunctions.squarefreePartition rho = 0
    exact ⟨hhalf, hstrip.1.2.1, hstrip.1.2.2.1, hstrip.1.2.2.2,
      (squarefreePartition_eq_zero_iff_xi_eq_zero_of_strictRightStrip
        hhalf hstrip.1.2.1).mpr hstrip.2⟩

/-- Squarefree right source support is finite in every bounded-height window. -/
theorem hedenmalmSquarefreeRightSourceZeros_finite (T : ℝ) :
    (hedenmalmSquarefreeRightSourceZeros T).Finite := by
  rw [hedenmalmSquarefreeRightSourceZeros_eq]
  exact (stripZeros_finite T).subset (fun _ h => h.1)

/-- Source-intrinsic reflection charge: twice squared squarefree conormal multiplicity over the
squarefree source zero support. Neither support nor multiplicity is defined using `xi`. -/
def hedenmalmSquarefreeFisherReflectionCharge (T : ℝ) : ℕ :=
  2 * ∑ rho ∈ (hedenmalmSquarefreeRightSourceZeros_finite T).toFinset,
    (hedenmalmSquarefreeConormalMultiplicity rho) ^ (2 : ℕ)

/-- Fixed-chart squarefree Fisher quotient has residue twice source conormal multiplicity at every
strict-right Xi zero. -/
theorem tendsto_hedenmalmSquarefreeFisherQuotient_residue_eq_two_mul_sourceMultiplicity
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ k : ℕ, hedenmalmSquarefreeConormalMultiplicity rho = k + 1 ∧
      Tendsto
        (fun v => (v - (rho - 2)) *
          (GaloisForLFunctions.squarefreeFisherScore 2 1 v /
            GaloisForLFunctions.squarefreeBoundaryOverlap 2 1 v))
        (nhdsWithin (rho - 2) ({rho - 2} : Set ℂ)ᶜ)
        (nhds (2 * (hedenmalmSquarefreeConormalMultiplicity rho : ℂ))) := by
  obtain ⟨k, horder, hlim⟩ :=
    tendsto_squarefreeFisherScore_div_overlap_residue_at_strictRightXiZero
      (sigma := 2) (epsilon := 1) (u := rho - 2) (rho := rho)
      (by norm_num) (by norm_num) (by ring) hhalf hone hzero
  have hmult : hedenmalmSquarefreeConormalMultiplicity rho = k + 1 := by
    rw [hedenmalmSquarefreeConormalMultiplicity_eq_xi hhalf hone, horder]
    simp
  refine ⟨k, hmult, ?_⟩
  simpa [hmult] using hlim

/-- Squarefree Fisher source charge is coefficient-exact canonical reflection self-intersection
charge. -/
theorem hedenmalmSquarefreeFisherReflectionCharge_eq (T : ℝ) :
    hedenmalmSquarefreeFisherReflectionCharge T =
      xiReflectionSelfIntersectionCharge T := by
  have hsupport :
      (hedenmalmSquarefreeRightSourceZeros_finite T).toFinset =
        (stripZeros_finite T).toFinset.filter (fun rho => 1 / 2 < rho.re) := by
    ext rho
    rw [Set.Finite.mem_toFinset, Finset.mem_filter, Set.Finite.mem_toFinset,
      hedenmalmSquarefreeRightSourceZeros_eq]
    rfl
  rw [hedenmalmSquarefreeFisherReflectionCharge, hsupport,
    xiReflectionSelfIntersectionCharge, xiStripWindowRightSquareOrder]
  congr 1
  apply Finset.sum_congr rfl
  intro rho hrho
  have hdata := Finset.mem_filter.mp hrho
  have hstrip : rho ∈ stripZeros T := by
    rw [Set.Finite.mem_toFinset] at hdata
    exact hdata.1
  rw [hedenmalmSquarefreeConormalMultiplicity_eq_xi hdata.2 hstrip.1.2.1]

end

end RHTower
