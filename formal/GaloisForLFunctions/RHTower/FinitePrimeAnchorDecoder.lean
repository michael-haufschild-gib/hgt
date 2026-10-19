import GaloisForLFunctions.BiScaleUncertainty.PrimeAnchorCompleteGraphError

/-!
# Finite observation decoding in the complete arithmetic graph

An arbitrary observation row is decoded by finite multiples inversion.
The error bound retains the exact zero-anchor defect, so neither realizability
of the observations nor a nonzero denominator is assumed.
-/

open Finset RHTower.Sieve RHTower.CHMDDoobGraph
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius

namespace RHTower.FinitePrimeAnchorDecoder
noncomputable section
set_option autoImplicit false

/-- Decode the finite multiples coordinates after division by the anchor. -/
def coefficients (N : ℕ) (a : ℝ) (z : ℕ → ℝ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff (fun q => z q / a) N

/-- Literal finite synthesis of the decoded row in the original source graph. -/
def graph (N k : ℕ) (a : ℝ) (z : ℕ → ℝ) : SourceGraph :=
  synthesis N k (coefficients N a z)

/-- Observation error relative to the arithmetic reference and its anchor. -/
def residual (N : ℕ) (a : ℝ) (c z : ℕ → ℝ) (q : ℕ) : ℝ :=
  z q - a * selbergMultiplesCoord N c q

/-- The singular-anchor loss and every weighted finite inversion cost. -/
def graphError (N k : ℕ) (a : ℝ) (c z : ℕ → ℝ) : ℝ :=
  |a / a - 1| * ‖synthesis N k c‖ +
    inversionCost N k (fun q => |residual N a c z q / a|)

/-- Error radius for the complete signed energy, including its mass term. -/
def energyError (N k : ℕ) (a : ℝ) (c z : ℕ → ℝ) : ℝ :=
  graphError N k a c z ^ 2 + 2 * graphError N k a c z * ‖synthesis N k c‖

theorem coordinates_coefficients (N q : ℕ) (a : ℝ) (z : ℕ → ℝ) :
    selbergMultiplesCoord N (coefficients N a z) q =
      if q ∈ Icc 1 N then z q / a else 0 :=
  selbergMultiplesCoord_ramanujan_inverse N _ q

theorem graph_zero_record (N k : ℕ) (a : ℝ) :
    graph N k a (fun _ => 0) = 0 := by
  simp [graph, synthesis, coefficients, pmRamanujanResidueCoeff]

theorem graph_zero_anchor (N k : ℕ) (z : ℕ → ℝ) :
    graph N k 0 z = 0 := by
  simp [graph, synthesis, coefficients, pmRamanujanResidueCoeff]

/-- Exact separation of the source, anchor defect and decoded observation noise. -/
theorem graph_decomposition (N k : ℕ) (a : ℝ) (c z : ℕ → ℝ) :
    graph N k a z =
      (a / a) • synthesis N k c + graph N k a (residual N a c z) := by
  have hc (d : ℕ) (hd : d ∈ Icc 1 N) :
      coefficients N a z d =
        (a / a) * c d + coefficients N a (residual N a c z) d := by
    rw [coefficients_inverse N c d hd]
    dsimp [coefficients, pmRamanujanResidueCoeff]
    have hsum :
        (∑ m ∈ Icc 1 (N / d), (μ m : ℝ) * (z (d * m) / a)) =
          (a / a) * (∑ m ∈ Icc 1 (N / d),
            (μ m : ℝ) * selbergMultiplesCoord N c (d * m)) +
          ∑ m ∈ Icc 1 (N / d), (μ m : ℝ) * (residual N a c z (d * m) / a) := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro m _
      dsimp [residual]
      ring
    rw [hsum]
    ring
  unfold graph synthesis
  rw [smul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [hc d hd, add_smul, mul_smul]

theorem graph_sub_reference (N k : ℕ) (a : ℝ) (c z : ℕ → ℝ) :
    graph N k a z - synthesis N k c =
      (a / a - 1) • synthesis N k c + graph N k a (residual N a c z) := by
  rw [graph_decomposition, sub_smul, one_smul]
  abel

/-- Arbitrary finite data have an explicit full-graph synthesis bound. -/
theorem graph_norm_le (N k : ℕ) (a : ℝ) (z : ℕ → ℝ) :
    ‖graph N k a z‖ ≤ inversionCost N k (fun q => |z q / a|) := by
  have hz : synthesis N k (fun _ => 0) = 0 := by simp [synthesis]
  have h := synthesis_error_le N k (coefficients N a z) (fun _ => 0)
    (fun q => |z q / a|) (fun q => by
      have hzero : selbergMultiplesCoord N (fun _ => 0) q = 0 := by
        simp [selbergMultiplesCoord]
      rw [hzero, sub_zero, coordinates_coefficients]
      split_ifs <;> simp)
  simpa only [hz, sub_zero, graph] using h

/-- No condition on the observed row or anchor is needed for this error budget. -/
theorem graph_error_le (N k : ℕ) (a : ℝ) (c z : ℕ → ℝ) :
    ‖graph N k a z - synthesis N k c‖ ≤ graphError N k a c z := by
  rw [graph_sub_reference]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  change _ ≤ |a / a - 1| * ‖synthesis N k c‖ +
    inversionCost N k (fun q => |residual N a c z q / a|)
  gcongr
  exact graph_norm_le N k a (residual N a c z)

theorem energy_error_le (N k : ℕ) (a : ℝ) (c z : ℕ → ℝ) :
    |sourceEnergy (graph N k a z) - sourceEnergy (synthesis N k c)| ≤
      energyError N k a c z := by
  have hg := graph_error_le N k a c z
  have hK := (norm_nonneg (graph N k a z - synthesis N k c)).trans hg
  unfold energyError
  refine (abs_sourceEnergy_sub_le _ _).trans ?_
  gcongr

/-- A rigorous energy interval around the decoded finite source. -/
theorem energy_enclosure (N k : ℕ) (a : ℝ) (c z : ℕ → ℝ) :
    sourceEnergy (graph N k a z) - energyError N k a c z ≤
        sourceEnergy (synthesis N k c) ∧
      sourceEnergy (synthesis N k c) ≤
        sourceEnergy (graph N k a z) + energyError N k a c z := by
  have h := abs_le.mp (energy_error_le N k a c z)
  constructor <;> linarith [h.1, h.2]

/-- Exact observations recover the source multiplied by the anchor's support indicator. -/
theorem exact_record (N k : ℕ) (a : ℝ) (c : ℕ → ℝ) :
    graph N k a (fun q => a * selbergMultiplesCoord N c q) =
      (a / a) • synthesis N k c := by
  have h := graph_decomposition N k a c (fun q => a * selbergMultiplesCoord N c q)
  have hr : residual N a c (fun q => a * selbergMultiplesCoord N c q) = fun _ => 0 := by
    funext q
    simp [residual]
  rw [hr, graph_zero_record, add_zero] at h
  exact h

/-- The zero-anchor correction is exact, including for nonzero reference sources. -/
theorem zero_anchor_error (N k : ℕ) (c z : ℕ → ℝ) :
    graphError N k 0 c z = ‖synthesis N k c‖ := by
  simp [graphError, inversionCost]

end
end RHTower.FinitePrimeAnchorDecoder
