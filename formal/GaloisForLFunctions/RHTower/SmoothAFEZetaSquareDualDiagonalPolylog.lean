import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDiagonalMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualFrozenDyadicMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualVariationPolylog

/-! # Polylogarithmic diagonal mean square for the square-dual source -/

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualSourceField_diagonal_le_polylog_raw :
    ∃ A K B : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ 0 ≤ B ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualSourceField (N : ℝ) t t‖ ^ (2 : ℕ)) ≤
      2 * (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ)) +
      2 * (5 * Real.pi * Real.exp 1 * K * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ (3 : ℕ) +
        (5 * Real.pi / 4) * A * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ (4 : ℕ)) := by
  obtain ⟨B, hB, hFrozen⟩ :=
    exists_integral_dyadic_normSq_smoothAFEZetaSquareDualFrozenSourceField_le_logFourth
  obtain ⟨A, K, hA, hK, hVariation⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_polylog
  refine ⟨A, K, B, hA, hK, hB, ?_⟩
  intro N hN
  let S : Set ℝ := Set.Icc (N : ℝ) (2 * N : ℝ)
  let F : ℝ → ℂ := fun t =>
    smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t
  let V : ℝ → ℂ := fun t =>
    smoothAFEZetaSquareDualVariationSourceField (N : ℝ) (N : ℝ) t t
  have hFint : Integrable (fun t => ‖F t‖ ^ (2 : ℕ)) (volume.restrict S) := by
    exact integrableOn_normSq_smoothAFEZetaSquareDualFrozenSourceField hN
  have hVint : Integrable (fun t => ‖V t‖ ^ (2 : ℕ)) (volume.restrict S) := by
    exact integrableOn_normSq_smoothAFEZetaSquareDualVariationSourceField_diagonal hN
  have hFm : AEStronglyMeasurable F (volume.restrict S) :=
    (measurable_smoothAFEZetaSquareDualFrozenSourceField N).aestronglyMeasurable.restrict
  have hVm : AEStronglyMeasurable V (volume.restrict S) :=
    (measurable_smoothAFEZetaSquareDualVariationSourceField_diagonal hN).aestronglyMeasurable.restrict
  have hsumInt := GaloisForLFunctions.HTGeometry.integrable_normSq_add_measure
    hFm hVm hFint hVint
  have hrhs : Integrable (fun t => 2 * ‖F t‖ ^ (2 : ℕ) + 2 * ‖V t‖ ^ (2 : ℕ))
      (volume.restrict S) := (hFint.const_mul 2).add (hVint.const_mul 2)
  have hpoint : ∀ t, ‖F t + V t‖ ^ (2 : ℕ) ≤ 2 * ‖F t‖ ^ (2 : ℕ) + 2 * ‖V t‖ ^ (2 : ℕ) := by
    intro t
    have htri := norm_add_le (F t) (V t)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖F t‖ - ‖V t‖)]
  have hmono :
      (∫ t, ‖F t + V t‖ ^ (2 : ℕ) ∂(volume.restrict S)) ≤
        ∫ t, 2 * ‖F t‖ ^ (2 : ℕ) + 2 * ‖V t‖ ^ (2 : ℕ) ∂(volume.restrict S) :=
    integral_mono hsumInt hrhs hpoint
  have hsplit :
      (∫ t, 2 * ‖F t‖ ^ (2 : ℕ) + 2 * ‖V t‖ ^ (2 : ℕ) ∂(volume.restrict S)) =
        2 * (∫ t, ‖F t‖ ^ (2 : ℕ) ∂(volume.restrict S)) +
          2 * (∫ t, ‖V t‖ ^ (2 : ℕ) ∂(volume.restrict S)) := by
    rw [integral_add (hFint.const_mul 2) (hVint.const_mul 2),
      integral_const_mul, integral_const_mul]
  have hdiagEq :
      (∫ t in S, ‖smoothAFEZetaSquareDualSourceField (N : ℝ) t t‖ ^ (2 : ℕ)) =
        ∫ t in S, ‖F t + V t‖ ^ (2 : ℕ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp only [F, V]
    rw [smoothAFEZetaSquareDualSourceField_diagonal_eq_frozen_add_variation hN ht]
  have hFb := hFrozen hN
  have hVb := hVariation hN
  rw [hdiagEq]
  exact hmono.trans_eq hsplit |>.trans (by
    dsimp only [F, V, S]
    gcongr)

theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualSourceField_diagonal_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualSourceField (N : ℝ) t t‖ ^ (2 : ℕ)) ≤
        C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by
  obtain ⟨A, K, B, hA, hK, hB, hraw⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualSourceField_diagonal_le_polylog_raw
  let C : ℝ := 2 * B + 10 * Real.pi * Real.exp 1 * K +
    (5 * Real.pi / 2) * A
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  let L : ℝ := 1 + Real.log (N : ℝ)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg hN1]
  have hL0 : 0 ≤ L := hL1.trans' (by norm_num)
  have h34 : L ^ (3 : ℕ) ≤ L ^ (4 : ℕ) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hL0 3) hL1
  have hb := hraw hN
  change (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualSourceField (N : ℝ) t t‖ ^ (2 : ℕ)) ≤
      C * (N : ℝ) * L ^ (4 : ℕ)
  refine hb.trans ?_
  change
    2 * (B * (N : ℝ) * L ^ (4 : ℕ)) +
      2 * (5 * Real.pi * Real.exp 1 * K * (N : ℝ) * L ^ (3 : ℕ) +
        (5 * Real.pi / 4) * A * (N : ℝ) * L ^ (4 : ℕ)) ≤
      C * (N : ℝ) * L ^ (4 : ℕ)
  calc
    2 * (B * (N : ℝ) * L ^ (4 : ℕ)) +
        2 * (5 * Real.pi * Real.exp 1 * K * (N : ℝ) * L ^ (3 : ℕ) +
          (5 * Real.pi / 4) * A * (N : ℝ) * L ^ (4 : ℕ))
      ≤ 2 * (B * (N : ℝ) * L ^ (4 : ℕ)) +
        2 * (5 * Real.pi * Real.exp 1 * K * (N : ℝ) * L ^ (4 : ℕ) +
          (5 * Real.pi / 4) * A * (N : ℝ) * L ^ (4 : ℕ)) := by gcongr
    _ = C * (N : ℝ) * L ^ (4 : ℕ) := by
      dsimp only [C]
      ring

end RHTower
