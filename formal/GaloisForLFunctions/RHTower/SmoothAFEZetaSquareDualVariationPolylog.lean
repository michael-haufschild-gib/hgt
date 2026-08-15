import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualVariationDuhamel
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeSourceFieldPolylog

/-! # Polylogarithmic dyadic mean square for square-dual height variation

The cumulative divisor-square average removes the fixed-power loss from the derivative source.
After measurable Duhamel, the literal dual height variation costs only `N log^4 N`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_dyadic_polylog :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualVariationSourceField
          (N : ℝ) (N : ℝ) t t‖ ^ 2) ≤
        (N : ℝ) ^ 2 *
          (5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2) *
                ((N : ℝ) / 2)) := by
  obtain ⟨A, K, hA, hK, hmv⟩ :=
    exists_integral_normSq_smoothAFEZetaSquareDualDerivativeSourceField_le_polylog
  refine ⟨A, K, hA, hK, ?_⟩
  intro N hN
  let S : Set ℝ := Set.Icc (N : ℝ) (2 * N : ℝ)
  let B : ℝ :=
    5 * Real.pi * Real.exp 1 *
        (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
      (5 * Real.pi / 2) *
        (A * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2) *
          ((N : ℝ) / 2)
  let g : ℝ × ℝ → ℝ := fun p =>
    ‖smoothAFEZetaSquareDualDerivativeSourceField
      (N : ℝ) p.1 p.2‖ ^ 2
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hH : (1 : ℝ) ≤ (N : ℝ) / 2 := by
    have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hDuhamel :=
    integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_duhamel hN
  have hgprod : IntegrableOn g (S ×ˢ S) volume := by
    dsimp only [g, S]
    exact integrableOn_normSq_smoothAFEZetaSquareDualDerivativeSourceField_prod_Icc hN
  let mu : Measure ℝ := volume.restrict S
  have hgprod' : Integrable g (mu.prod mu) := by
    dsimp only [mu]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]
    exact hgprod
  have hinnerInt : IntegrableOn (fun r : ℝ => ∫ t in S, g (r, t)) S volume := by
    change Integrable (fun r : ℝ => ∫ t, g (r, t) ∂mu) mu
    exact hgprod'.integral_prod_left
  have hfinite : volume S ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
  have hconstInt : IntegrableOn (fun _ : ℝ => B) S volume :=
    integrableOn_const hfinite (by simp)
  have hpoint : ∀ r ∈ S, (∫ t in S, g (r, t)) ≤ B := by
    intro r hr
    have hrIcc : r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) := by simpa [S] using hr
    have hb := hmv (center := 3 * (N : ℝ) / 2) hN hrIcc hH
    dsimp only [g, S, B]
    have hleft : 3 * (N : ℝ) / 2 - (N : ℝ) / 2 = (N : ℝ) := by ring
    have hright : 3 * (N : ℝ) / 2 + (N : ℝ) / 2 = 2 * (N : ℝ) := by ring
    simpa only [hleft, hright] using hb
  have houter := setIntegral_mono_on hinnerInt hconstInt measurableSet_Icc hpoint
  have hvolume : volume.real S = (N : ℝ) := by
    dsimp only [S]
    rw [Real.volume_real_Icc]
    rw [max_eq_left (by linarith : 0 ≤ (2 * N : ℝ) - (N : ℝ))]
    ring
  have houter' : (∫ r in S, ∫ t in S, g (r, t)) ≤ (N : ℝ) * B := by
    calc
      (∫ r in S, ∫ t in S, g (r, t)) ≤ ∫ _r in S, B := houter
      _ = volume.real S • B := by rw [setIntegral_const]
      _ = (N : ℝ) * B := by rw [hvolume, smul_eq_mul]
  exact hDuhamel.trans (by
    dsimp only [S, g] at houter'
    calc
      (N : ℝ) *
          (∫ r in Set.Icc (N : ℝ) (2 * N : ℝ),
            ∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
              ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2)
          ≤ (N : ℝ) * ((N : ℝ) *
              (5 * Real.pi * Real.exp 1 *
                  (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
                (5 * Real.pi / 2) *
                  (A * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2) *
                    ((N : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left houter' hN0.le
      _ = (N : ℝ) ^ 2 *
          (5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2) *
                ((N : ℝ) / 2)) := by ring)

theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_polylog :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualVariationSourceField
          (N : ℝ) (N : ℝ) t t‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 * K * (N : ℝ) *
            (1 + Real.log (N : ℝ)) ^ 3 +
          (5 * Real.pi / 4) * A * (N : ℝ) *
            (1 + Real.log (N : ℝ)) ^ 4 := by
  obtain ⟨A, K, hA, hK, hraw⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_dyadic_polylog
  refine ⟨A, K, hA, hK, ?_⟩
  intro N hN
  have hx : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hfirst :
      (N : ℝ) ^ 2 *
          (5 * Real.pi * Real.exp 1 *
            (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ))) =
        5 * Real.pi * Real.exp 1 * K * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ 3 := by
    field_simp [hx.ne']
  have hsecond :
      (N : ℝ) ^ 2 *
          ((5 * Real.pi / 2) *
            (A * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2) *
              ((N : ℝ) / 2)) =
        (5 * Real.pi / 4) * A * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ 4 := by
    field_simp [hx.ne']
    ring
  exact (hraw hN).trans_eq (by
    rw [mul_add, hfirst, hsecond])

end RHTower
