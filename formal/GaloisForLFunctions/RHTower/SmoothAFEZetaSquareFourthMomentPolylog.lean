import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareFourthMomentRouteTBudget
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDiagonalPolylog

/-! # Polylogarithmic exact-AFE fourth moment on dyadic blocks -/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualAFESummand_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualAFESummand N t‖ ^ (2 : ℕ)) ≤
          C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualSourceField_diagonal_le_polylog
  refine ⟨C, hC, ?_⟩
  intro N hN
  simpa only [norm_smoothAFEZetaSquareDualAFESummand_eq_sourceField] using hbound hN

theorem exists_integral_Icc_normSq_smoothAFEZetaSquarePrimalAFESummand_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquarePrimalAFESummand N t‖ ^ (2 : ℕ)) ≤
          C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by
  obtain ⟨B, hB, hraw⟩ :=
    exists_integral_normSq_smoothAFEZetaSquarePrimalSourceField_le
  let C : ℝ := 5 * Real.pi * Real.exp 1 * B + (5 * Real.pi / 4) * B
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  let L : ℝ := 1 + Real.log (N : ℝ)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg hN1]
  have hL0 : 0 ≤ L := by positivity
  have h34 : L ^ (3 : ℕ) ≤ L ^ (4 : ℕ) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hL0 3) hL1
  have hH : (1 : ℝ) ≤ (N : ℝ) / 2 := by
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hb := hraw
    (center := (3 / 2 : ℝ) * (N : ℝ))
    (H := (N : ℝ) / 2) hN hH
  have hb' :
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquarePrimalAFESummand N t‖ ^ (2 : ℕ)) ≤
      5 * Real.pi * Real.exp 1 *
          (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (3 : ℕ)) +
        (5 * Real.pi / 2) *
          (B * (1 + Real.log (N : ℝ)) ^ (4 : ℕ)) * ((N : ℝ) / 2) := by
    simpa only [smoothAFEZetaSquarePrimalAFESummand_eq_sourceField,
      show (3 / 2 : ℝ) * (N : ℝ) - (N : ℝ) / 2 = (N : ℝ) by ring,
      show (3 / 2 : ℝ) * (N : ℝ) + (N : ℝ) / 2 = 2 * (N : ℝ) by ring]
      using hb
  change (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquarePrimalAFESummand N t‖ ^ (2 : ℕ)) ≤
      C * (N : ℝ) * L ^ (4 : ℕ)
  refine hb'.trans ?_
  change
    5 * Real.pi * Real.exp 1 * (B * (N : ℝ) * L ^ (3 : ℕ)) +
      (5 * Real.pi / 2) * (B * L ^ (4 : ℕ)) * ((N : ℝ) / 2) ≤
        C * (N : ℝ) * L ^ (4 : ℕ)
  calc
    5 * Real.pi * Real.exp 1 * (B * (N : ℝ) * L ^ (3 : ℕ)) +
        (5 * Real.pi / 2) * (B * L ^ (4 : ℕ)) * ((N : ℝ) / 2)
      ≤ 5 * Real.pi * Real.exp 1 * (B * (N : ℝ) * L ^ (4 : ℕ)) +
        (5 * Real.pi / 2) * (B * L ^ (4 : ℕ)) * ((N : ℝ) / 2) := by gcongr
    _ = C * (N : ℝ) * L ^ (4 : ℕ) := by
      dsimp only [C]
      ring

theorem exists_integral_Icc_normSq_smoothAFEZetaSquarePoleAFESummand_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ (2 : ℕ)) ≤
          C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by
  obtain ⟨D, hD, hpoint⟩ := exists_norm_smoothAFEZetaSquarePoleAFESummand_le
  let C : ℝ := D ^ (2 : ℕ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hNpos : 0 < N := by omega
  have hNR0 : (0 : ℝ) ≤ N := by positivity
  let L : ℝ := 1 + Real.log (N : ℝ)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg hN1]
  have hL4 : 1 ≤ L ^ (4 : ℕ) := one_le_pow₀ hL1
  have hfun : IntegrableOn (fun t : ℝ => ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ (2 : ℕ))
      (Set.Icc (N : ℝ) (2 * N : ℝ)) :=
    ((continuous_smoothAFEZetaSquarePoleAFESummand hNpos).norm.pow 2).integrableOn_Icc
  have hconst : IntegrableOn (fun _ : ℝ => D ^ (2 : ℕ))
      (Set.Icc (N : ℝ) (2 * N : ℝ)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hmono := setIntegral_mono_on hfun hconst measurableSet_Icc
    (fun t ht => by
      have hp := hpoint hN ht.1 (by simpa using ht.2)
      exact pow_le_pow_left₀ (norm_nonneg _) hp 2)
  change (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ (2 : ℕ)) ≤
      C * (N : ℝ) * L ^ (4 : ℕ)
  calc
    (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ (2 : ℕ)) ≤
        ∫ _t in Set.Icc (N : ℝ) (2 * N : ℝ), D ^ (2 : ℕ) := hmono
    _ = D ^ (2 : ℕ) * (N : ℝ) := by
      rw [MeasureTheory.setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith : (N : ℝ) ≤ 2 * N)]
      simp only [smul_eq_mul]
      ring
    _ ≤ D ^ (2 : ℕ) * (N : ℝ) * L ^ (4 : ℕ) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hL4 (mul_nonneg (sq_nonneg D) hNR0)
    _ = C * (N : ℝ) * L ^ (4 : ℕ) := by rfl

theorem exists_integral_Icc_norm_riemannZeta_line_pow_four_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖riemannZeta (linePt t)‖ ^ (4 : ℕ)) ≤
          C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by
  obtain ⟨CP, hCP, hPbound⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquarePrimalAFESummand_le_polylog
  obtain ⟨CD, hCD, hDbound⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualAFESummand_le_polylog
  obtain ⟨CR, hCR, hRbound⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquarePoleAFESummand_le_polylog
  let C : ℝ := 3 * (CP + CD + CR)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  let S : Set ℝ := Set.Icc (N : ℝ) (2 * N : ℝ)
  let p : ℝ → ℝ := fun t => ‖smoothAFEZetaSquarePrimalAFESummand N t‖ ^ (2 : ℕ)
  let d : ℝ → ℝ := fun t => ‖smoothAFEZetaSquareDualAFESummand N t‖ ^ (2 : ℕ)
  let r : ℝ → ℝ := fun t => ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ (2 : ℕ)
  have hNpos : 0 < N := by omega
  have hPint : IntegrableOn p S := by
    simpa only [p, S, smoothAFEZetaSquarePrimalAFESummand_eq_sourceField] using
      (integrableOn_normSq_smoothAFEZetaSquarePrimalSourceField hN)
  have hDint : IntegrableOn d S := by
    simpa only [d, S] using
      (integrableOn_normSq_smoothAFEZetaSquareDualAFESummand hN)
  have hRint : IntegrableOn r S := by
    have hc :=
      ((continuous_smoothAFEZetaSquarePoleAFESummand hNpos).norm.pow 2).integrableOn_Icc
        (μ := volume) (a := (N : ℝ)) (b := 2 * (N : ℝ))
    refine hc.congr ?_
    filter_upwards with t
    simp only [Pi.pow_apply, r]
  have hZint : IntegrableOn (fun t : ℝ => ‖riemannZeta (linePt t)‖ ^ (4 : ℕ)) S := by
    have hc :=
      ((((continuous_riemannZeta_line).norm).pow 4).integrableOn_Icc
        (μ := volume) (a := (N : ℝ)) (b := 2 * (N : ℝ)))
    refine hc.congr ?_
    filter_upwards with t
    simp only [Pi.pow_apply]
  have hrhs : IntegrableOn (fun t => 3 * (p t + d t + r t)) S :=
    ((hPint.add hDint).add hRint).const_mul 3
  have hmono :
      (∫ t in S, ‖riemannZeta (linePt t)‖ ^ (4 : ℕ)) ≤
        ∫ t in S, 3 * (p t + d t + r t) :=
    setIntegral_mono_on hZint hrhs measurableSet_Icc fun t _ => by
      simpa only [p, d, r] using
        norm_riemannZeta_line_pow_four_le_exact_afe_summands hNpos t
  have hsplit :
      (∫ t in S, 3 * (p t + d t + r t)) =
        3 * ((∫ t in S, p t) + (∫ t in S, d t) + (∫ t in S, r t)) := by
    have hpd : (∫ t in S, p t + d t) =
        (∫ t in S, p t) + ∫ t in S, d t := by
      simpa only [Pi.add_apply] using integral_add hPint hDint
    have hpdr : (∫ t in S, p t + d t + r t) =
        (∫ t in S, p t + d t) + ∫ t in S, r t := by
      simpa only [Pi.add_apply] using integral_add (hPint.add hDint) hRint
    rw [integral_const_mul, hpdr, hpd]
  have hPb := hPbound hN
  have hDb := hDbound hN
  have hRb := hRbound hN
  have hmono' := hmono.trans_eq hsplit
  dsimp only [p, d, r, S] at hmono'
  calc
    (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ), ‖riemannZeta (linePt t)‖ ^ (4 : ℕ)) ≤
        3 * ((∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
          ‖smoothAFEZetaSquarePrimalAFESummand N t‖ ^ (2 : ℕ)) +
        (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
          ‖smoothAFEZetaSquareDualAFESummand N t‖ ^ (2 : ℕ)) +
        (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
          ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ (2 : ℕ))) := hmono'
    _ ≤ 3 * (CP * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) +
        CD * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) +
        CR * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ)) := by gcongr
    _ = C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by
      dsimp only [C]
      ring

end RHTower

