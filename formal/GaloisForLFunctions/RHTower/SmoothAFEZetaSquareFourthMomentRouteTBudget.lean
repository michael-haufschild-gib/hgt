import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePrimalIntegrability
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualIntegrability
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePrimalRouteTBudget
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePoleRouteTBudget
import GaloisForLFunctions.RHTower.HardyZ

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- The three literal summands are exactly the Gaussian square AFE on a natural conductor. -/
theorem smoothAFEZetaSquare_exact_afe_summands
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    riemannZeta (linePt t) ^ (2 : ℕ) =
      smoothAFEZetaSquarePrimalAFESummand N t +
      smoothAFEZetaSquareDualAFESummand N t -
      smoothAFEZetaSquarePoleAFESummand N t := by
  rw [smoothAFEZetaSquarePoleAFESummand_eq_exact_confluent_term]
  have hcast : (((N : ℝ) : ℂ)) = (N : ℂ) := by norm_cast
  simpa only [smoothAFEZetaSquarePrimalAFESummand,
    smoothAFEZetaSquareDualAFESummand,
    Nat.cast_ofNat, hcast] using
      (RHTower.Sieve.smoothAFEZetaSquare_exact_afe
        (x := (N : ℝ)) (by exact_mod_cast hN) t)

/-- Pointwise square-AFE reduction of the critical-line fourth power to the three exact sources. -/
theorem norm_riemannZeta_line_pow_four_le_exact_afe_summands
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    ‖riemannZeta (linePt t)‖ ^ (4 : ℕ) ≤
      3 * (‖smoothAFEZetaSquarePrimalAFESummand N t‖ ^ (2 : ℕ) +
        ‖smoothAFEZetaSquareDualAFESummand N t‖ ^ (2 : ℕ) +
        ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ (2 : ℕ)) := by
  let P := smoothAFEZetaSquarePrimalAFESummand N t
  let D := smoothAFEZetaSquareDualAFESummand N t
  let R := smoothAFEZetaSquarePoleAFESummand N t
  have hafe : riemannZeta (linePt t) ^ (2 : ℕ) = P + D - R := by
    simpa only [P, D, R] using smoothAFEZetaSquare_exact_afe_summands hN t
  have htri : ‖riemannZeta (linePt t) ^ (2 : ℕ)‖ ≤ ‖P‖ + ‖D‖ + ‖R‖ := by
    rw [hafe]
    calc
      ‖P + D - R‖ ≤ ‖P + D‖ + ‖R‖ := norm_sub_le _ _
      _ ≤ (‖P‖ + ‖D‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hab : 0 ≤ (‖P‖ - ‖D‖) ^ (2 : ℕ) := sq_nonneg _
  have hac : 0 ≤ (‖P‖ - ‖R‖) ^ (2 : ℕ) := sq_nonneg _
  have hbc : 0 ≤ (‖D‖ - ‖R‖) ^ (2 : ℕ) := sq_nonneg _
  rw [norm_pow] at hsq
  dsimp only [P, D, R] at hsq hab hac hbc ⊢
  nlinarith

/-- Unconditional exact-AFE fourth-moment closure on every retained dyadic block. -/
theorem exists_integral_Icc_norm_riemannZeta_line_pow_four_le_routeTBudget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖riemannZeta (linePt t)‖ ^ (4 : ℕ)) ≤
          C * (N : ℝ) ^ (101 / 100 : ℝ) := by
  obtain ⟨CP, hCP, hPbound⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquarePrimalAFESummand_le_routeTBudget
  obtain ⟨CD, hCD, hDbound⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualAFESummand_le_routeTBudget
  obtain ⟨CR, hCR, hRbound⟩ :=
    exists_integral_normSq_smoothAFEZetaSquarePoleAFESummand_le_routeTBudget
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
    _ ≤ 3 * (CP * (N : ℝ) ^ (101 / 100 : ℝ) +
        CD * (N : ℝ) ^ (101 / 100 : ℝ) +
        CR * (N : ℝ) ^ (101 / 100 : ℝ)) := by gcongr
    _ = C * (N : ℝ) ^ (101 / 100 : ℝ) := by
      dsimp only [C]
      ring

end RHTower
