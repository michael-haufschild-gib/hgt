import GaloisForLFunctions.RHTower.ZetaChiDisplacedDirichletCrossSubinterval
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFrozenCross

/-!
# Frozen differentiated AFE cross on dyadic subintervals

The literal conjugated direct mollified head and frozen chi-weighted reflected head inherit the
subinterval displaced-oscillation bound.  No phase or coefficient information is discarded.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Factorized coefficient bound for the frozen differentiated AFE cross on a dyadic
subinterval. -/
theorem exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_le_factors_subinterval
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀quarter : d₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ T a b : ℝ, 4 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T →
      ∀ (lam x : ℝ) (q : ℂ) (L M : ℕ),
    ‖∫ t in a..b,
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
          smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) *
        ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) *
        ((∑ r : Fin (L * M),
            ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r‖) *
          (∑ n : Fin L,
            ‖smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n‖)) *
        (∑ k : Fin M, ‖levinsonLinearMollifierFinCoeff M k‖) := by
  obtain ⟨K, hK, hcross⟩ :=
    exists_norm_integral_zetaChiDisplacedDirichletCross_le_l1_subinterval
      hd₀0 hd₀quarter
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ T a b hT ha hab hb lam x q L M
  rw [intervalIntegral.integral_congr (fun t _ =>
    conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_eq_cross
      lam d x q L M t)]
  refine (hcross d hd hdd₀ T a b hT ha hab hb ((L * M) * L) M
    (smoothAFEZetaDisplacedFrozenCrossPositiveCoeff lam d x q L M)
    (levinsonLinearMollifierFinCoeff M)).trans ?_
  have hconv := Sieve.sum_norm_dirConv_le (L * M) L
    (fun r => (starRingEnd ℂ)
      (smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r))
    (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n)
  have hC0 : 0 ≤ (6 / Real.sqrt (1 / (100 * T))) *
      ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) := by positivity
  have hM0 : 0 ≤ ∑ k : Fin M, ‖levinsonLinearMollifierFinCoeff M k‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    simpa [smoothAFEZetaDisplacedFrozenCrossPositiveCoeff] using hconv
    exact hC0
  · exact hM0

/-- Literal linear-mollifier specialization of the frozen differentiated AFE cross bound on a
dyadic subinterval. -/
theorem exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_le_explicit_subinterval
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀quarter : d₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ T a b : ℝ, 4 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T →
      ∀ (lam x : ℝ) (q : ℂ) (L : ℕ) {M : ℕ}, 1 < M →
    ‖∫ t in a..b,
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
          smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) *
        ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) *
        ((∑ r : Fin (L * M),
            ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r‖) *
          (∑ n : Fin L,
            ‖smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n‖)) *
        (2 * Real.sqrt M) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_le_factors_subinterval
      hd₀0 hd₀quarter
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ T a b hT ha hab hb lam x q L M hM
  refine (hbound d hd hdd₀ T a b hT ha hab hb lam x q L M).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact sum_norm_levinsonLinearMollifierFinCoeff_le hM
  · positivity

end

end RHTower
