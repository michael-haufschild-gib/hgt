import GaloisForLFunctions.RHTower.ZetaChiDisplacedDirichletCross
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDetectorEnergyDecomposition
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectMollifiedMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorMollifiedCutoffError
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Positive-frequency coefficient of the conjugated displaced direct head times the frozen
displaced reflected head. -/
def smoothAFEZetaDisplacedFrozenCrossPositiveCoeff
    (lam d x : ℝ) (q : ℂ) (L M : ℕ) : Fin ((L * M) * L) → ℂ :=
  Sieve.dirConv (L * M) L
    (fun r => (starRingEnd ℂ)
      (smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r))
    (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n)

theorem conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_eq_cross
    (lam d x : ℝ) (q : ℂ) (L M : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
      smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t =
    zetaChiDisplacedDirichletCross d ((L * M) * L) M
      (smoothAFEZetaDisplacedFrozenCrossPositiveCoeff lam d x q L M)
      (levinsonLinearMollifierFinCoeff M) t := by
  unfold smoothAFEZetaDisplacedMollifiedDirectHead
  unfold smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead
  unfold smoothAFEZetaDisplacedFrozenCrossPositiveCoeff
  unfold smoothAFEZetaDisplacedDirectMollifiedCoeff
  unfold zetaChiDisplacedDirichletCross
  rw [← Sieve.dirPoly_conj_neg]
  rw [← sieveDirPoly_levinsonLinearMollifierFinCoeff_neg]
  have hmul := Sieve.dirPoly_mul_eq_dirPoly (L * M) L
    (fun r => (starRingEnd ℂ)
      (Sieve.dirConv L M
        (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
        (levinsonLinearMollifierFinCoeff M) r))
    (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t
  calc
    _ = zetaChi (displacedLinePt d t) *
        ((Sieve.dirPoly (L * M)
            (fun r => (starRingEnd ℂ)
              (Sieve.dirConv L M
                (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
                (levinsonLinearMollifierFinCoeff M) r)) t *
          Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t) *
          Sieve.dirPoly M (levinsonLinearMollifierFinCoeff M) (-t)) := by ring
    _ = _ := by rw [hmul]

/-- Unconditional factorized bound for the literal frozen displaced smooth-AFE cross. -/
theorem exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_le_factors
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀quarter : d₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ T : ℝ, 4 ≤ T →
      ∀ (lam x : ℝ) (q : ℂ) (L M : ℕ),
    ‖∫ t in T..(2 * T),
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
    exists_norm_integral_zetaChiDisplacedDirichletCross_le_l1 hd₀0 hd₀quarter
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ T hT lam x q L M
  rw [intervalIntegral.integral_congr (fun t _ =>
    conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_eq_cross
      lam d x q L M t)]
  refine (hcross d hd hdd₀ T hT ((L * M) * L) M
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

/-- Linear-mollifier `ell^1` specialization of the frozen displaced smooth-AFE cross bound. -/
theorem exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_le_explicit
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀quarter : d₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ T : ℝ, 4 ≤ T →
      ∀ (lam x : ℝ) (q : ℂ) (L : ℕ) {M : ℕ}, 1 < M →
    ‖∫ t in T..(2 * T),
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
    exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_frozenReflected_le_factors
      hd₀0 hd₀quarter
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ T hT lam x q L M hM
  refine (hbound d hd hdd₀ T hT lam x q L M).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact sum_norm_levinsonLinearMollifierFinCoeff_le hM
  · positivity

end

end RHTower
