import GaloisForLFunctions.RHTower.ZetaChiCriticalDirichletCross
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDetectorEnergyDecomposition
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectMollifiedMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorMollifiedCutoffError
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Positive-frequency coefficient obtained by convolving the conjugated direct mollified head
with the frozen critical reflected detector head. -/
def smoothAFEZetaCriticalFrozenCrossPositiveCoeff
    (lam x : ℝ) (q : ℂ) (L M : ℕ) : Fin ((L * M) * L) → ℂ :=
  Sieve.dirConv (L * M) L
    (fun r => (starRingEnd ℂ)
      (smoothAFEZetaDisplacedDirectMollifiedCoeff lam 0 x L M r))
    (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam 0 q n)

/-- Exact reduction of the frozen critical direct/reflected cross to the generic chi-twisted
positive/negative Dirichlet cross. -/
theorem conj_smoothAFEZetaCriticalDirect_mul_frozenReflected_eq_cross
    (lam x : ℝ) (q : ℂ) (L M : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (smoothAFEZetaDisplacedMollifiedDirectHead lam 0 x L M t) *
      smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam 0 q L M t =
    zetaChiCriticalDirichletCross ((L * M) * L) M
      (smoothAFEZetaCriticalFrozenCrossPositiveCoeff lam x q L M)
      (levinsonLinearMollifierFinCoeff M) t := by
  unfold smoothAFEZetaDisplacedMollifiedDirectHead
  unfold smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead
  unfold smoothAFEZetaCriticalFrozenCrossPositiveCoeff
  unfold smoothAFEZetaDisplacedDirectMollifiedCoeff
  unfold zetaChiCriticalDirichletCross
  rw [← Sieve.dirPoly_conj_neg]
  rw [← sieveDirPoly_levinsonLinearMollifierFinCoeff_neg]
  have hmul := Sieve.dirPoly_mul_eq_dirPoly (L * M) L
    (fun r => (starRingEnd ℂ)
      (Sieve.dirConv L M
        (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam 0 x n)
        (levinsonLinearMollifierFinCoeff M) r))
    (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam 0 q n) t
  have hpt : displacedLinePt 0 t = linePt t := by
    simp [displacedLinePt, linePt]
  rw [hpt]
  calc
    _ = zetaChi (linePt t) *
        ((Sieve.dirPoly (L * M)
            (fun r => (starRingEnd ℂ)
              (Sieve.dirConv L M
                (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam 0 x n)
                (levinsonLinearMollifierFinCoeff M) r)) t *
          Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam 0 q n) t) *
          Sieve.dirPoly M (levinsonLinearMollifierFinCoeff M) (-t)) := by ring
    _ = _ := by rw [hmul]

/-- Frozen critical direct/reflected mixed integral with exact coefficient arrays retained. -/
theorem norm_integral_conj_smoothAFEZetaCriticalDirect_mul_frozenReflected_le
    {T : ℝ} (hT : 4 ≤ T) (lam x : ℝ) (q : ℂ) (L M : ℕ) :
    ‖∫ t in T..(2 * T),
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam 0 x L M t) *
          smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam 0 q L M t‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) *
        (∑ r : Fin ((L * M) * L),
          ‖smoothAFEZetaCriticalFrozenCrossPositiveCoeff lam x q L M r‖) *
        (∑ k : Fin M, ‖levinsonLinearMollifierFinCoeff M k‖) := by
  rw [intervalIntegral.integral_congr (fun t _ =>
    conj_smoothAFEZetaCriticalDirect_mul_frozenReflected_eq_cross lam x q L M t)]
  exact norm_integral_zetaChiCriticalDirichletCross_le_l1 hT ((L * M) * L) M
    (smoothAFEZetaCriticalFrozenCrossPositiveCoeff lam x q L M)
    (levinsonLinearMollifierFinCoeff M)

/-- Fully factorized coefficient bound for the frozen critical direct/reflected mixed integral. -/
theorem norm_integral_conj_smoothAFEZetaCriticalDirect_mul_frozenReflected_le_factors
    {T : ℝ} (hT : 4 ≤ T) (lam x : ℝ) (q : ℂ) (L M : ℕ) :
    ‖∫ t in T..(2 * T),
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam 0 x L M t) *
          smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam 0 q L M t‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) *
        ((∑ r : Fin (L * M),
            ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam 0 x L M r‖) *
          (∑ n : Fin L,
            ‖smoothAFEZetaDisplacedReflectedCombinedCoeff lam 0 q n‖)) *
        (∑ k : Fin M, ‖levinsonLinearMollifierFinCoeff M k‖) := by
  refine (norm_integral_conj_smoothAFEZetaCriticalDirect_mul_frozenReflected_le
    hT lam x q L M).trans ?_
  have hconv := Sieve.sum_norm_dirConv_le (L * M) L
    (fun r => (starRingEnd ℂ)
      (smoothAFEZetaDisplacedDirectMollifiedCoeff lam 0 x L M r))
    (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam 0 q n)
  have hC : 0 ≤ 6 / Real.sqrt (1 / (100 * T)) := by positivity
  have hM0 : 0 ≤ ∑ k : Fin M, ‖levinsonLinearMollifierFinCoeff M k‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    simpa [smoothAFEZetaCriticalFrozenCrossPositiveCoeff] using hconv
    exact hC
  · exact hM0

/-- Explicit linear-mollifier `ell^1` specialization of the frozen critical cross estimate. -/
theorem norm_integral_conj_smoothAFEZetaCriticalDirect_mul_frozenReflected_le_explicit
    {T : ℝ} (hT : 4 ≤ T) (lam x : ℝ) (q : ℂ) (L : ℕ) {M : ℕ} (hM : 1 < M) :
    ‖∫ t in T..(2 * T),
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam 0 x L M t) *
          smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam 0 q L M t‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) *
        ((∑ r : Fin (L * M),
            ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam 0 x L M r‖) *
          (∑ n : Fin L,
            ‖smoothAFEZetaDisplacedReflectedCombinedCoeff lam 0 q n‖)) *
        (2 * Real.sqrt M) := by
  refine (norm_integral_conj_smoothAFEZetaCriticalDirect_mul_frozenReflected_le_factors
    hT lam x q L M).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact sum_norm_levinsonLinearMollifierFinCoeff_le hM
  · positivity

end

end RHTower
