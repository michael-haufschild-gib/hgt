import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationDeviation
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeCanonical

/-!
# Bounded source derivative on each positive valuation class

The canonical contribution on a positive valuation class is dominated by the
already summable non-coprime canonical part. Restoring it converts the deviation
bound into a bound for the literal source.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

private theorem norm_valuationPart_succ_le_nonCoprimePart {p : ℕ} (hp : p.Prime)
    (k : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    ‖valuationPart p (k + 1) f n‖ ≤ ‖nonCoprimePart p f n‖ := by
  by_cases hn : p ^ (k + 1) ∣ n ∧ ¬p ^ (k + 1 + 1) ∣ n
  · have hd : p ∣ n :=
      (show p ∣ p ^ (k + 1) by rw [pow_succ']; exact dvd_mul_right _ _).trans hn.1
    have hc : ¬n.Coprime p := fun hc => (hp.coprime_iff_not_dvd.mp hc.symm) hd
    simp [valuationPart, valuationMask, nonCoprimePart, hn, hc]
  · simp [valuationPart, valuationMask, hn]

theorem LSeriesSummable_valuation_vonMangoldt_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeriesSummable (valuationPart p (k + 1)
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  refine (LSeriesSummable_nonCoprime_vonMangoldt_one p).norm.of_norm_bounded fun n =>
    LSeries.norm_term_le 1 ?_
  exact norm_valuationPart_succ_le_nonCoprimePart hp k _ n

theorem exists_norm_valuation_vonMangoldt_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 ≤ σ →
      ‖LSeries (valuationPart p (k + 1)
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (σ : ℂ)‖ ≤ C := by
  let f := valuationPart p (k + 1) (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  have hs : LSeriesSummable f 1 := LSeriesSummable_valuation_vonMangoldt_one hp k
  refine ⟨∑' n, ‖LSeries.term f 1 n‖, tsum_nonneg (fun _ => norm_nonneg _), fun σ hσ => ?_⟩
  have hs' : LSeriesSummable f (σ : ℂ) := hs.of_re_le_re (by simpa using hσ)
  exact (norm_tsum_le_tsum_norm hs'.norm).trans
    (hs'.norm.tsum_le_tsum (fun n =>
      LSeries.norm_term_le_of_re_le_re f (by simpa using hσ) n) hs.norm)

/-- Every fixed positive valuation class of the actual arithmetic source has
bounded real logarithmic derivative at the right endpoint. -/
theorem exists_abs_re_valuation_source_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(LSeries (valuationPart p (k + 1) (WeilHerglotz.lamC lam)) (σ : ℂ)).re| ≤ C := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_re_sourceValuationDeviation_le hW hp (k + 1)
  obtain ⟨B, hB0, hB⟩ := exists_norm_valuation_vonMangoldt_le hp k
  refine ⟨A + B, add_nonneg hA0 hB0, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hA] with σ hσ hAσ
  have hl := summable_valuationPart p (k + 1)
    (WeilHerglotz.summable_term_lamC hW (s := (σ : ℂ)) hσ)
  have hv := summable_valuationPart p (k + 1)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ)
  have he : LSeries (valuationPart p (k + 1) (WeilHerglotz.lamC lam)) (σ : ℂ) =
      sourceValuationDeviation lam p (k + 1) (σ : ℂ) +
        LSeries (valuationPart p (k + 1)
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (σ : ℂ) := by
    rw [sourceValuationDeviation, valuationPart_sub, LSeries_sub hl hv]
    ring
  rw [he, Complex.add_re]
  exact (abs_add_le _ _).trans
    (add_le_add hAσ ((Complex.abs_re_le_norm _).trans (hB σ hσ.le)))

end RHTower.WeilSingularArithmetic
