import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeDeviation
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeCanonical

/-!
# The actual source excluded by a finite coprime mask

Subtract the coprime deviation from the full deviation, then restore the
absolutely summable excluded canonical contribution.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

private theorem coprimePart_one (f : ℕ → ℂ) : coprimePart 1 f = f := by
  funext n
  have hn : n.Coprime 1 := (Nat.coprime_one_right_iff n).mpr trivial
  simp only [coprimePart, coprimeMask, if_pos hn, Complex.ofReal_one, one_mul]

private theorem coprimePart_sub (Q : ℕ) (f g : ℕ → ℂ) :
    coprimePart Q (f - g) = coprimePart Q f - coprimePart Q g := by
  funext n
  simp only [coprimePart, Pi.sub_apply, mul_sub]

private theorem LSeries_nonCoprime_lamC_eq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] {σ : ℝ} (hσ : 1 < σ) :
    LSeries (nonCoprimePart Q (WeilHerglotz.lamC lam)) (σ : ℂ) =
      sourceCoprimeDeviation lam 1 (σ : ℂ) - sourceCoprimeDeviation lam Q (σ : ℂ) +
        LSeries (nonCoprimePart Q
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (σ : ℂ) := by
  have hl := WeilHerglotz.summable_term_lamC hW (s := (σ : ℂ)) hσ
  have hv := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  simp only [sourceCoprimeDeviation, coprimePart_one, coprimePart_sub,
    nonCoprimePart_eq_sub, LSeries_sub hl hv,
    LSeries_sub hl (summable_coprimePart Q hl),
    LSeries_sub hv (summable_coprimePart Q hv),
    LSeries_sub (summable_coprimePart Q hl) (summable_coprimePart Q hv)]
  ring

/-- The literal source excluded by any fixed finite prime deletion has bounded
real logarithmic derivative near one. -/
theorem exists_abs_re_nonCoprime_source_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(LSeries (nonCoprimePart Q (WeilHerglotz.lamC lam)) (σ : ℂ)).re| ≤ K := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_re_sourceCoprimeDeviation_le hW 1
  obtain ⟨B, hB0, hB⟩ := exists_abs_re_sourceCoprimeDeviation_le hW Q
  obtain ⟨C, hC0, hC⟩ := exists_norm_nonCoprime_vonMangoldt_le Q
  refine ⟨A + B + C, add_nonneg (add_nonneg hA0 hB0) hC0, ?_⟩
  filter_upwards [hA, hB, self_mem_nhdsWithin] with σ hAσ hBσ hσ
  rw [LSeries_nonCoprime_lamC_eq hW Q hσ, Complex.add_re, Complex.sub_re]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hAσ hBσ))
    ((Complex.abs_re_le_norm _).trans (hC σ hσ.le)))

end RHTower.WeilSingularArithmetic
