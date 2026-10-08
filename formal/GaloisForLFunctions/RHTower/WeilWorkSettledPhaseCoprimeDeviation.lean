import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeCosineBound

/-!
# Bounded coprime logarithmic deviation at the pole

The canonical principal-character residue is nonzero. Dividing by its squared
Mellin weight converts the rational cosine bound to an unnormalized source bound.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem sourceCoprimeDeviation_im (lam : ℕ → ℝ) (Q : ℕ) (σ : ℝ) :
    (sourceCoprimeDeviation lam Q (σ : ℂ)).im = 0 := by
  let f : ℕ → ℝ := fun n => coprimeMask Q n *
    ((if 2 ≤ n then lam n else 0) - ArithmeticFunction.vonMangoldt n)
  have he : sourceCoprimeDeviation lam Q (σ : ℂ) =
      ((∑' n : ℕ, if n = 0 then 0 else f n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    unfold sourceCoprimeDeviation LSeries
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, if_true, Complex.ofReal_zero]
    · simp only [LSeries.term, if_neg hn, coprimePart, Pi.sub_apply, WeilHerglotz.lamC, f,
        Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [he]
  exact Complex.ofReal_im _

private def coprimeResidue (Q : ℕ) : ℝ :=
  ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹)

private theorem coprimeResidue_pos (Q : ℕ) : 0 < coprimeResidue Q := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp1
  apply sub_pos.mpr
  simpa only [one_div] using (div_lt_one hp0).mpr hp1

private def coprimeMellinWeight (Q : ℕ) [NeZero Q] (σ : ℝ) : ℝ :=
  (Gammaℝ (σ : ℂ) * (((σ : ℂ) - 1) * DirichletCharacter.LFunctionTrivChar Q (σ : ℂ)) ^ 2).re

private theorem tendsto_coprimeMellinWeight (Q : ℕ) [NeZero Q] :
    Tendsto (coprimeMellinWeight Q) (𝓝[>] 1) (𝓝 (coprimeResidue Q ^ 2)) := by
  have hres : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) *
      DirichletCharacter.LFunctionTrivChar Q (σ : ℂ)) (𝓝[>] 1)
      (𝓝 (coprimeResidue Q : ℂ)) := by
    simpa only [Function.comp_def, coprimeResidue, Complex.ofReal_prod,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast] using
      (DirichletCharacter.LFunctionTrivChar_residue_one (N := Q)).comp
        tendsto_ofReal_nhdsWithin_ne_one
  have hg0 : ContinuousAt (fun s : ℂ => (Gammaℝ s)⁻¹) 1 :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hg1 : ContinuousAt Gammaℝ (1 : ℂ) := by
    have hi := hg0.inv₀ (by simp : (Gammaℝ 1)⁻¹ ≠ 0)
    change ContinuousAt (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) 1 at hi
    simpa only [inv_inv] using hi
  have hg : Tendsto (fun σ : ℝ => Gammaℝ (σ : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    simpa only [Complex.Gammaℝ_one, Function.comp_def] using hg1.tendsto.comp
      (tendsto_ofReal_nhdsWithin_ne_one.mono_right nhdsWithin_le_nhds)
  have h := (Complex.continuous_re.tendsto _).comp (hg.mul (hres.pow 2))
  change Tendsto (fun σ : ℝ => (Gammaℝ (σ : ℂ) *
    (((σ : ℂ) - 1) * DirichletCharacter.LFunctionTrivChar Q (σ : ℂ)) ^ 2).re) _ _
  simpa only [Function.comp_def, one_mul, ← Complex.ofReal_pow, Complex.ofReal_re] using h

private theorem normalized_coprimeSquare_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (Q : ℕ) [NeZero Q] {σ : ℝ} (hσ : 1 < σ) :
    (σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
      LSeries (coprimePart Q (sourceSquareCoeff lam)) (σ : ℂ)).re =
        coprimeMellinWeight Q σ * (sourceCoprimeDeviation lam Q (σ : ℂ)).re := by
  rw [LSeries_coprimePart_sourceSquareCoeff hW Q (s := (σ : ℂ)) hσ]
  have he : (((σ - 1) ^ 2 : ℝ) : ℂ) * (Gammaℝ (σ : ℂ) *
      (sourceCoprimeDeviation lam Q (σ : ℂ) * DirichletCharacter.LFunctionTrivChar Q (σ : ℂ) ^ 2)) =
      (Gammaℝ (σ : ℂ) * (((σ : ℂ) - 1) *
        DirichletCharacter.LFunctionTrivChar Q (σ : ℂ)) ^ 2) *
          sourceCoprimeDeviation lam Q (σ : ℂ) := by
    push_cast
    ring
  have h := congrArg Complex.re he
  simpa only [coprimeMellinWeight, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    sourceCoprimeDeviation_im, mul_zero, zero_mul, sub_zero] using h

/-- Every finite coprime deletion has bounded real logarithmic deviation near one,
without a hypothesis on the deleted source. -/
theorem exists_abs_re_sourceCoprimeDeviation_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (Q : ℕ) [NeZero Q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(sourceCoprimeDeviation lam Q (σ : ℂ)).re| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_coprime_sourceSquare_normalized_le hW Q
  let a := coprimeResidue Q ^ 2 / 2
  have ha : 0 < a := half_pos (sq_pos_of_pos (coprimeResidue_pos Q))
  have hlower : ∀ᶠ σ in 𝓝[>] 1, a ≤ coprimeMellinWeight Q σ :=
    (tendsto_coprimeMellinWeight Q).eventually_const_le
      (half_lt_self (sq_pos_of_pos (coprimeResidue_pos Q)))
  refine ⟨C / a, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hC, hlower] with σ hσ hCσ hlowerσ
  rw [normalized_coprimeSquare_eq hW Q hσ, abs_mul,
    abs_of_pos (lt_of_lt_of_le ha hlowerσ)] at hCσ
  apply (le_div_iff₀ ha).mpr
  calc
    |(sourceCoprimeDeviation lam Q (σ : ℂ)).re| * a =
        a * |(sourceCoprimeDeviation lam Q (σ : ℂ)).re| := mul_comm _ _
    _ ≤ coprimeMellinWeight Q σ * |(sourceCoprimeDeviation lam Q (σ : ℂ)).re| :=
      mul_le_mul_of_nonneg_right hlowerσ (abs_nonneg _)
    _ ≤ C := hCσ

end RHTower.WeilSingularArithmetic
