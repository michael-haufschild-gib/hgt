import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationDifferenceBound

/-!
# Bounded actual logarithmic deviation on every fixed valuation class

The coprime square has a positive normalized residue. Dividing the finite local
difference bound by that weight controls the real logarithmic deviation.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

def sourceValuationDeviation (lam : ℕ → ℝ) (p k : ℕ) (s : ℂ) : ℂ :=
  LSeries (valuationPart p k
    (WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s

private theorem sourceValuationDeviation_im (lam : ℕ → ℝ) (p k : ℕ) (σ : ℝ) :
    (sourceValuationDeviation lam p k (σ : ℂ)).im = 0 := by
  let f : ℕ → ℝ := fun n => valuationMask p k n *
    ((if 2 ≤ n then lam n else 0) - ArithmeticFunction.vonMangoldt n)
  have he : sourceValuationDeviation lam p k (σ : ℂ) =
      ((∑' n : ℕ, if n = 0 then 0 else f n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    unfold sourceValuationDeviation LSeries
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, if_true, Complex.ofReal_zero]
    · simp only [LSeries.term, if_neg hn, valuationPart, Pi.sub_apply, WeilHerglotz.lamC, f,
        Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [he]
  exact Complex.ofReal_im _

private def residue (Q : ℕ) : ℝ := ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹)

private theorem residue_pos (Q : ℕ) : 0 < residue Q := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp1
  apply sub_pos.mpr
  simpa only [one_div] using (div_lt_one hp0).mpr hp1

private def weight (Q : ℕ) [NeZero Q] (σ : ℝ) : ℝ :=
  (Gammaℝ (σ : ℂ) * (((σ : ℂ) - 1) * DirichletCharacter.LFunctionTrivChar Q (σ : ℂ)) ^ 2).re

private theorem tendsto_weight (Q : ℕ) [NeZero Q] :
    Tendsto (weight Q) (𝓝[>] 1) (𝓝 (residue Q ^ 2)) := by
  have hres : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) *
      DirichletCharacter.LFunctionTrivChar Q (σ : ℂ)) (𝓝[>] 1) (𝓝 (residue Q : ℂ)) := by
    simpa only [Function.comp_def, residue, Complex.ofReal_prod, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast] using
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

private theorem normalized_valuation_square_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (p k : ℕ) [NeZero p] {σ : ℝ} (hσ : 1 < σ) :
    normalizedCoefficientMellin (LSeries.convolution
      (LSeries.convolution (valuationPart p k (WeilHerglotz.lamC lam -
        fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (coprimePart p 1))
      (coprimePart p 1)) σ = weight p σ * (sourceValuationDeviation lam p k (σ : ℂ)).re := by
  have hd0 : LSeriesSummable
      (WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    LSeriesSummable.sub (WeilHerglotz.summable_term_lamC hW (s := (σ : ℂ)) hσ)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ)
  have hd : LSeriesSummable (valuationPart p k
      (WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (σ : ℂ) :=
    summable_valuationPart p k hd0
  have hu : LSeriesSummable (coprimePart p 1) (σ : ℂ) :=
    summable_coprimePart p (LSeriesSummable_one_iff.mpr (show 1 < (σ : ℂ).re from hσ))
  rw [normalizedCoefficientMellin, LSeries_convolution' (hd.convolution hu) hu,
    LSeries_convolution' hd hu, LSeries_coprimePart_one p hσ]
  change (σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
    (sourceValuationDeviation lam p k (σ : ℂ) * _ * _)).re = _
  have he : (((σ - 1) ^ 2 : ℝ) : ℂ) * (Gammaℝ (σ : ℂ) *
      (sourceValuationDeviation lam p k (σ : ℂ) *
        DirichletCharacter.LFunctionTrivChar p (σ : ℂ) *
        DirichletCharacter.LFunctionTrivChar p (σ : ℂ))) =
      (Gammaℝ (σ : ℂ) * (((σ : ℂ) - 1) *
        DirichletCharacter.LFunctionTrivChar p (σ : ℂ)) ^ 2) *
          sourceValuationDeviation lam p k (σ : ℂ) := by
    push_cast
    ring
  have h := congrArg Complex.re he
  simpa only [weight, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    sourceValuationDeviation_im, mul_zero, zero_mul, sub_zero] using h

/-- No positivity or continuation assumption is placed on the valuation-restricted source. -/
theorem exists_abs_re_sourceValuationDeviation_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(sourceValuationDeviation lam p k (σ : ℂ)).re| ≤ C := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨C, hC0, hC⟩ := boundedNormalizedMellin_valuation_deviation_square hW hp k
  let a := residue p ^ 2 / 2
  have ha : 0 < a := half_pos (sq_pos_of_pos (residue_pos p))
  have hlower : ∀ᶠ σ in 𝓝[>] 1, a ≤ weight p σ :=
    (tendsto_weight p).eventually_const_le (half_lt_self (sq_pos_of_pos (residue_pos p)))
  refine ⟨C / a, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hC, hlower] with σ hσ hCσ hlowerσ
  rw [normalized_valuation_square_eq hW p k hσ, abs_mul,
    abs_of_pos (lt_of_lt_of_le ha hlowerσ)] at hCσ
  apply (le_div_iff₀ ha).mpr
  calc
    |(sourceValuationDeviation lam p k (σ : ℂ)).re| * a =
        a * |(sourceValuationDeviation lam p k (σ : ℂ)).re| := mul_comm _ _
    _ ≤ weight p σ * |(sourceValuationDeviation lam p k (σ : ℂ)).re| :=
      mul_le_mul_of_nonneg_right hlowerσ (abs_nonneg _)
    _ ≤ C := hCσ

end RHTower.WeilSingularArithmetic
