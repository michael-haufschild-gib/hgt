import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierEnergy

/-!
# Type-I moment with the source prime amplifier constructed internally

The full powered prime amplifier is split into its exact fixed Watt blocks.  Each block-large set
is fed to the restricted Deshouillers--Iwaniec receiver, with the amplifier lower bound proved
from set membership.  The resulting estimates are summed through the measurable finite cover.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Length of the `r`th literal Watt block in a powered `(P,2P]` prime factor. -/
def mtTypeIPrimeBlockLength (P ell : ℕ) (r : Fin ell) : ℕ :=
  P ^ ell * 2 ^ (r : ℕ)

/-- Exact restricted-moment bound charged to one powered-prime Watt block. -/
noncomputable def mtTypeIPrimeBlockMomentBound
    (C ε : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeBlockLength P ell r
  let b := mtTypeIPrimeRaisedCoeff P ell
  ((ell : ℝ) / V) * Real.sqrt
      (C * T ^ ε *
        (((T + (B : ℝ) ^ 2 * Real.sqrt T +
                (B : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ 2 * (B : ℝ)) +
            (T + (B : ℝ)) / (T ^ 4 * (B : ℝ))) *
          (1 / (B : ℝ)) *
          (∑ m ∈ Finset.Ioc B (2 * B), ‖b m‖ ^ 2))) *
      Real.sqrt
        (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
            (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
          generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
            (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Section 5.1 Type-I receiver with the prime amplifier, its power, its exact fixed block cover,
and every amplifier lower bound constructed internally.  The remaining clauses are precisely the
numeric Lemma 3.5 range conditions for those literal blocks. -/
theorem exists_setIntegral_mtTypeI_primeAmplifier_coveredRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ),
      1 ≤ A → 1 ≤ P → 0 < ell → 1 ≤ N → N < N' → N' ≤ 2 * N →
      2 ≤ T → 0 < V →
      (∀ r : Fin ell,
        T ≤ (N : ℝ) ∨
          (((mtTypeIPrimeBlockLength P ell r : ℕ) : ℝ) ≤ T ∧
            ((((2 * mtTypeIPrimeBlockLength P ell r) * (N' * N') : ℕ) : ℝ) ≤
              ((mtTypeIPrimeBlockLength P ell r : ℕ) : ℝ) ^ (5 / 4 : ℝ) *
                T ^ (3 / 4 : ℝ)))) →
      (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeBlockMomentBound C ε a A P ell N T V r := by
  obtain ⟨C, hC, hrestricted⟩ := exists_setIntegral_mtTypeI_amplified_coveredRange hε
  refine ⟨C, hC, ?_⟩
  intro a A P ell N N' T V hA hP hell hN hNN' hN' hT hV hcovered
  let f : ℝ → ℝ := fun t =>
    ‖mtWattCoefficientBlock a A t‖ ^ 2 * ‖mtWattUnitBlock N N' t‖ ^ 2
  have hunion : (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V, f t) ≤
      ∑ r : Fin ell,
        ∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r, f t :=
    setIntegral_mtTypeIPrimeAmplifierLargeSet_le_sum_blocks hell T V
      (((continuous_perronPoly _ _ _).norm.pow 2).mul
        ((continuous_perronPoly _ _ _).norm.pow 2))
      (fun _ => by positivity)
  have hblock : ∀ r : Fin ell,
      (∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r, f t) ≤
        mtTypeIPrimeBlockMomentBound C ε a A P ell N T V r := by
    intro r
    let B := mtTypeIPrimeBlockLength P ell r
    let b := mtTypeIPrimeRaisedCoeff P ell
    let K : ℝ := (ell : ℝ) / V
    have hB : 1 ≤ B := by
      have hBpos : 0 < B := by
        dsimp only [B, mtTypeIPrimeBlockLength]
        positivity
      omega
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hlarge : ∀ t ∈ mtTypeIPrimeAmplifierBlockLargeSet P ell T V r,
        1 ≤ K * ‖mtWattCoefficientBlock b B t‖ := by
      intro t ht
      have hscale : (1 : ℝ) = K * (V / (ell : ℝ)) := by
        dsimp only [K]
        have hellR : (0 : ℝ) < ell := by positivity
        field_simp
      rw [hscale]
      exact mul_le_mul_of_nonneg_left ht.2 hK
    have hr := hrestricted
      (mtTypeIPrimeAmplifierBlockLargeSet P ell T V r)
      a b A B N N' K hA hB hN hNN' hN' T hT (hcovered r) hK
      (measurableSet_mtTypeIPrimeAmplifierBlockLargeSet P ell T V r)
      (mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r) hlarge
    simpa only [f, B, b, K, mtTypeIPrimeBlockMomentBound] using hr
  change (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V, f t) ≤ _
  exact hunion.trans (Finset.sum_le_sum fun r _ => hblock r)

end

end RHTower.Sieve
