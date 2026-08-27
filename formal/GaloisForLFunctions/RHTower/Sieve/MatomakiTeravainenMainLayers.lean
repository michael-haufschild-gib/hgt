import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenErrorLayers

/-!
# Explicit main layers in Matomäki--Teräväinen equation (2.15)

The truncated-Legendre main term is the finite alternating sum over strictly descending block
chains.  This separates each displayed `ℓ`-layer from the recursive operator packaging.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Signed truncated-Legendre operator at exactly one chain length. -/
def mtSignedMainLayerAF {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ) :
    ℕ → Fin (t + 1) → ArithmeticFunction ℂ
  | 0, _ => T
  | depth + 1, j =>
      -(∑ i ∈ mtBlockPrefix j,
        mtPrimeBlockAF (block i) * mtSignedMainLayerAF T block depth i.castSucc)

/-- Recursive main operator equals the explicit finite sum of its signed chain layers. -/
theorem mtFiniteIterationMain_eq_sum_signedLayers {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ) (depth : ℕ) (j : Fin (t + 1)) :
    mtFiniteIterationMain T block cutoff depth j =
      ∑ layer ∈ Finset.range (depth + 1), mtSignedMainLayerAF T block layer j := by
  induction depth generalizing j with
  | zero => simp [mtFiniteIterationMain, mtSignedMainLayerAF]
  | succ depth ih =>
      rw [mtFiniteIterationMain]
      have hmain :
          (∑ i ∈ mtBlockPrefix j,
              mtPrimeBlockAF (block i) *
                mtFiniteIterationMain T block cutoff depth i.castSucc) =
            ∑ i ∈ mtBlockPrefix j,
              ∑ layer ∈ Finset.range (depth + 1),
                mtPrimeBlockAF (block i) *
                  mtSignedMainLayerAF T block layer i.castSucc := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i.castSucc, Finset.mul_sum]
      have hshift :
          -(∑ i ∈ mtBlockPrefix j,
              ∑ layer ∈ Finset.range (depth + 1),
                mtPrimeBlockAF (block i) *
                  mtSignedMainLayerAF T block layer i.castSucc) =
            ∑ layer ∈ Finset.range (depth + 1),
              -(∑ i ∈ mtBlockPrefix j,
                mtPrimeBlockAF (block i) *
                  mtSignedMainLayerAF T block layer i.castSucc) := by
        rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
      rw [hmain, Finset.sum_range_succ']
      simp only [mtSignedMainLayerAF]
      rw [sub_eq_add_neg, hshift]
      ring

/-- Equation (2.15) with both the truncated main term and source error displayed layer by layer. -/
theorem matomakiTeravainen_lemma23ii_finite_all_layers {t : ℕ}
    (data : MTFiniteIterationSourceData t) (α : ℕ → ℂ)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    mtDivisorSiftSum α (data.cutoff j) n =
      (∑ layer ∈ Finset.range (depth + 1),
          (mtCoefficientAF α *
            mtSignedMainLayerAF data.truncation data.block layer j) n) +
        (mtCoefficientAF α *
          mtFiniteIterationRemainder data.block data.cutoff depth j) n +
        ∑ layer ∈ Finset.range (depth + 1),
          mtLiteralSignedSourceErrorLayer data (mtCoefficientAF α) layer j n := by
  rw [matomakiTeravainen_lemma23ii_finite_literal_layers data α depth j hn,
    mtFiniteIterationMain_eq_sum_signedLayers,
    Finset.mul_sum, ArithmeticFunction.add_apply,
    arithmeticFunction_finset_sum_apply]

end

end RHTower.Sieve
