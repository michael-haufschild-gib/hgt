import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFiniteIterationSource

/-!
# Explicit error layers in Matomäki--Teräväinen Lemma 2.3(ii)

The accumulated error in equation (2.15) is the finite alternating sum of literal Lemma 2.3(i)
errors over strictly descending block chains.  This file exposes those layers separately; the
recursive definition is exactly the source ordering `j_ℓ < ⋯ < j₁`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Signed source error at exactly one displayed depth.  Successor depth chooses one block below
the current cutoff and reverses the sign. -/
def mtSignedSourceErrorLayerAF {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) : ℕ → Fin (t + 1) → ArithmeticFunction ℂ
  | 0, j => a * mtOneStepErrorKernel data.truncation data.block data.cutoff j
  | depth + 1, j =>
      -(∑ i ∈ mtBlockPrefix j,
        mtSignedSourceErrorLayerAF data
          (a * mtPrimeBlockAF (data.block i)) depth i.castSucc)

/-- Scalar recursion whose leaves are the literal `c₁+c₂+c₃` source errors. -/
def mtLiteralSignedSourceErrorLayer {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) : ℕ → Fin (t + 1) → ℕ → ℂ
  | 0, j, n =>
      mtLemma23Error (fun m => a m) data.z₀ data.D
        (data.lowerSpill j) (data.upperSpill j)
        (primesIco data.z₀ (data.cutoff j)) (data.lower j) n
  | depth + 1, j, n =>
      -(∑ i ∈ mtBlockPrefix j,
        mtLiteralSignedSourceErrorLayer data
          (a * mtPrimeBlockAF (data.block i)) depth i.castSucc n)

/-- Every signed operator layer evaluates to the corresponding finite sum of literal source
errors. -/
theorem mtSignedSourceErrorLayerAF_apply_eq_literal {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    mtSignedSourceErrorLayerAF data a depth j n =
      mtLiteralSignedSourceErrorLayer data a depth j n := by
  induction depth generalizing a j with
  | zero =>
      exact data.oneStepError_apply a j hn
  | succ depth ih =>
      rw [mtSignedSourceErrorLayerAF, mtLiteralSignedSourceErrorLayer,
        ArithmeticFunction.neg_apply, arithmeticFunction_finset_sum_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact ih (a * mtPrimeBlockAF (data.block i)) i.castSucc

/-- The recursively accumulated source error is exactly the sum of its signed depth layers. -/
theorem mtAccumulatedSourceErrorAF_eq_sum_signedLayers {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j : Fin (t + 1)) :
    mtAccumulatedSourceErrorAF data a depth j =
      ∑ layer ∈ Finset.range (depth + 1),
        mtSignedSourceErrorLayerAF data a layer j := by
  induction depth generalizing a j with
  | zero => simp [mtAccumulatedSourceErrorAF, mtSignedSourceErrorLayerAF]
  | succ depth ih =>
      rw [mtAccumulatedSourceErrorAF]
      have haccumulated :
          (∑ i ∈ mtBlockPrefix j,
              mtAccumulatedSourceErrorAF data
                (a * mtPrimeBlockAF (data.block i)) depth i.castSucc) =
            ∑ i ∈ mtBlockPrefix j,
              ∑ layer ∈ Finset.range (depth + 1),
                mtSignedSourceErrorLayerAF data
                  (a * mtPrimeBlockAF (data.block i)) layer i.castSucc := by
        apply Finset.sum_congr rfl
        intro i hi
        exact ih (a * mtPrimeBlockAF (data.block i)) i.castSucc
      have hshift :
          -(∑ i ∈ mtBlockPrefix j,
              ∑ layer ∈ Finset.range (depth + 1),
                mtSignedSourceErrorLayerAF data
                  (a * mtPrimeBlockAF (data.block i)) layer i.castSucc) =
            ∑ layer ∈ Finset.range (depth + 1),
              -(∑ i ∈ mtBlockPrefix j,
                mtSignedSourceErrorLayerAF data
                  (a * mtPrimeBlockAF (data.block i)) layer i.castSucc) := by
        rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
      rw [haccumulated, Finset.sum_range_succ']
      simp only [mtSignedSourceErrorLayerAF]
      rw [sub_eq_add_neg, hshift]
      ring

/-- Pointwise equation (2.15) with the error written as an explicit finite sum of literal signed
layers. -/
theorem matomakiTeravainen_lemma23ii_finite_literal_layers {t : ℕ}
    (data : MTFiniteIterationSourceData t) (α : ℕ → ℂ)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    mtDivisorSiftSum α (data.cutoff j) n =
      ((mtCoefficientAF α *
            mtFiniteIterationMain data.truncation data.block data.cutoff depth j) +
        (mtCoefficientAF α *
            mtFiniteIterationRemainder data.block data.cutoff depth j)) n +
        ∑ layer ∈ Finset.range (depth + 1),
          mtLiteralSignedSourceErrorLayer data (mtCoefficientAF α) layer j n := by
  rw [matomakiTeravainen_lemma23ii_finite_exact data α depth j hn,
    ArithmeticFunction.add_apply, ArithmeticFunction.add_apply,
    mtAccumulatedSourceErrorAF_eq_sum_signedLayers,
    arithmeticFunction_finset_sum_apply]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro layer hlayer
  exact mtSignedSourceErrorLayerAF_apply_eq_literal
    data (mtCoefficientAF α) layer j hn

end

end RHTower.Sieve
