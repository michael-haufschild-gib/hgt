import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayers
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFiniteIterationTermination

/-!
# Exact terminal algebra for Matomäki--Teräväinen Lemma 2.3(ii)

At source depth `L = ⌊log N / log z₀⌋`, the remainder vanishes.  Both surviving sums are displayed
as their literal finite signed layers, matching equation (2.15) without recursive shorthand.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Terminal equation (2.15), expanded into the literal `ℓ=0,…,L` main and error layers. -/
theorem matomakiTeravainen_lemma23ii_terminal_all_layers {t : ℕ}
    (data : MTFiniteIterationSourceData t) (α : ℕ → ℂ)
    (j : Fin (t + 1)) {n N : ℕ} (hn : 0 < n)
    (hz₀ : 1 < data.z₀) (hnN : n ≤ N) :
    let L := Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))
    mtDivisorSiftSum α (data.cutoff j) n =
      (∑ layer ∈ Finset.range (L + 1),
          (mtCoefficientAF α *
            mtSignedMainLayerAF data.truncation data.block layer j) n) +
        ∑ layer ∈ Finset.range (L + 1),
          mtLiteralSignedSourceErrorLayer data (mtCoefficientAF α) layer j n := by
  dsimp only
  rw [matomakiTeravainen_lemma23ii_terminal_exact data α j hn hz₀ hnN,
    mtFiniteIterationMain_eq_sum_signedLayers, Finset.mul_sum,
    mtAccumulatedSourceErrorAF_eq_sum_signedLayers]
  rw [ArithmeticFunction.add_apply, arithmeticFunction_finset_sum_apply,
    arithmeticFunction_finset_sum_apply]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro layer hlayer
  exact mtSignedSourceErrorLayerAF_apply_eq_literal
    data (mtCoefficientAF α) layer j hn

end

end RHTower.Sieve
