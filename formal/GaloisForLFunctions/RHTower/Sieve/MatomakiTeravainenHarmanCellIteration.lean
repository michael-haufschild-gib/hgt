import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCellConvolution
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedSchedule

/-!
# Repaired terminal iteration for exact Harman cells

Disjoint prime blocks make every pair- and triple-cell coefficient uniformly bounded by one.
The repaired Lemma 2.3(ii) therefore applies without a hidden divisor-envelope premise, and the
cell convolution identities identify its input with the literal nested Harman sums.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

/-- Exact repaired terminal expansion for any two disjoint prime blocks. -/
theorem eventually_exists_mtHarmanPairCell_terminalExpansion
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (z₁ Y : ℕ) (S₁ S₂ : Finset ℕ),
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      Disjoint S₁ S₂ →
      (∀ q ∈ S₁, q.Prime) → (∀ q ∈ S₂, q.Prime) →
      ∃ (data : MTFiniteIterationSourceData (z₁ - mtLowerCutoffNat X)),
        ∃ _cert : MTGridFreePaperScaleCertificate data A X,
          data.cutoff (Fin.last (z₁ - mtLowerCutoffNat X)) = z₁ ∧
          (let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
           ∀ n ∈ Finset.Icc 1 Y,
            mtHarmanPairCellSiftSum S₁ S₂ z₁ n =
              ((mtCoefficientAF (mtHarmanPairCellCoefficient S₁ S₂) *
                  mtFiniteIterationMain data.truncation data.block data.cutoff J
                    (Fin.last (z₁ - mtLowerCutoffNat X))) +
                mtAccumulatedSourceErrorAF data
                  (mtCoefficientAF (mtHarmanPairCellCoefficient S₁ S₂)) J
                  (Fin.last (z₁ - mtLowerCutoffNat X))) n) ∧
          (let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
           ∑ n ∈ Finset.Icc 1 Y,
              ‖mtAccumulatedSourceErrorAF data
                (mtCoefficientAF (mtHarmanPairCellCoefficient S₁ S₂)) J
                (Fin.last (z₁ - mtLowerCutoffNat X)) n‖ ^ 2 ≤
            15 * (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ))) := by
  filter_upwards [eventually_exists_matomakiTeravainen_lemma23ii_repaired A hA]
    with X hrepairX
  intro z₁ Y S₁ S₂ hz hzX hY hYX hdisjoint hprime₁ hprime₂
  have hcoeff : ∀ {m : ℕ}, 0 < m →
      ‖mtHarmanPairCellCoefficient S₁ S₂ m‖ ≤ (1 : ℝ) := by
    intro m hm
    exact norm_mtHarmanPairCellCoefficient_le_one_of_disjoint
      hdisjoint hprime₁ hprime₂ m
  obtain ⟨data, cert, hroot, hexact, herror⟩ :=
    hrepairX z₁ Y (mtHarmanPairCellCoefficient S₁ S₂) 1
      hz hzX hY hYX (by norm_num) hcoeff
  refine ⟨data, cert, hroot, ?_, ?_⟩
  · dsimp only at hexact ⊢
    intro n hn
    rw [mtHarmanPairCellSiftSum_eq_divisorSiftSum S₁ S₂ z₁
      (by rw [Finset.mem_Icc] at hn; omega)]
    exact hexact n hn
  · simpa only [one_pow, mul_one] using herror

/-- Exact repaired terminal expansion for any three pairwise-disjoint prime blocks. -/
theorem eventually_exists_mtHarmanTripleCell_terminalExpansion
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (z₁ Y : ℕ) (S₁ S₂ S₃ : Finset ℕ),
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      Disjoint S₁ S₂ → Disjoint S₁ S₃ → Disjoint S₂ S₃ →
      (∀ q ∈ S₁, q.Prime) → (∀ q ∈ S₂, q.Prime) →
      (∀ q ∈ S₃, q.Prime) →
      ∃ (data : MTFiniteIterationSourceData (z₁ - mtLowerCutoffNat X)),
        ∃ _cert : MTGridFreePaperScaleCertificate data A X,
          data.cutoff (Fin.last (z₁ - mtLowerCutoffNat X)) = z₁ ∧
          (let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
           ∀ n ∈ Finset.Icc 1 Y,
            mtHarmanTripleCellSiftSum S₁ S₂ S₃ z₁ n =
              ((mtCoefficientAF (mtHarmanTripleCellCoefficient S₁ S₂ S₃) *
                  mtFiniteIterationMain data.truncation data.block data.cutoff J
                    (Fin.last (z₁ - mtLowerCutoffNat X))) +
                mtAccumulatedSourceErrorAF data
                  (mtCoefficientAF (mtHarmanTripleCellCoefficient S₁ S₂ S₃)) J
                  (Fin.last (z₁ - mtLowerCutoffNat X))) n) ∧
          (let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
           ∑ n ∈ Finset.Icc 1 Y,
              ‖mtAccumulatedSourceErrorAF data
                (mtCoefficientAF (mtHarmanTripleCellCoefficient S₁ S₂ S₃)) J
                (Fin.last (z₁ - mtLowerCutoffNat X)) n‖ ^ 2 ≤
            15 * (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ))) := by
  filter_upwards [eventually_exists_matomakiTeravainen_lemma23ii_repaired A hA]
    with X hrepairX
  intro z₁ Y S₁ S₂ S₃ hz hzX hY hYX hdisjoint₁₂ hdisjoint₁₃ hdisjoint₂₃
    hprime₁ hprime₂ hprime₃
  have hcoeff : ∀ {m : ℕ}, 0 < m →
      ‖mtHarmanTripleCellCoefficient S₁ S₂ S₃ m‖ ≤ (1 : ℝ) := by
    intro m hm
    exact norm_mtHarmanTripleCellCoefficient_le_one_of_pairwise_disjoint
      hdisjoint₁₂ hdisjoint₁₃ hdisjoint₂₃ hprime₁ hprime₂ hprime₃ m
  obtain ⟨data, cert, hroot, hexact, herror⟩ :=
    hrepairX z₁ Y (mtHarmanTripleCellCoefficient S₁ S₂ S₃) 1
      hz hzX hY hYX (by norm_num) hcoeff
  refine ⟨data, cert, hroot, ?_, ?_⟩
  · dsimp only at hexact ⊢
    intro n hn
    rw [mtHarmanTripleCellSiftSum_eq_divisorSiftSum S₁ S₂ S₃ z₁
      (by rw [Finset.mem_Icc] at hn; omega)]
    exact hexact n hn
  · simpa only [one_pow, mul_one] using herror

end

end RHTower.Sieve
