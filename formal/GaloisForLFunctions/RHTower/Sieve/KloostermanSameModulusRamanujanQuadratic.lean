import GaloisForLFunctions.RHTower.Sieve.KloostermanDistinctModulusTerminalQuadratic

/-!
# Ramanujan decomposition of the equal-modulus Kloosterman quadratic

The exact equal-modulus interval completion is lifted through modulus weights and source
quadratic forms. Together with terminal distinct-modulus completion, this gives a three-part exact
frontier: Ramanujan main, bounded same-modulus completion remainder, and terminal distinct-modulus
carrier.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Ramanujan main term in one equal-modulus `[1,M]` correlation. -/
def kloostermanSameModulusRamanujanMainTerm
    (M q : ℕ) (n k : ℕ) : ℂ :=
  (((M : ℝ) / ((q + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
    ((q + 1 : ℕ) : ℂ) *
      RHTower.cglRamanujanAdditiveSum
        ⟨q + 1, Nat.succ_pos q⟩
        ((Int.cast (k : ℤ) : ZMod (q + 1)) - Int.cast (n : ℤ))

/-- Equal-modulus Gram contribution from the exact Ramanujan main terms. -/
def kloostermanSameModulusRamanujanGramMain
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) : ℂ :=
  ∑ q ∈ Q, star (w q) *
    (w q * kloostermanSameModulusRamanujanMainTerm M q n k)

/-- Equal-modulus Gram contribution from interval-completion remainders. -/
def kloostermanSameModulusRemainderGram
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) : ℂ :=
  ∑ q ∈ Q, star (w q) *
    (w q * kloostermanIntervalColumnRemainder M (q + 1)
      (Int.cast (n : ℤ)) (Int.cast (k : ℤ)))

/-- Weighted equal-modulus Gram is exactly Ramanujan main plus completion remainder. -/
theorem kloostermanSameModulusGram_Icc_eq_ramanujanMain_add_remainder
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    kloostermanSameModulusGram Q w (Finset.Icc 1 M) n k =
      kloostermanSameModulusRamanujanGramMain M Q w n k +
        kloostermanSameModulusRemainderGram M Q w n k := by
  unfold kloostermanSameModulusGram kloostermanSameModulusRamanujanGramMain
    kloostermanSameModulusRemainderGram
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [kloostermanCrossModulusCorrelation_Icc_same_eq_cglRamanujan_add_remainder]
  unfold kloostermanSameModulusRamanujanMainTerm
  ring

/-- Closed weighted bound for one equal-modulus completion-remainder Gram entry. -/
theorem norm_kloostermanSameModulusRemainderGram_le
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    ‖kloostermanSameModulusRemainderGram M Q w n k‖ ≤
      ∑ q ∈ Q, ‖w q‖ ^ 2 *
        (((q + 1 : ℕ) : ℝ) * Nat.totient (q + 1)) := by
  calc
    ‖kloostermanSameModulusRemainderGram M Q w n k‖ ≤
        ∑ q ∈ Q, ‖star (w q) *
          (w q * kloostermanIntervalColumnRemainder M (q + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ)))‖ := by
      unfold kloostermanSameModulusRemainderGram
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖w q‖ ^ 2 *
          ‖kloostermanIntervalColumnRemainder M (q + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [norm_mul, norm_star, norm_mul]
      ring
    _ ≤ ∑ q ∈ Q, ‖w q‖ ^ 2 *
        (((q + 1 : ℕ) : ℝ) * Nat.totient (q + 1)) := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr
      exact norm_kloostermanCrossModulusCorrelation_Icc_same_remainder_le
        M q (n : ℤ) (k : ℤ)

/-- Source quadratic form of the equal-modulus Ramanujan main. -/
def kloostermanSameModulusRamanujanMainQuadratic
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
    kloostermanSameModulusRamanujanGramMain M Q w n k

/-- Source quadratic form of the equal-modulus completion remainder. -/
def kloostermanSameModulusRemainderQuadratic
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
    kloostermanSameModulusRemainderGram M Q w n k

/-- Source off-diagonal form of the equal-modulus Ramanujan main. -/
def kloostermanSameModulusRamanujanMainOffDiagonal
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B.erase n, b k *
    kloostermanSameModulusRamanujanGramMain M Q w n k

/-- Source off-diagonal form of the equal-modulus completion remainder. -/
def kloostermanSameModulusRemainderOffDiagonal
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B.erase n, b k *
    kloostermanSameModulusRemainderGram M Q w n k

/-- Equal-modulus quadratic splits exactly into Ramanujan main and completion remainder. -/
theorem kloostermanSameModulusGramQuadratic_eq_ramanujanMain_add_remainder
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanSameModulusGramQuadratic M Q w B b =
      kloostermanSameModulusRamanujanMainQuadratic M Q w B b +
        kloostermanSameModulusRemainderQuadratic M Q w B b := by
  unfold kloostermanSameModulusGramQuadratic
    kloostermanSameModulusRamanujanMainQuadratic
    kloostermanSameModulusRemainderQuadratic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← mul_add]
  apply congrArg (star (b n) * ·)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [kloostermanSameModulusGram_Icc_eq_ramanujanMain_add_remainder]
  ring

/-- Equal-modulus source off-diagonal splits exactly into Ramanujan main and completion remainder. -/
theorem kloostermanSameModulusGramOffDiagonal_eq_ramanujanMain_add_remainder
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanSameModulusGramOffDiagonal M Q w B b =
      kloostermanSameModulusRamanujanMainOffDiagonal M Q w B b +
        kloostermanSameModulusRemainderOffDiagonal M Q w B b := by
  unfold kloostermanSameModulusGramOffDiagonal
    kloostermanSameModulusRamanujanMainOffDiagonal
    kloostermanSameModulusRemainderOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← mul_add]
  apply congrArg (star (b n) * ·)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [kloostermanSameModulusGram_Icc_eq_ramanujanMain_add_remainder]
  ring

/-- Transform output energy decomposes into Ramanujan main, same-modulus completion remainder, and
terminal distinct-modulus quadratic forms. -/
theorem ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_ramanujan_add_remainders
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ((∑ m ∈ Finset.Icc 1 M,
      ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ 2 : ℝ) : ℂ) =
      kloostermanSameModulusRamanujanMainQuadratic M Q w B b +
        kloostermanSameModulusRemainderQuadratic M Q w B b +
          kloostermanDistinctModulusTerminalGramQuadratic M Q w B b := by
  rw [ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_sameModulus_add_terminal,
    kloostermanSameModulusGramQuadratic_eq_ramanujanMain_add_remainder]

/-- Existing source off-diagonal decomposes into Ramanujan main, same-modulus completion remainder,
and terminal distinct-modulus off-diagonal forms. -/
theorem kloostermanIntegerKernelGramOffDiagonal_Icc_eq_ramanujan_add_remainders
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanIntegerKernelGramOffDiagonal Q w (Finset.Icc 1 M) B b =
      kloostermanSameModulusRamanujanMainOffDiagonal M Q w B b +
        kloostermanSameModulusRemainderOffDiagonal M Q w B b +
          kloostermanDistinctModulusTerminalGramOffDiagonal M Q w B b := by
  rw [kloostermanIntegerKernelGramOffDiagonal_Icc_eq_sameModulus_add_terminal,
    kloostermanSameModulusGramOffDiagonal_eq_ramanujanMain_add_remainder]

/-- Closed source-weighted bound for the equal-modulus completion-remainder off-diagonal. -/
theorem norm_kloostermanSameModulusRemainderOffDiagonal_le
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanSameModulusRemainderOffDiagonal M Q w B b‖ ≤
      ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n, ‖b k‖ *
        ∑ q ∈ Q, ‖w q‖ ^ 2 *
          (((q + 1 : ℕ) : ℝ) * Nat.totient (q + 1)) := by
  calc
    ‖kloostermanSameModulusRemainderOffDiagonal M Q w B b‖ ≤
        ∑ n ∈ B, ‖star (b n) * ∑ k ∈ B.erase n, b k *
          kloostermanSameModulusRemainderGram M Q w n k‖ := by
      unfold kloostermanSameModulusRemainderOffDiagonal
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ‖∑ k ∈ B.erase n, b k *
          kloostermanSameModulusRemainderGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_star]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n,
          ‖b k * kloostermanSameModulusRemainderGram M Q w n k‖ := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n,
          ‖b k‖ * ‖kloostermanSameModulusRemainderGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n, ‖b k‖ *
        ∑ q ∈ Q, ‖w q‖ ^ 2 *
          (((q + 1 : ℕ) : ℝ) * Nat.totient (q + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr with k hk
      exact norm_kloostermanSameModulusRemainderGram_le M Q w n k

end

end RHTower.Sieve
