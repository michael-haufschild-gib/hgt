import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealScaleSupport

/-!
# Scale support and divisor bounds for one block-chain long factor

This is the first factor in each fixed Harman box: an initial cell coefficient, every recursive
prime block, and one truncated-Moebius adic block.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem list_prod_map_nonneg
    {α : Type*} (Q : α → ℝ) (hQ : ∀ i, 0 ≤ Q i) (chain : List α) :
    0 ≤ (chain.map Q).prod := by
  induction chain with
  | nil => simp
  | cons i tail ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (hQ i) ih

theorem list_prod_map_eq_toFinset_prod
    {α : Type*} [DecidableEq α] (Q : α → ℝ)
    {chain : List α} (hchain : chain.Nodup) :
    (chain.map Q).prod = ∏ i ∈ chain.toFinset, Q i := by
  induction chain with
  | nil => simp
  | cons i tail ih =>
      rw [List.nodup_cons] at hchain
      simp [hchain.1, ih hchain.2]

theorem mtCoefficientAF_scaleSupported
    {alpha : ℕ → ℂ} {L U : ℝ}
    (halpha : ∀ {n : ℕ}, alpha n ≠ 0 → 0 < n ∧ L < (n : ℝ) ∧ (n : ℝ) ≤ U) :
    MTRealScaleSupported (mtCoefficientAF alpha) L U := by
  intro n hn
  have hnPos : 0 < n := by
    by_contra h
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    simp [mtCoefficientAF] at hn
  rw [mtCoefficientAF_apply_of_pos _ hnPos] at hn
  exact halpha hn

theorem mtCoefficientAF_polynomialDivisorBounded
    {alpha : ℕ → ℂ} (halpha : MTPolynomialDivisorBounded alpha) :
    MTPolynomialDivisorBounded (fun n => mtCoefficientAF alpha n) := by
  obtain ⟨C, hC, K, hbound⟩ := halpha
  refine ⟨C, hC, K, ?_⟩
  intro n hn
  change ‖mtCoefficientAF alpha n‖ ≤ C * (n.divisors.card : ℝ) ^ K
  rw [mtCoefficientAF_apply_of_pos _ hn]
  exact hbound hn

theorem mtRealIntervalAF_polynomialDivisorBounded
    {alpha : ℕ → ℂ} (halpha : MTPolynomialDivisorBounded alpha) (L U : ℝ) :
    MTPolynomialDivisorBounded (fun n => mtRealIntervalAF alpha L U n) := by
  obtain ⟨C, hC, K, hbound⟩ := halpha
  refine ⟨C, hC, K, ?_⟩
  intro n hn
  change ‖mtRealIntervalAF alpha L U n‖ ≤ C * (n.divisors.card : ℝ) ^ K
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hn]
  split
  · exact hbound hn
  · simp [mul_nonneg hC (by positivity : 0 ≤ (n.divisors.card : ℝ) ^ K)]

theorem mtPrimeBlockAF_polynomialDivisorBounded (S : Finset ℕ) :
    MTPolynomialDivisorBounded (fun n => mtPrimeBlockAF S n) := by
  refine ⟨1, by norm_num, 0, ?_⟩
  intro n hn
  change ‖mtPrimeBlockAF S n‖ ≤ 1 * (n.divisors.card : ℝ) ^ 0
  rw [mtPrimeBlockAF_apply_of_pos S hn]
  by_cases hmem : n ∈ S <;> simp [hmem]

/-- Initial coefficient convolved with every prime block in a list. -/
def mtBlockChainCoefficientAF {t : ℕ}
    (alpha : ℕ → ℂ) (block : Fin t → Finset ℕ) (chain : List (Fin t)) :
    ArithmeticFunction ℂ :=
  mtCoefficientAF alpha * mtPrimeBlockFamilyAF block chain.toFinset

theorem mtBlockChainCoefficientAF_eq_unsigned
    {t : ℕ} (alpha : ℕ → ℂ) (block : Fin t → Finset ℕ)
    {chain : List (Fin t)} (hchain : chain.Nodup) :
    mtBlockChainCoefficientAF alpha block chain =
      mtUnsignedBlockChainAF (mtCoefficientAF alpha) block chain := by
  rw [mtBlockChainCoefficientAF,
    mtUnsignedBlockChainAF_eq_family_mul _ _ hchain, mul_comm]

theorem mtUnsignedBlockChainAF_scaleSupported
    {t : ℕ} {alpha : ℕ → ℂ} {block : Fin t → Finset ℕ}
    {Q U : Fin t → ℝ} {Lalpha Ualpha : ℝ}
    (halpha : MTRealScaleSupported (mtCoefficientAF alpha) Lalpha Ualpha)
    (hblock : ∀ i, MTRealScaleSupported (mtPrimeBlockAF (block i)) (Q i) (U i))
    (hQ : ∀ i, 0 ≤ Q i) (hLalpha : 0 ≤ Lalpha)
    (chain : List (Fin t)) :
    MTRealScaleSupported
      (mtUnsignedBlockChainAF (mtCoefficientAF alpha) block chain)
      (Lalpha * (chain.map Q).prod) (Ualpha * (chain.map U).prod) := by
  induction chain with
  | nil =>
      intro n hn
      simpa [mtUnsignedBlockChainAF] using halpha hn
  | cons i tail ih =>
      have htailLower : 0 ≤ Lalpha * (tail.map Q).prod :=
        mul_nonneg hLalpha (list_prod_map_nonneg Q hQ tail)
      have hmul : MTRealScaleSupported
          (mtPrimeBlockAF (block i) *
            mtUnsignedBlockChainAF (mtCoefficientAF alpha) block tail)
          (Q i * (Lalpha * (tail.map Q).prod))
          (U i * (Ualpha * (tail.map U).prod)) :=
        MTRealScaleSupported.mul (hblock i) ih (hQ i) htailLower
      intro n hn
      simpa only [mtUnsignedBlockChainAF, List.map_cons, List.prod_cons,
        mul_assoc, mul_left_comm, mul_comm] using hmul hn

theorem mtBlockChainCoefficientAF_scaleSupported
    {t : ℕ} {alpha : ℕ → ℂ} {block : Fin t → Finset ℕ}
    {Q U : Fin t → ℝ} {Lalpha Ualpha : ℝ}
    (halpha : MTRealScaleSupported (mtCoefficientAF alpha) Lalpha Ualpha)
    (hblock : ∀ i, MTRealScaleSupported (mtPrimeBlockAF (block i)) (Q i) (U i))
    (hQ : ∀ i, 0 ≤ Q i) (hLalpha : 0 ≤ Lalpha)
    {chain : List (Fin t)} (hchain : chain.Nodup) :
    MTRealScaleSupported (mtBlockChainCoefficientAF alpha block chain)
      (Lalpha * ∏ i ∈ chain.toFinset, Q i)
      (Ualpha * ∏ i ∈ chain.toFinset, U i) := by
  rw [mtBlockChainCoefficientAF_eq_unsigned alpha block hchain]
  have hsupport : MTRealScaleSupported
      (mtUnsignedBlockChainAF (mtCoefficientAF alpha) block chain)
      (Lalpha * (chain.map Q).prod) (Ualpha * (chain.map U).prod) :=
    mtUnsignedBlockChainAF_scaleSupported halpha hblock hQ hLalpha chain
  intro n hn
  simpa only [list_prod_map_eq_toFinset_prod Q hchain,
    list_prod_map_eq_toFinset_prod U hchain] using hsupport hn

theorem mtUnsignedBlockChainAF_polynomialDivisorBounded
    {t : ℕ} {alpha : ℕ → ℂ} {block : Fin t → Finset ℕ}
    (halpha : MTPolynomialDivisorBounded (fun n => mtCoefficientAF alpha n))
    (chain : List (Fin t)) :
    MTPolynomialDivisorBounded
      (fun n => mtUnsignedBlockChainAF (mtCoefficientAF alpha) block chain n) := by
  induction chain with
  | nil => simpa [mtUnsignedBlockChainAF] using halpha
  | cons i tail ih =>
      simpa only [mtUnsignedBlockChainAF] using
        (mtPrimeBlockAF_polynomialDivisorBounded (block i)).arithmeticFunction_mul ih

theorem mtBlockChainCoefficientAF_polynomialDivisorBounded
    {t : ℕ} {alpha : ℕ → ℂ} {block : Fin t → Finset ℕ}
    (halpha : MTPolynomialDivisorBounded alpha)
    {chain : List (Fin t)} (hchain : chain.Nodup) :
    MTPolynomialDivisorBounded
      (fun n => mtBlockChainCoefficientAF alpha block chain n) := by
  rw [mtBlockChainCoefficientAF_eq_unsigned alpha block hchain]
  exact mtUnsignedBlockChainAF_polynomialDivisorBounded
    (mtCoefficientAF_polynomialDivisorBounded halpha) chain

/-- Long coefficient factor of one fixed adic block-chain box. -/
def mtBlockChainLongAF {t : ℕ}
    (alpha : ℕ → ℂ) (block : Fin t → Finset ℕ) (chain : List (Fin t))
    (z D : ℕ) (delta : ℝ) (i : ℕ) : ArithmeticFunction ℂ :=
  mtBlockChainCoefficientAF alpha block chain *
    mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) delta i

theorem mtBlockChainLongAF_scaleSupported
    {t : ℕ} {alpha : ℕ → ℂ} {block : Fin t → Finset ℕ}
    {Q U : Fin t → ℝ} {Lalpha Ualpha delta : ℝ}
    (halpha : MTRealScaleSupported (mtCoefficientAF alpha) Lalpha Ualpha)
    (hblock : ∀ i, MTRealScaleSupported (mtPrimeBlockAF (block i)) (Q i) (U i))
    (hQ : ∀ i, 0 ≤ Q i) (hLalpha : 0 ≤ Lalpha)
    {chain : List (Fin t)} (hchain : chain.Nodup)
    (z D i : ℕ) (hscale : 0 ≤ mtUpperAdicScale delta i) :
    MTRealScaleSupported (mtBlockChainLongAF alpha block chain z D delta i)
      ((Lalpha * ∏ j ∈ chain.toFinset, Q j) * mtUpperAdicScale delta i)
      ((Ualpha * ∏ j ∈ chain.toFinset, U j) *
        ((1 + delta) * mtUpperAdicScale delta i)) := by
  exact MTRealScaleSupported.mul
    (mtBlockChainCoefficientAF_scaleSupported halpha hblock hQ hLalpha hchain)
    (mtRealIntervalAF_scaleSupported _ _ _) (mul_nonneg hLalpha
      (Finset.prod_nonneg fun j hj => hQ j)) hscale

theorem mtBlockChainLongAF_polynomialDivisorBounded
    {t : ℕ} {alpha : ℕ → ℂ} {block : Fin t → Finset ℕ}
    (halpha : MTPolynomialDivisorBounded alpha)
    {chain : List (Fin t)} (hchain : chain.Nodup)
    (z D : ℕ) (delta : ℝ) (i : ℕ) :
    MTPolynomialDivisorBounded
      (fun n => mtBlockChainLongAF alpha block chain z D delta i n) := by
  exact (mtBlockChainCoefficientAF_polynomialDivisorBounded halpha hchain).arithmeticFunction_mul
    (mtRealIntervalAF_polynomialDivisorBounded
      (mtTruncLegendreCoefficient_polynomialDivisorBounded z D)
      (mtUpperAdicScale delta i) ((1 + delta) * mtUpperAdicScale delta i))

end

end RHTower.Sieve
