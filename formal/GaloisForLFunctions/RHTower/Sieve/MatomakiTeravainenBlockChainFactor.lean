import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenUpperAdicConvolution
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayerChains

/-!
# Fixed-chain convolution factors

The repaired main layers are sums over strict active block chains.  This file records their exact
sign, finite block product, and no-duplicate index geometry for later Type-II splitting.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Unsigned convolution product attached to a block-index list. -/
def mtUnsignedBlockChainAF {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ) :
    List (Fin t) → ArithmeticFunction ℂ
  | [] => T
  | i :: chain => mtPrimeBlockAF (block i) * mtUnsignedBlockChainAF T block chain

/-- Finite convolution product over a set of block indices. -/
def mtPrimeBlockFamilyAF {t : ℕ}
    (block : Fin t → Finset ℕ) (I : Finset (Fin t)) : ArithmeticFunction ℂ :=
  ∏ i ∈ I, mtPrimeBlockAF (block i)

/-- Every index in an active chain lies below its recursion cutoff. -/
theorem mem_activeBlockChain_lt {t depth : ℕ}
    {block : Fin t → Finset ℕ} {j : Fin (t + 1)}
    {chain : List (Fin t)} (hchain : chain ∈ mtActiveBlockChains block depth j) :
    ∀ i ∈ chain, i.1 < j.1 := by
  induction depth generalizing j chain with
  | zero =>
      simp [mtActiveBlockChains] at hchain
      subst chain
      simp
  | succ depth ih =>
      rw [mtActiveBlockChains] at hchain
      obtain ⟨head, hhead, tail, htail, rfl⟩ := by
        simpa only [Finset.mem_biUnion, Finset.mem_image] using hchain
      intro i hi
      rw [List.mem_cons] at hi
      have hheadLt : head.1 < j.1 := by
        exact mem_mtBlockPrefix.mp (Finset.mem_filter.mp hhead).1
      rcases hi with rfl | hi
      · exact hheadLt
      · exact (ih htail i hi).trans hheadLt

/-- Strict active block chains contain no repeated block index. -/
theorem activeBlockChain_nodup {t depth : ℕ}
    {block : Fin t → Finset ℕ} {j : Fin (t + 1)}
    {chain : List (Fin t)} (hchain : chain ∈ mtActiveBlockChains block depth j) :
    chain.Nodup := by
  induction depth generalizing j chain with
  | zero =>
      simp [mtActiveBlockChains] at hchain
      subst chain
      simp
  | succ depth ih =>
      rw [mtActiveBlockChains] at hchain
      obtain ⟨head, hhead, tail, htail, rfl⟩ := by
        simpa only [Finset.mem_biUnion, Finset.mem_image] using hchain
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have hlt := mem_activeBlockChain_lt htail head hmem
        simp at hlt
      · exact ih htail

/-- Recursive chain sign is the scalar `(-1)^length` times its unsigned product. -/
theorem mtSignedBlockChainAF_eq_sign_smul {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (chain : List (Fin t)) :
    mtSignedBlockChainAF T block chain =
      ((-1 : ℂ) ^ chain.length) • mtUnsignedBlockChainAF T block chain := by
  induction chain with
  | nil => simp [mtSignedBlockChainAF, mtUnsignedBlockChainAF]
  | cons i tail ih =>
      rw [mtSignedBlockChainAF, mtUnsignedBlockChainAF, ih]
      simp only [List.length_cons]
      rw [pow_succ]
      ext n
      simp [ArithmeticFunction.mul_apply]

/-- For a no-duplicate chain, list convolution equals the corresponding finite-set product. -/
theorem mtUnsignedBlockChainAF_eq_family_mul {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    {chain : List (Fin t)} (hchain : chain.Nodup) :
    mtUnsignedBlockChainAF T block chain =
      mtPrimeBlockFamilyAF block chain.toFinset * T := by
  induction chain with
  | nil => simp [mtUnsignedBlockChainAF, mtPrimeBlockFamilyAF]
  | cons i tail ih =>
      rw [List.nodup_cons] at hchain
      rw [mtUnsignedBlockChainAF, ih hchain.2]
      simp [mtPrimeBlockFamilyAF, hchain.1, mul_assoc]

/-- A selected block subset factors exactly from the full chain product. -/
theorem mtPrimeBlockFamilyAF_split {t : ℕ}
    (block : Fin t → Finset ℕ) {I S : Finset (Fin t)} (hIS : I ⊆ S) :
    mtPrimeBlockFamilyAF block S =
      mtPrimeBlockFamilyAF block I * mtPrimeBlockFamilyAF block (S \ I) := by
  classical
  unfold mtPrimeBlockFamilyAF
  have h := Finset.prod_sdiff (f := fun i => mtPrimeBlockAF (block i)) hIS
  simpa only [mul_comm] using h.symm

/-- One fixed-chain, fixed-`e`, fixed-cofactor adic box. -/
def mtBlockChainAdicBoxAF {t : ℕ}
    (α : ℕ → ℂ) (block : Fin t → Finset ℕ) (chain : List (Fin t))
    (z D : ℕ) (δ : ℝ) (i j : ℕ) : ArithmeticFunction ℂ :=
  ((mtCoefficientAF α * mtPrimeBlockFamilyAF block chain.toFinset) *
      mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ i) *
    mtUpperAdicOneAF δ j

/-- Same box with the exact alternating sign of its main-layer chain. -/
def mtSignedBlockChainAdicBoxAF {t : ℕ}
    (α : ℕ → ℂ) (block : Fin t → Finset ℕ) (chain : List (Fin t))
    (z D : ℕ) (δ : ℝ) (i j : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chain.length) •
    mtBlockChainAdicBoxAF α block chain z D δ i j

/-- Exact fixed-chain box expansion on a finite coefficient window. -/
theorem coefficient_mul_signedBlockChain_apply_eq_sum_adicBoxes
    {t : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (α : ℕ → ℂ) (block : Fin t → Finset ℕ) (chain : List (Fin t))
    (hchain : chain.Nodup) (z D : ℕ)
    {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (mtCoefficientAF α * mtSignedBlockChainAF (mtTruncLegendreAF z D) block chain) n =
      (∑ i ∈ Finset.range (mtUpperAdicIndex δ D + 1),
        ∑ j ∈ Finset.range (mtUpperAdicIndex δ N + 1),
          mtSignedBlockChainAdicBoxAF α block chain z D δ i j) n := by
  have hsupport : ∀ {e : ℕ}, D < e → mtTruncLegendreCoefficient z D e = 0 := by
    intro e he
    simp [mtTruncLegendreCoefficient, not_le_of_gt he]
  rw [mtSignedBlockChainAF_eq_sign_smul,
    mtUnsignedBlockChainAF_eq_family_mul _ _ hchain,
    mtTruncLegendreAF_eq_coefficient_mul_one,
    mtCoefficientAF_eq_sum_upperAdic hδ (mtTruncLegendreCoefficient z D) D hsupport]
  have hunsigned :
      ((mtCoefficientAF α *
        (mtPrimeBlockFamilyAF block chain.toFinset *
          ((∑ i ∈ Finset.range (mtUpperAdicIndex δ D + 1),
              mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ i) *
            mtCoefficientAF (fun _ => 1)))) n) =
        (∑ i ∈ Finset.range (mtUpperAdicIndex δ D + 1),
          ∑ j ∈ Finset.range (mtUpperAdicIndex δ N + 1),
            mtBlockChainAdicBoxAF α block chain z D δ i j) n := by
    calc
      ((mtCoefficientAF α *
          (mtPrimeBlockFamilyAF block chain.toFinset *
            ((∑ i ∈ Finset.range (mtUpperAdicIndex δ D + 1),
                mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ i) *
              mtCoefficientAF (fun _ => 1)))) n) =
          (∑ i ∈ Finset.range (mtUpperAdicIndex δ D + 1),
            ((mtCoefficientAF α * mtPrimeBlockFamilyAF block chain.toFinset) *
              mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ i) *
                mtCoefficientAF (fun _ => 1)) n := by
            congr 1
            rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i ∈ Finset.range (mtUpperAdicIndex δ D + 1),
          ∑ j ∈ Finset.range (mtUpperAdicIndex δ N + 1),
            mtBlockChainAdicBoxAF α block chain z D δ i j) n := by
        rw [arithmeticFunction_finset_sum_apply,
          arithmeticFunction_finset_sum_apply]
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_mtCoefficientAF_one_apply_eq_sum_upperAdic hδ
          ((mtCoefficientAF α * mtPrimeBlockFamilyAF block chain.toFinset) *
            mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ i) hn hnN
  rw [mul_smul_comm]
  change ((-1 : ℂ) ^ chain.length) *
      ((mtCoefficientAF α *
        (mtPrimeBlockFamilyAF block chain.toFinset *
          ((∑ i ∈ Finset.range (mtUpperAdicIndex δ D + 1),
              mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ i) *
            mtCoefficientAF (fun _ => 1)))) n) = _
  rw [hunsigned, arithmeticFunction_finset_sum_apply, Finset.mul_sum]
  rw [arithmeticFunction_finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [arithmeticFunction_finset_sum_apply, Finset.mul_sum]
  rw [arithmeticFunction_finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp [mtSignedBlockChainAdicBoxAF]

end

end RHTower.Sieve
