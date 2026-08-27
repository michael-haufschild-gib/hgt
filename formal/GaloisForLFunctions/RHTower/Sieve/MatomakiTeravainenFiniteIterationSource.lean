import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFiniteIteration

/-!
# Source identification for the finite Matomäki--Teräväinen iteration

The abstract residual kernel used by the finite operator iteration is identified here with the
literal `c₁ + c₂ + c₃` error from Lemma 2.3(i).  Thus every accumulated error in the recursion is
an actual source error for the recursively convolved coefficient sequence, not an assumed
analytic remainder.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Sifting level attached to a prime by its unique block.  Outside the block union its value is
irrelevant and fixed to zero. -/
def mtBlockLower {t : ℕ} (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ) (q : ℕ) : ℕ :=
  if h : ∃ i, q ∈ block i then cutoff (Classical.choose h).castSucc else 0

theorem mtBlockLower_eq_of_mem {t : ℕ} (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ)
    (hdisj : ∀ i k, i ≠ k → Disjoint (block i) (block k))
    (i : Fin t) {q : ℕ} (hq : q ∈ block i) :
    mtBlockLower block cutoff q = cutoff i.castSucc := by
  rw [mtBlockLower, dif_pos ⟨i, hq⟩]
  have hchosen : Classical.choose (show ∃ k, q ∈ block k from ⟨i, hq⟩) = i := by
    by_contra hne
    have hqChosen : q ∈ block (Classical.choose
        (show ∃ k, q ∈ block k from ⟨i, hq⟩)) :=
      Classical.choose_spec (show ∃ k, q ∈ block k from ⟨i, hq⟩)
    exact (Finset.disjoint_left.mp
      (hdisj _ i hne)) hqChosen hq
  rw [hchosen]

/-- Exact finite block data required at every recursive cutoff.  Its fields are only finite-set
geometry: they identify each prefix boundary with the literal source block union. -/
structure MTFiniteIterationSourceData (t : ℕ) where
  z₀ : ℕ
  D : ℕ
  block : Fin t → Finset ℕ
  cutoff : Fin (t + 1) → ℕ
  lowerSpill : Fin (t + 1) → Finset ℕ
  upperSpill : Fin (t + 1) → Finset ℕ
  lower : Fin (t + 1) → ℕ → ℕ
  block_prime : ∀ i q, q ∈ block i → q.Prime
  block_lower : ∀ i q, q ∈ block i → z₀ ≤ q
  block_disjoint : ∀ i k, i ≠ k → Disjoint (block i) (block k)
  cutoff_ge : ∀ j, z₀ ≤ cutoff j
  lower_subset : ∀ j, lowerSpill j ⊆ primesIco z₀ (cutoff j)
  spill_disjoint : ∀ j,
    Disjoint (primesIco z₀ (cutoff j) \ lowerSpill j) (upperSpill j)
  prefix_eq : ∀ j,
    mtPrefixBoundaryKernel block cutoff j =
      mtBoundaryKernel
        ((primesIco z₀ (cutoff j) \ lowerSpill j) ∪ upperSpill j) (lower j)

/-- Build source data from pairwise-disjoint prime blocks and the exact prefix-union identity.
The varying sifting level is recovered canonically from block membership. -/
def MTFiniteIterationSourceData.ofPrefixUnion {t : ℕ}
    (z₀ D : ℕ) (block : Fin t → Finset ℕ) (cutoff : Fin (t + 1) → ℕ)
    (lowerSpill upperSpill : Fin (t + 1) → Finset ℕ)
    (hblockPrime : ∀ i q, q ∈ block i → q.Prime)
    (hblockLower : ∀ i q, q ∈ block i → z₀ ≤ q)
    (hblockDisjoint : ∀ i k, i ≠ k → Disjoint (block i) (block k))
    (hcutoff : ∀ j, z₀ ≤ cutoff j)
    (hlower : ∀ j, lowerSpill j ⊆ primesIco z₀ (cutoff j))
    (hspill : ∀ j,
      Disjoint (primesIco z₀ (cutoff j) \ lowerSpill j) (upperSpill j))
    (hunion : ∀ j, (mtBlockPrefix j).biUnion block =
      (primesIco z₀ (cutoff j) \ lowerSpill j) ∪ upperSpill j) :
    MTFiniteIterationSourceData t where
  z₀ := z₀
  D := D
  block := block
  cutoff := cutoff
  lowerSpill := lowerSpill
  upperSpill := upperSpill
  lower := fun _ => mtBlockLower block cutoff
  block_prime := hblockPrime
  block_lower := hblockLower
  block_disjoint := hblockDisjoint
  cutoff_ge := hcutoff
  lower_subset := hlower
  spill_disjoint := hspill
  prefix_eq := by
    intro j
    unfold mtPrefixBoundaryKernel
    apply sum_primeBlock_mul_rho_eq_boundaryKernel_biUnion
    · intro i hi k hk hik
      exact hblockDisjoint i k hik
    · exact hunion j
    · intro i hi q hq
      exact mtBlockLower_eq_of_mem block cutoff hblockDisjoint i hq

/-- Common truncated Legendre operator in every layer of the source iteration. -/
def MTFiniteIterationSourceData.truncation {t : ℕ}
    (data : MTFiniteIterationSourceData t) : ArithmeticFunction ℂ :=
  mtTruncLegendreAF data.z₀ data.D

/-- One abstract iteration error is exactly the literal Lemma 2.3(i) error after convolution by
the current coefficient sequence. -/
theorem mtOneStepErrorKernel_apply_eq_mtLemma23Error
    {t : ℕ} (a : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ) (j : Fin (t + 1))
    (z₀ D : ℕ) (lowerSpill upperSpill : Finset ℕ) (lower : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) (hz : z₀ ≤ cutoff j)
    (hlower : lowerSpill ⊆ primesIco z₀ (cutoff j))
    (hdisj : Disjoint (primesIco z₀ (cutoff j) \ lowerSpill) upperSpill)
    (hprefix : mtPrefixBoundaryKernel block cutoff j =
      mtBoundaryKernel
        ((primesIco z₀ (cutoff j) \ lowerSpill) ∪ upperSpill) lower) :
    (a * mtOneStepErrorKernel (mtTruncLegendreAF z₀ D) block cutoff j) n =
      mtLemma23Error (fun m => a m) z₀ D lowerSpill upperSpill
        (primesIco z₀ (cutoff j)) lower n := by
  have hexact := matomakiTeravainen_lemma23i_exact_with_error
    (fun m => a m) (D := D) hn hz lowerSpill upperSpill lower hlower hdisj
  change mtDivisorSiftSum (fun m => a m) (cutoff j) n =
      mtDivisorTruncSum (fun m => a m) z₀ D n -
        mtC2BoundaryCoefficient (fun m => a m)
          ((primesIco z₀ (cutoff j) \ lowerSpill) ∪ upperSpill) lower n +
        mtLemma23Error (fun m => a m) z₀ D lowerSpill upperSpill
          (primesIco z₀ (cutoff j)) lower n at hexact
  rw [mtDivisorSiftSum_eq_mul_apply _ _ hn,
    mtDivisorTruncSum_eq_mul_apply _ _ _ hn,
    mtC2BoundaryCoefficient_eq_mul_boundaryKernel_apply _ _ _ hn,
    mtCoefficientAF_coe] at hexact
  rw [mtOneStepErrorKernel, hprefix, mul_add, mul_sub]
  change (a * mtRhoAF (cutoff j)) n - (a * mtTruncLegendreAF z₀ D) n +
      (a * mtBoundaryKernel
        ((primesIco z₀ (cutoff j) \ lowerSpill) ∪ upperSpill) lower) n =
    mtLemma23Error (fun m => a m) z₀ D lowerSpill upperSpill
      (primesIco z₀ (cutoff j)) lower n
  linear_combination hexact

/-- One source-data residual evaluated after an arbitrary accumulated coefficient is the literal
`c₁ + c₂ + c₃` error. -/
theorem MTFiniteIterationSourceData.oneStepError_apply {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    (a * mtOneStepErrorKernel data.truncation data.block data.cutoff j) n =
      mtLemma23Error (fun m => a m) data.z₀ data.D
        (data.lowerSpill j) (data.upperSpill j)
        (primesIco data.z₀ (data.cutoff j)) (data.lower j) n := by
  exact mtOneStepErrorKernel_apply_eq_mtLemma23Error
    a data.block data.cutoff j data.z₀ data.D
    (data.lowerSpill j) (data.upperSpill j) (data.lower j) hn
    (data.cutoff_ge j) (data.lower_subset j) (data.spill_disjoint j) (data.prefix_eq j)

/-- Signed accumulated source error through the displayed depth in equation (2.15). -/
def mtAccumulatedSourceErrorAF {t : ℕ} (data : MTFiniteIterationSourceData t) :
    ArithmeticFunction ℂ → ℕ → Fin (t + 1) → ArithmeticFunction ℂ
  | a, 0, j =>
      a * mtOneStepErrorKernel data.truncation data.block data.cutoff j
  | a, depth + 1, j =>
      a * mtOneStepErrorKernel data.truncation data.block data.cutoff j -
        ∑ i ∈ mtBlockPrefix j,
          mtAccumulatedSourceErrorAF data
            (a * mtPrimeBlockAF (data.block i)) depth i.castSucc

/-- Accumulating literal one-step errors commutes exactly with the finite operator iteration. -/
theorem mtAccumulatedSourceErrorAF_eq_mul_iterationError {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j : Fin (t + 1)) :
    mtAccumulatedSourceErrorAF data a depth j =
      a * mtFiniteIterationError data.truncation data.block data.cutoff depth j := by
  induction depth generalizing a j with
  | zero => rfl
  | succ depth ih =>
      simp only [mtAccumulatedSourceErrorAF, mtFiniteIterationError, mul_sub,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih]
      ring

/-- Equation (2.15) with every error layer source-identified. -/
theorem matomakiTeravainen_lemma23ii_finite_operator_exact {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j : Fin (t + 1)) :
    a * mtRhoAF (data.cutoff j) =
      a * mtFiniteIterationMain data.truncation data.block data.cutoff depth j +
        a * mtFiniteIterationRemainder data.block data.cutoff depth j +
        mtAccumulatedSourceErrorAF data a depth j := by
  have h := congrArg (fun F : ArithmeticFunction ℂ => a * F)
    (mtFiniteBuchstabIteration_exact data.truncation data.block data.cutoff depth j)
  rw [mul_add, mul_add] at h
  rw [mtAccumulatedSourceErrorAF_eq_mul_iterationError]
  exact h

/-- Divisor-sum form of finite Lemma 2.3(ii), at one integer `n`. -/
theorem matomakiTeravainen_lemma23ii_finite_exact {t : ℕ}
    (data : MTFiniteIterationSourceData t) (α : ℕ → ℂ)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    mtDivisorSiftSum α (data.cutoff j) n =
      ((mtCoefficientAF α *
            mtFiniteIterationMain data.truncation data.block data.cutoff depth j) +
        (mtCoefficientAF α *
            mtFiniteIterationRemainder data.block data.cutoff depth j) +
        mtAccumulatedSourceErrorAF data (mtCoefficientAF α) depth j) n := by
  rw [mtDivisorSiftSum_eq_mul_apply α (data.cutoff j) hn]
  exact congrArg (fun F : ArithmeticFunction ℂ => F n)
    (matomakiTeravainen_lemma23ii_finite_operator_exact
      data (mtCoefficientAF α) depth j)

/-- Fully expanded finite endpoint when depth reaches total block count. -/
theorem matomakiTeravainen_lemma23ii_full_exact {t : ℕ}
    (data : MTFiniteIterationSourceData t) (α : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mtDivisorSiftSum α (data.cutoff (Fin.last t)) n =
      ((mtCoefficientAF α *
          mtFiniteIterationMain data.truncation data.block data.cutoff t (Fin.last t)) +
        mtAccumulatedSourceErrorAF data (mtCoefficientAF α) t (Fin.last t)) n := by
  rw [matomakiTeravainen_lemma23ii_finite_exact data α t (Fin.last t) hn,
    mtFiniteIterationRemainder_eq_zero_of_index_le data.block data.cutoff t
      (Fin.last t) (by simp), mul_zero, add_zero]

end

end RHTower.Sieve
