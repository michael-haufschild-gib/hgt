import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenOuterBoxBoundaryMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedBoxSupport

/-!
# Literal base and one-prime outer box families

The base coefficient is a singleton narrow band at one.  One-prime coefficients are the disjoint
source-restricted blocks of the padded aligned schedule.  Both complete box families have a sharp
`ζ⁴` envelope and the corresponding product-collar square bound.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

def mtBaseOuterAlpha (_ : Fin 1) : ℕ → ℂ := mtUnitCoefficient

def mtBaseOuterScale (delta : ℝ) (_ : Fin 1) : ℝ := (1 + delta)⁻¹

def mtOnePrimeOuterAlpha {u : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (i : Fin u) : ℕ → ℂ :=
  mtFinsetIndicatorCoefficient (mtHarmanSourceBlock endpoint P i)

def mtOnePrimeOuterScale {u : ℕ} (endpoint : ℕ → ℕ) (i : Fin u) : ℝ :=
  mtAdjacentBlockLowerScale endpoint i.1

theorem mtUnitCoefficientAF_scaleSupported
    {delta : ℝ} (hdelta : 0 < delta) :
    MTRealScaleSupported (mtCoefficientAF mtUnitCoefficient)
      ((1 + delta)⁻¹) ((1 + delta) * (1 + delta)⁻¹) := by
  apply mtCoefficientAF_scaleSupported
  intro n hn
  unfold mtUnitCoefficient at hn
  split at hn <;> rename_i h
  · subst n
    have hden : 0 < 1 + delta := by linarith
    refine ⟨by norm_num, ?_, ?_⟩
    · norm_num
      rw [inv_lt_one₀ hden]
      linarith
    · field_simp
      norm_num
  · simp at hn

theorem mtBaseOuterScale_pos {delta : ℝ} (hdelta : 0 < delta) (i : Fin 1) :
    0 < mtBaseOuterScale delta i := by
  unfold mtBaseOuterScale
  exact inv_pos.mpr (by linarith)

theorem mtOnePrimeOuterAlpha_scaleSupported
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 1 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) (i : Fin u) :
    MTRealScaleSupported (mtCoefficientAF (mtOnePrimeOuterAlpha endpoint P i))
      (mtOnePrimeOuterScale endpoint i)
      ((1 + delta) * mtOnePrimeOuterScale endpoint i) := by
  rw [show mtCoefficientAF (mtOnePrimeOuterAlpha endpoint P i) =
      mtPrimeBlockAF (mtHarmanSourceBlock endpoint P i) by
    exact mtCoefficientAF_primeBlockIndicator_eq _]
  intro n hn
  have hs := mtHarmanSourceBlock_scaleSupported hendpoint P i hn
  exact ⟨hs.1, hs.2.1, hs.2.2.trans (hband i.1)⟩

theorem mtOnePrimeOuterScale_pos
    {u : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 2 ≤ endpoint i)
    (i : Fin u) : 0 < mtOnePrimeOuterScale endpoint i := by
  unfold mtOnePrimeOuterScale mtAdjacentBlockLowerScale
  exact_mod_cast (by have := hendpoint i.1; omega : 0 < endpoint i.1 - 1)

theorem sum_norm_mtBaseOuterAlpha_le_zeta
    (n : ℕ) :
    ∑ i ∈ (Finset.univ : Finset (Fin 1)),
        ‖mtCoefficientAF (mtBaseOuterAlpha i) n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 1) n : ℕ) : ℝ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [mtCoefficientAF]
  · simpa [mtBaseOuterAlpha, mtCoefficientAF_apply_of_pos _ hn, hn.ne'] using
      norm_mtUnitCoefficient_le_one n

theorem sum_norm_mtOnePrimeOuterAlpha_le_zeta
    {u : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    {P : Finset ℕ} (_hP : P ⊆ primesIco (endpoint 0) (endpoint u))
    (n : ℕ) :
    ∑ i ∈ (Finset.univ : Finset (Fin u)),
        ‖mtCoefficientAF (mtOnePrimeOuterAlpha endpoint P i) n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 1) n : ℕ) : ℝ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [mtCoefficientAF]
  · rw [show ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 1) n : ℕ) : ℝ) = 1 by
      simp [hn.ne']]
    let fibre := (Finset.univ : Finset (Fin u)).filter fun i =>
      n ∈ mtHarmanSourceBlock endpoint P i
    have hcard : fibre.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi k hk
      have hiSource := (Finset.mem_filter.mp hi).2
      have hkSource := (Finset.mem_filter.mp hk).2
      by_contra hik
      exact (Finset.disjoint_left.mp
        (mtAdjacentPrimeBlock_disjoint endpoint hmono i k hik))
          (Finset.mem_inter.mp hiSource).1 (Finset.mem_inter.mp hkSource).1
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin u)),
          ‖mtCoefficientAF (mtOnePrimeOuterAlpha endpoint P i) n‖ =
        (fibre.card : ℝ) := by
          rw [Finset.card_eq_sum_ones]
          push_cast
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hmem : n ∈ mtHarmanSourceBlock endpoint P i <;>
            simp [mtOnePrimeOuterAlpha, mtCoefficientAF_apply_of_pos _ hn,
              mtFinsetIndicatorCoefficient, hmem]
      _ ≤ 1 := by exact_mod_cast hcard

/-- Base-box product collar, with generalized-divisor order four. -/
theorem sum_normSq_mtBaseBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) (z₀ D recStart : ℕ) {recRoot delta : ℝ}
    (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z₀ D recStart delta recRoot hdelta hz₀ hroot).block)
    (maxDepth : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta + 1))
    (eMax kMax : ℕ) (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 3) ≤ 1 + eta) :
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
        data maxDepth j eMax kMax)
      (mtOuterSeparatedBoxAF mtBaseOuterAlpha data z₀ D delta)
      (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y n‖ ^ 2 ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 4) n : ℝ) ^ 2)) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 4) n : ℝ) ^ 2) := by
  simpa using sum_normSq_mtOuterSeparatedBoxFamily_productBoundary_le_collar_zeta_sq
    A (Finset.univ : Finset (Fin 1)) mtBaseOuterAlpha (mtBaseOuterScale delta)
      z₀ D recStart hdelta hz₀ hroot data hblocks
      (fun i hi => mtUnitCoefficientAF_scaleSupported hdelta)
      (fun i hi => mtBaseOuterScale_pos hdelta i)
      maxDepth j eMax kMax Y eta 1 hY heta hdilation
      sum_norm_mtBaseOuterAlpha_le_zeta

/-- One-prime box product collar, also with generalized-divisor order four. -/
theorem sum_normSq_mtOnePrimeBoxFamily_productBoundary_le_collar_zeta_sq
    {u : ℕ} {delta : ℝ}
    (A : Finset ℕ) (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (hendpoint : ∀ i, 2 ≤ endpoint i) (hmono : Monotone endpoint)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (hP : P ⊆ primesIco (endpoint 0) (endpoint u))
    (z₀ D recStart : ℕ) {recRoot : ℝ} (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z₀ D recStart delta recRoot hdelta hz₀ hroot).block)
    (maxDepth : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta + 1))
    (eMax kMax : ℕ) (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 3) ≤ 1 + eta) :
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin u))
        data maxDepth j eMax kMax)
      (mtOuterSeparatedBoxAF (mtOnePrimeOuterAlpha endpoint P) data z₀ D delta)
      (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpoint) delta recStart) Y n‖ ^ 2 ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 4) n : ℝ) ^ 2)) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 4) n : ℝ) ^ 2) := by
  simpa using sum_normSq_mtOuterSeparatedBoxFamily_productBoundary_le_collar_zeta_sq
    A (Finset.univ : Finset (Fin u)) (mtOnePrimeOuterAlpha endpoint P)
      (mtOnePrimeOuterScale endpoint) z₀ D recStart hdelta hz₀ hroot data hblocks
      (fun i hi => mtOnePrimeOuterAlpha_scaleSupported
        (fun k => (hendpoint k).trans' one_le_two) hband P i)
      (fun i hi => mtOnePrimeOuterScale_pos hendpoint i)
      maxDepth j eMax kMax Y eta 1 hY heta hdilation
      (sum_norm_mtOnePrimeOuterAlpha_le_zeta hmono hP)

end

end RHTower.Sieve
