import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockConvolution

/-!
# Finite Buchstab iteration for Matomäki--Teräväinen Lemma 2.3(ii)

For cutoffs `Q₀ < ... < Q_{t-1} < z₁`, write `Bᵢ` for the arithmetic-function
indicator of the `i`th prime block.  The one-step source identity has operator form

`Rⱼ = T - ∑_{i<j} Bᵢ * Rᵢ + Eⱼ`.

The definitions below iterate this identity exactly.  Their recursive sums enumerate precisely
the strictly descending block-index chains in equation (2.15); no infinite series or convergence
argument occurs.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Block indices strictly below cutoff index `j`. -/
def mtBlockPrefix {t : ℕ} (j : Fin (t + 1)) : Finset (Fin t) :=
  Finset.univ.filter (fun i => i.1 < j.1)

@[simp] theorem mem_mtBlockPrefix {t : ℕ} {j : Fin (t + 1)} {i : Fin t} :
    i ∈ mtBlockPrefix j ↔ i.1 < j.1 := by
  simp [mtBlockPrefix]

/-- Sum of the one-prime boundary operators below cutoff `j`. -/
def mtPrefixBoundaryKernel {t : ℕ}
    (block : Fin t → Finset ℕ) (cutoff : Fin (t + 1) → ℕ) (j : Fin (t + 1)) :
    ArithmeticFunction ℂ :=
  ∑ i ∈ mtBlockPrefix j,
    mtPrimeBlockAF (block i) * mtRhoAF (cutoff i.castSucc)

/-- Literal residual kernel in one application of Lemma 2.3(i). -/
def mtOneStepErrorKernel {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ) (j : Fin (t + 1)) : ArithmeticFunction ℂ :=
  mtRhoAF (cutoff j) - T + mtPrefixBoundaryKernel block cutoff j

/-- Alternating finite Legendre part after `depth + 1` displayed layers. -/
def mtFiniteIterationMain {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ) : ℕ → Fin (t + 1) → ArithmeticFunction ℂ
  | 0, _ => T
  | depth + 1, j =>
      T - ∑ i ∈ mtBlockPrefix j,
        mtPrimeBlockAF (block i) *
          mtFiniteIterationMain T block cutoff depth i.castSucc

/-- Unexpanded terminal sifted layer after `depth + 1` chosen blocks. -/
def mtFiniteIterationRemainder {t : ℕ}
    (block : Fin t → Finset ℕ) (cutoff : Fin (t + 1) → ℕ) :
    ℕ → Fin (t + 1) → ArithmeticFunction ℂ
  | 0, j =>
      -(∑ i ∈ mtBlockPrefix j,
        mtPrimeBlockAF (block i) * mtRhoAF (cutoff i.castSucc))
  | depth + 1, j =>
      -(∑ i ∈ mtBlockPrefix j,
        mtPrimeBlockAF (block i) *
          mtFiniteIterationRemainder block cutoff depth i.castSucc)

/-- Accumulated signed sum of the literal one-step errors. -/
def mtFiniteIterationError {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ) : ℕ → Fin (t + 1) → ArithmeticFunction ℂ
  | 0, j => mtOneStepErrorKernel T block cutoff j
  | depth + 1, j =>
      mtOneStepErrorKernel T block cutoff j -
        ∑ i ∈ mtBlockPrefix j,
          mtPrimeBlockAF (block i) *
            mtFiniteIterationError T block cutoff depth i.castSucc

/-- Equation (2.15) as an exact finite arithmetic-function identity at arbitrary depth. -/
theorem mtFiniteBuchstabIteration_exact {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ) (depth : ℕ) (j : Fin (t + 1)) :
    mtRhoAF (cutoff j) =
      mtFiniteIterationMain T block cutoff depth j +
        mtFiniteIterationRemainder block cutoff depth j +
        mtFiniteIterationError T block cutoff depth j := by
  induction depth generalizing j with
  | zero =>
      simp only [mtFiniteIterationMain, mtFiniteIterationRemainder,
        mtFiniteIterationError, mtOneStepErrorKernel, mtPrefixBoundaryKernel]
      ring
  | succ depth ih =>
      have hsplit :
          (∑ i ∈ mtBlockPrefix j,
              mtPrimeBlockAF (block i) * mtRhoAF (cutoff i.castSucc)) =
            (∑ i ∈ mtBlockPrefix j,
              mtPrimeBlockAF (block i) *
                mtFiniteIterationMain T block cutoff depth i.castSucc) +
            (∑ i ∈ mtBlockPrefix j,
              mtPrimeBlockAF (block i) *
                mtFiniteIterationRemainder block cutoff depth i.castSucc) +
            (∑ i ∈ mtBlockPrefix j,
              mtPrimeBlockAF (block i) *
                mtFiniteIterationError T block cutoff depth i.castSucc) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i.castSucc]
        ring
      simp only [mtFiniteIterationMain, mtFiniteIterationRemainder,
        mtFiniteIterationError, mtOneStepErrorKernel, mtPrefixBoundaryKernel]
      rw [hsplit]
      ring

/-- No strictly descending chain below index `j` has more than `j` terms. -/
theorem mtFiniteIterationRemainder_eq_zero_of_index_le {t : ℕ}
    (block : Fin t → Finset ℕ) (cutoff : Fin (t + 1) → ℕ)
    (depth : ℕ) (j : Fin (t + 1)) (hj : j.1 ≤ depth) :
    mtFiniteIterationRemainder block cutoff depth j = 0 := by
  induction depth generalizing j with
  | zero =>
      have hj0 : j.1 = 0 := by omega
      have hempty : mtBlockPrefix j = ∅ := by
        ext i
        simp [mem_mtBlockPrefix, hj0]
      simp [mtFiniteIterationRemainder, hempty]
  | succ depth ih =>
      simp only [mtFiniteIterationRemainder, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro i hi
      rw [mem_mtBlockPrefix] at hi
      have hiDepth : i.1 ≤ depth := by omega
      rw [ih i.castSucc hiDepth, mul_zero]

/-- Fully expanded endpoint: choosing depth equal to total number of blocks kills the remainder. -/
theorem mtFiniteBuchstabIteration_full {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (cutoff : Fin (t + 1) → ℕ) :
    mtRhoAF (cutoff (Fin.last t)) =
      mtFiniteIterationMain T block cutoff t (Fin.last t) +
        mtFiniteIterationError T block cutoff t (Fin.last t) := by
  rw [mtFiniteBuchstabIteration_exact T block cutoff t (Fin.last t),
    mtFiniteIterationRemainder_eq_zero_of_index_le block cutoff t (Fin.last t) (by simp),
    add_zero]

end

end RHTower.Sieve
