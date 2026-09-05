import GaloisForLFunctions.HTGeometry.PolynomialRootBudget
import GaloisForLFunctions.RHTower.PrimeArchMomentRootBudgetEscape
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion

/-!
# Completed prime--Gamma polynomial root certificates

The source certificates use only fixed finite linear combinations of the literal completed
prime--Gamma moments. Unconditionally, either one finite Hankel form is negative or these
certificates increase without bound. The proof derives RH internally only in the positive
Hankel branch, identifies all reciprocal Xi singular values with multiplicity, and uses their
sharp nonsummability. It does not choose a branch and is not a proof or disproof of RH.

Every proposed approximate contractive positive-root model obeys an explicit finite
coefficient-error budget. The generic polynomial approximation is classical; the arithmetic
alternative preserves the source definition and both reflection copies.
-/

open Filter Topology ContinuousLinearMap
open scoped BigOperators
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

/-- A fixed finite linear probe of literal completed prime--Gamma moments. -/
def primeArchRootMomentCertificate (n : ℕ) : ℝ :=
  rootMomentCertificate n normalizedPrimeArchMoment

/-- An unconditional arithmetic alternative: a finite negative Hankel form, or monotone
unbounded polynomial root certificates. Neither branch is assumed or selected. -/
theorem primeArch_negative_hankel_or_rootBudget_escape :
    (∃ N : ℕ, ∃ v : Fin N → ℝ,
      (∑ i : Fin N, ∑ j : Fin N,
        v i * v j * normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ))) < 0) ∨
    (Monotone primeArchRootMomentCertificate ∧
      Tendsto primeArchRootMomentCertificate atTop atTop) := by
  by_cases hc : CompleteHankelCone normalizedPrimeArchMoment
  · right
    have hRH := completeHankelCone_normalizedPrimeArchMoment_iff_riemannHypothesis.mp hc
    let a : ℕ → ℝ := approxNumber xiOrderedSignedPrimeOperator
    have ha0 : ∀ k, 0 ≤ a k := approxNumber_nonneg _
    have haa : Antitone a := approxNumber_antitone _
    have hasq : Summable (fun k => a k ^ 2) := by
      simpa only [a, MemSchattenClass, Real.rpow_two] using
        xiOrderedSignedPrimeOperator_memSchattenClass_two
    have hm (r : ℕ) : (∑' k, (a k ^ 2) ^ (r + 1)) = normalizedPrimeArchMoment r := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_tsum]
      simpa only [a, Complex.ofReal_pow] using
        (normalizedPrimeArchMoment_eq_orderedXi_approxNumber_moments_of_rh hRH r).symm
    have ha1 : ∀ k, a k ≤ 1 := by
      intro k
      have hsum : (∑' j, a j ^ 2) = normalizedPrimeArchMoment 0 := by
        simpa using hm 0
      have hk := hasq.le_tsum k (fun j _ => sq_nonneg (a j))
      rw [hsum] at hk
      nlinarith [normalizedPrimeArchMoment_zero_lt_one, ha0 k]
    have hns : ¬ Summable a := by
      intro hs
      apply xiOrderedSignedPrimeOperator_not_memSchattenClass_one
      exact hs.congr fun _ => (Real.rpow_one _).symm
    have he (n : ℕ) : primeArchRootMomentCertificate n =
        ∑' k, rootBudgetResponse n (a k) := by
      rw [primeArchRootMomentCertificate, ← (show
        (fun r => ∑' k, (a k ^ 2) ^ (r + 1)) = normalizedPrimeArchMoment from funext hm)]
      exact rootMomentCertificate_eq_tsum hasq ha0 haa n
    constructor
    · intro n m hnm
      rw [he n, he m]
      exact (summable_rootBudgetResponse hasq ha0 ha1 n).tsum_le_tsum
        (fun k => rootBudgetResponse_monotone (ha0 k) (ha1 k) hnm)
        (summable_rootBudgetResponse hasq ha0 ha1 m)
    · have ht := tendsto_rootBudgetResponse_atTop_of_not_summable hasq ha0 ha1 hns
      exact ht.congr (fun n => (he n).symm)
  · left
    unfold CompleteHankelCone at hc
    push Not at hc
    exact hc

/-- Every prescribed root ceiling has a finite source certificate of one of two explicit
forms. This sharpens a coordinate-gap existence statement to fixed polynomial probes. -/
theorem exists_primeArch_finite_rootBudget_certificate (C : ℝ) :
    (∃ N : ℕ, ∃ v : Fin N → ℝ,
      (∑ i : Fin N, ∑ j : Fin N,
        v i * v j * normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ))) < 0) ∨
    ∃ n : ℕ, C < primeArchRootMomentCertificate n := by
  rcases primeArch_negative_hankel_or_rootBudget_escape with hn | hp
  · exact Or.inl hn
  · right
    obtain ⟨n, hn⟩ := ((tendsto_atTop.1 hp.2) (C + 1)).exists
    exact ⟨n, by linarith⟩

/-- Any approximate positive root realization pays for its actual finite coefficient
errors. This is a universal inequality, not an assumed arithmetic landing. -/
theorem primeArchRootMomentCertificate_le_cost_add_error {a : ℕ → ℝ}
    (ha : Summable a) (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    (haa : Antitone a) (n : ℕ) :
    primeArchRootMomentCertificate n ≤ (∑' k, a k) +
      ∑ r ∈ Finset.range ((rootBudgetQuotient n).natDegree + 1),
        |(rootBudgetQuotient n).coeff r| *
          |normalizedPrimeArchMoment r - ∑' k, (a k ^ 2) ^ (r + 1)| :=
  rootMomentCertificate_le_rootBudget_add_error ha ha0 ha1 haa n normalizedPrimeArchMoment

end RHTower
