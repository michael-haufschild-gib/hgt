import GaloisForLFunctions.HTGeometry.PrimeLocalizedRowRegularity
import GaloisForLFunctions.HTGeometry.ProjectivePrimeLocalIncidenceDimension

/-!
# Projective-prime active-row regular-dimension universality

Every projectively active row equation is the prime localization of one global universal row
polynomial.  Its surviving coefficient makes it a non-zero-divisor after localization, while the
whole active block loses one Krull dimension per row.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators nonZeroDivisors

noncomputable section

/-- Global universal row polynomial before localizing its coefficient ring at a projective prime. -/
def projectiveUniversalRowPolynomial
    {row κ : Type} [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) (b : row) :
    MvPolynomial (Fin n) (MvPolynomial (κ × Fin (q + 1)) ℂ) :=
  ∑ a, MvPolynomial.monomial (exponent a)
    (universalRowCoefficientPolynomial q z b a)

@[simp] theorem projectiveUniversalRowPolynomial_coeff
    {row κ : Type} [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (hexponent : Function.Injective exponent) (b : row) (a : κ) :
    (projectiveUniversalRowPolynomial q n z exponent b).coeff (exponent a) =
      universalRowCoefficientPolynomial q z b a := by
  classical
  rw [projectiveUniversalRowPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  simp [hexponent.eq_iff]

/-- The existing localized row is exactly coefficientwise prime localization of the global row. -/
theorem projectiveUniversalRowPolynomial_localizes
    {row κ : Type} [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) [p.IsPrime]
    (b : row) :
    MvPolynomial.map (algebraMap _ (Localization.AtPrime p))
        (projectiveUniversalRowPolynomial q n z exponent b) =
      localizedUniversalRowPolynomial q n z exponent p b := by
  classical
  simp [projectiveUniversalRowPolynomial, localizedUniversalRowPolynomial]

/-- Every projectively active universal row polynomial becomes a non-zero-divisor at the chosen
coefficient prime. -/
theorem localizedUniversalRowPolynomial_mem_nonZeroDivisors_of_projectivePrimeGoodRow
    {row κ : Type} [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) [p.IsPrime]
    (b : projectivePrimeGoodRow q z p) :
    localizedUniversalRowPolynomial q n z exponent p b.1 ∈
      nonZeroDivisors (MvPolynomial (Fin n) (Localization.AtPrime p)) := by
  obtain ⟨a, ha⟩ := b.2
  rw [← projectiveUniversalRowPolynomial_localizes]
  apply primeLocalized_finMvPolynomial_mem_nonZeroDivisors_of_coeff_not_mem
    p n (projectiveUniversalRowPolynomial q n z exponent b.1) (exponent a)
  rwa [projectiveUniversalRowPolynomial_coeff q n z exponent hexponent]

/-- **Projective active-row regular-dimension law.**  Every active localized equation is regular,
at least `card row - q` rows remain active, and their block incidence ring satisfies the exact
one-dimension-per-row upper bound. -/
theorem projectivePrime_activeRows_regular_and_krullDim
    {row κ : Type} [Fintype row] [DecidableEq row] [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) [p.IsPrime]
    (hprojective : ∃ ad, MvPolynomial.X ad ∉ p) :
    (∀ b : projectivePrimeGoodRow q z p,
      localizedUniversalRowPolynomial q n z exponent p b.1 ∈
        nonZeroDivisors (MvPolynomial (Fin n) (Localization.AtPrime p))) ∧
      Fintype.card row ≤ q + Nat.card (projectivePrimeGoodRow q z p) ∧
      ringKrullDim (projectivePrimeActiveBlockRing q n z exponent p) +
          Nat.card (projectivePrimeGoodRow q z p) ≤
        ringKrullDim (Localization.AtPrime p) +
          Nat.card (projectivePrimeGoodRow q z p) * n := by
  refine ⟨fun b =>
    localizedUniversalRowPolynomial_mem_nonZeroDivisors_of_projectivePrimeGoodRow
      q n z exponent hexponent p b, ?_⟩
  exact projectivePrime_activeBlockRing_krullDim
    q n z hz exponent hexponent p hprojective

end

end GaloisForLFunctions.HTGeometry
