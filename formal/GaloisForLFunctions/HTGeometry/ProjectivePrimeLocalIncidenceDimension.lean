import GaloisForLFunctions.HTGeometry.ProjectiveCoefficientPrimeActivity
import GaloisForLFunctions.HTGeometry.IteratedUnitCoefficientBlockDimension

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

def projectivePrimeGoodRow
    {row κ : Type} (q : ℕ) (z : row → ℂ)
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) :=
  {b : row // ∃ a, universalRowCoefficientPolynomial q z b a ∉ p}

noncomputable instance projectivePrimeGoodRowFinite
    {row κ : Type} [Finite row] (q : ℕ) (z : row → ℂ)
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) :
    Finite (projectivePrimeGoodRow q z p) :=
  Finite.of_injective Subtype.val Subtype.val_injective

def localizedUniversalRowPolynomial
    {row κ : Type} [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) [p.IsPrime]
    (b : row) : MvPolynomial (Fin n) (Localization.AtPrime p) :=
  ∑ a, MvPolynomial.monomial (exponent a)
    (algebraMap _ (Localization.AtPrime p) (universalRowCoefficientPolynomial q z b a))

@[simp] theorem localizedUniversalRowPolynomial_coeff
    {row κ : Type} [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) [p.IsPrime]
    (b : row) (a : κ) :
    (localizedUniversalRowPolynomial q n z exponent p b).coeff (exponent a) =
      algebraMap _ (Localization.AtPrime p) (universalRowCoefficientPolynomial q z b a) := by
  classical
  rw [localizedUniversalRowPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  simp [hexponent.eq_iff]

def projectivePrimeActiveBlockRing
    {row κ : Type} [Fintype row] [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) [p.IsPrime] :
    CommAlgCat (Localization.AtPrime p) :=
  iteratedUnitCoefficientBlockRing (Localization.AtPrime p)
    (List.ofFn fun i : Fin (Nat.card (projectivePrimeGoodRow q z p)) =>
      localizedUniversalRowPolynomial q n z exponent p
        ((Finite.equivFin (projectivePrimeGoodRow q z p)).symm i).1)

/-- **Projective-prime local incidence dimension.** At every projectively nonzero coefficient
prime, at least `card row - q` active row equations have unit coefficients after localization,
and their fresh-block incidence coordinate ring loses one Krull dimension per active row. -/
theorem projectivePrime_activeBlockRing_krullDim
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) [p.IsPrime]
    (hprojective : ∃ ad, MvPolynomial.X ad ∉ p) :
    Fintype.card row ≤ q + Nat.card (projectivePrimeGoodRow q z p) ∧
      ringKrullDim (projectivePrimeActiveBlockRing q n z exponent p) +
          Nat.card (projectivePrimeGoodRow q z p) ≤
        ringKrullDim (Localization.AtPrime p) +
          Nat.card (projectivePrimeGoodRow q z p) * n := by
  classical
  constructor
  · have hcard : Nat.card (projectivePrimeGoodRow q z p) =
        Set.ncard {b | ∃ a, universalRowCoefficientPolynomial q z b a ∉ p} := by
      exact Nat.card_coe_set_eq _
    rw [hcard]
    exact projectiveCoefficientPrime_activeRows q z hz p hprojective
  · unfold projectivePrimeActiveBlockRing
    let Ps := List.ofFn fun i : Fin (Nat.card (projectivePrimeGoodRow q z p)) =>
      localizedUniversalRowPolynomial q n z exponent p
        ((Finite.equivFin (projectivePrimeGoodRow q z p)).symm i).1
    have hunit : ∀ P ∈ Ps, ∃ m, IsUnit (P.coeff m) := by
      intro P hP
      dsimp [Ps] at hP
      rw [List.mem_ofFn] at hP
      obtain ⟨i, rfl⟩ := hP
      let b : projectivePrimeGoodRow q z p :=
        (Finite.equivFin (projectivePrimeGoodRow q z p)).symm i
      obtain ⟨a, ha⟩ := b.2
      refine ⟨exponent a, ?_⟩
      rw [localizedUniversalRowPolynomial_coeff q n z exponent hexponent]
      exact IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
        ⟨universalRowCoefficientPolynomial q z b.1 a, ha⟩
    have hdim := iteratedUnitCoefficientBlockRing_krullDim_add_length_le Ps hunit
    simpa [Ps] using hdim

end
end GaloisForLFunctions.HTGeometry
