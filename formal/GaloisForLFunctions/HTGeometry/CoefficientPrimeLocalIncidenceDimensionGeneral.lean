import GaloisForLFunctions.HTGeometry.CoefficientPrimeActivityGeneral
import GaloisForLFunctions.HTGeometry.IteratedUnitCoefficientBlockDimension

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

def coefficientPrimeGoodRow
    {A row κ : Type} [CommRing A] [Algebra ℂ A]
    (q : ℕ) (z : row → ℂ) (coeff : κ × Fin (q + 1) → A) (p : Ideal A) :=
  {b : row // ∃ a, rowCoefficientPolynomialOf q z coeff b a ∉ p}

noncomputable instance coefficientPrimeGoodRowFinite
    {A row κ : Type} [CommRing A] [Algebra ℂ A] [Finite row]
    (q : ℕ) (z : row → ℂ) (coeff : κ × Fin (q + 1) → A) (p : Ideal A) :
    Finite (coefficientPrimeGoodRow q z coeff p) :=
  Finite.of_injective Subtype.val Subtype.val_injective

def localizedCoefficientRowPolynomial
    {A row κ : Type} [CommRing A] [Algebra ℂ A]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (coeff : κ × Fin (q + 1) → A)
    (exponent : κ → (Fin n →₀ ℕ)) (p : Ideal A) [p.IsPrime]
    (b : row) : MvPolynomial (Fin n) (Localization.AtPrime p) :=
  ∑ a, MvPolynomial.monomial (exponent a)
    (algebraMap A (Localization.AtPrime p) (rowCoefficientPolynomialOf q z coeff b a))

@[simp] theorem localizedCoefficientRowPolynomial_coeff
    {A row κ : Type} [CommRing A] [Algebra ℂ A]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (coeff : κ × Fin (q + 1) → A)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal A) [p.IsPrime] (b : row) (a : κ) :
    (localizedCoefficientRowPolynomial q n z coeff exponent p b).coeff (exponent a) =
      algebraMap A (Localization.AtPrime p) (rowCoefficientPolynomialOf q z coeff b a) := by
  classical
  rw [localizedCoefficientRowPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  simp [hexponent.eq_iff]

def coefficientPrimeActiveBlockRing
    {A row κ : Type} [CommRing A] [Algebra ℂ A]
    [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (coeff : κ × Fin (q + 1) → A)
    (exponent : κ → (Fin n →₀ ℕ)) (p : Ideal A) [p.IsPrime] :
    CommAlgCat (Localization.AtPrime p) :=
  iteratedUnitCoefficientBlockRing (Localization.AtPrime p)
    (List.ofFn fun i : Fin (Nat.card (coefficientPrimeGoodRow q z coeff p)) =>
      localizedCoefficientRowPolynomial q n z coeff exponent p
        ((Finite.equivFin (coefficientPrimeGoodRow q z coeff p)).symm i).1)

/-- General local incidence-height law over a prime specialization of an arbitrary complex
coefficient algebra. -/
theorem coefficientPrime_activeBlockRing_krullDim
    {A row κ : Type} [CommRing A] [Algebra ℂ A] [IsNoetherianRing A]
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (coeff : κ × Fin (q + 1) → A)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal A) [p.IsPrime] (hprojective : ∃ ad, coeff ad ∉ p) :
    Fintype.card row ≤ q + Nat.card (coefficientPrimeGoodRow q z coeff p) ∧
      ringKrullDim (coefficientPrimeActiveBlockRing q n z coeff exponent p) +
          Nat.card (coefficientPrimeGoodRow q z coeff p) ≤
        ringKrullDim (Localization.AtPrime p) +
          Nat.card (coefficientPrimeGoodRow q z coeff p) * n := by
  classical
  constructor
  · have hcard : Nat.card (coefficientPrimeGoodRow q z coeff p) =
        Set.ncard {b | ∃ a, rowCoefficientPolynomialOf q z coeff b a ∉ p} :=
      Nat.card_coe_set_eq _
    rw [hcard]
    exact coefficientPrime_activeRows q z hz coeff p hprojective
  · unfold coefficientPrimeActiveBlockRing
    let Ps := List.ofFn fun i : Fin (Nat.card (coefficientPrimeGoodRow q z coeff p)) =>
      localizedCoefficientRowPolynomial q n z coeff exponent p
        ((Finite.equivFin (coefficientPrimeGoodRow q z coeff p)).symm i).1
    have hunit : ∀ P ∈ Ps, ∃ m, IsUnit (P.coeff m) := by
      intro P hP
      dsimp [Ps] at hP
      rw [List.mem_ofFn] at hP
      obtain ⟨i, rfl⟩ := hP
      let b : coefficientPrimeGoodRow q z coeff p :=
        (Finite.equivFin (coefficientPrimeGoodRow q z coeff p)).symm i
      obtain ⟨a, ha⟩ := b.2
      refine ⟨exponent a, ?_⟩
      rw [localizedCoefficientRowPolynomial_coeff q n z coeff exponent hexponent]
      exact IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
        ⟨rowCoefficientPolynomialOf q z coeff b.1 a, ha⟩
    have hdim := iteratedUnitCoefficientBlockRing_krullDim_add_length_le Ps hunit
    simpa [Ps] using hdim

end
end GaloisForLFunctions.HTGeometry
