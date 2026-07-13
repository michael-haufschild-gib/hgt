import GaloisForLFunctions.HTGeometry.EvaluationCodimensionFieldCore
import Mathlib.RingTheory.Localization.FractionRing

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- Universal bounded row coefficient formed from an arbitrary coefficient-coordinate family in a
complex algebra. -/
def rowCoefficientPolynomialOf
    {A row κ : Type*} [CommRing A] [Algebra ℂ A]
    (q : ℕ) (z : row → ℂ) (coeff : κ × Fin (q + 1) → A)
    (b : row) (a : κ) : A :=
  ∑ d : Fin (q + 1), algebraMap ℂ A (z b ^ (d : ℕ)) * coeff (a, d)

/-- **Primewise coefficient activity.** If one coordinate of a bounded coefficient family survives
modulo a prime, at most `q` rows can have all row coefficients inside that prime. -/
theorem coefficientPrime_activeRows
    {A row κ : Type} [CommRing A] [Algebra ℂ A]
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (coeff : κ × Fin (q + 1) → A) (p : Ideal A) [p.IsPrime]
    (hprojective : ∃ ad, coeff ad ∉ p) :
    Fintype.card row ≤ q +
      Set.ncard {b | ∃ a, rowCoefficientPolynomialOf q z coeff b a ∉ p} := by
  classical
  let Q := A ⧸ p
  let K := FractionRing Q
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr Ideal.IsPrime.ne_top'
  letI : DecidableEq K := Classical.decEq K
  let φ : A →+* K := (algebraMap Q K).comp (Ideal.Quotient.mk p)
  let ψ : ℂ →+* K := φ.comp (algebraMap ℂ A)
  letI : Algebra ℂ K := ψ.toAlgebra
  let c : κ × Fin (q + 1) → K := fun ad => φ (coeff ad)
  let zK : row → K := fun b => ψ (z b)
  have hφker : ∀ r : A, φ r = 0 ↔ r ∈ p := by
    intro r
    change algebraMap Q K (Ideal.Quotient.mk p r) = 0 ↔ r ∈ p
    constructor
    · intro h
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply IsFractionRing.injective Q K
      simpa using h
    · intro hr
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  have hc : c ≠ 0 := by
    obtain ⟨ad, had⟩ := hprojective
    intro hzero
    have : c ad = 0 := by rw [hzero]; rfl
    exact had ((hφker (coeff ad)).mp this)
  have hzK : Function.Injective zK := by
    intro b₁ b₂ h
    apply hz
    exact ψ.injective h
  have hcount := card_rows_some_boundedCoefficientPolynomialOver_nonzero
    q zK hzK c hc
  have hpred : ∀ b,
      (∃ a, ∑ d, c (a, d) * zK b ^ (d : ℕ) ≠ 0) ↔
      (∃ a, rowCoefficientPolynomialOf q z coeff b a ∉ p) := by
    intro b
    apply exists_congr
    intro a
    have heval : (∑ d, c (a, d) * zK b ^ (d : ℕ)) =
        φ (rowCoefficientPolynomialOf q z coeff b a) := by
      rw [rowCoefficientPolynomialOf]
      change (∑ d : Fin (q + 1), φ (coeff (a, d)) * ψ (z b) ^ (d : ℕ)) =
        φ (∑ d : Fin (q + 1),
          algebraMap ℂ A (z b ^ (d : ℕ)) * coeff (a, d))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [map_mul]
      change φ (coeff (a, d)) * ψ (z b) ^ (d : ℕ) =
        ψ (z b ^ (d : ℕ)) * φ (coeff (a, d))
      rw [map_pow, mul_comm]
    rw [heval, ← hφker (rowCoefficientPolynomialOf q z coeff b a)]
  have hcard :
      (Finset.univ.filter fun b =>
        ∃ a, ∑ d, c (a, d) * zK b ^ (d : ℕ) ≠ 0).card =
      Set.ncard {b | ∃ a, rowCoefficientPolynomialOf q z coeff b a ∉ p} := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq]
    exact hpred b
  rw [hcard] at hcount
  exact hcount

end
end GaloisForLFunctions.HTGeometry
