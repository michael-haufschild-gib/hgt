import GaloisForLFunctions.HTGeometry.EvaluationCodimensionFieldCore
import Mathlib.RingTheory.Localization.FractionRing

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

set_option synthInstance.maxHeartbeats 200000

/-- Universal bounded coefficient polynomial for one monomial label and one row. -/
def universalRowCoefficientPolynomial
    {row κ : Type*} (q : ℕ) (z : row → ℂ) (b : row) (a : κ) :
    MvPolynomial (κ × Fin (q + 1)) ℂ :=
  ∑ d : Fin (q + 1), MvPolynomial.C (z b ^ (d : ℕ)) * MvPolynomial.X (a, d)

/-- At every projectively nonzero prime of the coefficient ring, at least `card row - q` rows
carry a coefficient polynomial outside that prime. -/
theorem projectiveCoefficientPrime_activeRows
    {row κ : Type} [Fintype row] [DecidableEq row]
    (q : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (p : Ideal (MvPolynomial (κ × Fin (q + 1)) ℂ)) [p.IsPrime]
    (hprojective : ∃ ad, MvPolynomial.X ad ∉ p) :
    Fintype.card row ≤ q +
      Set.ncard {b | ∃ a, universalRowCoefficientPolynomial q z b a ∉ p} := by
  classical
  let A := MvPolynomial (κ × Fin (q + 1)) ℂ
  let Q := A ⧸ p
  let K := FractionRing Q
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr Ideal.IsPrime.ne_top'
  letI : DecidableEq K := Classical.decEq K
  let φ : A →+* K :=
    (algebraMap Q K).comp (Ideal.Quotient.mk p)
  let ψ : ℂ →+* K := φ.comp MvPolynomial.C
  letI : Algebra ℂ K := ψ.toAlgebra
  let c : κ × Fin (q + 1) → K := fun ad => φ (MvPolynomial.X ad)
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
    exact had ((hφker (MvPolynomial.X ad)).mp this)
  have hzK : Function.Injective zK := by
    intro b₁ b₂ h
    apply hz
    exact ψ.injective h
  have hcount := card_rows_some_boundedCoefficientPolynomialOver_nonzero
    q zK hzK c hc
  have hpred : ∀ b,
      (∃ a, ∑ d, c (a, d) * zK b ^ (d : ℕ) ≠ 0) ↔
      (∃ a, universalRowCoefficientPolynomial q z b a ∉ p) := by
    intro b
    apply exists_congr
    intro a
    have heval : (∑ d, c (a, d) * zK b ^ (d : ℕ)) =
        φ (universalRowCoefficientPolynomial q z b a) := by
      change (∑ d : Fin (q + 1),
          φ (MvPolynomial.X (a, d)) * ψ (z b) ^ (d : ℕ)) =
        φ (∑ d : Fin (q + 1),
          MvPolynomial.C (z b ^ (d : ℕ)) * MvPolynomial.X (a, d))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [map_mul]
      change φ (MvPolynomial.X (a, d)) * ψ (z b) ^ (d : ℕ) =
        ψ (z b ^ (d : ℕ)) * φ (MvPolynomial.X (a, d))
      rw [map_pow, mul_comm]
    rw [heval, ← hφker (universalRowCoefficientPolynomial q z b a)]
  have hcard :
      Set.ncard {b | ∃ a, ∑ d, c (a, d) * zK b ^ (d : ℕ) ≠ 0} =
      Set.ncard {b | ∃ a, universalRowCoefficientPolynomial q z b a ∉ p} := by
    congr 1
    ext b
    exact hpred b
  rw [hcard] at hcount
  exact hcount

end
end GaloisForLFunctions.HTGeometry
