import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicPolynomial
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# The cusp algebra of actual cubic decay observations

Polynomials in the first decay mode and middle gap belong to the observation
algebra exactly when their outer linear coefficient vanishes. The three decay
modes generate this algebra. Faithful evaluation transfers the presentation to
functions on the physical section, where the middle gap is provably missing.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicCuspAlgebra : Subalgebra ℝ (Polynomial (Polynomial ℝ)) where
  carrier := {P | P.coeff 1=0}
  algebraMap_mem' r := by
    change (Polynomial.C (Polynomial.C r)).coeff 1=0
    simp
  zero_mem' := by simp
  one_mem' := by simp [Polynomial.coeff_one]
  add_mem' {P Q} hP hQ := by
    change P.coeff 1=0 at hP
    change Q.coeff 1=0 at hQ
    change (P+Q).coeff 1=0
    simp [hP,hQ]
  mul_mem' {P Q} hP hQ := by
    change P.coeff 1=0 at hP
    change Q.coeff 1=0 at hQ
    change (P*Q).coeff 1=0
    simp [Polynomial.mul_coeff_one,hP,hQ]

theorem cubicCuspAlgebra_mem (P : Polynomial (Polynomial ℝ)) :
    P ∈ cubicCuspAlgebra ↔ P.coeff 1=0 := Iff.rfl

theorem cubicCuspAlgebra_constant (p : Polynomial ℝ) :
    Polynomial.C p ∈ cubicCuspAlgebra := by
  rw [cubicCuspAlgebra_mem]
  simp

theorem cubicCuspAlgebra_square : (Polynomial.X^(2 : ℕ) : Polynomial (Polynomial ℝ)) ∈ cubicCuspAlgebra := by
  rw [cubicCuspAlgebra_mem]
  simp [Polynomial.coeff_X_pow]

theorem cubicCuspAlgebra_cube : (Polynomial.X^(3 : ℕ) : Polynomial (Polynomial ℝ)) ∈ cubicCuspAlgebra := by
  rw [cubicCuspAlgebra_mem]
  simp [Polynomial.coeff_X_pow]

def cubicCuspGenerators : Set (Polynomial (Polynomial ℝ)) :=
  {Polynomial.C Polynomial.X,Polynomial.X^(2 : ℕ),Polynomial.X^(3 : ℕ)}

theorem cubicCuspAlgebra_adjoin : Algebra.adjoin ℝ cubicCuspGenerators=cubicCuspAlgebra := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro P hP
    rcases hP with rfl | rfl | rfl
    · exact cubicCuspAlgebra_constant _
    · exact cubicCuspAlgebra_square
    · exact cubicCuspAlgebra_cube
  · let S := Algebra.adjoin ℝ cubicCuspGenerators
    have hU : Polynomial.C Polynomial.X ∈ S := Algebra.subset_adjoin (by left; rfl)
    have hV : (Polynomial.X^(2 : ℕ) : Polynomial (Polynomial ℝ)) ∈ S := Algebra.subset_adjoin (by right; left; rfl)
    have hW : (Polynomial.X^(3 : ℕ) : Polynomial (Polynomial ℝ)) ∈ S := Algebra.subset_adjoin (by right; right; rfl)
    have hC : ∀ p : Polynomial ℝ, Polynomial.C p ∈ S := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
      | monomial n r =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow]
        exact S.mul_mem (S.algebraMap_mem r) (S.pow_mem hU n)
    have hX : ∀ n : ℕ, n ≠ 1 → (Polynomial.X^n : Polynomial (Polynomial ℝ)) ∈ S := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn
        by_cases h0 : n=0
        · subst n; simp
        by_cases h2 : n=2
        · simpa [h2] using hV
        by_cases h3 : n=3
        · simpa [h3] using hW
        have hn4 : 4 ≤ n := by omega
        have hn2 : n=(n-2)+2 := by omega
        rw [hn2,pow_add]
        exact S.mul_mem (ih (n-2) (by omega) (by omega)) hV
    intro P hP
    change P ∈ S
    rw [← Polynomial.sum_monomial_eq P,Polynomial.sum_def]
    apply S.sum_mem
    intro n hn
    have hn1 : n ≠ 1 := by
      intro he
      subst n
      exact (Polynomial.mem_support_iff.mp hn) hP
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    exact S.mul_mem (hC _) (hX n hn1)

def cubicDecayObservationAlgebra : Subalgebra ℝ (cubicProbeSection → ℝ) :=
  Algebra.adjoin ℝ { (fun g => cubicDecayMode 0 g.val),
    (fun g => cubicDecayMode 1 g.val), (fun g => cubicDecayMode 2 g.val) }

theorem cubicDecayObservationAlgebra_presentation :
    cubicCuspAlgebra.map cubicPolynomialObservation=cubicDecayObservationAlgebra := by
  rw [← cubicCuspAlgebra_adjoin,AlgHom.map_adjoin]
  simp only [cubicCuspGenerators,Set.image_insert_eq,Set.image_singleton,
    cubicPolynomialObservation_firstMode,cubicPolynomialObservation_secondMode,
    cubicPolynomialObservation_thirdMode,cubicDecayObservationAlgebra]

theorem cubicCuspAlgebra_missingMiddle : (Polynomial.X : Polynomial (Polynomial ℝ)) ∉ cubicCuspAlgebra := by
  rw [cubicCuspAlgebra_mem]
  simp

theorem cubicDecayObservationAlgebra_missingMiddle :
    (fun g : cubicProbeSection => g.val 2) ∉ cubicDecayObservationAlgebra := by
  rw [← cubicDecayObservationAlgebra_presentation,← cubicPolynomialObservation_middle]
  rintro ⟨P,hP,hEq⟩
  have hPX := cubicPolynomialObservation_injective hEq
  exact cubicCuspAlgebra_missingMiddle (hPX ▸ hP)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
