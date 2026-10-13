import GaloisForLFunctions.HTGeometry.FiniteNodePolynomialIdeal

/-! # Idempotents modulo a finite nodal polynomial -/

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι]

theorem finite_node_polynomial_idempotent_iff_values
    (x : ι → ℝ) (hx : Function.Injective x) (p : Polynomial ℝ) :
    Lagrange.nodal Finset.univ x ∣ p ^ 2 - p ↔
      ∀ i, p.eval (x i) = 0 ∨ p.eval (x i) = 1 := by
  rw [← finite_node_polynomial_eval_zero_iff_dvd x hx (p ^ 2 - p)]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, sub_eq_zero]
  constructor
  · intro h i
    have hmul : p.eval (x i) * (p.eval (x i) - 1) = 0 := by nlinarith [h i]
    rcases mul_eq_zero.mp hmul with hi | hi
    · exact Or.inl hi
    · exact Or.inr (sub_eq_zero.mp hi)
  · intro h i
    rcases h i with hi | hi <;> simp only [hi, zero_pow (by decide : 2 ≠ 0), one_pow]

theorem finite_node_polynomial_eq_one_iff [Nonempty ι]
    (x : ι → ℝ) (hx : Function.Injective x) (p : Polynomial ℝ)
    (hdegree : p.degree < (Fintype.card ι : ℕ)) :
    p = 1 ↔ ∀ i, p.eval (x i) = 1 := by
  classical
  constructor
  · rintro rfl i
    exact Polynomial.eval_one
  · intro h
    have hp : p = Lagrange.interpolate Finset.univ x (fun _ => (1 : ℝ)) :=
      (Lagrange.eq_interpolate_iff (s := Finset.univ) (v := x) (f := p)
        (fun _ => (1 : ℝ)) hx.injOn).mp
        ⟨by simpa only [Finset.card_univ] using hdegree, fun i _ => h i⟩
    rw [hp]
    exact Lagrange.interpolate_one hx.injOn Finset.univ_nonempty

end GaloisForLFunctions.HTGeometry
