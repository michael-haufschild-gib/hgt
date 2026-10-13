import GaloisForLFunctions.HTGeometry.BinaryPolynomialDiagonalDivision

/-! Every bivariate polynomial has a unique quotient after subtracting its diagonal remainder. -/

open MvPolynomial
local notation "P₂" => MvPolynomial (Fin 2) ℝ
local notation "Δ" => (X (0 : Fin 2) - X (1 : Fin 2) : P₂)
local notation "ρ" => MvPolynomial.rename (R := ℝ) (fun _ : Fin 2 => (1 : Fin 2))

namespace GaloisForLFunctions.HTGeometry

theorem binaryPolynomial_existsUnique_diagonal_quotient (p : P₂) :
    ∃! q : P₂, p = ρ p + Δ * q := by
  have hΔ : Δ ≠ 0 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      ((MvPolynomial.X_inj (R := ℝ) 0 1).mp (sub_eq_zero.mp h))
  obtain ⟨q, hq⟩ := binaryPolynomial_sub_rename_diagonal_dvd p
  have hrepr : p = ρ p + Δ * q :=
    (sub_eq_iff_eq_add.mp hq).trans (add_comm _ _)
  refine ⟨q, hrepr, ?_⟩
  intro r hr
  exact mul_left_cancel₀ hΔ (add_left_cancel (hr.symm.trans hrepr))

theorem binaryPolynomial_diagonal_constant_iff_existsUnique (p : P₂) :
    (∀ x : ℝ, eval (fun _ => x) p = eval (fun _ => 0) p) ↔
      ∃! q : P₂, p = C (eval (fun _ => 0) p) + Δ * q := by
  constructor
  · intro h
    have hrename : ρ p = C (eval (fun _ => 0) p) := by
      apply MvPolynomial.funext
      intro z
      simpa only [eval_rename, Function.comp_def, eval_C] using h (z 1)
    simpa only [hrename] using binaryPolynomial_existsUnique_diagonal_quotient p
  · rintro ⟨q, hq, _⟩
    apply (binaryPolynomial_diagonal_constant_iff_dvd p).mpr
    exact ⟨q, sub_eq_iff_eq_add.mpr (hq.trans (add_comm _ _))⟩

end GaloisForLFunctions.HTGeometry
