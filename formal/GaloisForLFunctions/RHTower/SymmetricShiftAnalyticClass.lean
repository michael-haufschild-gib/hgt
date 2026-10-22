import GaloisForLFunctions.RHTower.SymmetricShiftFunctionalEquation
import GaloisForLFunctions.RHTower.XiZeroCountJensenBound
import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne

/-!
# Analytic class of symmetric shift products

For an entire function `F` and a real shift `a`, the symmetric shift product is
`F(s + a) F(s - a)`. This module shows that the product is again entire and inherits an
order-one growth envelope `‖f(s)‖ ≤ exp(C (1 + ‖s‖) log(2 + ‖s‖))`, and instantiates both facts
for the Riemann `ξ` function and for completed Dirichlet `L`-functions of nontrivial characters.

## Main results

- `analyticOnNhd_symmetricShiftProduct`, `orderOneEnvelope_symmetricShiftProduct`: closure of the
  entire and order-one-envelope classes under symmetric shifts.
- `xi_symmetricShiftProduct_analyticOnNhd`, `xi_symmetricShiftProduct_orderOneEnvelope`:
  `ξ(s + a) ξ(s - a)` is entire of order at most one.
- `completedLFunction_symmetricShiftProduct_analyticOnNhd`,
  `completedLFunction_symmetricShiftProduct_orderOneEnvelope`: the same for `Λ(s + a, χ) Λ(s - a, χ)`
  with `χ ≠ 1`.

## Hypotheses

The `ξ` and Dirichlet results are unconditional (the Dirichlet ones require `χ ≠ 1`). The general
closure lemmas take as input that `F` is entire, respectively that `F` has an order-one envelope.
-/

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- If `F` is entire, then the symmetric shift product `s ↦ F(s + a) F(s - a)` is entire. -/
theorem analyticOnNhd_symmetricShiftProduct
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) (a : ℝ) :
    AnalyticOnNhd ℂ (symmetricShiftProduct F a) univ := by
  rw [analyticOnNhd_univ_iff_differentiable] at hF ⊢
  unfold symmetricShiftProduct
  fun_prop

/-- If `F` satisfies an order-one growth envelope, so does `s ↦ F(s + a) F(s - a)`. -/
theorem orderOneEnvelope_symmetricShiftProduct
    {F : ℂ → ℂ} (hF : OrderOneEnvelope F) (a : ℝ) :
    OrderOneEnvelope (symmetricShiftProduct F a) := by
  have hplus := hF.comp_affine 1 (a : ℂ)
  have hminus := hF.comp_affine 1 (-(a : ℂ))
  refine (hplus.mul hminus).congr ?_
  intro s
  unfold symmetricShiftProduct
  simp only [one_mul]
  congr 1

/-- `s ↦ ξ(s + a) ξ(s - a)` is entire for every real shift `a`. -/
theorem xi_symmetricShiftProduct_analyticOnNhd (a : ℝ) :
    AnalyticOnNhd ℂ (symmetricShiftProduct xi a) univ :=
  analyticOnNhd_symmetricShiftProduct xi_analyticOnNhd_univ a

/-- `s ↦ ξ(s + a) ξ(s - a)` satisfies an order-one growth envelope for every real shift `a`. -/
theorem xi_symmetricShiftProduct_orderOneEnvelope (a : ℝ) :
    OrderOneEnvelope (symmetricShiftProduct xi a) :=
  orderOneEnvelope_symmetricShiftProduct orderOneEnvelope_xi a

/-- For a nontrivial Dirichlet character `χ`, `s ↦ Λ(s + a, χ) Λ(s - a, χ)` is entire. -/
theorem completedLFunction_symmetricShiftProduct_analyticOnNhd
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a : ℝ) :
    AnalyticOnNhd ℂ
      (symmetricShiftProduct (DirichletCharacter.completedLFunction χ) a) univ := by
  apply analyticOnNhd_symmetricShiftProduct
  rw [analyticOnNhd_univ_iff_differentiable]
  exact DirichletCharacter.differentiable_completedLFunction hχ

/-- For a nontrivial Dirichlet character `χ`, `s ↦ Λ(s + a, χ) Λ(s - a, χ)` satisfies an order-one
growth envelope. -/
theorem completedLFunction_symmetricShiftProduct_orderOneEnvelope
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a : ℝ) :
    OrderOneEnvelope
      (symmetricShiftProduct (DirichletCharacter.completedLFunction χ) a) :=
  orderOneEnvelope_symmetricShiftProduct (completedLFunction_orderOneEnvelope hχ) a

end


end RHTower
