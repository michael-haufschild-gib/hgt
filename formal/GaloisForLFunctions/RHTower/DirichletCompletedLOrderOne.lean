import GaloisForLFunctions.RHTower.HurwitzZetaOrderOne
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The completed Dirichlet L-function has order at most one

For a nontrivial character the two rational correction terms of `ZMod.completedLFunction_eq` vanish,
because `χ 0 = 0` and `∑ j, χ j = 0`.  The completed L-function therefore coincides with the entire
combination `completedLFunction₀`, a finite sum of entire Hurwitz completions weighted by `N ^ (-s)`.
Each ingredient carries an order-one growth envelope, and the class is closed under the operations
involved.
-/

open Complex HurwitzZeta
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Entire representation of the completed L-function of a nontrivial character.**  Both rational
correction terms of `ZMod.completedLFunction_eq` vanish, leaving a weighted finite sum of entire
Hurwitz completions. -/
theorem completedLFunction_eq_sum {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ s
      = (N : ℂ) ^ (-s) *
          (∑ j : ZMod N, (χ : ZMod N → ℂ) j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s)
        + (N : ℂ) ^ (-s) *
          (∑ j : ZMod N, (χ : ZMod N → ℂ) j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s) := by
  have hN1 : N ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  have hzero : (χ : ZMod N → ℂ) 0 = 0 := χ.map_zero' hN1
  have hsum : ∑ j : ZMod N, (χ : ZMod N → ℂ) j = 0 := χ.sum_eq_zero_of_ne_one hχ
  have hkey := ZMod.completedLFunction_eq (χ : ZMod N → ℂ) s
  rw [hzero, hsum] at hkey
  simp only [mul_zero, zero_div, sub_zero] at hkey
  show ZMod.completedLFunction (χ : ZMod N → ℂ) s = _
  rw [hkey]
  rfl

/-- **Order-one envelope of the completed Dirichlet L-function** of a nontrivial character. -/
theorem completedLFunction_orderOneEnvelope {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    OrderOneEnvelope (DirichletCharacter.completedLFunction χ) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcpow : OrderOneEnvelope (fun s : ℂ => (N : ℂ) ^ (-s)) :=
    orderOneEnvelope_natCast_cpow_neg hN0
  have heven : OrderOneEnvelope (fun s : ℂ =>
      ∑ j : ZMod N, (χ : ZMod N → ℂ) j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s) :=
    OrderOneEnvelope.finsetSum Finset.univ _ fun j _ =>
      (completedHurwitzZetaEven₀_orderOneEnvelope (ZMod.toAddCircle j)).const_mul _
  have hodd : OrderOneEnvelope (fun s : ℂ =>
      ∑ j : ZMod N, (χ : ZMod N → ℂ) j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s) :=
    OrderOneEnvelope.finsetSum Finset.univ _ fun j _ =>
      (completedHurwitzZetaOdd_orderOneEnvelope (ZMod.toAddCircle j)).const_mul _
  exact ((hcpow.mul heven).add (hcpow.mul hodd)).congr fun s => (completedLFunction_eq_sum hχ s).symm

end RHTower
