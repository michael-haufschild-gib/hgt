import GaloisForLFunctions.HTGeometry.PadicPowerSeriesEvaluation

/-!
# Weight-specialization map for the Birch--Tate Iwasawa series

For the trivial-character dyadic main conjecture, analytic and algebraic characteristic series
live in the one-variable Iwasawa algebra `ℤ₂⟦T⟧` and are specialized at
`T = κ(γ)^(2 : ℕ) - 1`. This module constructs the required evaluation homomorphism over `ℤ_p`; the
existing corpus map had only integer coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open PowerSeries

variable (p : ℕ) [Fact p.Prime]

/-- Evaluation of a power series over `ℤ_p` at a topologically nilpotent element. -/
noncomputable def padicIntEval {a : ℤ_[p]} (ha : ‖a‖ < 1) :
    PowerSeries ℤ_[p] →+* ℤ_[p] :=
  PowerSeries.eval₂Hom (φ := RingHom.id ℤ_[p]) continuous_id
    (hasEval_of_norm_lt_one p ha)

@[simp]
theorem padicIntEval_C {a : ℤ_[p]} (ha : ‖a‖ < 1) (x : ℤ_[p]) :
    padicIntEval p ha (PowerSeries.C x) = x := by
  rw [padicIntEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]
  rfl

@[simp]
theorem padicIntEval_X {a : ℤ_[p]} (ha : ‖a‖ < 1) :
    padicIntEval p ha (PowerSeries.X : PowerSeries ℤ_[p]) = a := by
  rw [padicIntEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

/-- Polynomial identities over the one-variable Iwasawa algebra specialize to `ℤ_p`. -/
theorem isRoot_padicIntEval {a : ℤ_[p]} (ha : ‖a‖ < 1)
    {g : Polynomial (PowerSeries ℤ_[p])} {z : PowerSeries ℤ_[p]} (hroot : g.eval z = 0) :
    (g.map (padicIntEval p ha)).eval (padicIntEval p ha z) = 0 := by
  rw [← eval_map_of_eval, hroot, map_zero]

/-- If `x` lies in the principal-unit neighbourhood of `1`, then the weight-two
specialization point `x² - 1` is topologically nilpotent. -/
theorem norm_sq_sub_one_lt_one {x : ℤ_[p]} (hx : ‖x - 1‖ < 1) :
    ‖x ^ (2 : ℕ) - 1‖ < 1 := by
  rw [show x ^ (2 : ℕ) - 1 = (x + 1) * (x - 1) by ring, norm_mul]
  calc
    ‖x + 1‖ * ‖x - 1‖ ≤ 1 * ‖x - 1‖ :=
      mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
    _ < 1 := by simpa using hx

/-- Weight-two specialization `T ↦ x² - 1` for a principal unit `x ∈ ℤ_p`. -/
noncomputable def padicIntWeightTwoEval {x : ℤ_[p]} (hx : ‖x - 1‖ < 1) :
    PowerSeries ℤ_[p] →+* ℤ_[p] :=
  padicIntEval p (norm_sq_sub_one_lt_one p hx)

@[simp]
theorem padicIntWeightTwoEval_C {x : ℤ_[p]} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    padicIntWeightTwoEval p hx (PowerSeries.C a) = a := by
  exact padicIntEval_C p (norm_sq_sub_one_lt_one p hx) a

@[simp]
theorem padicIntWeightTwoEval_X {x : ℤ_[p]} (hx : ‖x - 1‖ < 1) :
    padicIntWeightTwoEval p hx (PowerSeries.X : PowerSeries ℤ_[p]) = x ^ (2 : ℕ) - 1 := by
  exact padicIntEval_X p (norm_sq_sub_one_lt_one p hx)

end GaloisForLFunctions.HTGeometry
