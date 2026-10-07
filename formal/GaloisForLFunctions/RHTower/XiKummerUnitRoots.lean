import GaloisForLFunctions.RHTower.XiGlobalKummerLegendre

/-!
# Explicit roots of the actual marked units

In any extension of the actual marked field containing an Xi root `v`, the
forced factor root is `u_n/v`. Adding `i*beta_n*v` gives a square root of the
original unit representative, with a polynomially specified reciprocal.
These formulas connect both actual quadratic source fields to the same units.
-/

noncomputable section
namespace RHTower.XiGlobalKummer
variable {E : Type*} [Field E] [Algebra Marked E]

/-- The factor root forced by an actual marked root and a chosen Xi root. -/
def halfFactorFromRoot (v : E) (n : ℕ) : E :=
  algebraMap Marked E (markedRoot n) / v

/-- The square root of the actual source unit supplied by an Xi root. -/
def halfUnitFromRoot (v : E) (n : ℕ) : E :=
  halfFactorFromRoot v n +
    algebraMap Marked E markedI * algebraMap Marked E (betaMarked n) * v

theorem xiRoot_ne_zero {v : E} (hv : v * v = algebraMap Marked E xiMarked) : v ≠ 0 := by
  intro h
  have hxi : algebraMap Marked E xiMarked ≠ 0 :=
    (map_ne_zero (algebraMap Marked E)).mpr
      ((map_ne_zero (algebraMap K Marked)).mpr xiElement_ne_zero)
  exact hxi (by rw [← hv, h, zero_mul])

theorem halfFactorFromRoot_sq {v : E}
    (hv : v * v = algebraMap Marked E xiMarked) (n : ℕ) :
    halfFactorFromRoot v n ^ 2 = algebraMap Marked E (factorMarked n) := by
  have hu : algebraMap Marked E (markedRoot n) ^ 2 =
      algebraMap Marked E xiMarked * algebraMap Marked E (factorMarked n) := by
    rw [← map_pow, pow_two, markedRoot_sq, radicand, map_mul, map_mul]
    rfl
  rw [halfFactorFromRoot, div_pow, pow_two v, hv, hu]
  exact mul_div_cancel_left₀ _
    ((map_ne_zero (algebraMap Marked E)).mpr
      ((map_ne_zero (algebraMap K Marked)).mpr xiElement_ne_zero))

theorem halfFactorFromRoot_mul_root {v : E}
    (hv : v * v = algebraMap Marked E xiMarked) (n : ℕ) :
    halfFactorFromRoot v n * v = algebraMap Marked E (markedRoot n) :=
  div_mul_cancel₀ _ (xiRoot_ne_zero hv)

theorem halfUnitFromRoot_sq {v : E}
    (hv : v * v = algebraMap Marked E xiMarked) (n : ℕ) :
    halfUnitFromRoot v n ^ 2 = algebraMap Marked E (unitRepresentative n) := by
  have hi := congrArg (algebraMap Marked E) markedI_sq
  have hf := congrArg (algebraMap Marked E) (sourceParameter_add_factor n)
  simp only [map_pow, map_neg, map_one] at hi
  simp only [sourceParameter, map_add, map_mul, map_pow, map_one] at hf
  simp only [halfUnitFromRoot, unitRepresentative, sourceParameter, sourceY,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
  linear_combination halfFactorFromRoot_sq hv n +
    (algebraMap Marked E (betaMarked n)) ^ 2 * v ^ 2 * hi -
    (algebraMap Marked E (betaMarked n)) ^ 2 * hv + hf +
    2 * algebraMap Marked E markedI * algebraMap Marked E (betaMarked n) *
      halfFactorFromRoot_mul_root hv n

theorem halfUnitFromRoot_mul_opposite {v : E}
    (hv : v * v = algebraMap Marked E xiMarked) (n : ℕ) :
    halfUnitFromRoot v n * (halfFactorFromRoot v n -
      algebraMap Marked E markedI * algebraMap Marked E (betaMarked n) * v) = 1 := by
  have hi := congrArg (algebraMap Marked E) markedI_sq
  have hf := congrArg (algebraMap Marked E) (sourceParameter_add_factor n)
  simp only [map_pow, map_neg, map_one] at hi
  simp only [sourceParameter, map_add, map_mul, map_pow, map_one] at hf
  unfold halfUnitFromRoot
  linear_combination halfFactorFromRoot_sq hv n -
    (algebraMap Marked E (betaMarked n)) ^ 2 * v ^ 2 * hi +
    (algebraMap Marked E (betaMarked n)) ^ 2 * hv + hf

theorem halfUnitFromRoot_neg (v : E) (n : ℕ) :
    halfUnitFromRoot (-v) n = -halfUnitFromRoot v n := by
  simp only [halfUnitFromRoot, halfFactorFromRoot, div_neg, mul_neg]
  ring

end RHTower.XiGlobalKummer
