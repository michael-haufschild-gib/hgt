import GaloisForLFunctions.HTGeometry.FermatCubicCliffordHorizon
import Mathlib.Tactic.Ring

/-!
# The three-state Weyl representation of the Fermat cubic horizon

The order-three clock, shift, and a third Weyl monomial give an explicit three-dimensional
representation of the Fermat cubic generalized Clifford relations.  Combined with the abstract
shift-suspension theorem, this removes the representation hypothesis from the cubic horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- The order-three clock operator. -/
def fermatCubicClock (ω : K) : Module.End K (Fin 3 → K) where
  toFun f i := ![1, ω, ω ^ 2] i * f i
  map_add' f g := by
    funext i
    simp [mul_add]
  map_smul' c f := by
    funext i
    simp [mul_assoc, mul_comm]

/-- The cyclic order-three shift. -/
def fermatCubicShift : Module.End K (Fin 3 → K) where
  toFun f := ![f 2, f 0, f 1]
  map_add' f g := by
    funext i
    fin_cases i <;> simp
  map_smul' c f := by
    funext i
    fin_cases i <;> simp

/-- The third Weyl generator `clock²·shift`, written coordinatewise. -/
def fermatCubicThird (ω : K) : Module.End K (Fin 3 → K) where
  toFun f := ![f 2, ω ^ 2 * f 0, ω * f 1]
  map_add' f g := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' c f := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The cubic cyclotomic relation implies `ω³=1`. -/
theorem cube_eq_one_of_sq_add_self_add_one_eq_zero
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 := by
  calc
    ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
    _ = 1 := by rw [hω]; ring

theorem cube_nested_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω * (ω * (ω * x)) = x := by
  calc
    ω * (ω * (ω * x)) = ω ^ 3 * x := by ring
    _ = x := by rw [hω3, one_mul]

theorem sixth_nested_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω * (ω * (ω * (ω * (ω * (ω * x))))) = x := by
  calc
    ω * (ω * (ω * (ω * (ω * (ω * x))))) = (ω ^ 3) ^ 2 * x := by ring
    _ = x := by rw [hω3, one_pow, one_mul]

theorem fermatCubicClock_cube
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicClock ω ^ 3 = 1 := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicClock, Module.End.pow_apply,
      Function.iterate_succ_apply', cube_nested_mul_eq ω _ hω3,
      sixth_nested_mul_eq ω _ hω3]

theorem fermatCubicShift_cube :
    (fermatCubicShift (K := K)) ^ 3 = 1 := by
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicShift, Module.End.pow_apply, Function.iterate_succ_apply']

theorem fermatCubicThird_cube
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicThird ω ^ 3 = 1 := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicThird, Module.End.pow_apply,
      Function.iterate_succ_apply', cube_nested_mul_eq ω _ hω3]

theorem fermatCubicClock_mul_shift
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicClock ω * fermatCubicShift =
      ω • (fermatCubicShift * fermatCubicClock ω) := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicClock, fermatCubicShift, Module.End.mul_apply,
      cube_nested_mul_eq ω _ hω3]

theorem fermatCubicClock_mul_third
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicClock ω * fermatCubicThird ω =
      ω • (fermatCubicThird ω * fermatCubicClock ω) := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicClock, fermatCubicThird, Module.End.mul_apply,
      cube_nested_mul_eq ω _ hω3]

theorem fermatCubicShift_mul_third
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicShift * fermatCubicThird ω =
      ω • (fermatCubicThird ω * fermatCubicShift) := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicShift, fermatCubicThird, Module.End.mul_apply,
      cube_nested_mul_eq ω _ hω3]

end

end GaloisForLFunctions.HTGeometry
