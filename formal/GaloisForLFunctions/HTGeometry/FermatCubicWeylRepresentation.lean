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

theorem cube_square_nested_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω ^ 2 * (ω ^ 2 * (ω ^ 2 * x)) = x := by
  calc
    ω ^ 2 * (ω ^ 2 * (ω ^ 2 * x)) = (ω ^ 3) ^ 2 * x := by ring
    _ = x := by rw [hω3, one_pow, one_mul]

theorem omega_mul_square_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω * (ω ^ 2 * x) = x := by
  calc
    ω * (ω ^ 2 * x) = ω ^ 3 * x := by ring
    _ = x := by rw [hω3, one_mul]

theorem square_mul_omega_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω ^ 2 * (ω * x) = x := by
  calc
    ω ^ 2 * (ω * x) = ω ^ 3 * x := by ring
    _ = x := by rw [hω3, one_mul]

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
      cube_square_nested_mul_eq ω _ hω3]

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
      Function.iterate_succ_apply', omega_mul_square_mul_eq ω _ hω3,
      square_mul_omega_mul_eq ω _ hω3]

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
      cube_nested_mul_eq ω _ hω3, pow_two, mul_assoc]

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
      cube_nested_mul_eq ω _ hω3, pow_two, mul_assoc]

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
      cube_nested_mul_eq ω _ hω3, pow_two, mul_assoc]

/-- A fixed nonzero root state for the three-state Weyl realization. -/
def fermatCubicWeylRoot : Fin 3 → K := ![1, 0, 0]

theorem fermatCubicWeylRoot_ne_zero :
    (fermatCubicWeylRoot (K := K)) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  simp [fermatCubicWeylRoot] at h0

/-- **Explicit Fermat cubic differential-field horizon.**  The three-state Weyl packet has
complete differential dependence exactly on `c₀³+c₁³+c₂³=0`. -/
theorem fermatCubicWeylField_dependenceHorizon_eq
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    {c : Fin 3 → K | ¬ AlgebraicIndependent K
      (generalizedCliffordShiftFieldJet
        (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
          (fermatCubicThird ω) c)
        fermatCubicWeylRoot)} =
      {c : Fin 3 → K | fermatCubicPotential c = 0} := by
  apply fermatCubicShiftField_dependenceHorizon_eq
    ω (fermatCubicClock ω) fermatCubicShift (fermatCubicThird ω)
    hω
    (fermatCubicClock_cube ω hω)
    fermatCubicShift_cube
    (fermatCubicThird_cube ω hω)
    (fermatCubicClock_mul_shift ω hω)
    (fermatCubicClock_mul_third ω hω)
    (fermatCubicShift_mul_third ω hω)
    fermatCubicWeylRoot fermatCubicWeylRoot_ne_zero

/-- The explicit Weyl model also gives a genuine linear law space of rational-field derivations
with the Fermat cubic as its exact dependence horizon. -/
theorem fermatCubicWeylLinearDependenceHorizon_eq
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    linearDerivationDependenceHorizon
        (generalizedCliffordShiftFieldDerivationLaw
          (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
            (fermatCubicThird ω)))
        (generalizedCliffordShiftFieldRoot fermatCubicWeylRoot) =
      {c : Fin 3 → K | fermatCubicPotential c = 0} := by
  apply fermatCubicLinearDependenceHorizon_eq
    ω (fermatCubicClock ω) fermatCubicShift (fermatCubicThird ω)
    hω
    (fermatCubicClock_cube ω hω)
    fermatCubicShift_cube
    (fermatCubicThird_cube ω hω)
    (fermatCubicClock_mul_shift ω hω)
    (fermatCubicClock_mul_third ω hω)
    (fermatCubicShift_mul_third ω hω)
    fermatCubicWeylRoot fermatCubicWeylRoot_ne_zero

end

end GaloisForLFunctions.HTGeometry
