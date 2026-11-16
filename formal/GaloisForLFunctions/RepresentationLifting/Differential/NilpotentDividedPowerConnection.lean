import GaloisForLFunctions.RepresentationLifting.Differential.DividedPowerCoefficients
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Integral homotopy for nilpotent connections

On divided-power coefficient lists, the connection `∂ - N` factors as
`∂ (1 - I N)`. Nilpotence makes `1 - I N` invertible by a finite geometric
sum. This produces a contracting homotopy, identifies horizontal sections
with their initial values, and solves every inhomogeneous equation without
integer denominators. The free square-zero shift supplies a concrete instance
over every commutative ring.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.DividedPower

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The constant-coefficient connection on divided-power polynomials. -/
def connection (N : Module.End R V) : Module.End R (ℕ →₀ V) := derivative R V - lift N

/-- The finite nilpotent correction `1 - I N` is an integral linear equivalence. -/
def gaugeEquiv (N : Module.End R V) (hN : IsNilpotent N) : (ℕ →₀ V) ≃ₗ[R] (ℕ →₀ V) :=
  LinearMap.GeneralLinearGroup.toLinearEquiv
    (integral_mul_lift_isNilpotent N hN).isUnit_one_sub.unit

theorem gaugeEquiv_apply (N : Module.End R V) (hN : IsNilpotent N) (p : ℕ →₀ V) :
    gaugeEquiv N hN p = p - integral R V (lift N p) := by
  change ((integral_mul_lift_isNilpotent N hN).isUnit_one_sub.unit :
    Module.End R (ℕ →₀ V)) p = _
  rw [IsUnit.unit_spec]
  rfl

theorem gaugeEquiv_zero (N : Module.End R V) (hN : IsNilpotent N) (p : ℕ →₀ V) :
    gaugeEquiv N hN p 0 = p 0 := by
  rw [gaugeEquiv_apply]
  change p 0 - integral R V (lift N p) 0 = p 0
  rw [integral_zero, sub_zero]

theorem gaugeEquiv_symm_zero (N : Module.End R V) (hN : IsNilpotent N) (p : ℕ →₀ V) :
    (gaugeEquiv N hN).symm p 0 = p 0 := by
  have h := gaugeEquiv_zero N hN ((gaugeEquiv N hN).symm p)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The connection is ordinary divided-power differentiation after the nilpotent correction. -/
theorem derivative_gaugeEquiv (N : Module.End R V) (hN : IsNilpotent N) (p : ℕ →₀ V) :
    derivative R V (gaugeEquiv N hN p) = connection N p := by
  rw [gaugeEquiv_apply, map_sub, derivative_integral]
  rfl

/-- Integration corrected by the nilpotent coefficient operator. -/
def homotopy (N : Module.End R V) (hN : IsNilpotent N) : Module.End R (ℕ →₀ V) :=
  (gaugeEquiv N hN).symm.toLinearMap.comp (integral R V)

/-- The horizontal section with prescribed initial value. -/
def horizontal (N : Module.End R V) (hN : IsNilpotent N) : V →ₗ[R] (ℕ →₀ V) :=
  (gaugeEquiv N hN).symm.toLinearMap.comp (constant R V)

/-- The corrected integral is a right inverse of the connection. -/
theorem connection_homotopy (N : Module.End R V) (hN : IsNilpotent N) (p : ℕ →₀ V) :
    connection N (homotopy N hN p) = p := by
  change connection N ((gaugeEquiv N hN).symm (integral R V p)) = p
  rw [← derivative_gaugeEquiv N hN, LinearEquiv.apply_symm_apply, derivative_integral]

/-- The opposite homotopy identity removes the horizontal section with the same initial value. -/
theorem homotopy_connection (N : Module.End R V) (hN : IsNilpotent N) (p : ℕ →₀ V) :
    homotopy N hN (connection N p) = p - horizontal N hN (p 0) := by
  change (gaugeEquiv N hN).symm (integral R V (connection N p)) =
    p - (gaugeEquiv N hN).symm (constant R V (p 0))
  rw [← derivative_gaugeEquiv N hN, integral_derivative, map_sub,
    LinearEquiv.symm_apply_apply, gaugeEquiv_zero]

@[simp] theorem horizontal_zero (N : Module.End R V) (hN : IsNilpotent N) (v : V) :
    horizontal N hN v 0 = v := by
  change (gaugeEquiv N hN).symm (constant R V v) 0 = v
  rw [gaugeEquiv_symm_zero, constant_zero]

@[simp] theorem homotopy_zero (N : Module.End R V) (hN : IsNilpotent N) (p : ℕ →₀ V) :
    homotopy N hN p 0 = 0 := by
  change (gaugeEquiv N hN).symm (integral R V p) 0 = 0
  rw [gaugeEquiv_symm_zero, integral_zero]

/-- The prescribed-initial-value section is horizontal. -/
theorem connection_horizontal (N : Module.End R V) (hN : IsNilpotent N) (v : V) :
    connection N (horizontal N hN v) = 0 := by
  change connection N ((gaugeEquiv N hN).symm (constant R V v)) = 0
  rw [← derivative_gaugeEquiv N hN, LinearEquiv.apply_symm_apply]
  ext n
  simp

/-- The horizontal coefficients are the finite divided-power exponential `N^n v`. -/
theorem horizontal_coeff (N : Module.End R V) (hN : IsNilpotent N) (v : V) (n : ℕ) :
    horizontal N hN v n = (N ^ n) v := by
  induction n with
  | zero => exact horizontal_zero N hN v
  | succ n ih =>
    have h := congrArg (fun p : ℕ →₀ V => p n) (connection_horizontal N hN v)
    change horizontal N hN v (n + 1) - N (horizontal N hN v n) = 0 at h
    rw [sub_eq_zero] at h
    rw [h, ih, pow_succ', Module.End.mul_apply]

/-- Initial value and connection image are independent coordinates on divided-power sections. -/
def normalFormEquiv (N : Module.End R V) (hN : IsNilpotent N) :
    (ℕ →₀ V) ≃ₗ[R] (V × (ℕ →₀ V)) where
  toFun p := (p 0, connection N p)
  invFun z := horizontal N hN z.1 + homotopy N hN z.2
  left_inv p := by
    change horizontal N hN (p 0) + homotopy N hN (connection N p) = p
    rw [homotopy_connection]
    exact (add_comm _ _).trans (sub_add_cancel _ _)
  right_inv z := by
    apply Prod.ext
    · change horizontal N hN z.1 0 + homotopy N hN z.2 0 = z.1
      rw [horizontal_zero, homotopy_zero, add_zero]
    · change connection N (horizontal N hN z.1 + homotopy N hN z.2) = z.2
      rw [map_add, connection_horizontal, connection_homotopy, zero_add]
  map_add' p q := by
    apply Prod.ext
    · rfl
    · exact map_add (connection N) p q
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · exact map_smul (connection N) c p

/-- Every initial-value problem for the nilpotent connection has a unique finite solution. -/
theorem existsUnique_connection_solution (N : Module.End R V) (hN : IsNilpotent N)
    (v : V) (f : ℕ →₀ V) : ∃! p : ℕ →₀ V, p 0 = v ∧ connection N p = f := by
  let e := normalFormEquiv N hN
  refine ⟨e.symm (v, f), ?_, ?_⟩
  · have h := e.apply_symm_apply (v, f)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro p hp
    apply e.injective
    exact (Prod.ext hp.1 hp.2).trans (e.apply_symm_apply (v, f)).symm

variable (R V)

/-- The free square-zero shift sends `(x,y)` to `(y,0)`. -/
def squareZeroShift : Module.End R (V × V) where
  toFun x := (x.2, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem squareZeroShift_sq : squareZeroShift R V ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  rw [pow_two, Module.End.mul_apply]
  rfl

/-- Integral solvability for the free square-zero connection, in every characteristic. -/
theorem squareZero_existsUnique_connection_solution (v : V × V) (f : ℕ →₀ (V × V)) :
    ∃! p : ℕ →₀ (V × V), p 0 = v ∧ connection (squareZeroShift R V) p = f :=
  existsUnique_connection_solution (squareZeroShift R V) ⟨2, squareZeroShift_sq R V⟩ v f

#print axioms connection_homotopy
#print axioms homotopy_connection
#print axioms horizontal_coeff
#print axioms normalFormEquiv
#print axioms squareZero_existsUnique_connection_solution

end GaloisForLFunctions.RepresentationLifting.DividedPower
