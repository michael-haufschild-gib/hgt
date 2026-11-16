import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Integral calculus on divided-power coefficient lists

The finitely supported list `p n` represents the coefficient of `ℓ^[n]`
in a module-valued divided-power polynomial. Differentiation shifts
coefficients down and integration shifts them up. Both operations are
defined over the coefficient ring without division by integers.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.DividedPower

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- Differentiation in the divided-power basis. -/
def derivative : Module.End R (ℕ →₀ V) := Finsupp.lcomapDomain Nat.succ Nat.succ_injective

/-- Integration with zero constant coefficient in the divided-power basis. -/
def integral : Module.End R (ℕ →₀ V) := Finsupp.lmapDomain V R Nat.succ

/-- A constant divided-power polynomial. -/
def constant : V →ₗ[R] (ℕ →₀ V) := Finsupp.lsingle 0

/-- Evaluation at the origin. -/
def evaluation : (ℕ →₀ V) →ₗ[R] V := Finsupp.lapply 0

variable {R V}

/-- An endomorphism acts separately on every divided-power coefficient. -/
def lift (N : Module.End R V) : Module.End R (ℕ →₀ V) := Finsupp.mapRange.linearMap N

@[simp] theorem derivative_apply (p : ℕ →₀ V) (n : ℕ) :
    derivative R V p n = p (n + 1) := rfl

@[simp] theorem integral_zero (p : ℕ →₀ V) : integral R V p 0 = 0 :=
  Finsupp.mapDomain_notin_range p 0 (by simp)

@[simp] theorem integral_succ (p : ℕ →₀ V) (n : ℕ) :
    integral R V p (n + 1) = p n :=
  Finsupp.mapDomain_apply Nat.succ_injective p n

@[simp] theorem constant_zero (v : V) : constant R V v 0 = v := by
  simp only [constant, Finsupp.lsingle_apply, Finsupp.single_eq_same]

@[simp] theorem constant_succ (v : V) (n : ℕ) : constant R V v (n + 1) = 0 := by
  simp [constant]

@[simp] theorem evaluation_apply (p : ℕ →₀ V) : evaluation R V p = p 0 := rfl

@[simp] theorem lift_apply (N : Module.End R V) (p : ℕ →₀ V) (n : ℕ) :
    lift N p n = N (p n) := rfl

/-- Every divided-power coefficient list has an integral. -/
theorem derivative_integral (p : ℕ →₀ V) : derivative R V (integral R V p) = p := by
  ext n
  exact integral_succ p n

/-- Integration of the derivative removes precisely the constant coefficient. -/
theorem integral_derivative (p : ℕ →₀ V) :
    integral R V (derivative R V p) = p - constant R V (p 0) := by
  ext n
  cases n <;> simp

/-- The derivative kernel consists exactly of constants over every coefficient ring. -/
theorem derivative_eq_zero_iff (p : ℕ →₀ V) :
    derivative R V p = 0 ↔ p = constant R V (p 0) := by
  constructor
  · intro h
    have hi := integral_derivative (R := R) p
    rw [h, map_zero] at hi
    exact sub_eq_zero.mp hi.symm
  · intro h
    rw [h]
    ext n
    simp

/-- Powers of the lifted endomorphism are computed coefficient by coefficient. -/
theorem lift_pow_apply (N : Module.End R V) (m : ℕ) (p : ℕ →₀ V) (n : ℕ) :
    ((lift N) ^ m) p n = (N ^ m) (p n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, lift_apply, ih,
      pow_succ', Module.End.mul_apply]

/-- Coefficientwise extension preserves nilpotence. -/
theorem lift_isNilpotent (N : Module.End R V) (hN : IsNilpotent N) :
    IsNilpotent (lift N) := by
  obtain ⟨m, hm⟩ := hN
  refine ⟨m, ?_⟩
  apply LinearMap.ext
  intro p
  apply Finsupp.ext
  intro n
  rw [lift_pow_apply, hm]
  rfl

/-- Integration commutes with every coefficientwise endomorphism. -/
theorem integral_commute_lift (N : Module.End R V) : Commute (integral R V) (lift N) := by
  show integral R V * lift N = lift N * integral R V
  apply LinearMap.ext
  intro p
  apply Finsupp.ext
  intro n
  cases n <;> simp only [Module.End.mul_apply, integral_zero, integral_succ, lift_apply, map_zero]

/-- The integral followed by a nilpotent coefficient map is again nilpotent. -/
theorem integral_mul_lift_isNilpotent (N : Module.End R V) (hN : IsNilpotent N) :
    IsNilpotent (integral R V * lift N) := by
  obtain ⟨m, hm⟩ := lift_isNilpotent N hN
  exact ⟨m, by rw [(integral_commute_lift N).mul_pow, hm, mul_zero]⟩

#print axioms derivative_eq_zero_iff
#print axioms integral_mul_lift_isNilpotent

end GaloisForLFunctions.RepresentationLifting.DividedPower
