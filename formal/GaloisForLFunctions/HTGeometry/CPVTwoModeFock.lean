import GaloisForLFunctions.HTGeometry.WickFockModel
import Mathlib

/-!
# Two-mode pseudo-spin operators on the corpus polynomial Fock space

The bosonic realization in arXiv:2601.07437, equation (20), acts on the existing
polynomial Fock domain. With `H = 2 K₀`, the commutators are `[H,P]=2P`,
`[H,M]=-2M`, `[P,M]=-H`. The number difference commutes with all three.
No abstract commutation relations are assumed.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV
open MvPolynomial

abbrev Fock := MvPolynomial Bool ℂ
abbrev FockEnd := Module.End ℂ Fock

/-- Pair creation, using the corpus creation operators. -/
def pairCreate : FockEnd := fockCre ℂ Bool false * fockCre ℂ Bool true
/-- Pair annihilation, using the corpus annihilation operators. -/
def pairAnn : FockEnd := fockAnn ℂ Bool false * fockAnn ℂ Bool true
/-- Twice the unscaled pseudo-spin energy generator. -/
def pairCartan : FockEnd :=
  fockCre ℂ Bool false * fockAnn ℂ Bool false +
    fockCre ℂ Bool true * fockAnn ℂ Bool true + 1
/-- Conserved difference of the two occupation numbers. -/
def pairCharge : FockEnd :=
  fockCre ℂ Bool false * fockAnn ℂ Bool false -
    fockCre ℂ Bool true * fockAnn ℂ Bool true

@[simp] theorem pairCreate_apply (p : Fock) :
    pairCreate p = X false * (X true * p) := rfl
@[simp] theorem pairAnn_apply (p : Fock) :
    pairAnn p = pderiv false (pderiv true p) := rfl
@[simp] theorem pairCartan_apply (p : Fock) :
    pairCartan p = X false * pderiv false p + X true * pderiv true p + p := rfl
@[simp] theorem pairCharge_apply (p : Fock) :
    pairCharge p = X false * pderiv false p - X true * pderiv true p := rfl

/-- The Cartan generator raises pair-creation weight by two. -/
theorem pairCartan_create :
    pairCartan * pairCreate - pairCreate * pairCartan = (2 : ℂ) • pairCreate := by
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply, MvPolynomial.smul_eq_C_mul, map_ofNat]
  ring

/-- The pair commutator includes the vacuum contribution. -/
theorem pairCreate_ann :
    pairCreate * pairAnn - pairAnn * pairCreate = -pairCartan := by
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply]
  ring

/-- Pair annihilation lowers Cartan weight by two. -/
theorem pairCartan_ann :
    pairCartan * pairAnn - pairAnn * pairCartan = (-2 : ℂ) • pairAnn := by
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply, MvPolynomial.smul_eq_C_mul, map_ofNat,
    GaloisForLFunctions.pderiv_comm true false]
  ring

/-- Pair creation preserves occupation-number difference. -/
theorem pairCharge_create : pairCharge * pairCreate = pairCreate * pairCharge := by
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply]
  ring

/-- Pair annihilation preserves occupation-number difference. -/
theorem pairCharge_ann : pairCharge * pairAnn = pairAnn * pairCharge := by
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply, GaloisForLFunctions.pderiv_comm true false]

/-- Charge and Cartan energy commute on the full polynomial domain. -/
theorem pairCharge_cartan : pairCharge * pairCartan = pairCartan * pairCharge := by
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply, GaloisForLFunctions.pderiv_comm true false]
  ring

/-- Casimir decomposition on the entire two-mode Fock domain. -/
theorem pairCasimir_charge :
    pairCartan * pairCartan - (2 : ℂ) • pairCartan - (4 : ℂ) • (pairCreate * pairAnn) =
      pairCharge * pairCharge - 1 := by
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply, MvPolynomial.smul_eq_C_mul, map_ofNat,
    GaloisForLFunctions.pderiv_comm true false]
  ring

/-- Unnormalized occupation state with `d` unpaired quanta and `n` pairs. -/
def pairState (d n : ℕ) : Fock := X false ^ (n + d) * X true ^ n

/-- Euler's degree identity for either actual Fock mode. -/
theorem fock_euler_power (i : Bool) (n : ℕ) :
    X i * pderiv i ((X i : Fock) ^ n) = (n : ℂ) • (X i : Fock) ^ n := by
  rw [pderiv_pow, pderiv_X_self, mul_one]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one, MvPolynomial.smul_eq_C_mul, map_natCast, pow_succ]
    ring

/-- The first number operator reads the total first-mode occupation. -/
theorem pairState_number_left (d n : ℕ) :
    X false * pderiv false (pairState d n) = ((n + d : ℕ) : ℂ) • pairState d n := by
  unfold pairState
  rw [pderiv_mul, mul_add]
  simp only [pderiv_pow, pderiv_X_of_ne (by simp : true ≠ false), mul_zero, add_zero]
  have h := fock_euler_power false (n + d)
  simp only [pderiv_pow, pderiv_X_self, mul_one, MvPolynomial.smul_eq_C_mul] at h ⊢
  linear_combination (X true ^ n) * h

/-- The second number operator reads the pair occupation. -/
theorem pairState_number_right (d n : ℕ) :
    X true * pderiv true (pairState d n) = (n : ℂ) • pairState d n := by
  unfold pairState
  rw [pderiv_mul]
  simp only [pderiv_pow, pderiv_X_of_ne (by simp : false ≠ true), mul_zero, zero_mul, zero_add]
  have h := fock_euler_power true n
  simp only [pderiv_pow, pderiv_X_self, mul_one, MvPolynomial.smul_eq_C_mul] at h ⊢
  linear_combination (X false ^ (n + d)) * h

/-- Every charge sector has exactly the pseudo-spin ladder spectrum. -/
theorem pairCartan_state (d n : ℕ) :
    pairCartan (pairState d n) = ((2 * n + d + 1 : ℕ) : ℂ) • pairState d n := by
  rw [pairCartan_apply, pairState_number_left, pairState_number_right]
  simp [MvPolynomial.smul_eq_C_mul, map_ofNat]
  ring

/-- The sector label is the actual conserved number difference. -/
theorem pairCharge_state (d n : ℕ) :
    pairCharge (pairState d n) = (d : ℂ) • pairState d n := by
  rw [pairCharge_apply, pairState_number_left, pairState_number_right]
  simp [MvPolynomial.smul_eq_C_mul]
  ring

/-- Pair creation moves to the next level within the same charge sector. -/
theorem pairCreate_state (d n : ℕ) : pairCreate (pairState d n) = pairState d (n + 1) := by
  simp only [pairCreate_apply, pairState, show n + 1 + d = (n + d) + 1 by omega, pow_succ]
  ring

/-- Pair annihilation has the positive-discrete-series ladder coefficient. -/
theorem pairAnn_state_succ (d n : ℕ) :
    pairAnn (pairState d (n + 1)) =
      (((n + 1) * (n + d + 1) : ℕ) : ℂ) • pairState d n := by
  simp [pairAnn_apply, pairState,
    show n + 1 + d = (n + d) + 1 by omega, MvPolynomial.smul_eq_C_mul]
  ring

/-- Every sector has a lowest-weight vector annihilated by the lowering operator. -/
theorem pairAnn_state_zero (d : ℕ) : pairAnn (pairState d 0) = 0 := by
  simp [pairAnn_apply, pairState]

/-- The Casimir on sector `d` is `d² - 1`, or `K(K-1)` after dividing by four. -/
theorem pairCasimir_state (d n : ℕ) :
    (pairCartan * pairCartan - (2 : ℂ) • pairCartan -
      (4 : ℂ) • (pairCreate * pairAnn)) (pairState d n) =
      ((d : ℂ) ^ 2 - 1) • pairState d n := by
  rw [pairCasimir_charge]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, pairCharge_state,
    map_smul, Module.End.one_apply, sub_smul, one_smul, smul_smul, pow_two]

end GaloisForLFunctions.HTGeometry.CPV
