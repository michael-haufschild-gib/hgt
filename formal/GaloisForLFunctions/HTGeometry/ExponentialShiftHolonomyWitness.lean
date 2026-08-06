import GaloisForLFunctions.HTGeometry.FundamentalMatrixNonexistence
import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances
import GaloisForLFunctions.HTGeometry.TwistedGaugeAction

/-!
# An analytic source datum with nontrivial adjoint holonomy

The complex exponential, viewed inside the meromorphic differential field of the plane, satisfies
`exp(z + 1) = e · exp(z)`.  Its adjoint local system for the shift by one is therefore the scalar
`e`, and over the constant base field no gauge can trivialize it, because a constant gauge acts on a
scalar local system trivially while `e ≠ 1`.

So the curved source-boundary theory is not a theory of an empty class: here is a concrete analytic
observable whose source datum has nontrivial adjoint holonomy, and it carries a fundamental matrix,
namely the exponential itself.
-/

open Set Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Bottcher

open scoped UnivMeroFieldInstances

/-- The exponential as an element of the meromorphic differential field of the plane. -/
def expMero : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement Complex.exp analyticOnNhd_cexp

/-- **The analytic first-order relation.**  Shifting the variable by one multiplies the exponential
by the constant `e`. -/
theorem expMero_shift :
    addTranslationMeroEquiv 1 expMero
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (Complex.exp 1) * expMero := by
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => Complex.exp 1) (Set.univ : Set ℂ) :=
    analyticOnNhd_const
  have hstep : analyticMeroElement (fun z => Complex.exp (z + 1))
        (analyticOnNhd_comp_addTranslation analyticOnNhd_cexp 1)
      = analyticMeroElement (fun z : ℂ => (fun _ : ℂ => Complex.exp 1) z * Complex.exp z)
        (hconst.mul analyticOnNhd_cexp) := by
    congr 1
    funext z
    rw [Complex.exp_add]
    ring
  rw [expMero, addTranslationMeroEquiv_analyticMeroElement 1 analyticOnNhd_cexp, hstep,
    analyticMeroElement_mul hconst analyticOnNhd_cexp,
    analyticMeroElement_const (Set.univ : Set ℂ) (Complex.exp 1)]
  rfl

/-- The exponential is a nonzero element of the field, hence invertible. -/
theorem expMero_ne_zero : expMero ≠ 0 := by
  rw [expMero, Ne, analyticMeroElement_eq_zero_iff analyticOnNhd_cexp]
  intro h
  exact Complex.exp_ne_zero 0 (h 0 (Set.mem_univ 0))

/-! ### The datum -/

/-- The shift by one, as the single source direction. -/
def shiftSource : Unit → meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ) :=
  fun _ => addTranslationMeroEquiv 1

/-- The base acts trivially: the constants are fixed. -/
def constBase : Unit → ℂ ≃+* ℂ := fun _ => RingEquiv.refl ℂ

/-- The adjoint local system of the exponential: the scalar `e`. -/
def expLocalSystem : Unit → Matrix Unit Unit ℂ := fun _ _ _ => Complex.exp 1

/-- Its inverse. -/
def expLocalSystemInv : Unit → Matrix Unit Unit ℂ := fun _ _ _ => (Complex.exp 1)⁻¹

/-- The fundamental matrix of the datum: the exponential itself. -/
def expFundamental : Matrix Unit Unit (meroField (Set.univ : Set ℂ)) := fun _ _ => expMero

/-- Its inverse. -/
def expFundamentalInv : Matrix Unit Unit (meroField (Set.univ : Set ℂ)) := fun _ _ => expMero⁻¹

theorem expFundamental_mul_inv : expFundamental * expFundamentalInv = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [expFundamental, expFundamentalInv, Finset.univ_unique, Finset.sum_singleton,
    Matrix.one_apply, Subsingleton.elim p q]
  exact mul_inv_cancel₀ expMero_ne_zero

theorem expFundamentalInv_mul : expFundamentalInv * expFundamental = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [expFundamental, expFundamentalInv, Finset.univ_unique, Finset.sum_singleton,
    Matrix.one_apply, Subsingleton.elim p q]
  exact inv_mul_cancel₀ expMero_ne_zero

theorem expLocalSystem_mul_inv (i : Unit) : expLocalSystem i * expLocalSystemInv i = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [expLocalSystem, expLocalSystemInv, Finset.univ_unique, Finset.sum_singleton,
    Matrix.one_apply, Subsingleton.elim p q]
  exact mul_inv_cancel₀ (Complex.exp_ne_zero 1)

theorem expLocalSystemInv_mul (i : Unit) : expLocalSystemInv i * expLocalSystem i = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [expLocalSystem, expLocalSystemInv, Finset.univ_unique, Finset.sum_singleton,
    Matrix.one_apply, Subsingleton.elim p q]
  exact inv_mul_cancel₀ (Complex.exp_ne_zero 1)

/-- **The exponential is a fundamental matrix for its own local system.** -/
theorem expFundamental_isFundamental (i : Unit) :
    expFundamental.map (shiftSource i)
      = (baseMat (expLocalSystem i) : Matrix Unit Unit (meroField (Set.univ : Set ℂ)))
        * expFundamental := by
  ext p q
  rw [Matrix.map_apply, Matrix.mul_apply]
  simp only [expFundamental, shiftSource, baseMat, expLocalSystem, Matrix.map_apply,
    Finset.univ_unique, Finset.sum_singleton]
  exact expMero_shift

/-- The source direction fixes the constants of the base. -/
theorem shiftSource_algebraMap (i : Unit) (c : ℂ) :
    shiftSource i (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (constBase i c) :=
  addTranslationMeroEquiv_algebraMap_complex 1 c

/-! ### The holonomy is not trivializable -/

/-- `e` is not `1`. -/
theorem exp_one_ne_one : Complex.exp 1 ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hre := congrArg Complex.re hn
  simp at hre

/-- **Nontrivial adjoint holonomy.**  No base gauge carries the exponential's local system to the
identity: over the constants the gauge action on a scalar local system is trivial, and `e ≠ 1`. -/
theorem expLocalSystem_holonomy_nontrivial (P Q : Matrix Unit Unit ℂ)
    (hinv : ∀ p q : Unit, (∑ r, Q p r * P r q) = if p = q then 1 else 0) (i : Unit) :
    gaugeLinearPart constBase P Q expLocalSystem i ≠ fun _ _ => (1 : ℂ) := by
  intro h
  have hQP : Q () () * P () () = 1 := by
    have hi := hinv () ()
    simpa using hi
  have hval : gaugeLinearPart constBase P Q expLocalSystem i () () = 1 := by rw [h]
  rw [gaugeLinearPart] at hval
  simp only [Finset.univ_unique, Finset.sum_singleton, constBase, RingEquiv.coe_refl, id_eq,
    expLocalSystem] at hval
  refine exp_one_ne_one ?_
  calc Complex.exp 1 = Q () () * P () () * Complex.exp 1 := by rw [hQP, one_mul]
    _ = P () () * Complex.exp 1 * Q () () := by ring
    _ = 1 := hval

end

end GaloisForLFunctions.HTGeometry
