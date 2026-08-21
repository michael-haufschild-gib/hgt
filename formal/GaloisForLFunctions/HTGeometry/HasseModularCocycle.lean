import GaloisForLFunctions.HTGeometry.ModularFormationDouble
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The literal Hasse modular cocycle

In logarithmic scale the raw Hasse–Fermi marginal has base density `e^{y/2}/(e^{e^y}+1)`.  Its
Hellinger midpoint and modular half-cocycle are explicit, the cocycle is reflection odd, and its
derivative at the origin is `1/2 − e/(e+1) ≠ 0`.  Consequently the base is not reflection
invariant: logarithmic inversion does not carry the tilted Fermi family to its reflected member,
so the raw Fermi packet admits no reciprocal functional-equation action.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The raw Hasse–Fermi base density in logarithmic scale. -/
def hasseLogBase (y : ℝ) : ℝ := Real.exp (y / 2) / (Real.exp (Real.exp y) + 1)

theorem hasseLogBase_denom_pos (y : ℝ) : 0 < Real.exp (Real.exp y) + 1 := by positivity

theorem hasseLogBase_pos (y : ℝ) : 0 < hasseLogBase y := by
  rw [hasseLogBase]
  exact div_pos (Real.exp_pos _) (hasseLogBase_denom_pos y)

/-- The explicit Hellinger midpoint of the Hasse base (FEL.D7). -/
def hasseHellinger (y : ℝ) : ℝ :=
  1 / Real.sqrt ((Real.exp (Real.exp y) + 1) * (Real.exp (Real.exp (-y)) + 1))

/-- The explicit Hasse modular half-cocycle (FEL.D8). -/
def hasseCocycle (y : ℝ) : ℝ :=
  y / 2 + Real.log (Real.exp (Real.exp (-y)) + 1) / 2 - Real.log (Real.exp (Real.exp y) + 1) / 2

theorem hasseHellinger_eq (y : ℝ) :
    hellingerMid hasseLogBase (fun t : ℝ => -t) y = hasseHellinger y := by
  have hdy := hasseLogBase_denom_pos y
  have hdny := hasseLogBase_denom_pos (-y)
  rw [hellingerMid, hasseHellinger, hasseLogBase, hasseLogBase]
  rw [show Real.exp (y / 2) / (Real.exp (Real.exp y) + 1) *
      (Real.exp (-y / 2) / (Real.exp (Real.exp (-y)) + 1))
      = 1 / ((Real.exp (Real.exp y) + 1) * (Real.exp (Real.exp (-y)) + 1)) by
    rw [div_mul_div_comm, ← Real.exp_add, show y / 2 + -y / 2 = (0 : ℝ) by ring,
      Real.exp_zero]]
  rw [one_div, one_div, Real.sqrt_inv]

theorem hasseCocycle_eq (y : ℝ) :
    modularHalfCocycle hasseLogBase (fun t : ℝ => -t) y = hasseCocycle y := by
  have hdy := hasseLogBase_denom_pos y
  have hdny := hasseLogBase_denom_pos (-y)
  rw [modularHalfCocycle, hasseCocycle, hasseLogBase, hasseLogBase]
  rw [show Real.exp (y / 2) / (Real.exp (Real.exp y) + 1) /
      (Real.exp (-y / 2) / (Real.exp (Real.exp (-y)) + 1))
      = Real.exp y * ((Real.exp (Real.exp (-y)) + 1) / (Real.exp (Real.exp y) + 1)) by
    field_simp
    rw [← Real.exp_add]
    ring_nf]
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_exp]
  ring

/-- The Hasse cocycle is reflection odd (FEL.D2). -/
theorem hasseCocycle_odd (y : ℝ) : hasseCocycle (-y) = - hasseCocycle y := by
  rw [hasseCocycle, hasseCocycle, neg_neg]
  ring

/-- The Hasse base factors through its Hellinger midpoint and cocycle (FEL.D9). -/
theorem hasseLogBase_factor (y : ℝ) :
    hasseLogBase y = hasseHellinger y * Real.exp (hasseCocycle y) ∧
      hasseLogBase (-y) = hasseHellinger y * Real.exp (-hasseCocycle y) := by
  constructor
  · have h := eq_hellingerMid_mul_exp (b := hasseLogBase) (R := fun t : ℝ => -t)
      hasseLogBase_pos y
    rwa [hasseHellinger_eq, hasseCocycle_eq] at h
  · have h := reflect_eq_hellingerMid_mul_exp (b := hasseLogBase) (R := fun t : ℝ => -t)
      hasseLogBase_pos (fun t => neg_neg t) y
    rwa [hasseHellinger_eq, hasseCocycle_eq] at h

/-! ## The derivative at the origin -/

theorem hasDerivAt_log_exp_exp (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (Real.exp (Real.exp t) + 1))
      (Real.exp (Real.exp y) * Real.exp y / (Real.exp (Real.exp y) + 1)) y := by
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (Real.exp t))
      (Real.exp (Real.exp y) * Real.exp y) y := (Real.hasDerivAt_exp y).exp
  exact (h2.add_const 1).log (ne_of_gt (hasseLogBase_denom_pos y))

theorem hasDerivAt_log_exp_exp_neg (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (Real.exp (Real.exp (-t)) + 1))
      (Real.exp (Real.exp (-y)) * (Real.exp (-y) * (-1)) / (Real.exp (Real.exp (-y)) + 1)) y := by
  have h1 : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) y := hasDerivAt_neg y
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-y) * (-1)) y := h1.exp
  have h3 : HasDerivAt (fun t : ℝ => Real.exp (Real.exp (-t)))
      (Real.exp (Real.exp (-y)) * (Real.exp (-y) * (-1))) y := h2.exp
  exact (h3.add_const 1).log (ne_of_gt (hasseLogBase_denom_pos (-y)))

/-- **(FEL.D10).**  The Hasse cocycle has nonzero derivative at the origin. -/
theorem hasDerivAt_hasseCocycle_zero :
    HasDerivAt hasseCocycle (1 / 2 - Real.exp 1 / (Real.exp 1 + 1)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
  have h2 := (hasDerivAt_log_exp_exp_neg 0).div_const 2
  have h3 := (hasDerivAt_log_exp_exp 0).div_const 2
  have hsum := (h1.add h2).sub h3
  refine hsum.congr_deriv ?_
  simp only [neg_zero, Real.exp_zero]
  ring

theorem exp_one_div_ne_half : Real.exp 1 / (Real.exp 1 + 1) ≠ 1 / 2 := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
    linarith
  intro h
  rw [div_eq_div_iff (by positivity) (by norm_num)] at h
  linarith

theorem hasseCocycle_deriv_zero_ne : (1 : ℝ) / 2 - Real.exp 1 / (Real.exp 1 + 1) ≠ 0 := by
  intro h
  exact exp_one_div_ne_half (by linarith)

/-- The Hasse cocycle is not identically zero, so the raw Hasse base is not reflection
invariant. -/
theorem exists_hasseCocycle_ne_zero : ∃ y : ℝ, hasseCocycle y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hzero : HasDerivAt hasseCocycle 0 0 := by
    have : hasseCocycle = fun _ : ℝ => (0 : ℝ) := funext hcon
    rw [this]
    exact hasDerivAt_const 0 0
  have := hasDerivAt_hasseCocycle_zero.unique hzero
  exact hasseCocycle_deriv_zero_ne this

/-- **(FEL.D5) for the literal Hasse base.**  The raw Hasse base is not reflection invariant. -/
theorem not_hasseLogBase_even : ¬ ∀ y : ℝ, hasseLogBase (-y) = hasseLogBase y := by
  intro heven
  obtain ⟨y, hy⟩ := exists_hasseCocycle_ne_zero
  refine hy ?_
  rw [← hasseCocycle_eq]
  exact (modularHalfCocycle_eq_zero_iff (b := hasseLogBase) (R := fun t : ℝ => -t)
    hasseLogBase_pos).2 heven y

/-! ## No reciprocal functional-equation action on the raw Fermi packet -/

/-- **(FEL.26).**  The common exponential tilt cancels: a reciprocal reflection of the tilted
family is a reciprocal reflection of the base. -/
theorem hasseTilt_reflection_forces_base {a Z Z' : ℝ}
    (h : ∀ y : ℝ, Real.exp (a * -y) * hasseLogBase (-y) / Z
      = Real.exp (-a * y) * hasseLogBase y / Z') (y : ℝ) :
    hasseLogBase (-y) / Z = hasseLogBase y / Z' := by
  have hy := h y
  rw [show a * -y = -a * y by ring, mul_div_assoc, mul_div_assoc] at hy
  exact mul_left_cancel₀ (Real.exp_ne_zero (-a * y)) hy

/-- **(FEL.25)–(FEL.27).**  Logarithmic inversion does not carry the tilt `a` of the raw Fermi
family to the tilt `-a`: it would force the base to be reflection invariant, and it is not. -/
theorem no_reciprocal_fermi_action {Z Z' : ℝ} (hZ : 0 < Z) (hZ' : 0 < Z')
    (h : ∀ y : ℝ, hasseLogBase (-y) / Z = hasseLogBase y / Z') : False := by
  have hb0 : 0 < hasseLogBase 0 := hasseLogBase_pos 0
  have h0 := h 0
  rw [neg_zero, div_eq_div_iff (ne_of_gt hZ) (ne_of_gt hZ')] at h0
  have hZZ : Z = Z' := (mul_left_cancel₀ (ne_of_gt hb0) h0).symm
  subst hZZ
  refine not_hasseLogBase_even fun y => ?_
  have hy := h y
  rw [div_eq_div_iff (ne_of_gt hZ) (ne_of_gt hZ)] at hy
  exact mul_right_cancel₀ (ne_of_gt hZ) hy

end

end GaloisForLFunctions.HTGeometry
