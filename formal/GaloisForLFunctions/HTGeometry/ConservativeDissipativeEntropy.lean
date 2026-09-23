import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

/-!
# Conservative mass transport and Boltzmann energy loss

The energy-based evolution mechanism of Schaffer–Exl (arXiv:2609.04530)
applies to the existing thermodynamic affinity and entropy-production laws.
Exponential population coordinates discharge positivity; squared raw weights
discharge symmetric conductance positivity. The resulting nonlinear field
preserves mass to first order, decreases free energy, and has exactly the
edgewise detailed-balance stationary states. Directional derivatives are
proved directly; no solution of a nonlinear ODE is assumed.
-/
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*}

/-- Symmetric nonnegative transport weights from unrestricted raw coefficients. -/
def entropyConductance (a : ι → ι → ℝ) (i j : ι) : ℝ := a i j ^ (2 : ℕ) + a j i ^ (2 : ℕ)

theorem entropyConductance_symm (a : ι → ι → ℝ) (i j : ι) :
    entropyConductance a i j = entropyConductance a j i := by
  simp [entropyConductance, add_comm]

theorem entropyConductance_nonneg (a : ι → ι → ℝ) (i j : ι) :
    0 ≤ entropyConductance a i j := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem entropyConductance_eq_zero_iff (a : ι → ι → ℝ) (i j : ι) :
    entropyConductance a i j = 0 ↔ a i j = 0 ∧ a j i = 0 := by
  rw [entropyConductance, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _),
    sq_eq_zero_iff, sq_eq_zero_iff]

variable [Fintype ι]

/-- Mass flux in positive population coordinates `pᵢ = exp xᵢ`. -/
def entropyFlux (a : ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, entropyConductance a i j * (Real.exp (x j) - Real.exp (x i))

/-- Nonlinear logarithmic-coordinate field representing the conservative population flux. -/
def entropyField (a : ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-(x i)) * entropyFlux a x i

/-- Boltzmann free energy of the exponential populations. -/
def entropyEnergy (x : ι → ℝ) : ℝ := ∑ i, Real.exp (x i) * (x i - 1)

theorem entropyProductionValue_exp (u v : ℝ) :
    entropyProductionValue (Real.exp u) (Real.exp v) = (Real.exp u - Real.exp v) * (u - v) := by
  simp [entropyProductionValue, thermodynamicAffinity,
    Real.log_div (Real.exp_ne_zero u) (Real.exp_ne_zero v)]

/-- Exact cancellation of total population flux. -/
theorem entropyFlux_mass (a : ι → ι → ℝ) (x : ι → ℝ) : ∑ i, entropyFlux a x i = 0 := by
  have hswap : (∑ i, ∑ j, entropyConductance a i j * (Real.exp (x j) - Real.exp (x i))) =
      -(∑ i, ∑ j, entropyConductance a i j * (Real.exp (x j) - Real.exp (x i))) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [entropyConductance_symm a j i]
    ring
  unfold entropyFlux
  linarith

/-- The entropy directional derivative is exactly minus total edge production. -/
theorem entropyFlux_power (a : ι → ι → ℝ) (x : ι → ℝ) :
    ∑ i, x i * entropyFlux a x i =
      -((2 : ℝ)⁻¹) * ∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (x i)) (Real.exp (x j)) := by
  have hswap : (∑ i, ∑ j, entropyConductance a i j *
      (Real.exp (x j) - Real.exp (x i)) * x j) = -(∑ i, x i * entropyFlux a x i) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [entropyFlux, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [entropyConductance_symm a j i]
    ring
  have hpair : (∑ i, x i * entropyFlux a x i) -
      (∑ i, ∑ j, entropyConductance a i j * (Real.exp (x j) - Real.exp (x i)) * x j) =
      -(∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (x i)) (Real.exp (x j))) := by
    simp only [entropyFlux, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [entropyProductionValue_exp]
    ring
  rw [hswap] at hpair
  linarith

/-- Differentiation in logarithmic coordinates discharges positivity of every population. -/
theorem hasDerivAt_entropyEnergy (x v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => entropyEnergy (fun i => x i + t * v i))
      (∑ i, Real.exp (x i) * x i * v i) 0 := by
  apply HasDerivAt.congr_deriv (HasDerivAt.fun_sum fun i _ =>
    (((hasDerivAt_const 0 (x i)).add ((hasDerivAt_id 0).mul_const (v i))).exp).mul
      (((hasDerivAt_const 0 (x i)).add ((hasDerivAt_id 0).mul_const (v i))).sub_const 1))
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, id_eq, zero_mul, add_zero, zero_add, one_mul]
  ring

/-- Exact nonlinear energy law, with all coefficients and states unrestricted. -/
theorem hasDerivAt_entropyField_energy (a : ι → ι → ℝ) (x : ι → ℝ) :
    HasDerivAt (fun t : ℝ => entropyEnergy (fun i => x i + t * entropyField a x i))
      (-((2 : ℝ)⁻¹) * ∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (x i)) (Real.exp (x j))) 0 := by
  convert hasDerivAt_entropyEnergy x (entropyField a x) using 1
  rw [← entropyFlux_power]
  apply Finset.sum_congr rfl
  intro i _
  simp only [entropyField]
  have he := Real.exp_add (x i) (-(x i))
  simp only [add_neg_cancel, Real.exp_zero] at he
  calc
    x i * entropyFlux a x i =
        (Real.exp (x i) * Real.exp (-x i)) * (x i * entropyFlux a x i) := by rw [← he, one_mul]
    _ = _ := by ring

/-- Total entropy production is nonnegative for every raw network and logarithmic state. -/
theorem entropyProduction_nonneg (a : ι → ι → ℝ) (x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, entropyConductance a i j *
      entropyProductionValue (Real.exp (x i)) (Real.exp (x j)) := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (entropyConductance_nonneg a i j)
      (entropyProductionValue_nonneg (Real.exp_pos _) (Real.exp_pos _))

/-- Sharp lossless classification: every active transport edge has equal endpoint populations. -/
theorem entropyProduction_eq_zero_iff (a : ι → ι → ℝ) (x : ι → ℝ) :
    (∑ i, ∑ j, entropyConductance a i j *
      entropyProductionValue (Real.exp (x i)) (Real.exp (x j))) = 0 ↔
      ∀ i j, (a i j = 0 ∧ a j i = 0) ∨ x i = x j := by
  have hp : ∀ i j, 0 ≤ entropyConductance a i j *
      entropyProductionValue (Real.exp (x i)) (Real.exp (x j)) := fun i j =>
    mul_nonneg (entropyConductance_nonneg a i j)
      (entropyProductionValue_nonneg (Real.exp_pos _) (Real.exp_pos _))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hp i j)]
  simp only [Finset.mem_univ, forall_true_left]
  simp_rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp _ j)]
  simp only [Finset.mem_univ, forall_true_left, mul_eq_zero, entropyConductance_eq_zero_iff,
    entropyProductionValue_eq_zero_iff_eq (Real.exp_pos _) (Real.exp_pos _), Real.exp_injective.eq_iff]

/-- Nonlinear stationarity is exactly edgewise detailed balance. -/
theorem entropyField_eq_zero_iff (a : ι → ι → ℝ) (x : ι → ℝ) :
    entropyField a x = 0 ↔ ∀ i j, (a i j = 0 ∧ a j i = 0) ∨ x i = x j := by
  constructor
  · intro hf
    have hflux : ∀ i, entropyFlux a x i = 0 := by
      intro i
      have hi := congrFun hf i
      simpa only [entropyField, Pi.zero_apply, mul_eq_zero, Real.exp_ne_zero, false_or] using hi
    apply (entropyProduction_eq_zero_iff a x).mp
    have h := entropyFlux_power a x
    simp only [hflux, mul_zero, Finset.sum_const_zero] at h
    linarith
  · intro h
    funext i
    change Real.exp (-(x i)) * entropyFlux a x i = 0
    suffices hz : entropyFlux a x i = 0 by rw [hz, mul_zero]
    apply Finset.sum_eq_zero
    intro j _
    rcases h i j with hij | hij
    · rw [(entropyConductance_eq_zero_iff a i j).mpr hij, zero_mul]
    · rw [hij, sub_self, mul_zero]

/-- The nonlinear field decreases Boltzmann free energy at every state. -/
theorem entropyField_energy_nonpos (a : ι → ι → ℝ) (x : ι → ℝ) :
    deriv (fun t : ℝ => entropyEnergy (fun i => x i + t * entropyField a x i)) 0 ≤ 0 := by
  rw [(hasDerivAt_entropyField_energy a x).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (entropyProduction_nonneg a x)

/-- Positive population transport conserves total mass to first order. -/
theorem hasDerivAt_entropyField_mass (a : ι → ι → ℝ) (x : ι → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ i, Real.exp (x i + t * entropyField a x i)) 0 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (((hasDerivAt_const 0 (x i)).add
      ((hasDerivAt_id 0).mul_const (entropyField a x i))).exp)
  apply hd.congr_deriv
  simp only [Pi.add_apply, id_eq, zero_mul, add_zero, zero_add, one_mul,
    entropyField, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simpa only [one_mul] using (entropyFlux_mass a x)

end
end GaloisForLFunctions.HTGeometry.SchafferExl
