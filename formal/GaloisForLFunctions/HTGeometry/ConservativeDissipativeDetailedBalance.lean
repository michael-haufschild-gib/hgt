import GaloisForLFunctions.HTGeometry.ConservativeDissipativeEntropy

set_option autoImplicit false

/-!
# Prescribed-reference conservative–dissipative transport

The energy construction from Schaffer–Exl (arXiv:2609.04530) admits a
reference-weighted mobility. Every positive reference `exp r` is preserved,
relative Boltzmann energy decreases by the established edge entropy production,
and total population is conserved to first order. In population coordinates
the nonlinear logarithmic field is exactly a linear master equation. Its
constructed nonnegative jump rates satisfy detailed balance identically.
-/
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Relative Boltzmann free energy for positive reference populations `exp r`. -/
def relativeEntropyEnergy (r x : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (r i + x i) * (x i - 1)

/-- The reference-weighted logarithmic field, expressed through the established entropy field. -/
def relativeEntropyField (a : ι → ι → ℝ) (r x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-(r i)) * entropyField a x i

/-- Positive reference weights preserve the exact detailed-balance stationary set. -/
theorem relativeEntropyField_eq_zero_iff (a : ι → ι → ℝ) (r x : ι → ℝ) :
    relativeEntropyField a r x = 0 ↔ ∀ i j, (a i j = 0 ∧ a j i = 0) ∨ x i = x j := by
  rw [← entropyField_eq_zero_iff]
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simpa only [relativeEntropyField, Pi.zero_apply, mul_eq_zero, Real.exp_ne_zero, false_or] using hi
  · intro h
    funext i
    simp [relativeEntropyField, h]

/-- Every multiple of the prescribed positive reference is stationary, even on a disconnected graph. -/
theorem relativeEntropyField_constant (a : ι → ι → ℝ) (r : ι → ℝ) (c : ℝ) :
    relativeEntropyField a r (fun _ => c) = 0 := by
  apply (relativeEntropyField_eq_zero_iff a r _).mpr
  exact fun _ _ => Or.inr rfl

/-- Population velocity is the conservative flux independently of the reference. -/
theorem relativeEntropyField_population (a : ι → ι → ℝ) (r x : ι → ℝ) (i : ι) :
    Real.exp (r i + x i) * relativeEntropyField a r x i = entropyFlux a x i := by
  simp only [relativeEntropyField, entropyField, ← mul_assoc, ← Real.exp_add]
  rw [show r i + x i + (-r i + -x i) = 0 by ring, Real.exp_zero, one_mul]

/-- Differentiation of the relative energy along arbitrary logarithmic directions. -/
theorem hasDerivAt_relativeEntropyEnergy (r x v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => relativeEntropyEnergy r (fun i => x i + t * v i))
      (∑ i, Real.exp (r i + x i) * x i * v i) 0 := by
  apply HasDerivAt.congr_deriv (HasDerivAt.fun_sum fun i _ =>
    ((((hasDerivAt_const 0 (x i)).add ((hasDerivAt_id 0).mul_const (v i))).const_add (r i)).exp).mul
      (((hasDerivAt_const 0 (x i)).add ((hasDerivAt_id 0).mul_const (v i))).sub_const 1))
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, id_eq, zero_mul, add_zero, zero_add, one_mul]
  ring

/-- The prescribed reference changes the mobility while retaining exact edge entropy production. -/
theorem hasDerivAt_relativeEntropyField_energy (a : ι → ι → ℝ) (r x : ι → ℝ) :
    HasDerivAt (fun t : ℝ => relativeEntropyEnergy r
      (fun i => x i + t * relativeEntropyField a r x i))
      (-((2 : ℝ)⁻¹) * ∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (x i)) (Real.exp (x j))) 0 := by
  apply (hasDerivAt_relativeEntropyEnergy r x (relativeEntropyField a r x)).congr_deriv
  rw [← entropyFlux_power]
  apply Finset.sum_congr rfl
  intro i _
  calc
    Real.exp (r i + x i) * x i * relativeEntropyField a r x i =
        x i * (Real.exp (r i + x i) * relativeEntropyField a r x i) := by ring
    _ = _ := by rw [relativeEntropyField_population]

theorem relativeEntropyField_energy_nonpos (a : ι → ι → ℝ) (r x : ι → ℝ) :
    deriv (fun t : ℝ => relativeEntropyEnergy r
      (fun i => x i + t * relativeEntropyField a r x i)) 0 ≤ 0 := by
  rw [(hasDerivAt_relativeEntropyField_energy a r x).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (entropyProduction_nonneg a x)

/-- Mass conservation survives the nonuniform reference. -/
theorem hasDerivAt_relativeEntropyField_mass (a : ι → ι → ℝ) (r x : ι → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ i, Real.exp (r i + (x i + t * relativeEntropyField a r x i))) 0 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((((hasDerivAt_const 0 (x i)).add
      ((hasDerivAt_id 0).mul_const (relativeEntropyField a r x i))).const_add (r i)).exp)
  apply hd.congr_deriv
  simpa only [Pi.add_apply, id_eq, zero_mul, add_zero, zero_add, one_mul,
    relativeEntropyField_population] using entropyFlux_mass a x

/-- Jump rate from `i` to `j`, with the positive reference in its denominator. -/
def relativeEntropyJumpRate (a : ι → ι → ℝ) (r : ι → ℝ) (i j : ι) : ℝ :=
  Real.exp (-(r i)) * entropyConductance a i j

omit [Fintype ι] in
theorem relativeEntropyJumpRate_nonneg (a : ι → ι → ℝ) (r : ι → ℝ) (i j : ι) :
    0 ≤ relativeEntropyJumpRate a r i j :=
  mul_nonneg (Real.exp_pos _).le (entropyConductance_nonneg a i j)

omit [Fintype ι] in
/-- Exact detailed balance for the constructed jump rates. -/
theorem relativeEntropyJumpRate_balance (a : ι → ι → ℝ) (r : ι → ℝ) (i j : ι) :
    Real.exp (r i) * relativeEntropyJumpRate a r i j =
      Real.exp (r j) * relativeEntropyJumpRate a r j i := by
  simp only [relativeEntropyJumpRate, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_mul, entropyConductance_symm a i j]

/-- The nonlinear logarithmic field is exactly a linear master equation in positive populations. -/
theorem relativeEntropyField_masterEquation (a : ι → ι → ℝ) (r x : ι → ℝ) (i : ι) :
    Real.exp (r i + x i) * relativeEntropyField a r x i =
      ∑ j, (relativeEntropyJumpRate a r j i * Real.exp (r j + x j) -
        relativeEntropyJumpRate a r i j * Real.exp (r i + x i)) := by
  rw [relativeEntropyField_population]
  apply Finset.sum_congr rfl
  intro j _
  simp only [relativeEntropyJumpRate, entropyConductance_symm a j i]
  have he (k : ι) : Real.exp (-r k) * Real.exp (r k + x k) = Real.exp (x k) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    entropyConductance a i j * (Real.exp (x j) - Real.exp (x i)) =
        entropyConductance a i j * (Real.exp (-r j) * Real.exp (r j + x j)) -
          entropyConductance a i j * (Real.exp (-r i) * Real.exp (r i + x i)) := by rw [he, he, mul_sub]
    _ = _ := by ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
