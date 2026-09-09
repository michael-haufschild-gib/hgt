import GaloisForLFunctions.HTGeometry.ConservativeDissipativeDensityImplicit

set_option autoImplicit false

/-!
# Exact implicit thermodynamic entropy accounting

The Schaffer–Exl energy mechanism (arXiv:2609.04530) extends to the actual
positive implicit update of the constructed detailed-balance network.
The relative Boltzmann energy drop splits exactly into physical edge
production and a nonnegative directed Boltzmann remainder between old and
new populations. The remainder vanishes precisely when the state is
unchanged. Entropy is therefore strictly decreased outside zero steps and
the existing edgewise detailed-balance stationary set.
-/
open scoped BigOperators NNReal
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Directed Boltzmann remainder in unrestricted logarithmic coordinates. -/
def entropyRemainderValue (x y : ℝ) : ℝ :=
  Real.exp x * (x - y - 1) + Real.exp y

/-- Convexity of the exponential makes the directed entropy remainder nonnegative. -/
theorem entropyRemainderValue_nonneg (x y : ℝ) : 0 ≤ entropyRemainderValue x y := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - x)) (Real.exp_pos x).le
  rw [← Real.exp_add, add_sub_cancel] at h
  unfold entropyRemainderValue
  nlinarith

variable {ι : Type*} [Fintype ι]

/-- Additional entropy loss of the implicit step, beyond physical edge production. -/
def relativeEntropyRemainder (r x y : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (r i) * entropyRemainderValue (x i) (y i)

theorem relativeEntropyRemainder_nonneg (r x y : ι → ℝ) :
    0 ≤ relativeEntropyRemainder r x y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Real.exp_pos (r i)).le (entropyRemainderValue_nonneg (x i) (y i))

/-- Exact finite Boltzmann decomposition into tangent work and a nonnegative remainder. -/
theorem relativeEntropyEnergy_decomposition (r x y : ι → ℝ) :
    relativeEntropyEnergy r x - relativeEntropyEnergy r y =
      relativeEntropyRemainder r x y + ∑ i, y i * (Real.exp (r i + x i) - Real.exp (r i + y i)) := by
  simp only [relativeEntropyEnergy, relativeEntropyRemainder, entropyRemainderValue,
    Real.exp_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The implicit population equation converts entropy tangent work into physical edge production. -/
theorem implicitEntropyLog_work (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    ∑ i, implicitEntropyLog a r x t i *
      (Real.exp (r i + x i) - Real.exp (r i + implicitEntropyLog a r x t i)) =
      (t : ℝ) * (2 : ℝ)⁻¹ * ∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (implicitEntropyLog a r x t i))
          (Real.exp (implicitEntropyLog a r x t j)) := by
  have he : ∀ i, Real.exp (r i + x i) - Real.exp (r i + implicitEntropyLog a r x t i) =
      -(t : ℝ) * entropyFlux a (implicitEntropyLog a r x t) i := by
    intro i
    linarith [implicitEntropyLog_population_equation a r x t i]
  simp only [he, mul_left_comm (implicitEntropyLog a r x t _), ← Finset.mul_sum, entropyFlux_power]
  ring

/-- Exact implicit entropy balance separates physical dissipation from temporal convexity loss. -/
theorem implicitEntropyLog_energy_balance (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    relativeEntropyEnergy r (implicitEntropyLog a r x t) +
      (t : ℝ) * (2 : ℝ)⁻¹ * ∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (implicitEntropyLog a r x t i))
          (Real.exp (implicitEntropyLog a r x t j)) +
      relativeEntropyRemainder r x (implicitEntropyLog a r x t) = relativeEntropyEnergy r x := by
  have h := relativeEntropyEnergy_decomposition r x (implicitEntropyLog a r x t)
  rw [implicitEntropyLog_work] at h
  linarith

/-- Every implicit positive transport step decreases entropy by at least its physical production. -/
theorem implicitEntropyLog_energy_dissipation (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    relativeEntropyEnergy r (implicitEntropyLog a r x t) +
      (t : ℝ) * (2 : ℝ)⁻¹ * ∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (implicitEntropyLog a r x t i))
          (Real.exp (implicitEntropyLog a r x t j)) ≤ relativeEntropyEnergy r x := by
  linarith [implicitEntropyLog_energy_balance a r x t,
    relativeEntropyRemainder_nonneg r x (implicitEntropyLog a r x t)]

/-- Unconditional monotonicity of relative Boltzmann energy under the actual implicit update. -/
theorem implicitEntropyLog_energy_le (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    relativeEntropyEnergy r (implicitEntropyLog a r x t) ≤ relativeEntropyEnergy r x := by
  have hp := mul_nonneg (mul_nonneg t.coe_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹))
    (entropyProduction_nonneg a (implicitEntropyLog a r x t))
  linarith [implicitEntropyLog_energy_dissipation a r x t]

/-- The directed Boltzmann remainder vanishes exactly at an unchanged scalar state. -/
theorem entropyRemainderValue_eq_zero_iff (x y : ℝ) :
    entropyRemainderValue x y = 0 ↔ x = y := by
  constructor
  · intro hz
    by_contra hxy
    have h := mul_lt_mul_of_pos_left
      (Real.add_one_lt_exp (sub_ne_zero.mpr (Ne.symm hxy))) (Real.exp_pos x)
    rw [← Real.exp_add, add_sub_cancel] at h
    unfold entropyRemainderValue at hz
    nlinarith
  · rintro rfl
    simp [entropyRemainderValue]

/-- Positive reference weights make zero temporal entropy loss equivalent to an unchanged state. -/
theorem relativeEntropyRemainder_eq_zero_iff (r x y : ι → ℝ) :
    relativeEntropyRemainder r x y = 0 ↔ x = y := by
  constructor
  · intro hz
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (Real.exp_pos (r i)).le (entropyRemainderValue_nonneg (x i) (y i)))).mp hz
    funext i
    exact (entropyRemainderValue_eq_zero_iff (x i) (y i)).mp
      ((mul_eq_zero.mp (h i (Finset.mem_univ i))).resolve_left (Real.exp_ne_zero (r i)))
  · rintro rfl
    simp [relativeEntropyRemainder, entropyRemainderValue]

/-- Every actual change of logarithmic state causes strict entropy loss. -/
theorem implicitEntropyLog_energy_eq_iff (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    relativeEntropyEnergy r (implicitEntropyLog a r x t) = relativeEntropyEnergy r x ↔
      implicitEntropyLog a r x t = x := by
  constructor
  · intro he
    have hp := mul_nonneg (mul_nonneg t.coe_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹))
      (entropyProduction_nonneg a (implicitEntropyLog a r x t))
    have hr := relativeEntropyRemainder_nonneg r x (implicitEntropyLog a r x t)
    have hz : relativeEntropyRemainder r x (implicitEntropyLog a r x t) = 0 := by
      linarith [implicitEntropyLog_energy_balance a r x t]
    exact ((relativeEntropyRemainder_eq_zero_iff r x (implicitEntropyLog a r x t)).mp hz).symm
  · intro h
    rw [h]

/-- At a nonzero step, fixed states are exactly the established edgewise detailed-balance states. -/
theorem implicitEntropyLog_fixed_iff (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    implicitEntropyLog a r x t = x ↔
      t = 0 ∨ ∀ i j, (a i j = 0 ∧ a j i = 0) ∨ x i = x j := by
  constructor
  · intro h
    have he := implicitEntropyLog_energy_balance a r x t
    rw [h, (relativeEntropyRemainder_eq_zero_iff r x x).mpr rfl] at he
    have hz : (t : ℝ) * (∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (x i)) (Real.exp (x j))) = 0 := by linarith
    rcases mul_eq_zero.mp hz with ht | hp
    · exact Or.inl (NNReal.coe_eq_zero.mp ht)
    · exact Or.inr ((entropyProduction_eq_zero_iff a x).mp hp)
  · rintro (rfl | hb)
    · funext i
      simp [implicitEntropyLog, positiveImplicitDensity, densityImplicitStep, densityShift]
    · have hf := (entropyField_eq_zero_iff a x).mpr hb
      have hflux : ∀ i, entropyFlux a x i = 0 := by
        intro i
        have hi := congrFun hf i
        simpa only [entropyField, Pi.zero_apply, mul_eq_zero, Real.exp_ne_zero, false_or] using hi
      have hs : densityShift a r t (fun i => Real.exp (x i)) = fun i => Real.exp (x i) := by
        funext i
        change Real.exp (x i) - (t : ℝ) * (Real.exp (-(r i)) * entropyFlux a x i) = Real.exp (x i)
        rw [hflux]
        ring
      have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp (densityShift_isUnit a r t)).1
      have hd := hi ((densityShift_implicitStep a r (fun i => Real.exp (x i)) t).trans hs.symm)
      funext i
      change Real.log (densityImplicitStep a r t (fun j => Real.exp (x j)) i) = x i
      rw [hd, Real.log_exp]

/-- Entropy is preserved exactly for a zero step or an edgewise stationary input. -/
theorem implicitEntropyLog_energy_eq_iff_detailedBalance (a : ι → ι → ℝ)
    (r x : ι → ℝ) (t : ℝ≥0) :
    relativeEntropyEnergy r (implicitEntropyLog a r x t) = relativeEntropyEnergy r x ↔
      t = 0 ∨ ∀ i j, (a i j = 0 ∧ a j i = 0) ∨ x i = x j := by
  rw [implicitEntropyLog_energy_eq_iff, implicitEntropyLog_fixed_iff]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
