import GaloisForLFunctions.HTGeometry.ConservativeDissipativeMasterFlow
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false

/-!
# Positive implicit detailed-balance transport

The Schaffer–Exl energy construction (arXiv:2609.04530), applied to the
constructed reversible network, admits a positive backward Euler update.
A finite maximum principle proves invertibility at every nonnegative step
size. The actual inverse preserves order, confines densities and logarithms
to their input extrema, conserves population, and fixes the prescribed
positive reference. No positivity or invertibility premise is assumed.
-/
open scoped BigOperators NNReal Ring
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Linear density generator relative to the constructed positive reference. -/
def densityGenerator (a : ι → ι → ℝ) (r : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p i => Real.exp (-(r i)) * ∑ j, entropyConductance a i j * (p j - p i)
    map_add' p q := by
      funext i
      simp only [Pi.add_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    map_smul' c p := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  }

/-- Reference-density backward Euler shift for arbitrary nonnegative step size. -/
def densityShift (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ≥0) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  1 - (t : ℝ) • densityGenerator a r

/-- Every density coordinate lies between two coordinates of its implicit shift. -/
theorem densityShift_extrema (a : ι → ι → ℝ) (r p : ι → ℝ) (t : ℝ≥0) (i : ι) :
    ∃ j k, densityShift a r t p j ≤ p i ∧ p i ≤ densityShift a r t p k := by
  classical
  have hs : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ p hs
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ p hs
  have hmin : 0 ≤ densityGenerator a r p j := by
    change 0 ≤ Real.exp (-(r j)) * ∑ l, entropyConductance a j l * (p l - p j)
    exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun l _ =>
      mul_nonneg (entropyConductance_nonneg a j l) (sub_nonneg.mpr (hj l (Finset.mem_univ l))))
  have hmax : densityGenerator a r p k ≤ 0 := by
    change Real.exp (-(r k)) * ∑ l, entropyConductance a k l * (p l - p k) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (Finset.sum_nonpos fun l _ =>
      mul_nonpos_of_nonneg_of_nonpos (entropyConductance_nonneg a k l)
        (sub_nonpos.mpr (hk l (Finset.mem_univ l))))
  refine ⟨j, k, ?_, ?_⟩
  · change p j - (t : ℝ) * densityGenerator a r p j ≤ p i
    exact (sub_le_self _ (mul_nonneg t.coe_nonneg hmin)).trans (hj i (Finset.mem_univ i))
  · change p i ≤ p k - (t : ℝ) * densityGenerator a r p k
    have hneg := mul_nonpos_of_nonneg_of_nonpos t.coe_nonneg hmax
    have hki := hk i (Finset.mem_univ i)
    linarith

/-- Finite-dimensional maximum principle constructs the inverse without a step restriction. -/
theorem densityShift_isUnit (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ≥0) :
    IsUnit (densityShift a r t) := by
  apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
  apply (LinearMap.isUnit_iff_ker_eq_bot _).mpr
  rw [LinearMap.ker_eq_bot']
  intro p hp
  funext i
  obtain ⟨j, k, hj, hk⟩ := densityShift_extrema a r p t i
  have hzero : densityShift a r t p = 0 := hp
  rw [hzero] at hj hk
  exact le_antisymm hk hj

/-- Actual backward Euler density update, with positivity derived from its maximum principle. -/
def densityImplicitStep (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ≥0) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (densityShift a r t)⁻¹ʳ

theorem densityShift_implicitStep (a : ι → ι → ℝ) (r p : ι → ℝ) (t : ℝ≥0) :
    densityShift a r t (densityImplicitStep a r t p) = p := by
  have h := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T p)
    (Ring.mul_inverse_cancel _ (densityShift_isUnit a r t))
  simpa only [densityImplicitStep, mul_apply_eq_comp, one_apply_eq_self] using h

/-- The inverse cannot create a new coordinate minimum or maximum. -/
theorem densityImplicitStep_extrema (a : ι → ι → ℝ) (r p : ι → ℝ) (t : ℝ≥0) (i : ι) :
    ∃ j k, p j ≤ densityImplicitStep a r t p i ∧ densityImplicitStep a r t p i ≤ p k := by
  have h := densityShift_extrema a r (densityImplicitStep a r t p) t i
  simpa only [densityShift_implicitStep] using h

/-- Positive density update constructed from arbitrary logarithmic coordinates. -/
def positiveImplicitDensity (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) : ι → ℝ :=
  densityImplicitStep a r t (fun i => Real.exp (x i))

theorem positiveImplicitDensity_pos (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (i : ι) :
    0 < positiveImplicitDensity a r x t i := by
  obtain ⟨j, _, hj, _⟩ := densityImplicitStep_extrema a r (fun i => Real.exp (x i)) t i
  exact (Real.exp_pos (x j)).trans_le hj

/-- The implicit density logarithm exists as an actual positive finite update. -/
def implicitEntropyLog (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (i : ι) : ℝ :=
  Real.log (positiveImplicitDensity a r x t i)

theorem exp_implicitEntropyLog (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (i : ι) :
    Real.exp (implicitEntropyLog a r x t i) = positiveImplicitDensity a r x t i :=
  Real.exp_log (positiveImplicitDensity_pos a r x t i)

/-- The new population satisfies the exact implicit thermodynamic flux equation. -/
theorem implicitEntropyLog_population_equation (a : ι → ι → ℝ) (r x : ι → ℝ)
    (t : ℝ≥0) (i : ι) :
    Real.exp (r i + implicitEntropyLog a r x t i) - Real.exp (r i + x i) =
      (t : ℝ) * entropyFlux a (implicitEntropyLog a r x t) i := by
  have h := congrFun (densityShift_implicitStep a r (fun j => Real.exp (x j)) t) i
  change positiveImplicitDensity a r x t i - (t : ℝ) * (Real.exp (-(r i)) *
    ∑ j, entropyConductance a i j * (positiveImplicitDensity a r x t j - positiveImplicitDensity a r x t i)) = Real.exp (x i) at h
  have hmul := congrArg (fun z : ℝ => Real.exp (r i) * z) h
  simp only [mul_sub, mul_left_comm (Real.exp (r i)) (t : ℝ), ← mul_assoc,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hmul
  simp only [Real.exp_add] at hmul
  simp only [Real.exp_add, exp_implicitEntropyLog, entropyFlux, mul_sub]
  linarith [hmul]

/-- Total reference-weighted population is conserved by every implicit step. -/
theorem implicitEntropyLog_mass (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    ∑ i, Real.exp (r i + implicitEntropyLog a r x t i) = ∑ i, Real.exp (r i + x i) := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => implicitEntropyLog_population_equation a r x t i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, entropyFlux_mass, mul_zero] at h
  exact sub_eq_zero.mp h

/-- The implicit density update preserves coordinatewise order. -/
theorem densityImplicitStep_monotone (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ≥0) :
    Monotone (densityImplicitStep a r t) := by
  intro p q hp i
  obtain ⟨_, k, _, hk⟩ := densityImplicitStep_extrema a r (p - q) t i
  simpa only [map_sub, Pi.sub_apply, sub_nonpos] using hk.trans (sub_nonpos.mpr (hp k))

/-- Every constant reference density is fixed by the implicit shift. -/
theorem densityShift_constant (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ≥0) (c : ℝ) :
    densityShift a r t (fun _ => c) = fun _ => c := by
  funext i
  change c - (t : ℝ) * (Real.exp (-(r i)) * ∑ j, entropyConductance a i j * (c - c)) = c
  simp

/-- The inverse shift fixes every constant density, hence every scalar multiple of the reference. -/
theorem densityImplicitStep_constant (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ≥0) (c : ℝ) :
    densityImplicitStep a r t (fun _ => c) = fun _ => c := by
  have h := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T (fun _ => c))
    (Ring.inverse_mul_cancel _ (densityShift_isUnit a r t))
  simpa only [densityImplicitStep, mul_apply_eq_comp, one_apply_eq_self, densityShift_constant] using h

/-- The actual positive-reference equilibrium is fixed by the logarithmic update. -/
theorem implicitEntropyLog_reference (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ≥0) :
    implicitEntropyLog a r 0 t = 0 := by
  funext i
  simp [implicitEntropyLog, positiveImplicitDensity, densityImplicitStep_constant]

/-- Logarithmic coordinates also remain between the original coordinate extrema. -/
theorem implicitEntropyLog_extrema (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (i : ι) :
    ∃ j k, x j ≤ implicitEntropyLog a r x t i ∧ implicitEntropyLog a r x t i ≤ x k := by
  obtain ⟨j, k, hj, hk⟩ := densityImplicitStep_extrema a r (fun i => Real.exp (x i)) t i
  refine ⟨j, k, Real.exp_le_exp.mp ?_, Real.exp_le_exp.mp ?_⟩
  · simpa only [exp_implicitEntropyLog, positiveImplicitDensity] using hj
  · simpa only [exp_implicitEntropyLog, positiveImplicitDensity] using hk

end
end GaloisForLFunctions.HTGeometry.SchafferExl
