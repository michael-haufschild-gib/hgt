import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitBoundaryReflection
import GaloisForLFunctions.RHTower.LogarithmicMellinPrefixOscillator

/-!
# The actual critical boundary defect as a reflected oscillator energy

The position and momentum use the actual signed Möbius profiles and their
moving entry cutoffs. The normalized defect equals the integral of
`p(s)p(T-s)-q(s)q(T-s)/4`. The minus sign is essential: local Noether
conservation does not assert positivity of this reflected quadratic form.
-/

noncomputable section
open MeasureTheory

namespace RHTower

def ccmPrimeDeficitBoundaryPosition (m k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(t / 2)) * ccmPrimeDeficitBoundaryExpProfile m k t -
    Real.exp (-(t / 2)) * ccmPrimeDeficitBoundaryCountProfile m k t

def ccmPrimeDeficitBoundaryMomentum (m k : ℕ) (t : ℝ) : ℝ :=
  (Real.exp (-(t / 2)) * ccmPrimeDeficitBoundaryExpProfile m k t +
    Real.exp (-(t / 2)) * ccmPrimeDeficitBoundaryCountProfile m k t) / 2

private theorem critical_exp_profile_eq (m k : ℕ) (t : ℝ) :
    Real.exp (-(t / 2)) * ccmPrimeDeficitBoundaryExpProfile m k t =
      Real.exp (t / 2) * mellinPrefixReciprocal (logarithmicLongTail m moebiusCoeff)
        (min (m + 3 * k) ⌊Real.exp t⌋₊) := by
  rw [ccmPrimeDeficitBoundaryExpProfile, logarithmicFiniteEntryProfile_exp_eq_prefix,
    ← mul_assoc, ← Real.exp_add, show -(t / 2) + t = t / 2 by ring]

theorem ccmPrimeDeficitBoundaryPosition_eq_moving_prefix (m k : ℕ) (t : ℝ) :
    ccmPrimeDeficitBoundaryPosition m k t =
      mellinPrefixPosition (logarithmicLongTail m moebiusCoeff)
        (min (m + 3 * k) ⌊Real.exp t⌋₊) t := by
  rw [ccmPrimeDeficitBoundaryPosition, critical_exp_profile_eq,
    ccmPrimeDeficitBoundaryCountProfile, logarithmicFiniteEntryProfile_one_eq_prefix]
  rfl

theorem ccmPrimeDeficitBoundaryMomentum_eq_moving_prefix (m k : ℕ) (t : ℝ) :
    ccmPrimeDeficitBoundaryMomentum m k t =
      mellinPrefixMomentum (logarithmicLongTail m moebiusCoeff)
        (min (m + 3 * k) ⌊Real.exp t⌋₊) t := by
  rw [ccmPrimeDeficitBoundaryMomentum, critical_exp_profile_eq,
    ccmPrimeDeficitBoundaryCountProfile, logarithmicFiniteEntryProfile_one_eq_prefix]
  rfl

theorem ccmPrimeDeficitBoundary_noether_energy (m k : ℕ) (t : ℝ) :
    ccmPrimeDeficitBoundaryMomentum m k t ^ 2 - ccmPrimeDeficitBoundaryPosition m k t ^ 2 / 4 =
      mellinPrefixReciprocal (logarithmicLongTail m moebiusCoeff)
        (min (m + 3 * k) ⌊Real.exp t⌋₊) *
      mellinPrefixMass (logarithmicLongTail m moebiusCoeff)
        (min (m + 3 * k) ⌊Real.exp t⌋₊) := by
  rw [ccmPrimeDeficitBoundaryMomentum_eq_moving_prefix,
    ccmPrimeDeficitBoundaryPosition_eq_moving_prefix, mellinPrefix_noether_energy]

def ccmPrimeDeficitBoundaryReflectedEnergyDensity (m k : ℕ) (T s : ℝ) : ℝ :=
  ccmPrimeDeficitBoundaryMomentum m k s * ccmPrimeDeficitBoundaryMomentum m k (T - s) -
    ccmPrimeDeficitBoundaryPosition m k s * ccmPrimeDeficitBoundaryPosition m k (T - s) / 4

theorem ccmPrimeDeficitBoundaryReflectedEnergyDensity_eq (m k : ℕ) (T s : ℝ) :
    ccmPrimeDeficitBoundaryReflectedEnergyDensity m k T s =
      Real.exp (-(T / 2)) *
        (ccmPrimeDeficitBoundaryExpProfile m k s * ccmPrimeDeficitBoundaryCountProfile m k (T - s) +
          ccmPrimeDeficitBoundaryExpProfile m k (T - s) * ccmPrimeDeficitBoundaryCountProfile m k s) / 2 := by
  have he : Real.exp (-(s / 2)) * Real.exp (-((T - s) / 2)) = Real.exp (-(T / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold ccmPrimeDeficitBoundaryReflectedEnergyDensity ccmPrimeDeficitBoundaryMomentum
    ccmPrimeDeficitBoundaryPosition
  calc
    _ = (Real.exp (-(s / 2)) * Real.exp (-((T - s) / 2))) *
        (ccmPrimeDeficitBoundaryExpProfile m k s * ccmPrimeDeficitBoundaryCountProfile m k (T - s) +
          ccmPrimeDeficitBoundaryExpProfile m k (T - s) * ccmPrimeDeficitBoundaryCountProfile m k s) / 2 := by ring
    _ = _ := by rw [he]

private theorem reflected_pair_integrable (m k : ℕ) (T : ℝ) :
    IntervalIntegrable (fun s => ccmPrimeDeficitBoundaryExpProfile m k (T - s) *
      ccmPrimeDeficitBoundaryCountProfile m k s) volume 0 T := by
  have hi := intervalIntegrable_ccmPrimeDeficitBoundaryProfile_pair m k T 0 T
  simpa using (hi.comp_sub_left T).symm

theorem intervalIntegrable_ccmPrimeDeficitBoundaryReflectedEnergyDensity (m k : ℕ) (T : ℝ) :
    IntervalIntegrable (ccmPrimeDeficitBoundaryReflectedEnergyDensity m k T) volume 0 T := by
  have hi := ((intervalIntegrable_ccmPrimeDeficitBoundaryProfile_pair m k T 0 T).add
    (reflected_pair_integrable m k T)).const_mul (Real.exp (-(T / 2)))
  apply (hi.div_const 2).congr
  intro s _
  exact (ccmPrimeDeficitBoundaryReflectedEnergyDensity_eq m k T s).symm

/-- Exact critical-scale action identity for the actual signed arithmetic
tail, including all moving-cutoff and entry contributions. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_critical_eq_reflected_energy
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ} (h0 : 0 ≤ T)
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    Real.exp (-(T / 2)) *
      (ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T) =
      ∫ s in (0 : ℝ)..T, ccmPrimeDeficitBoundaryReflectedEnergyDensity m k T s := by
  have hreflect : (∫ s in (0 : ℝ)..T, ccmPrimeDeficitBoundaryExpProfile m k (T - s) *
      ccmPrimeDeficitBoundaryCountProfile m k s) =
      ∫ s in (0 : ℝ)..T, ccmPrimeDeficitBoundaryExpProfile m k s *
        ccmPrimeDeficitBoundaryCountProfile m k (T - s) := by
    simpa using intervalIntegral.integral_comp_sub_left
      (fun s => ccmPrimeDeficitBoundaryExpProfile m k s *
        ccmPrimeDeficitBoundaryCountProfile m k (T - s)) T (a := 0) (b := T)
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_reflection hm hk h0 hT]
  simp_rw [ccmPrimeDeficitBoundaryReflectedEnergyDensity_eq]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_ccmPrimeDeficitBoundaryProfile_pair m k T 0 T)
      (reflected_pair_integrable m k T), hreflect]
  ring

end RHTower
