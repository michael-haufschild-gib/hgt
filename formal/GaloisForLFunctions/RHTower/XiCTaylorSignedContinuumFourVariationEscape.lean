import GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumFourVariationNoGo
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The four-row Route-J continuum variation bound is sharp

For every positive reflected damping `c` and carrier frequency `u`, this file constructs an
explicit nonzero Lebesgue density supported in one open sine chamber which annihilates all four
physical reflected value/derivative rows.

The phase-weighted density is a sum of five disjoint translated rectangle bumps. Its coefficient
polynomial is

`(X - exp (c L))² (X - exp (-c L))²`.

The reciprocal double roots give both value and derivative cancellation at `q = ±c`; its
coefficients alternate `+,-,+,-,+`. The source therefore has a global four-change certificate.
The preceding four-row no-go proves that it has no three-change certificate, so the lower bound is
exact. This is a genuine regular survivor, not a phase-node singularity, but it remains a local
row-level construction rather than a canonical divisor-independent theta/prime--Gamma source law.
-/

open Real Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

def routeJRectangleBumpSupport (L : ℝ) (j : ℕ) : Set ℝ :=
  Ioc (L / 4 + (j : ℝ) * L) (3 * L / 4 + (j : ℝ) * L)

def routeJRectangleBump (L : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (routeJRectangleBumpSupport L j).indicator (fun _ => 1) t

theorem routeJRectangleBump_eq_indicator (L : ℝ) (j : ℕ) :
    (fun t => routeJRectangleBump L j t) =
      (routeJRectangleBumpSupport L j).indicator
        (fun _ => 1) :=
  rfl

theorem routeJRectangleBumpSupport_not_mem_of_mem
    {L t : ℝ} (hL : 0 < L) {j k : ℕ} (hjk : j ≠ k)
    (ht : t ∈ routeJRectangleBumpSupport L j) :
    t ∉ routeJRectangleBumpSupport L k := by
  intro htk
  simp only [routeJRectangleBumpSupport, mem_Ioc] at ht htk
  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
  · have hcast : (j : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr hjklt
    have hmul := mul_le_mul_of_nonneg_right hcast hL.le
    linarith
  · have hcast : (k : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr hkjlt
    have hmul := mul_le_mul_of_nonneg_right hcast hL.le
    linarith

theorem integrable_exp_mul_routeJRectangleBump
    (q L : ℝ) (j : ℕ) :
    Integrable (fun t => Real.exp (q * t) * routeJRectangleBump L j t) := by
  let lo := L / 4 + (j : ℝ) * L
  let hi := 3 * L / 4 + (j : ℝ) * L
  have hcont : Continuous (fun t : ℝ => Real.exp (q * t)) := by fun_prop
  have hset :
      IntegrableOn (fun t : ℝ => Real.exp (q * t)) (Ioc lo hi) :=
    (hcont.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have heq :
      (fun t => Real.exp (q * t) * routeJRectangleBump L j t) =
        (Ioc lo hi).indicator (fun t => Real.exp (q * t)) := by
    funext t
    by_cases ht : t ∈ Ioc lo hi
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
  rw [heq]
  exact hset.integrable_indicator measurableSet_Ioc

theorem integrable_t_mul_exp_mul_routeJRectangleBump
    (q L : ℝ) (j : ℕ) :
    Integrable
      (fun t => t * Real.exp (q * t) * routeJRectangleBump L j t) := by
  let lo := L / 4 + (j : ℝ) * L
  let hi := 3 * L / 4 + (j : ℝ) * L
  have hcont : Continuous (fun t : ℝ => t * Real.exp (q * t)) := by fun_prop
  have hset :
      IntegrableOn (fun t : ℝ => t * Real.exp (q * t)) (Ioc lo hi) :=
    (hcont.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have heq :
      (fun t => t * Real.exp (q * t) * routeJRectangleBump L j t) =
        (Ioc lo hi).indicator (fun t => t * Real.exp (q * t)) := by
    funext t
    by_cases ht : t ∈ Ioc lo hi
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
  rw [heq]
  exact hset.integrable_indicator measurableSet_Ioc

theorem integral_exp_mul_routeJRectangleBump_shift
    {L : ℝ} (hL : 0 < L) (q : ℝ) (j : ℕ) :
    (∫ t, Real.exp (q * t) * routeJRectangleBump L j t) =
      Real.exp (q * ((j : ℝ) * L)) *
        ∫ t, Real.exp (q * t) * routeJRectangleBump L 0 t := by
  let lo : ℝ := L / 4
  let hi : ℝ := 3 * L / 4
  let shift : ℝ := (j : ℝ) * L
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have heqj :
      (fun t => Real.exp (q * t) * routeJRectangleBump L j t) =
        (Ioc (lo + shift) (hi + shift)).indicator
          (fun t => Real.exp (q * t)) := by
    funext t
    by_cases ht : t ∈ Ioc (lo + shift) (hi + shift)
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, shift, ht]
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, shift, ht]
  have heq0 :
      (fun t => Real.exp (q * t) * routeJRectangleBump L 0 t) =
        (Ioc lo hi).indicator (fun t => Real.exp (q * t)) := by
    funext t
    by_cases ht : t ∈ Ioc lo hi
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
  rw [heqj, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le
      (show lo + shift ≤ hi + shift by linarith),
    ← intervalIntegral.integral_comp_add_right
      (fun t : ℝ => Real.exp (q * t)) shift]
  have hfun :
      (fun t : ℝ => Real.exp (q * (t + shift))) =
        fun t => Real.exp (q * shift) * Real.exp (q * t) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, intervalIntegral.integral_const_mul,
    heq0, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hlohi]

theorem integral_t_mul_exp_mul_routeJRectangleBump_shift
    {L : ℝ} (hL : 0 < L) (q : ℝ) (j : ℕ) :
    (∫ t, t * Real.exp (q * t) * routeJRectangleBump L j t) =
      Real.exp (q * ((j : ℝ) * L)) *
        ((∫ t, t * Real.exp (q * t) * routeJRectangleBump L 0 t) +
          ((j : ℝ) * L) *
            ∫ t, Real.exp (q * t) * routeJRectangleBump L 0 t) := by
  let lo : ℝ := L / 4
  let hi : ℝ := 3 * L / 4
  let shift : ℝ := (j : ℝ) * L
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have heqj :
      (fun t => t * Real.exp (q * t) * routeJRectangleBump L j t) =
        (Ioc (lo + shift) (hi + shift)).indicator
          (fun t => t * Real.exp (q * t)) := by
    funext t
    by_cases ht : t ∈ Ioc (lo + shift) (hi + shift)
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, shift, ht]
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, shift, ht]
  have heq0D :
      (fun t => t * Real.exp (q * t) * routeJRectangleBump L 0 t) =
        (Ioc lo hi).indicator (fun t => t * Real.exp (q * t)) := by
    funext t
    by_cases ht : t ∈ Ioc lo hi
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
  have heq0V :
      (fun t => Real.exp (q * t) * routeJRectangleBump L 0 t) =
        (Ioc lo hi).indicator (fun t => Real.exp (q * t)) := by
    funext t
    by_cases ht : t ∈ Ioc lo hi
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
    · simp [routeJRectangleBump, routeJRectangleBumpSupport, lo, hi, ht]
  rw [heqj, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le
      (show lo + shift ≤ hi + shift by linarith),
    ← intervalIntegral.integral_comp_add_right
      (fun t : ℝ => t * Real.exp (q * t)) shift]
  have hfun :
      (fun t : ℝ => (t + shift) * Real.exp (q * (t + shift))) =
        fun t => Real.exp (q * shift) *
          (t * Real.exp (q * t) + shift * Real.exp (q * t)) := by
    funext t
    rw [show q * (t + shift) = q * t + q * shift by ring,
      Real.exp_add]
    ring
  have hDii :
      IntervalIntegrable (fun t : ℝ => t * Real.exp (q * t)) volume lo hi := by
    exact (by fun_prop : Continuous
      (fun t : ℝ => t * Real.exp (q * t))).intervalIntegrable lo hi
  have hSii :
      IntervalIntegrable
        (fun t : ℝ => shift * Real.exp (q * t)) volume lo hi := by
    exact (by fun_prop : Continuous
      (fun t : ℝ => shift * Real.exp (q * t))).intervalIntegrable lo hi
  have hsplit :
      (∫ t in lo..hi,
          t * Real.exp (q * t) + shift * Real.exp (q * t)) =
        (∫ t in lo..hi, t * Real.exp (q * t)) +
          shift * ∫ t in lo..hi, Real.exp (q * t) := by
    rw [intervalIntegral.integral_add hDii hSii,
      intervalIntegral.integral_const_mul]
  rw [hfun, intervalIntegral.integral_const_mul, hsplit,
    heq0D, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hlohi,
    heq0V, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hlohi]

def routeJReciprocalDoubleRootCoeff (r : ℝ) (j : Fin 5) : ℝ :=
  ![1,
    -2 * (r + r⁻¹),
    r ^ 2 + r⁻¹ ^ 2 + 4,
    -2 * (r + r⁻¹),
    1] j

def routeJFiveBumpPhaseDensity (L r t : ℝ) : ℝ :=
  routeJReciprocalDoubleRootCoeff r 0 * routeJRectangleBump L 0 t +
  routeJReciprocalDoubleRootCoeff r 1 * routeJRectangleBump L 1 t +
  routeJReciprocalDoubleRootCoeff r 2 * routeJRectangleBump L 2 t +
  routeJReciprocalDoubleRootCoeff r 3 * routeJRectangleBump L 3 t +
  routeJReciprocalDoubleRootCoeff r 4 * routeJRectangleBump L 4 t

theorem routeJFiveBumpPhaseDensity_eq_coeff_of_mem
    {L r t : ℝ} (hL : 0 < L) (j : Fin 5)
    (ht : t ∈ routeJRectangleBumpSupport L j) :
    routeJFiveBumpPhaseDensity L r t =
      routeJReciprocalDoubleRootCoeff r j := by
  fin_cases j
  · have h1 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 0 ≠ 1 by omega) ht
    have h2 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 0 ≠ 2 by omega) ht
    have h3 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 0 ≠ 3 by omega) ht
    have h4 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 0 ≠ 4 by omega) ht
    simp [routeJFiveBumpPhaseDensity, routeJRectangleBump, ht, h1, h2, h3, h4]
  · have h0 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 1 ≠ 0 by omega) ht
    have h2 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 1 ≠ 2 by omega) ht
    have h3 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 1 ≠ 3 by omega) ht
    have h4 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 1 ≠ 4 by omega) ht
    simp [routeJFiveBumpPhaseDensity, routeJRectangleBump, ht, h0, h2, h3, h4]
  · have h0 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 2 ≠ 0 by omega) ht
    have h1 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 2 ≠ 1 by omega) ht
    have h3 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 2 ≠ 3 by omega) ht
    have h4 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 2 ≠ 4 by omega) ht
    simp [routeJFiveBumpPhaseDensity, routeJRectangleBump, ht, h0, h1, h3, h4]
  · have h0 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 3 ≠ 0 by omega) ht
    have h1 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 3 ≠ 1 by omega) ht
    have h2 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 3 ≠ 2 by omega) ht
    have h4 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 3 ≠ 4 by omega) ht
    simp [routeJFiveBumpPhaseDensity, routeJRectangleBump, ht, h0, h1, h2, h4]
  · have h0 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 4 ≠ 0 by omega) ht
    have h1 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 4 ≠ 1 by omega) ht
    have h2 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 4 ≠ 2 by omega) ht
    have h3 := routeJRectangleBumpSupport_not_mem_of_mem hL
      (show 4 ≠ 3 by omega) ht
    simp [routeJFiveBumpPhaseDensity, routeJRectangleBump, ht, h0, h1, h2, h3]

theorem routeJFiveBumpPhaseDensity_eq_zero_of_not_mem
    {L r t : ℝ}
    (ht : ∀ j : Fin 5, t ∉ routeJRectangleBumpSupport L j) :
    routeJFiveBumpPhaseDensity L r t = 0 := by
  have h0 : t ∉ routeJRectangleBumpSupport L 0 := by simpa using ht 0
  have h1 : t ∉ routeJRectangleBumpSupport L 1 := by simpa using ht 1
  have h2 : t ∉ routeJRectangleBumpSupport L 2 := by simpa using ht 2
  have h3 : t ∉ routeJRectangleBumpSupport L 3 := by simpa using ht 3
  have h4 : t ∉ routeJRectangleBumpSupport L 4 := by simpa using ht 4
  simp [routeJFiveBumpPhaseDensity, routeJRectangleBump, h0, h1, h2, h3, h4]

@[simp] theorem routeJReciprocalDoubleRootCoeff_zero (r : ℝ) :
    routeJReciprocalDoubleRootCoeff r 0 = 1 := by
  simp [routeJReciprocalDoubleRootCoeff]

@[simp] theorem routeJReciprocalDoubleRootCoeff_one (r : ℝ) :
    routeJReciprocalDoubleRootCoeff r 1 = -2 * (r + r⁻¹) := by
  simp [routeJReciprocalDoubleRootCoeff]

@[simp] theorem routeJReciprocalDoubleRootCoeff_two (r : ℝ) :
    routeJReciprocalDoubleRootCoeff r 2 = r ^ 2 + r⁻¹ ^ 2 + 4 := by
  simp [routeJReciprocalDoubleRootCoeff]

@[simp] theorem routeJReciprocalDoubleRootCoeff_three (r : ℝ) :
    routeJReciprocalDoubleRootCoeff r 3 = -2 * (r + r⁻¹) := by
  simp [routeJReciprocalDoubleRootCoeff]

@[simp] theorem routeJReciprocalDoubleRootCoeff_four (r : ℝ) :
    routeJReciprocalDoubleRootCoeff r 4 = 1 := by
  simp [routeJReciprocalDoubleRootCoeff]

theorem routeJReciprocalDoubleRootCoeff_alternating
    {r : ℝ} (hr : 0 < r) :
    0 < routeJReciprocalDoubleRootCoeff r 0 ∧
      routeJReciprocalDoubleRootCoeff r 1 < 0 ∧
      0 < routeJReciprocalDoubleRootCoeff r 2 ∧
      routeJReciprocalDoubleRootCoeff r 3 < 0 ∧
      0 < routeJReciprocalDoubleRootCoeff r 4 := by
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  simp only [routeJReciprocalDoubleRootCoeff_zero,
    routeJReciprocalDoubleRootCoeff_one,
    routeJReciprocalDoubleRootCoeff_two,
    routeJReciprocalDoubleRootCoeff_three,
    routeJReciprocalDoubleRootCoeff_four]
  constructor
  · norm_num
  constructor
  · exact mul_neg_of_neg_of_pos (by norm_num) (add_pos hr hrinv)
  constructor
  · positivity
  constructor
  · exact mul_neg_of_neg_of_pos (by norm_num) (add_pos hr hrinv)
  · norm_num

theorem routeJReciprocalDoubleRootCoeff_value_at_r
    {r : ℝ} (hr : r ≠ 0) :
    routeJReciprocalDoubleRootCoeff r 0 +
      routeJReciprocalDoubleRootCoeff r 1 * r +
      routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
      routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
      routeJReciprocalDoubleRootCoeff r 4 * r ^ 4 = 0 := by
  simp only [routeJReciprocalDoubleRootCoeff_zero,
    routeJReciprocalDoubleRootCoeff_one,
    routeJReciprocalDoubleRootCoeff_two,
    routeJReciprocalDoubleRootCoeff_three,
    routeJReciprocalDoubleRootCoeff_four]
  field_simp [hr]
  ring

theorem routeJReciprocalDoubleRootCoeff_deriv_at_r
    {r : ℝ} (hr : r ≠ 0) :
    routeJReciprocalDoubleRootCoeff r 1 * r +
      2 * routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
      3 * routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
      4 * routeJReciprocalDoubleRootCoeff r 4 * r ^ 4 = 0 := by
  simp only [routeJReciprocalDoubleRootCoeff_one,
    routeJReciprocalDoubleRootCoeff_two,
    routeJReciprocalDoubleRootCoeff_three,
    routeJReciprocalDoubleRootCoeff_four]
  field_simp [hr]
  ring

theorem routeJReciprocalDoubleRootCoeff_value_at_inv
    {r : ℝ} (hr : r ≠ 0) :
    routeJReciprocalDoubleRootCoeff r 0 +
      routeJReciprocalDoubleRootCoeff r 1 * r⁻¹ +
      routeJReciprocalDoubleRootCoeff r 2 * r⁻¹ ^ 2 +
      routeJReciprocalDoubleRootCoeff r 3 * r⁻¹ ^ 3 +
      routeJReciprocalDoubleRootCoeff r 4 * r⁻¹ ^ 4 = 0 := by
  simp only [routeJReciprocalDoubleRootCoeff_zero,
    routeJReciprocalDoubleRootCoeff_one,
    routeJReciprocalDoubleRootCoeff_two,
    routeJReciprocalDoubleRootCoeff_three,
    routeJReciprocalDoubleRootCoeff_four]
  field_simp [hr]
  ring

theorem routeJReciprocalDoubleRootCoeff_deriv_at_inv
    {r : ℝ} (hr : r ≠ 0) :
    routeJReciprocalDoubleRootCoeff r 1 * r⁻¹ +
      2 * routeJReciprocalDoubleRootCoeff r 2 * r⁻¹ ^ 2 +
      3 * routeJReciprocalDoubleRootCoeff r 3 * r⁻¹ ^ 3 +
      4 * routeJReciprocalDoubleRootCoeff r 4 * r⁻¹ ^ 4 = 0 := by
  simp only [routeJReciprocalDoubleRootCoeff_one,
    routeJReciprocalDoubleRootCoeff_two,
    routeJReciprocalDoubleRootCoeff_three,
    routeJReciprocalDoubleRootCoeff_four]
  field_simp [hr]
  ring

theorem routeJFiveBumpPhaseDensity_four_change_pattern
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    ∀ t : ℝ,
      0 ≤ (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) *
        routeJFiveBumpPhaseDensity L r t := by
  intro t
  have hcoeff := routeJReciprocalDoubleRootCoeff_alternating hr
  by_cases h0 : t ∈ routeJRectangleBumpSupport L 0
  · have ht : L / 4 < t ∧ t ≤ 3 * L / 4 := by
      simpa [routeJRectangleBumpSupport] using h0
    have hp := routeJFiveBumpPhaseDensity_eq_coeff_of_mem (r := r) hL 0 h0
    have h1 : t - L < 0 := by linarith
    have h2 : t - 2 * L < 0 := by linarith
    have h3 : t - 3 * L < 0 := by linarith
    have h4 : t - 4 * L < 0 := by linarith
    have hP :
        0 < (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) := by
      rw [show (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) =
        ((t - L) * (t - 2 * L)) * ((t - 3 * L) * (t - 4 * L)) by ring]
      exact mul_pos (mul_pos_of_neg_of_neg h1 h2)
        (mul_pos_of_neg_of_neg h3 h4)
    rw [hp]
    exact (mul_pos hP hcoeff.1).le
  · by_cases h1mem : t ∈ routeJRectangleBumpSupport L 1
    · have ht : L / 4 + L < t ∧ t ≤ 3 * L / 4 + L := by
        simpa [routeJRectangleBumpSupport] using h1mem
      have hp := routeJFiveBumpPhaseDensity_eq_coeff_of_mem (r := r) hL 1 h1mem
      have h1 : 0 < t - L := by linarith
      have h2 : t - 2 * L < 0 := by linarith
      have h3 : t - 3 * L < 0 := by linarith
      have h4 : t - 4 * L < 0 := by linarith
      have hP :
          (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) < 0 := by
        exact mul_neg_of_pos_of_neg
          (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg h1 h2) h3) h4
      rw [hp]
      exact (mul_pos_of_neg_of_neg hP hcoeff.2.1).le
    · by_cases h2mem : t ∈ routeJRectangleBumpSupport L 2
      · have ht : L / 4 + 2 * L < t ∧ t ≤ 3 * L / 4 + 2 * L := by
          simpa [routeJRectangleBumpSupport] using h2mem
        have hp := routeJFiveBumpPhaseDensity_eq_coeff_of_mem (r := r) hL 2 h2mem
        have h1 : 0 < t - L := by linarith
        have h2 : 0 < t - 2 * L := by linarith
        have h3 : t - 3 * L < 0 := by linarith
        have h4 : t - 4 * L < 0 := by linarith
        have hP :
            0 < (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) := by
          rw [show (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) =
            ((t - L) * (t - 2 * L)) * ((t - 3 * L) * (t - 4 * L)) by ring]
          exact mul_pos (mul_pos h1 h2) (mul_pos_of_neg_of_neg h3 h4)
        rw [hp]
        exact (mul_pos hP hcoeff.2.2.1).le
      · by_cases h3mem : t ∈ routeJRectangleBumpSupport L 3
        · have ht : L / 4 + 3 * L < t ∧ t ≤ 3 * L / 4 + 3 * L := by
            simpa [routeJRectangleBumpSupport] using h3mem
          have hp := routeJFiveBumpPhaseDensity_eq_coeff_of_mem (r := r) hL 3 h3mem
          have h1 : 0 < t - L := by linarith
          have h2 : 0 < t - 2 * L := by linarith
          have h3 : 0 < t - 3 * L := by linarith
          have h4 : t - 4 * L < 0 := by linarith
          have hP :
              (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) < 0 := by
            exact mul_neg_of_pos_of_neg
              (mul_pos (mul_pos h1 h2) h3) h4
          rw [hp]
          exact (mul_pos_of_neg_of_neg hP hcoeff.2.2.2.1).le
        · by_cases h4mem : t ∈ routeJRectangleBumpSupport L 4
          · have ht : L / 4 + 4 * L < t ∧ t ≤ 3 * L / 4 + 4 * L := by
              simpa [routeJRectangleBumpSupport] using h4mem
            have hp := routeJFiveBumpPhaseDensity_eq_coeff_of_mem (r := r) hL 4 h4mem
            have h1 : 0 < t - L := by linarith
            have h2 : 0 < t - 2 * L := by linarith
            have h3 : 0 < t - 3 * L := by linarith
            have h4 : 0 < t - 4 * L := by linarith
            have hP :
                0 < (t - L) * (t - 2 * L) * (t - 3 * L) *
                  (t - 4 * L) :=
              mul_pos (mul_pos (mul_pos h1 h2) h3) h4
            rw [hp]
            exact (mul_pos hP hcoeff.2.2.2.2).le
          · have hp : routeJFiveBumpPhaseDensity L r t = 0 := by
              apply routeJFiveBumpPhaseDensity_eq_zero_of_not_mem
              intro j
              fin_cases j
              · exact h0
              · exact h1mem
              · exact h2mem
              · exact h3mem
              · exact h4mem
            rw [hp, mul_zero]

theorem routeJFiveBumpPhaseDensity_support_in_sine_chamber
    {u L r t : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi)
    (hp : routeJFiveBumpPhaseDensity L r t ≠ 0) :
    0 < t ∧ 0 < Real.sin (u * t) := by
  have hmem : ∃ j : Fin 5, t ∈ routeJRectangleBumpSupport L j := by
    by_contra h
    push Not at h
    exact hp (routeJFiveBumpPhaseDensity_eq_zero_of_not_mem h)
  obtain ⟨j, hj⟩ := hmem
  have hjbounds :
      L / 4 + (j : ℕ) * L < t ∧
        t ≤ 3 * L / 4 + (j : ℕ) * L := by
    simpa [routeJRectangleBumpSupport] using hj
  have hjnonneg : (0 : ℝ) ≤ (j : ℕ) := by positivity
  have hjle : ((j : ℕ) : ℝ) ≤ 4 := by
    exact_mod_cast Nat.le_of_lt_succ j.isLt
  have htpos : 0 < t := by
    have hbase : 0 < L / 4 := by positivity
    have hshift : 0 ≤ ((j : ℕ) : ℝ) * L :=
      mul_nonneg hjnonneg hL.le
    linarith
  have htupper : t < 5 * L := by
    have hmul :
        ((j : ℕ) : ℝ) * L ≤ 4 * L :=
      mul_le_mul_of_nonneg_right hjle hL.le
    linarith
  have hutpos : 0 < u * t := mul_pos hu htpos
  have hutpi : u * t < Real.pi := by
    have := mul_lt_mul_of_pos_left htupper hu
    linarith
  exact ⟨htpos, Real.sin_pos_of_pos_of_lt_pi hutpos hutpi⟩

def routeJFiveBumpSourceDensity (u L r t : ℝ) : ℝ :=
  if Real.sin (u * t) = 0 then 0
  else routeJFiveBumpPhaseDensity L r t / Real.sin (u * t)

theorem routeJFiveBumpSourceDensity_phase_eq
    {u L r : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi) (t : ℝ) :
    Real.sin (u * t) * routeJFiveBumpSourceDensity u L r t =
      routeJFiveBumpPhaseDensity L r t := by
  by_cases hs : Real.sin (u * t) = 0
  · have hp : routeJFiveBumpPhaseDensity L r t = 0 := by
      by_contra hp
      exact (routeJFiveBumpPhaseDensity_support_in_sine_chamber
        hu hL hchamber hp).2.ne' hs
    simp [routeJFiveBumpSourceDensity, hs, hp]
  · rw [routeJFiveBumpSourceDensity, if_neg hs]
    field_simp [hs]

theorem routeJFiveBumpSourceDensity_pos_on_first_bump
    {u L r t : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi)
    (ht : t ∈ routeJRectangleBumpSupport L 0) :
    0 < routeJFiveBumpSourceDensity u L r t := by
  have hp :
      routeJFiveBumpPhaseDensity L r t =
        routeJReciprocalDoubleRootCoeff r 0 :=
    routeJFiveBumpPhaseDensity_eq_coeff_of_mem (r := r) hL 0 ht
  have hphaseDensity :
      routeJFiveBumpPhaseDensity L r t ≠ 0 := by
    rw [hp, routeJReciprocalDoubleRootCoeff_zero]
    norm_num
  have hs :=
    (routeJFiveBumpPhaseDensity_support_in_sine_chamber
      hu hL hchamber hphaseDensity).2
  rw [routeJFiveBumpSourceDensity]
  simp only [hs.ne', if_false]
  rw [hp, routeJReciprocalDoubleRootCoeff_zero]
  exact div_pos (by norm_num) hs

theorem integrable_exp_mul_routeJFiveBumpPhaseDensity
    (q L r : ℝ) :
    Integrable
      (fun t => Real.exp (q * t) * routeJFiveBumpPhaseDensity L r t) := by
  have h0 := (integrable_exp_mul_routeJRectangleBump q L 0).const_mul
    (routeJReciprocalDoubleRootCoeff r 0)
  have h1 := (integrable_exp_mul_routeJRectangleBump q L 1).const_mul
    (routeJReciprocalDoubleRootCoeff r 1)
  have h2 := (integrable_exp_mul_routeJRectangleBump q L 2).const_mul
    (routeJReciprocalDoubleRootCoeff r 2)
  have h3 := (integrable_exp_mul_routeJRectangleBump q L 3).const_mul
    (routeJReciprocalDoubleRootCoeff r 3)
  have h4 := (integrable_exp_mul_routeJRectangleBump q L 4).const_mul
    (routeJReciprocalDoubleRootCoeff r 4)
  exact ((((h0.add h1).add h2).add h3).add h4).congr
    (Eventually.of_forall fun t => by
      dsimp [routeJFiveBumpPhaseDensity]
      ring)

theorem integrable_t_mul_exp_mul_routeJFiveBumpPhaseDensity
    (q L r : ℝ) :
    Integrable
      (fun t =>
        t * Real.exp (q * t) * routeJFiveBumpPhaseDensity L r t) := by
  have h0 := (integrable_t_mul_exp_mul_routeJRectangleBump q L 0).const_mul
    (routeJReciprocalDoubleRootCoeff r 0)
  have h1 := (integrable_t_mul_exp_mul_routeJRectangleBump q L 1).const_mul
    (routeJReciprocalDoubleRootCoeff r 1)
  have h2 := (integrable_t_mul_exp_mul_routeJRectangleBump q L 2).const_mul
    (routeJReciprocalDoubleRootCoeff r 2)
  have h3 := (integrable_t_mul_exp_mul_routeJRectangleBump q L 3).const_mul
    (routeJReciprocalDoubleRootCoeff r 3)
  have h4 := (integrable_t_mul_exp_mul_routeJRectangleBump q L 4).const_mul
    (routeJReciprocalDoubleRootCoeff r 4)
  exact ((((h0.add h1).add h2).add h3).add h4).congr
    (Eventually.of_forall fun t => by
      dsimp [routeJFiveBumpPhaseDensity]
      ring)

theorem integral_exp_mul_routeJFiveBumpPhaseDensity
    {L : ℝ} (hL : 0 < L) (q r : ℝ) :
    (∫ t, Real.exp (q * t) * routeJFiveBumpPhaseDensity L r t) =
      (∫ t, Real.exp (q * t) * routeJRectangleBump L 0 t) *
        (routeJReciprocalDoubleRootCoeff r 0 +
          routeJReciprocalDoubleRootCoeff r 1 * Real.exp (q * L) +
          routeJReciprocalDoubleRootCoeff r 2 * Real.exp (q * L) ^ 2 +
          routeJReciprocalDoubleRootCoeff r 3 * Real.exp (q * L) ^ 3 +
          routeJReciprocalDoubleRootCoeff r 4 * Real.exp (q * L) ^ 4) := by
  let f : ℕ → ℝ → ℝ := fun j t =>
    Real.exp (q * t) * routeJRectangleBump L j t
  let a : Fin 5 → ℝ := routeJReciprocalDoubleRootCoeff r
  have hj (j : ℕ) :
      Real.exp (q * ((j : ℝ) * L)) = Real.exp (q * L) ^ j := by
    rw [show q * ((j : ℝ) * L) = (j : ℝ) * (q * L) by ring,
      Real.exp_nat_mul]
  have hf0 : Integrable (f 0) := integrable_exp_mul_routeJRectangleBump q L 0
  have hf1 : Integrable (f 1) := integrable_exp_mul_routeJRectangleBump q L 1
  have hf2 : Integrable (f 2) := integrable_exp_mul_routeJRectangleBump q L 2
  have hf3 : Integrable (f 3) := integrable_exp_mul_routeJRectangleBump q L 3
  have hf4 : Integrable (f 4) := integrable_exp_mul_routeJRectangleBump q L 4
  let g0 : ℝ → ℝ := fun t => a 0 * f 0 t
  let g1 : ℝ → ℝ := fun t => a 1 * f 1 t
  let g2 : ℝ → ℝ := fun t => a 2 * f 2 t
  let g3 : ℝ → ℝ := fun t => a 3 * f 3 t
  let g4 : ℝ → ℝ := fun t => a 4 * f 4 t
  have hg0 : Integrable g0 := hf0.const_mul (a 0)
  have hg1 : Integrable g1 := hf1.const_mul (a 1)
  have hg2 : Integrable g2 := hf2.const_mul (a 2)
  have hg3 : Integrable g3 := hf3.const_mul (a 3)
  have hg4 : Integrable g4 := hf4.const_mul (a 4)
  have heq :
      (fun t => Real.exp (q * t) * routeJFiveBumpPhaseDensity L r t) =
        (((g0 + g1) + g2) + g3) + g4 := by
    funext t
    simp only [Pi.add_apply]
    dsimp [a, f, g0, g1, g2, g3, g4,
      routeJFiveBumpPhaseDensity]
    ring
  rw [heq,
    integral_add' (((hg0.add hg1).add hg2).add hg3) hg4,
    integral_add' ((hg0.add hg1).add hg2) hg3,
    integral_add' (hg0.add hg1) hg2,
    integral_add' hg0 hg1]
  dsimp only [g0, g1, g2, g3, g4]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul,
    integral_exp_mul_routeJRectangleBump_shift hL q 1,
    integral_exp_mul_routeJRectangleBump_shift hL q 2,
    integral_exp_mul_routeJRectangleBump_shift hL q 3,
    integral_exp_mul_routeJRectangleBump_shift hL q 4,
    hj 1, hj 2, hj 3, hj 4]
  dsimp [a, f, g0, g1, g2, g3, g4]
  ring

theorem integral_t_mul_exp_mul_routeJFiveBumpPhaseDensity
    {L : ℝ} (hL : 0 < L) (q r : ℝ) :
    (∫ t, t * Real.exp (q * t) * routeJFiveBumpPhaseDensity L r t) =
      (∫ t, t * Real.exp (q * t) * routeJRectangleBump L 0 t) *
          (routeJReciprocalDoubleRootCoeff r 0 +
            routeJReciprocalDoubleRootCoeff r 1 * Real.exp (q * L) +
            routeJReciprocalDoubleRootCoeff r 2 * Real.exp (q * L) ^ 2 +
            routeJReciprocalDoubleRootCoeff r 3 * Real.exp (q * L) ^ 3 +
            routeJReciprocalDoubleRootCoeff r 4 * Real.exp (q * L) ^ 4) +
        L * (∫ t, Real.exp (q * t) * routeJRectangleBump L 0 t) *
          (routeJReciprocalDoubleRootCoeff r 1 * Real.exp (q * L) +
            2 * routeJReciprocalDoubleRootCoeff r 2 * Real.exp (q * L) ^ 2 +
            3 * routeJReciprocalDoubleRootCoeff r 3 * Real.exp (q * L) ^ 3 +
            4 * routeJReciprocalDoubleRootCoeff r 4 * Real.exp (q * L) ^ 4) := by
  let f : ℕ → ℝ → ℝ := fun j t =>
    t * Real.exp (q * t) * routeJRectangleBump L j t
  let a : Fin 5 → ℝ := routeJReciprocalDoubleRootCoeff r
  have hj (j : ℕ) :
      Real.exp (q * ((j : ℝ) * L)) = Real.exp (q * L) ^ j := by
    rw [show q * ((j : ℝ) * L) = (j : ℝ) * (q * L) by ring,
      Real.exp_nat_mul]
  have hf0 : Integrable (f 0) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 0
  have hf1 : Integrable (f 1) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 1
  have hf2 : Integrable (f 2) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 2
  have hf3 : Integrable (f 3) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 3
  have hf4 : Integrable (f 4) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 4
  let g0 : ℝ → ℝ := fun t => a 0 * f 0 t
  let g1 : ℝ → ℝ := fun t => a 1 * f 1 t
  let g2 : ℝ → ℝ := fun t => a 2 * f 2 t
  let g3 : ℝ → ℝ := fun t => a 3 * f 3 t
  let g4 : ℝ → ℝ := fun t => a 4 * f 4 t
  have hg0 : Integrable g0 := hf0.const_mul (a 0)
  have hg1 : Integrable g1 := hf1.const_mul (a 1)
  have hg2 : Integrable g2 := hf2.const_mul (a 2)
  have hg3 : Integrable g3 := hf3.const_mul (a 3)
  have hg4 : Integrable g4 := hf4.const_mul (a 4)
  have heq :
      (fun t =>
        t * Real.exp (q * t) * routeJFiveBumpPhaseDensity L r t) =
        (((g0 + g1) + g2) + g3) + g4 := by
    funext t
    simp only [Pi.add_apply]
    dsimp [a, f, g0, g1, g2, g3, g4,
      routeJFiveBumpPhaseDensity]
    ring
  rw [heq,
    integral_add' (((hg0.add hg1).add hg2).add hg3) hg4,
    integral_add' ((hg0.add hg1).add hg2) hg3,
    integral_add' (hg0.add hg1) hg2,
    integral_add' hg0 hg1]
  dsimp only [g0, g1, g2, g3, g4]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul,
    integral_t_mul_exp_mul_routeJRectangleBump_shift hL q 1,
    integral_t_mul_exp_mul_routeJRectangleBump_shift hL q 2,
    integral_t_mul_exp_mul_routeJRectangleBump_shift hL q 3,
    integral_t_mul_exp_mul_routeJRectangleBump_shift hL q 4,
    hj 1, hj 2, hj 3, hj 4]
  dsimp [a, f, g0, g1, g2, g3, g4]
  ring

theorem routeJFiveBumpPhaseDensity_value_moments_zero
    {c L : ℝ} (hL : 0 < L) :
    (∫ t, Real.exp (c * t) *
        routeJFiveBumpPhaseDensity L (Real.exp (c * L)) t) = 0 ∧
      (∫ t, Real.exp (-c * t) *
        routeJFiveBumpPhaseDensity L (Real.exp (c * L)) t) = 0 := by
  let r := Real.exp (c * L)
  have hr : r ≠ 0 := Real.exp_ne_zero _
  constructor
  · rw [integral_exp_mul_routeJFiveBumpPhaseDensity hL]
    change _ * (
      routeJReciprocalDoubleRootCoeff r 0 +
        routeJReciprocalDoubleRootCoeff r 1 * r +
        routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
        routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
        routeJReciprocalDoubleRootCoeff r 4 * r ^ 4) = 0
    rw [routeJReciprocalDoubleRootCoeff_value_at_r hr, mul_zero]
  · rw [integral_exp_mul_routeJFiveBumpPhaseDensity hL]
    have hexp : Real.exp (-c * L) = r⁻¹ := by
      dsimp [r]
      rw [show -c * L = -(c * L) by ring, Real.exp_neg]
    rw [hexp, routeJReciprocalDoubleRootCoeff_value_at_inv hr, mul_zero]

theorem routeJFiveBumpPhaseDensity_derivative_moments_zero
    {c L : ℝ} (hL : 0 < L) :
    (∫ t, t * Real.exp (c * t) *
        routeJFiveBumpPhaseDensity L (Real.exp (c * L)) t) = 0 ∧
      (∫ t, t * Real.exp (-c * t) *
        routeJFiveBumpPhaseDensity L (Real.exp (c * L)) t) = 0 := by
  let r := Real.exp (c * L)
  have hr : r ≠ 0 := Real.exp_ne_zero _
  constructor
  · rw [integral_t_mul_exp_mul_routeJFiveBumpPhaseDensity hL]
    change
      _ * (routeJReciprocalDoubleRootCoeff r 0 +
        routeJReciprocalDoubleRootCoeff r 1 * r +
        routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
        routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
        routeJReciprocalDoubleRootCoeff r 4 * r ^ 4) +
      _ * _ * (routeJReciprocalDoubleRootCoeff r 1 * r +
        2 * routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
        3 * routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
        4 * routeJReciprocalDoubleRootCoeff r 4 * r ^ 4) = 0
    rw [routeJReciprocalDoubleRootCoeff_value_at_r hr,
      routeJReciprocalDoubleRootCoeff_deriv_at_r hr]
    ring
  · rw [integral_t_mul_exp_mul_routeJFiveBumpPhaseDensity hL]
    have hexp : Real.exp (-c * L) = r⁻¹ := by
      dsimp [r]
      rw [show -c * L = -(c * L) by ring, Real.exp_neg]
    rw [hexp, routeJReciprocalDoubleRootCoeff_value_at_inv hr,
      routeJReciprocalDoubleRootCoeff_deriv_at_inv hr]
    ring

theorem routeJFiveBumpSourceDensity_value_row_eq
    {u L r : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi) (q t : ℝ) :
    routeJContinuumSineValueIntegrand q u
        (routeJFiveBumpSourceDensity u L r) t =
      Real.exp (q * t) * routeJFiveBumpPhaseDensity L r t := by
  unfold routeJContinuumSineValueIntegrand
  rw [show routeJFiveBumpSourceDensity u L r t * Real.exp (q * t) *
      Real.sin (u * t) =
        Real.exp (q * t) *
          (Real.sin (u * t) * routeJFiveBumpSourceDensity u L r t) by ring,
    routeJFiveBumpSourceDensity_phase_eq hu hL hchamber]

theorem routeJFiveBumpSourceDensity_derivative_row_eq
    {u L r : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi) (q t : ℝ) :
    routeJContinuumSineDerivativeIntegrand q u
        (routeJFiveBumpSourceDensity u L r) t =
      t * Real.exp (q * t) * routeJFiveBumpPhaseDensity L r t := by
  unfold routeJContinuumSineDerivativeIntegrand
  rw [show t * routeJFiveBumpSourceDensity u L r t * Real.exp (q * t) *
      Real.sin (u * t) =
        t * Real.exp (q * t) *
          (Real.sin (u * t) * routeJFiveBumpSourceDensity u L r t) by ring,
    routeJFiveBumpSourceDensity_phase_eq hu hL hchamber]

theorem integrable_routeJFiveBumpSourceDensity_value_row
    {u L r : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi) (q : ℝ) :
    Integrable
      (routeJContinuumSineValueIntegrand q u
        (routeJFiveBumpSourceDensity u L r)) := by
  exact (integrable_exp_mul_routeJFiveBumpPhaseDensity q L r).congr
    (Eventually.of_forall fun t =>
      (routeJFiveBumpSourceDensity_value_row_eq
        hu hL hchamber q t).symm)

theorem integrable_routeJFiveBumpSourceDensity_derivative_row
    {u L r : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi) (q : ℝ) :
    Integrable
      (routeJContinuumSineDerivativeIntegrand q u
        (routeJFiveBumpSourceDensity u L r)) := by
  exact (integrable_t_mul_exp_mul_routeJFiveBumpPhaseDensity q L r).congr
    (Eventually.of_forall fun t =>
      (routeJFiveBumpSourceDensity_derivative_row_eq
        hu hL hchamber q t).symm)

theorem routeJFiveBumpSourceDensity_four_rows_zero
    {c u L : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi) :
    (∫ t, routeJContinuumSineValueIntegrand c u
        (routeJFiveBumpSourceDensity u L (Real.exp (c * L))) t) = 0 ∧
      (∫ t, routeJContinuumSineValueIntegrand (-c) u
        (routeJFiveBumpSourceDensity u L (Real.exp (c * L))) t) = 0 ∧
      (∫ t, routeJContinuumSineDerivativeIntegrand c u
        (routeJFiveBumpSourceDensity u L (Real.exp (c * L))) t) = 0 ∧
      (∫ t, routeJContinuumSineDerivativeIntegrand (-c) u
        (routeJFiveBumpSourceDensity u L (Real.exp (c * L))) t) = 0 := by
  have hV := routeJFiveBumpPhaseDensity_value_moments_zero
    (c := c) hL
  have hD := routeJFiveBumpPhaseDensity_derivative_moments_zero
    (c := c) hL
  constructor
  · rw [show routeJContinuumSineValueIntegrand c u
        (routeJFiveBumpSourceDensity u L (Real.exp (c * L))) =
      fun t => Real.exp (c * t) *
        routeJFiveBumpPhaseDensity L (Real.exp (c * L)) t by
          funext t
          exact routeJFiveBumpSourceDensity_value_row_eq
            hu hL hchamber c t]
    exact hV.1
  constructor
  · rw [show routeJContinuumSineValueIntegrand (-c) u
        (routeJFiveBumpSourceDensity u L (Real.exp (c * L))) =
      fun t => Real.exp (-c * t) *
        routeJFiveBumpPhaseDensity L (Real.exp (c * L)) t by
          funext t
          exact routeJFiveBumpSourceDensity_value_row_eq
            hu hL hchamber (-c) t]
    exact hV.2
  constructor
  · rw [show routeJContinuumSineDerivativeIntegrand c u
        (routeJFiveBumpSourceDensity u L (Real.exp (c * L))) =
      fun t => t * Real.exp (c * t) *
        routeJFiveBumpPhaseDensity L (Real.exp (c * L)) t by
          funext t
          exact routeJFiveBumpSourceDensity_derivative_row_eq
            hu hL hchamber c t]
    exact hD.1
  · rw [show routeJContinuumSineDerivativeIntegrand (-c) u
        (routeJFiveBumpSourceDensity u L (Real.exp (c * L))) =
      fun t => t * Real.exp (-c * t) *
        routeJFiveBumpPhaseDensity L (Real.exp (c * L)) t by
          funext t
          exact routeJFiveBumpSourceDensity_derivative_row_eq
            hu hL hchamber (-c) t]
    exact hD.2

theorem routeJFiveBumpSourceDensity_support
    {u L r t : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi)
    (hh : routeJFiveBumpSourceDensity u L r t ≠ 0) :
    0 < t ∧ Real.sin (u * t) ≠ 0 := by
  have hs : Real.sin (u * t) ≠ 0 := by
    intro hs
    simp [routeJFiveBumpSourceDensity, hs] at hh
  have hp :
      routeJFiveBumpPhaseDensity L r t ≠ 0 := by
    rw [← routeJFiveBumpSourceDensity_phase_eq hu hL hchamber]
    exact mul_ne_zero hs hh
  exact ⟨(routeJFiveBumpPhaseDensity_support_in_sine_chamber
    hu hL hchamber hp).1, hs⟩

theorem routeJFiveBumpSourceDensity_not_ae_zero
    {u L r : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi) :
    ¬ routeJFiveBumpSourceDensity u L r =ᵐ[volume] 0 := by
  intro hae
  have hnotmem :
      ∀ᵐ t : ℝ ∂volume, t ∉ routeJRectangleBumpSupport L 0 := by
    filter_upwards [hae] with t ht
    intro hmem
    exact (routeJFiveBumpSourceDensity_pos_on_first_bump
      hu hL hchamber hmem).ne' ht
  have hvolzero : volume (routeJRectangleBumpSupport L 0) = 0 := by
    have hz := (ae_iff.mp hnotmem)
    have hset :
        {t : ℝ | ¬t ∉ routeJRectangleBumpSupport L 0} =
          routeJRectangleBumpSupport L 0 := by
      ext t
      simp
    rw [hset] at hz
    exact hz
  have hvolpos : 0 < volume (routeJRectangleBumpSupport L 0) := by
    rw [routeJRectangleBumpSupport, Real.volume_Ioc]
    apply ENNReal.ofReal_pos.mpr
    norm_num
    linarith
  rw [hvolzero] at hvolpos
  exact (lt_irrefl 0 hvolpos)

theorem routeJFiveBumpSourceDensity_four_change_pattern
    {c u L : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi) :
    ∀ t : ℝ,
      0 ≤ (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) *
        (Real.sin (u * t) *
          routeJFiveBumpSourceDensity u L (Real.exp (c * L)) t) := by
  intro t
  rw [routeJFiveBumpSourceDensity_phase_eq hu hL hchamber]
  exact routeJFiveBumpPhaseDensity_four_change_pattern
    hL (Real.exp_pos _) t

theorem routeJFiveBumpSourceDensity_no_three_change_pattern
    {c u L a b d : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hL : 0 < L)
    (hchamber : u * (5 * L) < Real.pi)
    (ha : 0 < a) (hab : a < b) (hbd : b < d) :
    ¬ ((∀ᵐ t : ℝ ∂volume,
          0 ≤ (t - a) * (t - b) * (t - d) *
            (Real.sin (u * t) *
              routeJFiveBumpSourceDensity u L (Real.exp (c * L)) t)) ∨
        (∀ᵐ t : ℝ ∂volume,
          (t - a) * (t - b) * (t - d) *
            (Real.sin (u * t) *
              routeJFiveBumpSourceDensity u L (Real.exp (c * L)) t) ≤ 0)) := by
  intro hpattern
  let h := routeJFiveBumpSourceDensity u L (Real.exp (c * L))
  have hrows := routeJFiveBumpSourceDensity_four_rows_zero
    (c := c) hu hL hchamber
  have hae :
      h =ᵐ[volume] 0 := by
    apply routeJ_nonAtomicContinuum_sineRows_atMostThreeChanges_ae_zero
      hc ha hab hbd
      (Eventually.of_forall fun t ht =>
        routeJFiveBumpSourceDensity_support hu hL hchamber ht)
      hpattern
    · exact integrable_routeJFiveBumpSourceDensity_value_row
        hu hL hchamber c
    · exact integrable_routeJFiveBumpSourceDensity_value_row
        hu hL hchamber (-c)
    · exact integrable_routeJFiveBumpSourceDensity_derivative_row
        hu hL hchamber c
    · exact integrable_routeJFiveBumpSourceDensity_derivative_row
        hu hL hchamber (-c)
    · exact hrows.1
    · exact hrows.2.1
    · exact hrows.2.2.1
    · exact hrows.2.2.2
  exact routeJFiveBumpSourceDensity_not_ae_zero hu hL hchamber hae

/-- **Sharpness of the four-row variation obstruction.** For every positive reflected damping
and carrier frequency, an explicit nonzero Lebesgue density supported in one sine chamber
annihilates all four physical rows and has exactly four phase-weighted sign changes. -/
theorem exists_routeJ_nonAtomicContinuum_exactFourChange_survivor
    {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    ∃ L : ℝ, 0 < L ∧ u * (5 * L) < Real.pi ∧
      let h := routeJFiveBumpSourceDensity u L (Real.exp (c * L))
      (¬ h =ᵐ[volume] 0) ∧
      (∀ t, h t ≠ 0 → 0 < t ∧ Real.sin (u * t) ≠ 0) ∧
      Integrable (routeJContinuumSineValueIntegrand c u h) ∧
      Integrable (routeJContinuumSineValueIntegrand (-c) u h) ∧
      Integrable (routeJContinuumSineDerivativeIntegrand c u h) ∧
      Integrable (routeJContinuumSineDerivativeIntegrand (-c) u h) ∧
      (∫ t, routeJContinuumSineValueIntegrand c u h t) = 0 ∧
      (∫ t, routeJContinuumSineValueIntegrand (-c) u h t) = 0 ∧
      (∫ t, routeJContinuumSineDerivativeIntegrand c u h t) = 0 ∧
      (∫ t, routeJContinuumSineDerivativeIntegrand (-c) u h t) = 0 ∧
      (∀ t,
        0 ≤ (t - L) * (t - 2 * L) * (t - 3 * L) * (t - 4 * L) *
          (Real.sin (u * t) * h t)) ∧
      (∀ a b d, 0 < a → a < b → b < d →
        ¬ ((∀ᵐ t : ℝ ∂volume,
              0 ≤ (t - a) * (t - b) * (t - d) *
                (Real.sin (u * t) * h t)) ∨
            (∀ᵐ t : ℝ ∂volume,
              (t - a) * (t - b) * (t - d) *
                (Real.sin (u * t) * h t) ≤ 0))) := by
  let L := Real.pi / (6 * u)
  have hden : 0 < 6 * u := mul_pos (by norm_num) hu
  have hL : 0 < L := div_pos Real.pi_pos hden
  have hchamber : u * (5 * L) < Real.pi := by
    have hu0 : u ≠ 0 := hu.ne'
    dsimp [L]
    rw [show u * (5 * (Real.pi / (6 * u))) =
      5 * Real.pi / 6 by field_simp [hu0]]
    linarith [Real.pi_pos]
  refine ⟨L, hL, hchamber, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact routeJFiveBumpSourceDensity_not_ae_zero hu hL hchamber
  · intro t ht
    exact routeJFiveBumpSourceDensity_support hu hL hchamber ht
  · exact integrable_routeJFiveBumpSourceDensity_value_row
      hu hL hchamber c
  · exact integrable_routeJFiveBumpSourceDensity_value_row
      hu hL hchamber (-c)
  · exact integrable_routeJFiveBumpSourceDensity_derivative_row
      hu hL hchamber c
  · exact integrable_routeJFiveBumpSourceDensity_derivative_row
      hu hL hchamber (-c)
  · exact (routeJFiveBumpSourceDensity_four_rows_zero
      (c := c) hu hL hchamber).1
  · exact (routeJFiveBumpSourceDensity_four_rows_zero
      (c := c) hu hL hchamber).2.1
  · exact (routeJFiveBumpSourceDensity_four_rows_zero
      (c := c) hu hL hchamber).2.2.1
  · exact (routeJFiveBumpSourceDensity_four_rows_zero
      (c := c) hu hL hchamber).2.2.2
  · exact routeJFiveBumpSourceDensity_four_change_pattern hu hL hchamber
  · intro a b d ha hab hbd
    exact routeJFiveBumpSourceDensity_no_three_change_pattern
      hc hu hL hchamber ha hab hbd

end

end RHTower
