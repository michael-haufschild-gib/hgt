import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The alternating harmonic tail

The even alternating harmonic partial sum is the harmonic difference `H_{2c} - H_c`, and the
geometric identity `∑_{i < m} (-x)^i = (1 - (-x)^m)/(1+x)` integrates on `[0,1]` to

`∑_{i < m} (-1)^i/(i+1) = log 2 - (-1)^m ∫_0^1 x^m/(1+x) dx`.

Splitting `1/(1+x) = 1/2 + (1-x)/(2(1+x))` evaluates the tail to `1/(2(m+1))` up to an error of at
most `1/(2(m+1)(m+2))`.  Together these give the exact expansion

`H_{2c} - H_c - log 2 = -1/(2(2c+1)) + O(c^{-2})`,

which is the second-order Euler--Maclaurin correction obtained without any Euler--Maclaurin
machinery.
-/

open Real MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-- The alternating harmonic partial sum. -/
def burnolAlternatingHarmonic (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i / (i + 1)

/-- The alternating harmonic tail integral. -/
def burnolAltTail (m : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, x ^ m / (1 + x)

theorem burnolHarmonic_range (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1) := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih =>
      rw [harmonic_succ, Finset.sum_range_succ, ← ih]
      push_cast
      ring

/-- **The even alternating harmonic sum is a harmonic difference.** -/
theorem burnolAlternatingHarmonic_two_mul (c : ℕ) :
    burnolAlternatingHarmonic (2 * c) = ((harmonic (2 * c) : ℚ) : ℝ) - ((harmonic c : ℚ) : ℝ) := by
  induction c with
  | zero => simp [burnolAlternatingHarmonic, harmonic]
  | succ c ih =>
      have hstep : 2 * (c + 1) = (2 * c + 1) + 1 := by ring
      rw [burnolAlternatingHarmonic] at ih ⊢
      rw [hstep, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        burnolHarmonic_range, burnolHarmonic_range, burnolHarmonic_range,
        burnolHarmonic_range, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have hpar : (-1 : ℝ) ^ (2 * c) = 1 := by
        rw [pow_mul]
        norm_num
      have hpar' : (-1 : ℝ) ^ (2 * c + 1) = -1 := by
        rw [pow_succ, hpar]
        ring
      rw [hpar, hpar']
      have hc1 : ((c : ℝ) + 1) ≠ 0 := by positivity
      have hc2 : ((2 * c : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      have hc3 : ((2 * c + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      push_cast at hc2 hc3 ⊢
      field_simp
      ring

/-! ## The tail integral -/

theorem burnolIntervalIntegrable_pow_div (m : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ m / (1 + x)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine ContinuousOn.div (continuousOn_pow m) (by fun_prop) ?_
  intro x hx
  have : (0 : ℝ) ≤ x := hx.1
  positivity

theorem integral_one_div_one_add : (∫ x in (0 : ℝ)..1, 1 / (1 + x)) = Real.log 2 := by
  have hcomp : (∫ x in (0 : ℝ)..1, (fun u : ℝ => 1 / u) (x + 1)) =
      ∫ u in (0 + 1 : ℝ)..(1 + 1), 1 / u :=
    intervalIntegral.integral_comp_add_right (fun u : ℝ => 1 / u) 1
  have hnot : (0 : ℝ) ∉ Set.uIcc (0 + 1 : ℝ) (1 + 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 + 1 : ℝ) ≤ 1 + 1)]
    intro hc
    have := hc.1
    norm_num at this
  have hcongr : (∫ x in (0 : ℝ)..1, 1 / (1 + x)) =
      ∫ x in (0 : ℝ)..1, (fun u : ℝ => 1 / u) (x + 1) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [add_comm]
  rw [hcongr, hcomp, integral_one_div hnot]
  norm_num

/-- **The alternating partial sum through the tail integral.** -/
theorem burnolAlternatingHarmonic_eq (m : ℕ) :
    burnolAlternatingHarmonic m = Real.log 2 - (-1 : ℝ) ^ m * burnolAltTail m := by
  have hgeom : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (∑ i ∈ Finset.range m, (-x) ^ i) = (1 - (-x) ^ m) / (1 + x) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hne : (-x : ℝ) ≠ 1 := by
      intro hc
      have : x = -1 := by linarith [hc]
      linarith [hx.1]
    rw [geom_sum_eq hne]
    have hden : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    field_simp
    ring
  have hleft : (∫ x in (0 : ℝ)..1, ∑ i ∈ Finset.range m, (-x) ^ i) =
      burnolAlternatingHarmonic m := by
    have hcongr : (∫ x in (0 : ℝ)..1, ∑ i ∈ Finset.range m, (-x) ^ i) =
        ∫ x in (0 : ℝ)..1, ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * x ^ i := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      exact Finset.sum_congr rfl fun i _ => by rw [neg_pow]
    rw [hcongr, intervalIntegral.integral_finsetSum
      (fun i _ => (((continuous_pow i).intervalIntegrable 0 1).const_mul _)),
      burnolAlternatingHarmonic]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    rw [div_eq_mul_inv]
  have hright : (∫ x in (0 : ℝ)..1, (1 - (-x) ^ m) / (1 + x)) =
      Real.log 2 - (-1 : ℝ) ^ m * burnolAltTail m := by
    have hcongr : (∫ x in (0 : ℝ)..1, (1 - (-x) ^ m) / (1 + x)) =
        ∫ x in (0 : ℝ)..1, (1 / (1 + x) - (-1 : ℝ) ^ m * (x ^ m / (1 + x))) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hden : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
      rw [neg_pow]
      field_simp
    rw [hcongr, intervalIntegral.integral_sub
      (by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
        intro x hx
        have : (0 : ℝ) ≤ x := hx.1
        positivity)
      ((burnolIntervalIntegrable_pow_div m).const_mul _),
      integral_one_div_one_add, intervalIntegral.integral_const_mul, burnolAltTail]
  rw [← hleft, intervalIntegral.integral_congr hgeom, hright]

/-! ## The exact size of the tail -/

theorem burnolAltTail_split (m : ℕ) :
    burnolAltTail m = 1 / (2 * (m + 1)) +
      (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) / (1 + x)) / 2 := by
  have hint2 : IntervalIntegrable (fun x : ℝ => x ^ m * (1 - x) / (1 + x)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have : (0 : ℝ) ≤ x := hx.1
    positivity
  have hcongr : (fun x : ℝ => x ^ m / (1 + x)) =ᶠ[Filter.principal (Set.uIcc (0 : ℝ) 1)]
      fun x : ℝ => x ^ m / 2 + x ^ m * (1 - x) / (1 + x) / 2 := by
    rw [Filter.eventuallyEq_principal]
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hden : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    field_simp
    ring
  rw [burnolAltTail, intervalIntegral.integral_congr (Filter.eventuallyEq_principal.mp hcongr),
    intervalIntegral.integral_add
      (((continuous_pow m).intervalIntegrable 0 1).div_const 2) (hint2.div_const 2),
    intervalIntegral.integral_div, intervalIntegral.integral_div, integral_pow]
  norm_num
  ring

theorem burnolAltTailRemainder_nonneg (m : ℕ) :
    0 ≤ ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) / (1 + x) := by
  refine intervalIntegral.integral_nonneg (by norm_num) fun x hx => ?_
  have h0 : (0 : ℝ) ≤ x := hx.1
  have h1 : x ≤ 1 := hx.2
  positivity

theorem burnolAltTailRemainder_le (m : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) / (1 + x)) ≤ 1 / ((m + 1) * (m + 2)) := by
  have hint2 : IntervalIntegrable (fun x : ℝ => x ^ m * (1 - x) / (1 + x)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have : (0 : ℝ) ≤ x := hx.1
    positivity
  have hint3 : IntervalIntegrable (fun x : ℝ => x ^ m - x ^ (m + 1)) volume 0 1 :=
    ((continuous_pow m).intervalIntegrable 0 1).sub ((continuous_pow (m + 1)).intervalIntegrable 0 1)
  have hmono : (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) / (1 + x)) ≤
      ∫ x in (0 : ℝ)..1, (x ^ m - x ^ (m + 1)) := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint2 hint3 fun x hx => ?_
    have h0 : (0 : ℝ) ≤ x := hx.1
    have h1 : x ≤ 1 := hx.2
    have hden : (1 : ℝ) ≤ 1 + x := by linarith
    have hnum : (0 : ℝ) ≤ x ^ m * (1 - x) := by positivity
    have hstep : x ^ m * (1 - x) / (1 + x) ≤ x ^ m * (1 - x) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hnum, hden]
    have hexp : x ^ m * (1 - x) = x ^ m - x ^ (m + 1) := by ring
    linarith [hstep, hexp.le, hexp.ge]
  refine le_trans hmono (le_of_eq ?_)
  rw [intervalIntegral.integral_sub ((continuous_pow m).intervalIntegrable 0 1)
    ((continuous_pow (m + 1)).intervalIntegrable 0 1), integral_pow, integral_pow]
  have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The exact second-order size of the alternating harmonic difference.** -/
theorem abs_burnolAltTail_sub_le (m : ℕ) :
    |burnolAltTail m - 1 / (2 * (m + 1))| ≤ 1 / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  rw [burnolAltTail_split m]
  have h0 := burnolAltTailRemainder_nonneg m
  have h1 := burnolAltTailRemainder_le m
  have hpos : (0 : ℝ) < ((m : ℝ) + 1) * ((m : ℝ) + 2) := by positivity
  rw [show 1 / (2 * ((m : ℝ) + 1)) + (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) / (1 + x)) / 2 -
      1 / (2 * ((m : ℝ) + 1)) = (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) / (1 + x)) / 2 by ring,
    abs_le]
  constructor
  · have hp2 : (0 : ℝ) ≤ 1 / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2)) := by positivity
    linarith
  · have hid : 1 / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2)) =
        (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) / 2 := by
      field_simp
    rw [hid]
    linarith

end RHTower
