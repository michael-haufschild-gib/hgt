import GaloisForLFunctions.HTGeometry.DiscreteAbelRing
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Signed Abel cancellation of centered modular ramps

The zero-mean residue ramp has an exact nonpositive quadratic primitive.
Decreasing nonnegative weights preserve this orientation and charge the response
only to the initial weight. At square-root hyperbola births this yields a uniform
`1/16` response budget, including the moving terminal block.
-/

noncomputable section
open Finset
namespace HTGeometry

/-- The zero-mean residue ramp on the integers modulo `d`. -/
def centeredModularRamp (d k : ℕ) : ℝ :=
  ((k % d : ℕ) : ℝ) / d - ((d : ℝ) - 1) / (2 * d)

/-- The exact quadratic primitive of the centered residue ramp. -/
def centeredModularPrimitive (d N : ℕ) : ℝ :=
  ((N % d : ℕ) : ℝ) * (((N % d : ℕ) : ℝ) - d) / (2 * d)

@[simp] theorem centeredModularPrimitive_zero (d : ℕ) :
    centeredModularPrimitive d 0 = 0 := by
  simp [centeredModularPrimitive]

/-- Discrete differentiation of the quadratic primitive includes the wrap at every period. -/
theorem centeredModularPrimitive_succ {d : ℕ} (hd : 0 < d) (N : ℕ) :
    centeredModularPrimitive d (N + 1) - centeredModularPrimitive d N =
      centeredModularRamp d N := by
  have hres : N % d < d := Nat.mod_lt N hd
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hmod : (N + 1) % d = (N % d + 1) % d := by simp [Nat.add_mod]
  by_cases h : N % d + 1 < d
  · have heq : (N + 1) % d = N % d + 1 := by rw [hmod, Nat.mod_eq_of_lt h]
    unfold centeredModularPrimitive centeredModularRamp
    rw [heq]
    push_cast
    field_simp
    ring
  · have heq : (N + 1) % d = 0 := by
      rw [hmod, show N % d + 1 = d by omega, Nat.mod_self]
    have hlast : ((N % d : ℕ) : ℝ) + 1 = d := by exact_mod_cast (show N % d + 1 = d by omega)
    unfold centeredModularPrimitive centeredModularRamp
    rw [heq]
    push_cast
    field_simp
    nlinarith

/-- Complete periods cancel exactly; a partial period retains only its quadratic residue. -/
theorem sum_centeredModularRamp (d N : ℕ) :
    (∑ k ∈ range N, centeredModularRamp d k) = centeredModularPrimitive d N := by
  by_cases hd : d = 0
  · subst d
    simp [centeredModularRamp, centeredModularPrimitive]
  · induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      have h := centeredModularPrimitive_succ (by omega : 0 < d) N
      linarith

/-- All partial periods have the same nonpositive orientation and a quadratic-width budget. -/
theorem centeredModularPrimitive_bounds (d N : ℕ) :
    -(d : ℝ) / 8 ≤ centeredModularPrimitive d N ∧
      centeredModularPrimitive d N ≤ 0 := by
  by_cases hd : d = 0
  · subst d
    simp [centeredModularPrimitive]
  · have hdR : (0 : ℝ) < d := by positivity
    have hr : (0 : ℝ) ≤ ((N % d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrd : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N (by omega)).le
    unfold centeredModularPrimitive
    constructor
    · rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (((N % d : ℕ) : ℝ) - (d : ℝ) / 2)]
    · apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hrd)
      · positivity

/-- The weighted response preserves the signed primitive, including the terminal boundary. -/
theorem sum_centeredModularRamp_mul_eq (d N : ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ range N, centeredModularRamp d k * w k) =
      (∑ k ∈ range N, centeredModularPrimitive d (k+1) * (w k - w (k+1))) +
        centeredModularPrimitive d N * w N := by
  by_cases hd : d = 0
  · subst d
    simp [centeredModularRamp, centeredModularPrimitive]
  · induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, sum_range_succ, ih]
      have h := centeredModularPrimitive_succ (by omega : 0 < d) N
      nlinarith [congrArg (fun x : ℝ => x * w N) h]

/-- For decreasing nonnegative weights, every complete weighted residue response is nonpositive
and its absolute size is charged only to the initial weight. -/
theorem sum_centeredModularRamp_mul_bounds (d N : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w) :
    -(d : ℝ) / 8 * w 0 ≤ (∑ k ∈ range N, centeredModularRamp d k * w k) ∧
      (∑ k ∈ range N, centeredModularRamp d k * w k) ≤ 0 := by
  rw [sum_centeredModularRamp_mul_eq]
  have hdelta (k : ℕ) : 0 ≤ w k - w (k+1) := sub_nonneg.mpr (hmono (by omega))
  have htel : (∑ k ∈ range N, (w k - w (k+1))) + w N = w 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ]; linarith
  constructor
  · have hs : (∑ k ∈ range N, -(d : ℝ) / 8 * (w k - w (k+1))) ≤
        ∑ k ∈ range N, centeredModularPrimitive d (k+1) * (w k - w (k+1)) := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (centeredModularPrimitive_bounds d (k+1)).1 (hdelta k)
    have ht := mul_le_mul_of_nonneg_right (centeredModularPrimitive_bounds d N).1 (hw N)
    rw [← mul_sum] at hs
    have hm := congrArg (fun x : ℝ => -(d : ℝ) / 8 * x) htel
    nlinarith only [hs, ht, hm]
  · apply add_nonpos
    · apply sum_nonpos
      intro k _
      exact mul_nonpos_of_nonpos_of_nonneg (centeredModularPrimitive_bounds d (k+1)).2 (hdelta k)
    · exact mul_nonpos_of_nonpos_of_nonneg (centeredModularPrimitive_bounds d N).2 (hw N)

/-- Half-order Abel step at a shifted integer time. -/
def halfOrderAbelStep (B k : ℕ) : ℝ :=
  Real.sqrt (B+k+1 : ℕ) - Real.sqrt (B+k : ℕ)

theorem halfOrderAbelStep_nonneg (B k : ℕ) : 0 ≤ halfOrderAbelStep B k := by
  apply sub_nonneg.mpr
  exact Real.sqrt_le_sqrt (by exact_mod_cast (show B+k ≤ B+k+1 by omega))

theorem halfOrderAbelStep_antitone (B : ℕ) : Antitone (halfOrderAbelStep B) := by
  intro i j hij
  have hi := Real.sq_sqrt (show (0:ℝ) ≤ B+i from by positivity)
  have hi1 := Real.sq_sqrt (show (0:ℝ) ≤ B+i+1 from by positivity)
  have hj := Real.sq_sqrt (show (0:ℝ) ≤ B+j from by positivity)
  have hj1 := Real.sq_sqrt (show (0:ℝ) ≤ B+j+1 from by positivity)
  have hroot : Real.sqrt (B+i : ℕ) ≤ Real.sqrt (B+j : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij B)
  have hroot1 : Real.sqrt (B+i+1 : ℕ) ≤ Real.sqrt (B+j+1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show B+i+1 ≤ B+j+1 by omega))
  have hi0 := halfOrderAbelStep_nonneg B i
  have hj0 := halfOrderAbelStep_nonneg B j
  unfold halfOrderAbelStep at hi0 hj0 ⊢
  have hprod :
      (Real.sqrt (B+j+1 : ℕ) - Real.sqrt (B+j : ℕ)) *
        (Real.sqrt (B+i+1 : ℕ) + Real.sqrt (B+i : ℕ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (add_le_add hroot1 hroot) hj0
    push_cast at hi hi1 hj hj1 h ⊢
    nlinarith
  have hpos : 0 < Real.sqrt (B+i+1 : ℕ) + Real.sqrt (B+i : ℕ) := by positivity
  push_cast at hi hi1 hj hj1 hprod hpos ⊢
  nlinarith

/-- At its hyperbola birth, each residue channel has a uniform half-order boundary budget. -/
theorem halfOrderAbelStep_square_initial (d : ℕ) :
    (d : ℝ) * halfOrderAbelStep (d*d) 0 ≤ 1/2 := by
  have hd := Real.sqrt_mul_self (Nat.cast_nonneg (α := ℝ) d)
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ (d*d+1 : ℕ) from by positivity)
  have hstep := sq_nonneg (Real.sqrt (d*d+1 : ℕ) - d)
  simp only [halfOrderAbelStep, Nat.add_zero]
  push_cast at hd hsq hstep ⊢
  rw [hd]
  nlinarith

/-- Every literal centered hyperbola channel has nonpositive half-order response, with a
uniform `1/16` ceiling on its magnitude, independently of modulus and moving upper cutoff. -/
theorem sum_centeredModularRamp_halfOrder_bounds (d N : ℕ) :
    -(1/16 : ℝ) ≤
      (∑ k ∈ range N, centeredModularRamp d k * halfOrderAbelStep (d*d) k) ∧
    (∑ k ∈ range N, centeredModularRamp d k * halfOrderAbelStep (d*d) k) ≤ 0 := by
  have h := sum_centeredModularRamp_mul_bounds d N (halfOrderAbelStep (d*d))
    (halfOrderAbelStep_nonneg _) (halfOrderAbelStep_antitone _)
  have hi := halfOrderAbelStep_square_initial d
  constructor
  · nlinarith [h.1]
  · exact h.2

/-- Birth at a complete period preserves every residue coefficient. -/
@[simp] theorem centeredModularRamp_mul_add (d b k : ℕ) :
    centeredModularRamp d (d*b+k) = centeredModularRamp d k := by
  simp [centeredModularRamp, Nat.add_mod]

/-- The same uniform bound in the literal moving hyperbola interval. Empty intervals are
included, so the statement requires no cutoff or positivity hypotheses. -/
theorem sum_centeredModularRamp_halfOrder_Ico_bounds (d M : ℕ) :
    -(1/16 : ℝ) ≤
      (∑ k ∈ Ico (d*d) M, centeredModularRamp d k * halfOrderAbelStep 0 k) ∧
    (∑ k ∈ Ico (d*d) M, centeredModularRamp d k * halfOrderAbelStep 0 k) ≤ 0 := by
  have h := sum_centeredModularRamp_halfOrder_bounds d (M-d*d)
  rw [Finset.sum_Ico_eq_sum_range]
  simpa only [centeredModularRamp_mul_add,
    halfOrderAbelStep, Nat.zero_add] using h

end HTGeometry
