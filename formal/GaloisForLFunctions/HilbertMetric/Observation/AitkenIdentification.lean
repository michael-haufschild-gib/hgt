import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Three-point identification with an unknown offset

Aitken differencing, as in arXiv:2611.13534, Corollary 3.2, removes a
constant observation offset and identifies a geometric mode. The exact
formulas include zero amplitudes and constant modes.
-/

namespace GaloisForLFunctions.HilbertMetric.Observation
noncomputable section
open scoped Classical
variable {K : Type*} [Field K]
/-- Three-point extrapolation of the constant component. -/
def aitkenOffset (x y z : K) : K := x - (y - x) ^ 2 / (z - 2 * y + x)
/-- Ratio of consecutive first differences; insensitive to additive offsets. -/
def differenceRatio (x y z : K) : K := (z - y) / (y - x)
/-- Exact extrapolation, including the constant-sequence degeneracy. -/
theorem aitkenOffset_geometric (c a q : K) :
    aitkenOffset (c + a) (c + a * q) (c + a * q ^ 2) =
      if q = 1 then c + a else c := by
  classical
  by_cases hq : q = 1
  · subst q
    simp [aitkenOffset]
  · rw [if_neg hq]
    by_cases ha : a = 0
    · subst a
      simp [aitkenOffset]
    · have hd : a * (q - 1) ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero _ (sub_ne_zero.mpr hq))
      unfold aitkenOffset
      rw [show c + a * q ^ 2 - 2 * (c + a * q) + (c + a) = a * (q - 1) ^ 2 by ring]
      field_simp
      ring

/-- A nonconstant geometric component is identified by three observations. -/
theorem differenceRatio_geometric (c a q : K) :
    differenceRatio (c + a) (c + a * q) (c + a * q ^ 2) =
      if a = 0 ∨ q = 1 then 0 else q := by
  classical
  by_cases h : a = 0 ∨ q = 1
  · rcases h with ha | hq
    · subst a
      simp [differenceRatio]
    · subst q
      simp [differenceRatio]
  · rw [if_neg h]
    have ha : a ≠ 0 := fun ha => h (Or.inl ha)
    have hq : q ≠ 1 := fun hq => h (Or.inr hq)
    have hd := mul_ne_zero ha (sub_ne_zero.mpr hq)
    unfold differenceRatio
    rw [show c + a * q - (c + a) = a * (q - 1) by ring]
    field_simp
    ring
/-- A sampled decaying exponential with arbitrary offset and positive amplitude. -/
def shiftedExponential (c a t : ℝ) (n : ℕ) : ℝ :=
  c + Real.exp a * Real.exp (-Real.exp t) ^ n

/-- Three consecutive observations recover the offset at every sampling depth. -/
theorem shiftedExponential_offset (c a t : ℝ) (n : ℕ) :
    aitkenOffset (shiftedExponential c a t n)
      (shiftedExponential c a t (n + 1))
      (shiftedExponential c a t (n + 2)) = c := by
  have hq : Real.exp (-Real.exp t) ≠ 1 :=
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos t))).ne
  simpa only [shiftedExponential, pow_add, pow_one, ← mul_assoc, if_neg hq] using
    aitkenOffset_geometric c (Real.exp a * Real.exp (-Real.exp t) ^ n)
      (Real.exp (-Real.exp t))

/-- The logarithm of the difference ratio recovers the decay rate. -/
theorem shiftedExponential_rate (c a t : ℝ) (n : ℕ) :
    -Real.log (differenceRatio (shiftedExponential c a t n)
      (shiftedExponential c a t (n + 1))
      (shiftedExponential c a t (n + 2))) = Real.exp t := by
  have hq : Real.exp (-Real.exp t) ≠ 1 :=
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos t))).ne
  have ha : Real.exp a * Real.exp (-Real.exp t) ^ n ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero a) (pow_ne_zero _ (Real.exp_ne_zero _))
  have h := differenceRatio_geometric c
    (Real.exp a * Real.exp (-Real.exp t) ^ n) (Real.exp (-Real.exp t))
  simp only [ha, hq, false_or, if_false] at h
  have hratio : differenceRatio (shiftedExponential c a t n)
      (shiftedExponential c a t (n + 1))
      (shiftedExponential c a t (n + 2)) = Real.exp (-Real.exp t) := by
    simpa only [shiftedExponential, pow_add, pow_one, ← mul_assoc] using h
  rw [hratio, Real.log_exp, neg_neg]

#print axioms aitkenOffset_geometric
#print axioms differenceRatio_geometric
#print axioms shiftedExponential_offset
#print axioms shiftedExponential_rate

end
end GaloisForLFunctions.HilbertMetric.Observation
