import GaloisForLFunctions.HTGeometry.ClockGapEnvelopeRecovery
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring

/-!
# Sharp recovery at every positive integral gap order

For gap order `k = q + 1`, the possible values `a = u(0)` of an `L`-Lipschitz
real error field satisfying `|x|^k |u(x)| ≤ epsilon` everywhere are exactly

`k^k |a|^(k+1) ≤ (k+1)^(k+1) L^k epsilon`.

The signed distance tent from `ClockGapEnvelopeRecovery` realizes every feasible
value. Homogeneous Bernoulli supplies the sharp polynomial bound without derivatives.
Zero Lipschitz constant, zero noise, zero anchor, and both signs are included.
This classifies the complete error class; it does not derive a Lipschitz estimate
from continuity or use a finite set of observations in place of the global bound.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Sharp homogeneous power-times-affine bound, with all nonnegative data bundled. -/
theorem powerClockGap_polynomial_bound (q : ℕ) (L A t : NNReal) :
    ((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1) * (t : ℝ) ^ (q + 1) *
        ((A : ℝ) - (L : ℝ) * t) ≤
      ((q + 1 : ℕ) : ℝ) ^ (q + 1) * (A : ℝ) ^ (q + 2) := by
  let k := q + 1
  have hk : (0 : ℝ) < k := by dsimp [k]; positivity
  let r : ℝ := ((k + 1 : ℕ) : ℝ) * L * t
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have h := pow_add_mul_le_add_pow (a := r) (b := (k : ℝ) * A - r)
    hr (by nlinarith [A.coe_nonneg]) (k + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [show r + ((k : ℝ) * A - r) = (k : ℝ) * A by ring] at h
  have hleft : r ^ (k + 1) + ((k + 1 : ℕ) : ℝ) * r ^ k * ((k : ℝ) * A - r) =
      (k : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1) * (L : ℝ) ^ k * (t : ℝ) ^ k *
        ((A : ℝ) - (L : ℝ) * t)) := by
    dsimp [r]
    simp only [pow_succ, mul_pow, Nat.cast_add, Nat.cast_one]
    ring
  have hright : ((k : ℝ) * A) ^ (k + 1) =
      (k : ℝ) * ((k : ℝ) ^ k * (A : ℝ) ^ (k + 1)) := by
    rw [mul_pow, pow_succ (k : ℝ)]
    ring
  rw [hleft, hright] at h
  exact (mul_le_mul_iff_right₀ hk).mp h

/-- Exact uniform bound on the least envelope at every positive integral gap order. -/
theorem powerClockGap_envelope_iff (q : ℕ) (L epsilon : NNReal) (a : ℝ) :
    (∀ x : ℝ, |x| ^ (q + 1) * clockGapEnvelope L 0 a x ≤ epsilon) ↔
      ((q + 1 : ℕ) : ℝ) ^ (q + 1) * |a| ^ (q + 2) ≤
        ((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1) * epsilon := by
  simp only [clockGapEnvelope, Real.dist_eq, sub_zero]
  let k := q + 1
  have hk : (0 : ℝ) < k := by dsimp [k]; positivity
  have hkpow : 0 < (k : ℝ) ^ k := pow_pos hk _
  by_cases hL : (L : ℝ) = 0
  · simp only [hL, zero_mul, sub_zero, max_eq_right (abs_nonneg a),
      zero_pow (Nat.succ_ne_zero q), mul_zero]
    constructor
    · intro h
      by_cases ha : a = 0
      · simp [ha]
      · have hA : 0 < |a| := abs_pos.mpr ha
        let t : ℝ := ((epsilon : ℝ) + 1) / |a| + 1
        have ht : 1 ≤ t := by
          dsimp [t]
          have hratio : 0 ≤ ((epsilon : ℝ) + 1) / |a| := by positivity
          linarith
        have htp : t ≤ t ^ (q + 1) := by
          have hp : 1 ≤ t ^ q := one_le_pow₀ ht
          rw [pow_succ]
          nlinarith
        have hh := h t
        rw [abs_of_nonneg (by linarith : 0 ≤ t)] at hh
        have heq : t * |a| = (epsilon : ℝ) + 1 + |a| := by
          dsimp [t]
          rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hA), one_mul]
        nlinarith [mul_le_mul_of_nonneg_right htp (abs_nonneg a)]
    · intro h x
      have ha : a = 0 := by
        by_contra ha
        have hp : 0 < (k : ℝ) ^ k * |a| ^ (k + 1) :=
          mul_pos hkpow (pow_pos (abs_pos.mpr ha) _)
        exact (not_le_of_gt hp) h
      simp [ha]
  · have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne L.coe_nonneg (Ne.symm hL)
    let B : ℝ := ((k + 1 : ℕ) : ℝ) ^ (k + 1) * (L : ℝ) ^ k
    have hB : 0 < B := by dsimp [B]; positivity
    constructor
    · intro h
      let t : ℝ := (k : ℝ) * |a| / (((k + 1 : ℕ) : ℝ) * L)
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have htrel : ((k + 1 : ℕ) : ℝ) * L * t = (k : ℝ) * |a| := by
        dsimp [t]
        field_simp
      have hcrest : ((k + 1 : ℕ) : ℝ) * (|a| - (L : ℝ) * t) = |a| := by
        push_cast at htrel ⊢
        nlinarith
      have hid : B * (t ^ k * (|a| - (L : ℝ) * t)) =
          (k : ℝ) ^ k * |a| ^ (k + 1) := by
        calc
          _ = (((k + 1 : ℕ) : ℝ) * L * t) ^ k *
              (((k + 1 : ℕ) : ℝ) * (|a| - (L : ℝ) * t)) := by
                dsimp [B]
                simp only [mul_pow, pow_succ]
                ring
          _ = (k : ℝ) ^ k * |a| ^ (k + 1) := by
            rw [htrel, hcrest, mul_pow, pow_succ]
            ring
      have hh := h t
      rw [abs_of_nonneg ht] at hh
      have hlo := le_max_right (0 : ℝ) (|a| - (L : ℝ) * t)
      have hprod := (mul_le_mul_of_nonneg_left hlo (pow_nonneg ht (q + 1))).trans hh
      change (k : ℝ) ^ k * |a| ^ (k + 1) ≤ B * epsilon
      rw [← hid]
      exact mul_le_mul_of_nonneg_left hprod hB.le
    · intro h x
      by_cases hx : 0 ≤ |a| - (L : ℝ) * |x|
      · rw [max_eq_right hx]
        apply (mul_le_mul_iff_right₀ hB).mp
        calc
          B * (|x| ^ (q + 1) * (|a| - (L : ℝ) * |x|)) =
              B * |x| ^ (q + 1) * (|a| - (L : ℝ) * |x|) := by ring
          _ ≤ ((q + 1 : ℕ) : ℝ) ^ (q + 1) * |a| ^ (q + 2) :=
            powerClockGap_polynomial_bound q L ⟨|a|, abs_nonneg a⟩ ⟨|x|, abs_nonneg x⟩
          _ ≤ B * epsilon := h
      · rw [max_eq_left (le_of_not_ge hx), mul_zero]
        exact epsilon.coe_nonneg

/-- Complete feasible-anchor classification, including all zero endpoint cases. -/
theorem powerClockGap_feasible_iff (q : ℕ) (L epsilon : NNReal) (a : ℝ) :
    (∃ u : ℝ → ℝ, LipschitzWith L u ∧ u 0 = a ∧
      ∀ x : ℝ, |x| ^ (q + 1) * |u x| ≤ epsilon) ↔
      ((q + 1 : ℕ) : ℝ) ^ (q + 1) * |a| ^ (q + 2) ≤
        ((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1) * epsilon := by
  exact (weightedClockGap_feasible_iff L epsilon
    (fun x : ℝ => ⟨|x| ^ (q + 1), pow_nonneg (abs_nonneg x) _⟩) 0 a).trans
    (powerClockGap_envelope_iff q L epsilon a)

/-- The explicit signed tent meets exactly the sharp feasible-anchor condition. -/
theorem powerClockGap_extremizer_bound_iff (q : ℕ) (L epsilon : NNReal) (a : ℝ) :
    (∀ x : ℝ, |x| ^ (q + 1) * |clockGapExtremizer L 0 a x| ≤ epsilon) ↔
      ((q + 1 : ℕ) : ℝ) ^ (q + 1) * |a| ^ (q + 2) ≤
        ((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1) * epsilon := by
  simp only [clockGapExtremizer_abs]
  exact powerClockGap_envelope_iff q L epsilon a

end GaloisForLFunctions.HTGeometry
