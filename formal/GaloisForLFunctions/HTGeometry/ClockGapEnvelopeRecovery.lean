import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Exact recovery across a weighted observation gap

For any nonnegative observation weight on a pseudometric space, the possible
anchor values of a Lipschitz error field are classified by an explicit envelope.
One signed distance tent attains the least absolute value at every point at once.
The equivalent affine criterion contains neither division by the gap nor an
unknown field. For the linear gap on the real line, feasibility is exactly
`a ^ 2 ≤ 4 * L * epsilon`, including zero noise and zero Lipschitz constant.

This supplies a quantitative companion to continuous clock recovery through mass
collisions. It is an exact classification of the stated Lipschitz error class;
it does not infer a Lipschitz bound from continuity alone.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

/-- The least possible absolute size forced by an anchor value and a Lipschitz bound. -/
def clockGapEnvelope (L : NNReal) (p : X) (a : ℝ) (x : X) : ℝ :=
  max 0 (|a| - (L : ℝ) * dist x p)

/-- A signed distance tent realizing the least envelope simultaneously everywhere. -/
def clockGapExtremizer (L : NNReal) (p : X) (a : ℝ) (x : X) : ℝ :=
  if 0 ≤ a then clockGapEnvelope L p a x else -clockGapEnvelope L p a x

/-- Taking the positive part preserves the distance cone Lipschitz constant. -/
theorem clockGapEnvelope_lipschitz (L : NNReal) (p : X) (a : ℝ) :
    LipschitzWith L (clockGapEnvelope L p a) := by
  have h : LipschitzWith L (fun x : X => |a| - (L : ℝ) * dist x p) := by
    apply LipschitzWith.of_le_add_mul
    intro x y
    have hd := dist_triangle y x p
    rw [dist_comm y x] at hd
    nlinarith [mul_le_mul_of_nonneg_left hd L.coe_nonneg]
  exact h.const_max 0

/-- The extremizer attains the envelope at every point. -/
theorem clockGapExtremizer_abs (L : NNReal) (p : X) (a : ℝ) (x : X) :
    |clockGapExtremizer L p a x| = clockGapEnvelope L p a x := by
  have h : 0 ≤ clockGapEnvelope L p a x := le_max_left _ _
  simp only [clockGapExtremizer]
  split <;> simp [abs_of_nonneg h]

/-- Both signs of the prescribed anchor value are realized exactly. -/
theorem clockGapExtremizer_anchor (L : NNReal) (p : X) (a : ℝ) :
    clockGapExtremizer L p a p = a := by
  simp only [clockGapExtremizer, clockGapEnvelope, dist_self, mul_zero, sub_zero,
    max_eq_right (abs_nonneg a)]
  split
  · exact abs_of_nonneg ‹0 ≤ a›
  · rw [abs_of_neg (lt_of_not_ge ‹¬0 ≤ a›), neg_neg]

/-- The signed extremizer has the prescribed Lipschitz constant. -/
theorem clockGapExtremizer_lipschitz (L : NNReal) (p : X) (a : ℝ) :
    LipschitzWith L (clockGapExtremizer L p a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases ha : 0 ≤ a
  · simpa only [clockGapExtremizer, if_pos ha] using
      (clockGapEnvelope_lipschitz L p a).dist_le_mul x y
  · simp only [clockGapExtremizer, if_neg ha, Real.dist_eq]
    rw [show -clockGapEnvelope L p a x - -clockGapEnvelope L p a y =
      -(clockGapEnvelope L p a x - clockGapEnvelope L p a y) by linarith, abs_neg]
    simpa only [Real.dist_eq] using (clockGapEnvelope_lipschitz L p a).dist_le_mul x y

/-- The envelope is the attained minimum over all fields with the prescribed anchor. -/
theorem clockGapEnvelope_isLeast (L : NNReal) (p : X) (a : ℝ) (x : X) :
    IsLeast {r : ℝ | ∃ u : X → ℝ, LipschitzWith L u ∧ u p = a ∧ |u x| = r}
      (clockGapEnvelope L p a x) := by
  constructor
  · exact ⟨clockGapExtremizer L p a, clockGapExtremizer_lipschitz L p a,
      clockGapExtremizer_anchor L p a, clockGapExtremizer_abs L p a x⟩
  · rintro b ⟨u, hu, ha, rfl⟩
    apply max_le (abs_nonneg _)
    have hlip := hu.dist_le_mul x p
    rw [Real.dist_eq, ha] at hlip
    have hrev := abs_abs_sub_abs_le_abs_sub (u x) a
    have hneg := neg_le_abs (|u x| - |a|)
    linarith

/-- Exact feasible-anchor classification for arbitrary nonnegative gap weights. -/
theorem weightedClockGap_feasible_iff (L epsilon : NNReal) (g : X → NNReal)
    (p : X) (a : ℝ) :
    (∃ u : X → ℝ, LipschitzWith L u ∧ u p = a ∧
      ∀ x, (g x : ℝ) * |u x| ≤ epsilon) ↔
    ∀ x, (g x : ℝ) * clockGapEnvelope L p a x ≤ epsilon := by
  constructor
  · rintro ⟨u, hu, ha, hbound⟩ x
    exact (mul_le_mul_of_nonneg_left
      ((clockGapEnvelope_isLeast L p a x).2 ⟨u, hu, ha, rfl⟩)
      (g x).coe_nonneg).trans (hbound x)
  · intro h
    exact ⟨clockGapExtremizer L p a, clockGapExtremizer_lipschitz L p a,
      clockGapExtremizer_anchor L p a, fun x => by rw [clockGapExtremizer_abs]; exact h x⟩

/-- Exact feasibility without division by the gap or an unknown function. -/
theorem weightedClockGap_feasible_iff_affine (L epsilon : NNReal) (g : X → NNReal)
    (p : X) (a : ℝ) :
    (∃ u : X → ℝ, LipschitzWith L u ∧ u p = a ∧
      ∀ x, (g x : ℝ) * |u x| ≤ epsilon) ↔
    ∀ x, (g x : ℝ) * |a| ≤ (epsilon : ℝ) + (g x : ℝ) * L * dist x p := by
  rw [weightedClockGap_feasible_iff]
  constructor
  · intro h x
    have hm := mul_le_mul_of_nonneg_left
      (le_max_right (0 : ℝ) (|a| - (L : ℝ) * dist x p)) (g x).coe_nonneg
    have hb := h x
    dsimp [clockGapEnvelope] at hb
    nlinarith
  · intro h x
    dsimp [clockGapEnvelope]
    by_cases hx : 0 ≤ |a| - (L : ℝ) * dist x p
    · rw [max_eq_right hx]
      nlinarith [h x]
    · rw [max_eq_left (le_of_not_ge hx), mul_zero]
      exact epsilon.coe_nonneg

/-- The exact tent bound for the linear gap, with all zero endpoints included. -/
theorem linearClockGap_envelope_iff (L epsilon : NNReal) (a : ℝ) :
    (∀ x : ℝ, |x| * clockGapEnvelope L 0 a x ≤ epsilon) ↔
      a ^ 2 ≤ 4 * (L : ℝ) * epsilon := by
  simp only [clockGapEnvelope, Real.dist_eq, sub_zero]
  by_cases hL : (L : ℝ) = 0
  · simp only [hL, zero_mul, sub_zero, max_eq_right (abs_nonneg a)]
    constructor
    · intro h
      by_cases ha : a = 0
      · simp [ha]
      · have hA : 0 < |a| := abs_pos.mpr ha
        have ht : 0 ≤ ((epsilon : ℝ) + 1) / |a| := by positivity
        have hh := h (((epsilon : ℝ) + 1) / |a|)
        rw [abs_of_nonneg ht, div_mul_cancel₀ _ (ne_of_gt hA)] at hh
        linarith
    · intro h x
      have ha : a = 0 := by nlinarith [sq_nonneg a]
      simp [ha]
  · have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne L.coe_nonneg (Ne.symm hL)
    constructor
    · intro h
      let t : ℝ := |a| / (2 * (L : ℝ))
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have htrel : 2 * (L : ℝ) * t = |a| := by
        dsimp [t]
        field_simp
      have hh := h t
      rw [abs_of_nonneg ht] at hh
      have hlo := le_max_right (0 : ℝ) (|a| - (L : ℝ) * t)
      have hprod := (mul_le_mul_of_nonneg_left hlo ht).trans hh
      have hmul := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4 * (L : ℝ) by positivity)
      nlinarith [sq_abs a, sq_nonneg (|a| - 2 * (L : ℝ) * t)]
    · intro h x
      by_cases hx : 0 ≤ |a| - (L : ℝ) * |x|
      · rw [max_eq_right hx]
        have hs := sq_nonneg (|a| - 2 * (L : ℝ) * |x|)
        have habs := sq_abs a
        nlinarith
      · rw [max_eq_left (le_of_not_ge hx), mul_zero]
        exact epsilon.coe_nonneg

/-- Sharp linear-gap recovery: a feasible anchor exists exactly when its square is at most `4 L epsilon`. -/
theorem linearClockGap_feasible_iff (L epsilon : NNReal) (a : ℝ) :
    (∃ u : ℝ → ℝ, LipschitzWith L u ∧ u 0 = a ∧
      ∀ x : ℝ, |x| * |u x| ≤ epsilon) ↔
      a ^ 2 ≤ 4 * (L : ℝ) * epsilon := by
  have h := weightedClockGap_feasible_iff L epsilon (fun x : ℝ => ⟨|x|, abs_nonneg x⟩) 0 a
  exact h.trans (linearClockGap_envelope_iff L epsilon a)

end

end GaloisForLFunctions.HTGeometry
