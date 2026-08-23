import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Sharp two-cell Hilbert coercivity

A gap between the normalized coefficients of two orthogonal Hilbert probes forces ambient
energy.  The coefficient is the exact harmonic two-cell factor `L * R / (L + R)`.
-/

open scoped RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Sharp two-cell lower bound from two orthogonal Hilbert probes.  If `u,v` have squared norms
`L,R`, the gap between the corresponding normalized coefficients costs at least the harmonic
cell coefficient times the squared gap in ambient energy. -/
theorem harmonicAverageGap_le_norm_sq
    {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    {u v f : E}
    (huu : inner ℝ u u = L) (hvv : inner ℝ v v = R)
    (huv : inner ℝ u v = 0) :
    L * R / (L + R) *
        (inner ℝ v f / R - inner ℝ u f / L) ^ 2 ≤ ‖f‖ ^ 2 := by
  let z : E := R⁻¹ • v - L⁻¹ • u
  have hvu : inner ℝ v u = 0 := by
    rw [real_inner_comm, huv]
  have hzinner : inner ℝ z f =
      inner ℝ v f / R - inner ℝ u f / L := by
    simp only [z, inner_sub_left, real_inner_smul_left]
    field_simp [hL.ne', hR.ne']
  have hznorm : ‖z‖ ^ 2 = 1 / R + 1 / L := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [z, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, huu, hvv, huv, hvu]
    field_simp [hL.ne', hR.ne']
    ring
  have hcs := norm_inner_le_norm (𝕜 := ℝ) z f
  have hsq : (inner ℝ z f) ^ 2 ≤ ‖z‖ ^ 2 * ‖f‖ ^ 2 := by
    have hp := pow_le_pow_left₀ (norm_nonneg (inner ℝ z f)) hcs 2
    rw [mul_pow] at hp
    simpa [Real.norm_eq_abs, sq_abs] using hp
  rw [hzinner, hznorm] at hsq
  have hprod : 0 < L * R := mul_pos hL hR
  have hsum : 0 < L + R := add_pos hL hR
  have hrecip : 1 / R + 1 / L = (L + R) / (L * R) := by
    field_simp [hL.ne', hR.ne']
  rw [hrecip] at hsq
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hsum).2
  have hmul := mul_le_mul_of_nonneg_left hsq hprod.le
  calc
    L * R * (inner ℝ v f / R - inner ℝ u f / L) ^ 2 ≤
        L * R * ((L + R) / (L * R) * ‖f‖ ^ 2) := hmul
    _ = ‖f‖ ^ 2 * (L + R) := by field_simp [hprod.ne']

/-! ## Adjacent cells of a real interval -/

/-- Lebesgue length of the intersection of `(a,b]` and `(c,d]`. -/
def realIntervalOverlapLength (a b c d : ℝ) : ℝ :=
  max (min b d - max a c) 0

/-- On a left cell containing no endpoint in its interior, an interval indicator is constant
almost everywhere, with value determined by the left-hand trace at `t`. -/
theorem realIntervalOverlapLength_leftCell
    {a b t L : ℝ} (hL : 0 < L)
    (ha : a ≤ t - L ∨ t ≤ a) (hb : b ≤ t - L ∨ t ≤ b) :
    realIntervalOverlapLength a b (t - L) t =
      if a < t ∧ t ≤ b then L else 0 := by
  by_cases hocc : a < t ∧ t ≤ b
  · have hale : a ≤ t - L := ha.resolve_right (not_le.mpr hocc.1)
    rw [if_pos hocc, realIntervalOverlapLength, min_eq_right hocc.2,
      max_eq_right hale, max_eq_left]
    · ring
    · linarith
  · rw [if_neg hocc, realIntervalOverlapLength, max_eq_right]
    have hgap : t ≤ a ∨ b < t := by
      simpa only [not_and_or, not_lt, not_le] using hocc
    rcases hgap with hta | hbt
    · exact sub_nonpos.mpr ((min_le_right b t).trans
        (hta.trans (le_max_left a (t - L))))
    · have hble : b ≤ t - L := hb.resolve_right (not_le.mpr hbt)
      exact sub_nonpos.mpr ((min_le_left b t).trans
        (hble.trans (le_max_right a (t - L))))

/-- Right-cell counterpart of `realIntervalOverlapLength_leftCell`. -/
theorem realIntervalOverlapLength_rightCell
    {a b t R : ℝ} (hR : 0 < R)
    (ha : a ≤ t ∨ t + R ≤ a) (hb : b ≤ t ∨ t + R ≤ b) :
    realIntervalOverlapLength a b t (t + R) =
      if a ≤ t ∧ t < b then R else 0 := by
  by_cases hocc : a ≤ t ∧ t < b
  · have hRle : t + R ≤ b := hb.resolve_left (not_le.mpr hocc.2)
    rw [if_pos hocc, realIntervalOverlapLength, min_eq_right hRle,
      max_eq_right hocc.1, max_eq_left]
    · ring
    · linarith
  · rw [if_neg hocc, realIntervalOverlapLength, max_eq_right]
    have hgap : t < a ∨ b ≤ t := by
      simpa only [not_and_or, not_le, not_lt] using hocc
    rcases hgap with hta | hbt
    · have hRle : t + R ≤ a := ha.resolve_left (not_le.mpr hta)
      exact sub_nonpos.mpr ((min_le_right b (t + R)).trans
        (hRle.trans (le_max_left a t)))
    · exact sub_nonpos.mpr ((min_le_left b (t + R)).trans
        (hbt.trans (le_max_right a t)))

/-- Difference of normalized adjacent-cell masses is exactly the signed endpoint trace jump.
The separation assumptions say neither endpoint lies in either open cell. -/
theorem normalized_realIntervalOverlap_gap_eq_endpointJump
    {a b t L R : ℝ} (hL : 0 < L) (hR : 0 < R) (hab : a < b)
    (haL : a ≤ t - L ∨ t ≤ a) (hbL : b ≤ t - L ∨ t ≤ b)
    (haR : a ≤ t ∨ t + R ≤ a) (hbR : b ≤ t ∨ t + R ≤ b) :
    realIntervalOverlapLength a b t (t + R) / R -
        realIntervalOverlapLength a b (t - L) t / L =
      (if a = t then 1 else 0) - (if b = t then 1 else 0) := by
  rw [realIntervalOverlapLength_rightCell hR haR hbR,
    realIntervalOverlapLength_leftCell hL haL hbL]
  by_cases hat : a = t
  · subst a
    have htb : t < b := hab
    simp [htb, htb.ne', hR.ne']
  · by_cases hbt : b = t
    · subst b
      have hatlt : a < t := hab
      simp [hatlt, hat, hL.ne']
    · by_cases hatlt : a < t
      · by_cases htb : t < b
        · simp [hat, hbt, hatlt, hatlt.le, htb, htb.le,
            hL.ne', hR.ne']
        · have hble : b ≤ t := le_of_not_gt htb
          have hblt : b < t := lt_of_le_of_ne hble hbt
          have hnright : ¬ (a ≤ t ∧ t < b) := fun h => (not_lt_of_ge hble) h.2
          have hnleft : ¬ (a < t ∧ t ≤ b) := fun h => (not_le_of_gt hblt) h.2
          simp [hat, hbt, hnright, hnleft]
      · have hta : t ≤ a := le_of_not_gt hatlt
        have htb : t < b := lt_of_le_of_lt hta hab
        have htat : t < a := lt_of_le_of_ne hta (Ne.symm hat)
        have hnright : ¬ (a ≤ t ∧ t < b) := fun h => (not_le_of_gt htat) h.1
        have hnleft : ¬ (a < t ∧ t ≤ b) := fun h => (not_lt_of_ge hta) h.1
        simp [hat, hbt, hnright, hnleft]

end GaloisForLFunctions.HTGeometry
