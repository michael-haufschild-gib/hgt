import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinFluxLaw
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The base-change tower

Over `𝔽_{q^d}` the black hole has parameters `(q^d, V_d)`, where `V_d = α^d + β^d`: a second-order recurrence in
`d` (`towerTrace`), and two ticks at level `1` are one tick at level `2`: the Frobenius polynomials factor,
`P(w) P(-w) = P₂(w²)` (`frobPoly_base_change`).

* **The fakes survive the tower.** If `|t| ≤ q`, then every level has positive channel counts,
  `|V_d| < q^d + 1` (`abs_towerTrace_lt`). So the channels cannot go negative at any level, and an
  overdamped oscillator stays overdamped at every level (`towerTrace_overdamped`).
* **A weak uniform law self-improves.** A bound on the first-return excess of the tower with any constant,
  `|V_d| ≤ C q^{d/2}` for all `d`, already gives the sharp window `t² ≤ 4q` (`tower_bound_iff`). This is the
  tensor-power trick. It says what kind of estimate would suffice, and the fakes say that wave dynamics
  does not supply it.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-- The trace of the base change to `𝔽_{q^d}`: `V_0 = 2`, `V_1 = t`, `V_{d+2} = t V_{d+1} - q V_d`. -/
def towerTrace (q t : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => t
  | d + 2 => t * towerTrace q t (d + 1) - q * towerTrace q t d

theorem towerTrace_add_two (q t : ℝ) (d : ℕ) :
    towerTrace q t (d + 2) = t * towerTrace q t (d + 1) - q * towerTrace q t d := rfl

/-- The tower trace from the two roots. -/
theorem towerTrace_roots {q t : ℝ} {α β : ℂ} (hs : α + β = t) (hp : α * β = q) (d : ℕ) :
    (towerTrace q t d : ℂ) = α ^ d + β ^ d := by
  induction d using Nat.twoStepInduction with
  | zero => simp [towerTrace]; norm_num
  | one => simp [towerTrace, hs]
  | more d h0 h1 =>
    rw [towerTrace_add_two]
    push_cast
    rw [h0, h1, ← hs, ← hp]
    ring

/-- **Two ticks at level one are one tick at level two.** -/
theorem frobPoly_base_change (q t : ℂ) (w : ℂ) :
    (1 - t * w + q * w ^ 2) * (1 + t * w + q * w ^ 2) =
      1 - (t ^ 2 - 2 * q) * w ^ 2 + q ^ 2 * (w ^ 2) ^ 2 := by
  ring

theorem towerTrace_two (q t : ℝ) : towerTrace q t 2 = t ^ 2 - 2 * q := by
  simp [towerTrace]
  ring

/-- Real roots with `|t| ≤ q` have modulus above one. -/
theorem one_lt_abs_of_real_roots {q t x x' : ℝ} (hq : 1 < q) (ht : |t| ≤ q) (hs : x + x' = t)
    (hp : x * x' = q) : 1 < |x| ∧ 1 < |x'| := by
  have hq0 : 0 < q := by linarith
  have habs : |x| * |x'| = q := by rw [← abs_mul, hp, abs_of_pos hq0]
  have hsum : |x| + |x'| = |t| := by
    rw [← hs]
    have hxx : 0 < x * x' := by linarith
    rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at hxx) with h | h
    · have h' : x' < 0 := by
        by_contra hc
        have := mul_nonpos_of_nonpos_of_nonneg h.le (not_lt.mp hc)
        linarith
      rw [abs_of_neg h, abs_of_neg h', abs_of_neg (by linarith)]
      ring
    · have h' : 0 < x' := by
        by_contra hc
        have := mul_nonpos_of_nonneg_of_nonpos h.le (not_lt.mp hc)
        linarith
      rw [abs_of_pos h, abs_of_pos h', abs_of_pos (by linarith)]
  have hx : 0 ≤ |x| := abs_nonneg x
  have hx' : 0 ≤ |x'| := abs_nonneg x'
  constructor
  · by_contra hc
    have hle := not_lt.mp hc
    nlinarith
  · by_contra hc
    have hle := not_lt.mp hc
    nlinarith

/-- **The channels stay positive up the tower.** -/
theorem abs_towerTrace_lt {q t : ℝ} (hq : 1 < q) (ht : |t| ≤ q) {d : ℕ} (hd : 0 < d) :
    |towerTrace q t d| < q ^ d + 1 := by
  have hq0 : 0 < q := by linarith
  by_cases hdisc : t ^ 2 ≤ 4 * q
  · obtain ⟨α, β, hs, hp, hna, hnb⟩ := exists_roots_on_circle hdisc
    have hr : 1 < Real.sqrt q := by
      rw [Real.lt_sqrt (by norm_num)]
      linarith
    have hrsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
    have hc := towerTrace_roots hs hp d
    have hnorm : |towerTrace q t d| ≤ 2 * Real.sqrt q ^ d := by
      have : ‖((towerTrace q t d : ℝ) : ℂ)‖ ≤ ‖α ^ d‖ + ‖β ^ d‖ := by
        rw [hc]
        exact norm_add_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_pow, hna, hnb] at this
      linarith
    have hlt : 2 * Real.sqrt q ^ d < q ^ d + 1 := by
      have e : q ^ d = (Real.sqrt q ^ d) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul, hrsq]
      rw [e]
      have h1 : 1 < Real.sqrt q ^ d := one_lt_pow₀ hr hd.ne'
      nlinarith
    linarith
  · obtain ⟨x, x', hs, hp, -, -⟩ := exists_slow_mode hq0 (not_le.mp hdisc)
    obtain ⟨h1, h2⟩ := one_lt_abs_of_real_roots hq ht hs hp
    have hc : towerTrace q t d = x ^ d + x' ^ d := by
      have := towerTrace_roots (q := q) (t := t) (α := (x : ℂ)) (β := (x' : ℂ))
        (by rw [← hs]; push_cast; ring) (by rw [← hp]; push_cast; ring) d
      exact_mod_cast this
    have hxd : 1 < |x| ^ d := one_lt_pow₀ h1 hd.ne'
    have hxd' : 1 < |x'| ^ d := one_lt_pow₀ h2 hd.ne'
    have hprod : q ^ d = |x| ^ d * |x'| ^ d := by
      rw [← mul_pow, ← abs_mul, hp, abs_of_pos hq0]
    rw [hc, hprod]
    calc |x ^ d + x' ^ d| ≤ |x ^ d| + |x' ^ d| := abs_add_le _ _
      _ = |x| ^ d + |x'| ^ d := by rw [abs_pow, abs_pow]
      _ < |x| ^ d * |x'| ^ d + 1 := by nlinarith

/-- **An overdamped oscillator stays overdamped.** -/
theorem towerTrace_overdamped {q t : ℝ} (hq : 0 < q) (hover : 4 * q < t ^ 2) {d : ℕ} (hd : 0 < d) :
    4 * q ^ d < towerTrace q t d ^ 2 := by
  obtain ⟨x, x', hs, hp, hbig, hsmall⟩ := exists_slow_mode hq hover
  have hc : towerTrace q t d = x ^ d + x' ^ d := by
    have := towerTrace_roots (q := q) (t := t) (α := (x : ℂ)) (β := (x' : ℂ))
      (by rw [← hs]; push_cast; ring) (by rw [← hp]; push_cast; ring) d
    exact_mod_cast this
  have hpd : q ^ d = x ^ d * x' ^ d := by rw [← mul_pow, hp]
  have hne : x ^ d - x' ^ d ≠ 0 := by
    intro h0
    have heq : x ^ d = x' ^ d := sub_eq_zero.mp h0
    have habs : |x| ^ d = |x'| ^ d := by rw [← abs_pow, ← abs_pow, heq]
    have h1 : |x'| < |x| := by
      apply sq_lt_sq.mp
      linarith
    have := pow_lt_pow_left₀ h1 (abs_nonneg x') hd.ne'
    linarith
  rw [hc, hpd]
  have := sq_pos_of_ne_zero hne
  nlinarith

/-- **A weak uniform law self-improves.** A bound on the tower with any constant gives the sharp window. -/
theorem tower_bound_iff {q t : ℝ} (hq : 0 < q) :
    (∃ C : ℝ, ∀ d : ℕ, |towerTrace q t d| ≤ C * Real.sqrt q ^ d) ↔ t ^ 2 ≤ 4 * q := by
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hrsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  constructor
  · rintro ⟨C, hC⟩
    by_contra hlt
    obtain ⟨x, x', hs, hp, hbig, hsmall⟩ := exists_slow_mode hq (not_le.mp hlt)
    have hc (d : ℕ) : towerTrace q t d = x ^ d + x' ^ d := by
      have := towerTrace_roots (q := q) (t := t) (α := (x : ℂ)) (β := (x' : ℂ))
        (by rw [← hs]; push_cast; ring) (by rw [← hp]; push_cast; ring) d
      exact_mod_cast this
    have hxabs : Real.sqrt q < |x| := by
      have : Real.sqrt q ^ 2 < |x| ^ 2 := by rw [sq_abs, hrsq]; exact hbig
      exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg x) this
    have hx'abs : |x'| < Real.sqrt q := by
      have : |x'| ^ 2 < Real.sqrt q ^ 2 := by rw [sq_abs, hrsq]; exact hsmall
      exact lt_of_pow_lt_pow_left₀ 2 hr.le this
    set a := |x| / Real.sqrt q with ha
    have ha1 : 1 < a := by
      rw [ha, one_lt_div hr]
      exact hxabs
    have hunb : Tendsto (fun d : ℕ => a ^ d) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt ha1
    obtain ⟨d, hd⟩ := (hunb.eventually (eventually_gt_atTop (|C| + 1))).exists
    have hrd : 0 < Real.sqrt q ^ d := pow_pos hr d
    have h1 := hC d
    rw [hc d] at h1
    have h2 : |x| ^ d - |x'| ^ d ≤ |x ^ d + x' ^ d| := by
      have := abs_sub_abs_le_abs_sub (x ^ d) (-(x' ^ d))
      simpa [abs_pow, sub_neg_eq_add, abs_neg] using this
    have h3 : |x'| ^ d ≤ Real.sqrt q ^ d := pow_le_pow_left₀ (abs_nonneg _) hx'abs.le d
    have h4 : |x| ^ d = a ^ d * Real.sqrt q ^ d := by
      rw [ha, div_pow]
      field_simp
    have h5 : C * Real.sqrt q ^ d ≤ |C| * Real.sqrt q ^ d :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hrd.le
    have h6 : (|C| + 1) * Real.sqrt q ^ d < a ^ d * Real.sqrt q ^ d :=
      mul_lt_mul_of_pos_right hd hrd
    nlinarith
  · intro h
    obtain ⟨α, β, hs, hp, hna, hnb⟩ := exists_roots_on_circle h
    refine ⟨2, fun d => ?_⟩
    have hc := towerTrace_roots hs hp d
    have : ‖((towerTrace q t d : ℝ) : ℂ)‖ ≤ ‖α ^ d‖ + ‖β ^ d‖ := by
      rw [hc]
      exact norm_add_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_pow, hna, hnb] at this
    linarith

end GaloisForLFunctions.ArithmeticScatteringHolography

end
