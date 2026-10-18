import GaloisForLFunctions.RHTower.ThetaJensenSaddleCoercivity

/-!
# All-order bounds for centered theta moments

The polynomial Ward identity and the global saddle score inequality give
uniform bounds at the Hermite scale. No saddle expansion is assumed.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem thetaJensenWeight_pos (x : ℝ) : 0 < thetaJensenWeight x := by
  unfold thetaJensenWeight thetaCuspGaussianApertureLeadingChannelWeight
  exact Real.exp_pos _

theorem thetaJensenCenteredMoment_even_nonneg (n p : ℕ) (s : ℝ) :
    0 ≤ thetaJensenCenteredMoment n (2 * p) s := by
  rw [thetaJensenCenteredMoment_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  have hw := (thetaJensenWeight_pos x).le
  rw [pow_mul]
  positivity

theorem thetaJensenCenteredMoment_zero (n : ℕ) (s : ℝ) :
    thetaJensenCenteredMoment n 0 s = thetaCuspGaussianApertureTailChannelMoment 0 4 n := by
  rw [thetaJensenCenteredMoment_eq_integral]
  simp only [pow_zero, one_mul, thetaJensenWeight]
  exact integral_pow_leadingChannelWeight_eq_moment 0 n

theorem thetaJensenCenteredMoment_zero_pos (n : ℕ) (s : ℝ) :
    0 < thetaJensenCenteredMoment n 0 s := by
  rw [thetaJensenCenteredMoment_zero]
  exact thetaCuspGaussianApertureTailChannelMoment_pos (by rfl) 4 n

theorem thetaJensenCenteredMoment_global_ward_bound (n p : ℕ) {s : ℝ} (hs : 1 ≤ s)
    (hscore : thetaJensenScore s = (n : ℝ) + 1 / 2) :
    ((n : ℝ) + 1 / 2) * thetaJensenCenteredMoment n (2 * p + 2) s ≤
      2 * s ^ 2 * ((2 * p : ℕ) + (1 : ℝ)) *
        (s ^ 2 * thetaJensenCenteredMoment n (2 * p) s +
          thetaJensenCenteredMoment n (2 * p + 1) s) := by
  have h := integral_mono_ae
    ((integrableOn_thetaJensen_centered n (2 * p + 2) s).const_mul ((n : ℝ) + 1 / 2))
    ((integrableOn_thetaJensen_centeredScore n (2 * p + 1) s).const_mul (2 * s ^ 2)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hc := thetaJensenScore_global_coercivity hs hx.le
      rw [hscore] at hc
      have hw := (thetaJensenWeight_pos x).le
      have hfactor : 0 ≤ (x ^ 2 - s ^ 2) ^ (2 * p) * x ^ (2 * n) * thetaJensenWeight x := by
        rw [pow_mul]
        positivity
      have hm := mul_le_mul_of_nonneg_right hc hfactor
      convert hm using 1 <;> simp only [pow_add, pow_one] <;> ring)
  rw [integral_const_mul, integral_const_mul, ← thetaJensenCenteredMoment_eq_integral,
    thetaJensen_centered_ward] at h
  exact h.trans_eq (by ring)

theorem thetaJensenCenteredMoment_odd_le (n p : ℕ) (s : ℝ) :
    2 * s ^ 2 * thetaJensenCenteredMoment n (2 * p + 1) s ≤
      s ^ 4 * thetaJensenCenteredMoment n (2 * p) s +
        thetaJensenCenteredMoment n (2 * p + 2) s := by
  have h := integral_mono_ae
    ((integrableOn_thetaJensen_centered n (2 * p + 1) s).const_mul (2 * s ^ 2))
    (((integrableOn_thetaJensen_centered n (2 * p) s).const_mul (s ^ 4)).add
      (integrableOn_thetaJensen_centered n (2 * p + 2) s)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hw := (thetaJensenWeight_pos x).le
      have hfactor : 0 ≤ (x ^ 2 - s ^ 2) ^ (2 * p) * x ^ (2 * n) * thetaJensenWeight x := by
        rw [pow_mul]
        positivity
      have hh := mul_nonneg (sq_nonneg ((x ^ 2 - s ^ 2) - s ^ 2)) hfactor
      simp only [Pi.add_apply, pow_add, pow_one]
      nlinarith)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul,
    integral_add ((integrableOn_thetaJensen_centered n (2 * p) s).const_mul (s ^ 4))
      (integrableOn_thetaJensen_centered n (2 * p + 2) s), integral_const_mul,
    ← thetaJensenCenteredMoment_eq_integral, ← thetaJensenCenteredMoment_eq_integral,
    ← thetaJensenCenteredMoment_eq_integral] at h
  exact h

/-- One more centered pair costs at most a fixed degree factor times `s⁴/(n+1/2)`. -/
theorem thetaJensenCenteredMoment_recurrence (n p : ℕ) {s : ℝ} (hs : 1 ≤ s)
    (hscore : thetaJensenScore s = (n : ℝ) + 1 / 2)
    (hlarge : 2 * (2 * (p : ℝ) + 1) ≤ (n : ℝ) + 1 / 2) :
    ((n : ℝ) + 1 / 2) * thetaJensenCenteredMoment n (2 * p + 2) s ≤
      6 * (2 * (p : ℝ) + 1) * s ^ 4 * thetaJensenCenteredMoment n (2 * p) s := by
  have hg := thetaJensenCenteredMoment_global_ward_bound n p hs hscore
  have hy := mul_le_mul_of_nonneg_left (thetaJensenCenteredMoment_odd_le n p s)
    (show 0 ≤ 2 * (p : ℝ) + 1 by positivity)
  have hm : 0 ≤ thetaJensenCenteredMoment n (2 * p + 2) s := by
    simpa only [Nat.mul_add, Nat.mul_one] using thetaJensenCenteredMoment_even_nonneg n (p + 1) s
  have hl := mul_le_mul_of_nonneg_right hlarge hm
  push_cast at hg
  nlinarith

def thetaJensenMomentBoundConstant : ℕ → ℝ
  | 0 => 1
  | p + 1 => 6 * (2 * (p : ℝ) + 1) * thetaJensenMomentBoundConstant p

theorem thetaJensenMomentBoundConstant_pos (p : ℕ) : 0 < thetaJensenMomentBoundConstant p := by
  induction p with
  | zero => norm_num [thetaJensenMomentBoundConstant]
  | succ p ih =>
    rw [thetaJensenMomentBoundConstant]
    positivity

/-- Every fixed centered even moment is bounded at the scale `s²/sqrt(n+1/2)`. -/
theorem thetaJensenCenteredMoment_uniform_bound (n : ℕ) {s : ℝ} (hs : 1 ≤ s)
    (hscore : thetaJensenScore s = (n : ℝ) + 1 / 2) :
    ∀ p : ℕ, 4 * (p : ℝ) ≤ (n : ℝ) + 1 / 2 →
      ((n : ℝ) + 1 / 2) ^ p * thetaJensenCenteredMoment n (2 * p) s ≤
        thetaJensenMomentBoundConstant p * s ^ (4 * p) * thetaJensenCenteredMoment n 0 s := by
  intro p
  induction p with
  | zero =>
    intro hp
    simp [thetaJensenMomentBoundConstant]
  | succ p ih =>
    intro hp
    have hp' : 4 * (p : ℝ) ≤ (n : ℝ) + 1 / 2 := by
      push_cast at hp
      linarith
    have hlarge : 2 * (2 * (p : ℝ) + 1) ≤ (n : ℝ) + 1 / 2 := by
      push_cast at hp
      linarith
    have hrec := thetaJensenCenteredMoment_recurrence n p hs hscore hlarge
    have hlow := ih hp'
    rw [show 2 * (p + 1) = 2 * p + 2 by omega]
    calc
      ((n : ℝ) + 1 / 2) ^ (p + 1) * thetaJensenCenteredMoment n (2 * p + 2) s =
          ((n : ℝ) + 1 / 2) ^ p *
            (((n : ℝ) + 1 / 2) * thetaJensenCenteredMoment n (2 * p + 2) s) := by
        rw [pow_succ]
        ring
      _ ≤ ((n : ℝ) + 1 / 2) ^ p *
          (6 * (2 * (p : ℝ) + 1) * s ^ 4 * thetaJensenCenteredMoment n (2 * p) s) :=
        mul_le_mul_of_nonneg_left hrec (by positivity)
      _ = 6 * (2 * (p : ℝ) + 1) * s ^ 4 *
          (((n : ℝ) + 1 / 2) ^ p * thetaJensenCenteredMoment n (2 * p) s) := by ring
      _ ≤ 6 * (2 * (p : ℝ) + 1) * s ^ 4 *
          (thetaJensenMomentBoundConstant p * s ^ (4 * p) * thetaJensenCenteredMoment n 0 s) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = thetaJensenMomentBoundConstant (p + 1) * s ^ (4 * (p + 1)) *
          thetaJensenCenteredMoment n 0 s := by
        rw [thetaJensenMomentBoundConstant, show 4 * (p + 1) = 4 * p + 4 by omega, pow_add]
        ring

end RHTower
