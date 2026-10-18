import GaloisForLFunctions.RHTower.ThetaJensenCenteredMomentBounds

/-!
# Theta concentration below the Hermite scale

Local score coercivity improves the global centered-moment bounds. Every
positive even moment, normalized at the scale `s²/sqrt(n+1/2)`, tends to zero.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem thetaJensenScore_local_with_tail {s x : ℝ} (hs : 2 ≤ s) (hx : 0 ≤ x) (p : ℕ) :
    thetaJensenScore s * s ^ 2 * (x ^ 2 - s ^ 2) ^ (2 * p + 2) ≤
      8 * Real.exp 2 * s ^ 3 * (x ^ 2 - s ^ 2) ^ (2 * p + 1) *
        (thetaJensenScore x - thetaJensenScore s) +
          thetaJensenScore s * (x ^ 2 - s ^ 2) ^ (2 * p + 4) := by
  have hs0 : 0 < s := by linarith
  have hS := thetaJensenScore_pos hs0
  have hpow : 0 ≤ (x ^ 2 - s ^ 2) ^ (2 * p) := by rw [pow_mul]; positivity
  have hcorr : 0 ≤ (x ^ 2 - s ^ 2) * (thetaJensenScore x - thetaJensenScore s) := by
    have h := thetaJensenScore_global_coercivity (show 1 ≤ s by linarith) hx
    have h0 := mul_nonneg hS.le (sq_nonneg (x ^ 2 - s ^ 2))
    have hm : 0 ≤ (2 * s ^ 2) *
        ((x ^ 2 - s ^ 2) * (thetaJensenScore x - thetaJensenScore s)) := by
      simpa only [mul_assoc] using h0.trans h
    exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hm)
      (by positivity : 0 < 2 * s ^ 2)
  by_cases hlocal : |x - s| ≤ 1
  · have h := mul_le_mul_of_nonneg_right (thetaJensenScore_local_coercivity hs hlocal)
      (mul_nonneg (sq_nonneg s) hpow)
    have ht : 0 ≤ thetaJensenScore s * (x ^ 2 - s ^ 2) ^ (2 * p + 4) := by
      rw [pow_add]
      positivity
    simp only [pow_add, pow_one] at h ht ⊢
    nlinarith
  · have hbig : 1 < |x - s| := lt_of_not_ge hlocal
    have hsq : 1 ≤ (x - s) ^ 2 := by nlinarith [sq_abs (x - s), abs_nonneg (x - s)]
    have hD : s ^ 2 ≤ (x ^ 2 - s ^ 2) ^ 2 := by
      calc
        s ^ 2 ≤ (x + s) ^ 2 := by nlinarith
        _ ≤ (x - s) ^ 2 * (x + s) ^ 2 := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (x + s))
        _ = _ := by ring
    have h := mul_le_mul_of_nonneg_right hD
      (mul_nonneg hS.le (mul_nonneg hpow (sq_nonneg (x ^ 2 - s ^ 2))))
    have hc := mul_nonneg (show 0 ≤ 8 * Real.exp 2 * s ^ 3 * (x ^ 2 - s ^ 2) ^ (2 * p) by positivity)
      hcorr
    simp only [pow_add, pow_one] at h hc ⊢
    nlinarith

theorem thetaJensenCenteredMoment_local_ward_bound (n p : ℕ) {s : ℝ} (hs : 2 ≤ s)
    (hscore : thetaJensenScore s = (n : ℝ) + 1 / 2) :
    ((n : ℝ) + 1 / 2) * s ^ 2 * thetaJensenCenteredMoment n (2 * p + 2) s ≤
      8 * Real.exp 2 * s ^ 3 * ((2 * p : ℕ) + (1 : ℝ)) *
        (s ^ 2 * thetaJensenCenteredMoment n (2 * p) s +
          thetaJensenCenteredMoment n (2 * p + 1) s) +
            ((n : ℝ) + 1 / 2) * thetaJensenCenteredMoment n (2 * p + 4) s := by
  have h := integral_mono_ae
    ((integrableOn_thetaJensen_centered n (2 * p + 2) s).const_mul (((n : ℝ) + 1 / 2) * s ^ 2))
    (((integrableOn_thetaJensen_centeredScore n (2 * p + 1) s).const_mul (8 * Real.exp 2 * s ^ 3)).add
      ((integrableOn_thetaJensen_centered n (2 * p + 4) s).const_mul ((n : ℝ) + 1 / 2))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hc := thetaJensenScore_local_with_tail hs hx.le p
      rw [hscore] at hc
      have hw := (thetaJensenWeight_pos x).le
      have hm := mul_le_mul_of_nonneg_right hc
        (show 0 ≤ x ^ (2 * n) * thetaJensenWeight x by positivity)
      convert hm using 1 <;> (try simp only [Pi.add_apply]) <;> ring)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul,
    integral_add
      ((integrableOn_thetaJensen_centeredScore n (2 * p + 1) s).const_mul (8 * Real.exp 2 * s ^ 3))
      ((integrableOn_thetaJensen_centered n (2 * p + 4) s).const_mul ((n : ℝ) + 1 / 2)),
    integral_const_mul, integral_const_mul, ← thetaJensenCenteredMoment_eq_integral,
    ← thetaJensenCenteredMoment_eq_integral, thetaJensen_centered_ward] at h
  exact h.trans_eq (by ring)

def thetaJensenNormalizedCenteredMoment (n p : ℕ) : ℝ :=
  ((n : ℝ) + 1 / 2) ^ p * thetaJensenCenteredMoment n (2 * p) (thetaJensenSaddle n) /
    (thetaJensenSaddle n ^ (4 * p) * thetaJensenCenteredMoment n 0 (thetaJensenSaddle n))

theorem thetaJensenNormalizedCenteredMoment_nonneg (n p : ℕ) :
    0 ≤ thetaJensenNormalizedCenteredMoment n p := by
  have hs := thetaJensenSaddle_pos n
  have hm := thetaJensenCenteredMoment_even_nonneg n p (thetaJensenSaddle n)
  have h0 := thetaJensenCenteredMoment_zero_pos n (thetaJensenSaddle n)
  unfold thetaJensenNormalizedCenteredMoment
  positivity

theorem thetaJensenNormalizedCenteredMoment_le (n p : ℕ) (hs : 1 ≤ thetaJensenSaddle n)
    (hp : 4 * (p : ℝ) ≤ (n : ℝ) + 1 / 2) :
    thetaJensenNormalizedCenteredMoment n p ≤ thetaJensenMomentBoundConstant p := by
  have hs0 := thetaJensenSaddle_pos n
  have h0 := thetaJensenCenteredMoment_zero_pos n (thetaJensenSaddle n)
  unfold thetaJensenNormalizedCenteredMoment
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_assoc] using
    thetaJensenCenteredMoment_uniform_bound n hs (thetaJensenSaddle_score n) p hp

theorem thetaJensenNormalizedCenteredMoment_local_bound (n p : ℕ) (hs : 2 ≤ thetaJensenSaddle n) :
    thetaJensenNormalizedCenteredMoment n (p + 1) ≤
      (12 * Real.exp 2 * (2 * (p : ℝ) + 1) / thetaJensenSaddle n) *
          thetaJensenNormalizedCenteredMoment n p +
        (4 * Real.exp 2 * (2 * (p : ℝ) + 1) /
          (((n : ℝ) + 1 / 2) * thetaJensenSaddle n)) *
          thetaJensenNormalizedCenteredMoment n (p + 1) +
        (thetaJensenSaddle n ^ 2 / ((n : ℝ) + 1 / 2)) *
          thetaJensenNormalizedCenteredMoment n (p + 2) := by
  let s := thetaJensenSaddle n
  let r : ℝ := (n : ℝ) + 1 / 2
  have hs0 : 0 < s := thetaJensenSaddle_pos n
  have hr : 0 < r := by dsimp [r]; positivity
  have h0 := thetaJensenCenteredMoment_zero_pos n s
  have hg := mul_le_mul_of_nonneg_left
    (thetaJensenCenteredMoment_local_ward_bound n p hs (thetaJensenSaddle_score n))
    (show 0 ≤ 2 * s ^ 2 by positivity)
  have hy := mul_le_mul_of_nonneg_left (thetaJensenCenteredMoment_odd_le n p s)
    (show 0 ≤ 8 * Real.exp 2 * s ^ 3 * (2 * (p : ℝ) + 1) by positivity)
  have hraw : 2 * r * s ^ 4 * thetaJensenCenteredMoment n (2 * p + 2) s ≤
      24 * Real.exp 2 * s ^ 7 * (2 * (p : ℝ) + 1) * thetaJensenCenteredMoment n (2 * p) s +
        8 * Real.exp 2 * s ^ 3 * (2 * (p : ℝ) + 1) * thetaJensenCenteredMoment n (2 * p + 2) s +
        2 * r * s ^ 2 * thetaJensenCenteredMoment n (2 * p + 4) s := by
    change 2 * s ^ 2 * (_ : ℝ) ≤ _ at hg
    push_cast at hg
    dsimp only [r, s] at *
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hraw
    (show 0 ≤ r ^ p / (2 * s ^ (4 * p + 8) * thetaJensenCenteredMoment n 0 s) by positivity)
  change _ ≤ _ at hscaled
  convert hscaled using 1 <;> try rfl
  all_goals
    try dsimp only [thetaJensenNormalizedCenteredMoment, r, s]
    try simp only [
      show 2 * (p + 1) = 2 * p + 2 by omega, show 2 * (p + 2) = 2 * p + 4 by omega,
      show 4 * (p + 1) = 4 * p + 4 by omega, show 4 * (p + 2) = 4 * p + 8 by omega]
    try simp only [pow_add, pow_succ]
    try field_simp
    all_goals ring

/-- Every positive even centered moment is negligible at the Hermite scale. -/
theorem tendsto_thetaJensenNormalizedCenteredMoment_succ (p : ℕ) :
    Tendsto (fun n => thetaJensenNormalizedCenteredMoment n (p + 1)) atTop (𝓝 0) := by
  let D : ℝ := 12 * Real.exp 2 * (2 * (p : ℝ) + 1) * thetaJensenMomentBoundConstant p +
    8 * Real.exp 2 * (2 * (p : ℝ) + 1) * thetaJensenMomentBoundConstant (p + 1)
  have hlim : Tendsto (fun n => D / thetaJensenSaddle n + thetaJensenMomentBoundConstant (p + 2) *
      (thetaJensenSaddle n ^ 2 / ((n : ℝ) + 1 / 2))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_thetaJensenSaddle).add
      (tendsto_thetaJensenSaddle_sq_div_shape.const_mul (thetaJensenMomentBoundConstant (p + 2)))
  refine squeeze_zero' (Eventually.of_forall (fun n => thetaJensenNormalizedCenteredMoment_nonneg n _))
    ?_ hlim
  have hcast := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [tendsto_thetaJensenSaddle.eventually (eventually_ge_atTop 2),
    hcast.eventually (eventually_ge_atTop (4 * ((p : ℝ) + 2)))] with n hs hn
  have hs0 := thetaJensenSaddle_pos n
  have hr : 0 < (n : ℝ) + 1 / 2 := by positivity
  have h₀ := thetaJensenNormalizedCenteredMoment_le n p (by linarith) (by linarith)
  have h₁ := thetaJensenNormalizedCenteredMoment_le n (p + 1) (by linarith) (by push_cast; linarith)
  have h₂ := thetaJensenNormalizedCenteredMoment_le n (p + 2) (by linarith) (by push_cast; linarith)
  have hcoef : 4 * Real.exp 2 * (2 * (p : ℝ) + 1) /
      (((n : ℝ) + 1 / 2) * thetaJensenSaddle n) ≤
        8 * Real.exp 2 * (2 * (p : ℝ) + 1) / thetaJensenSaddle n := by
    apply (div_le_div_iff₀ (by positivity) hs0).mpr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn0
      (show 0 ≤ 8 * Real.exp 2 * (2 * (p : ℝ) + 1) * thetaJensenSaddle n by positivity)]
  have hfirst := mul_le_mul_of_nonneg_left h₀
    (show 0 ≤ 12 * Real.exp 2 * (2 * (p : ℝ) + 1) / thetaJensenSaddle n by positivity)
  have hsecond := (mul_le_mul_of_nonneg_left h₁
    (show 0 ≤ 4 * Real.exp 2 * (2 * (p : ℝ) + 1) /
      (((n : ℝ) + 1 / 2) * thetaJensenSaddle n) by positivity)).trans
        (mul_le_mul_of_nonneg_right hcoef (thetaJensenMomentBoundConstant_pos (p + 1)).le)
  have hthird := mul_le_mul_of_nonneg_left h₂
    (show 0 ≤ thetaJensenSaddle n ^ 2 / ((n : ℝ) + 1 / 2) by positivity)
  have h := (thetaJensenNormalizedCenteredMoment_local_bound n p hs).trans
    (add_le_add (add_le_add hfirst hsecond) hthird)
  exact h.trans_eq (by dsimp only [D]; ring)

end RHTower
