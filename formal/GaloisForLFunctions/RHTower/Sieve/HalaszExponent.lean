import GaloisForLFunctions.RHTower.Sieve.ShellTotalCost

/-!
# The Halász exponent

The quantity the shell cut produces is the PRODUCT of the uniform bound with the logarithm of its
own reciprocal, and that product — not either factor alone — is what an exponential bound on the
uniform factor controls.  The map `t ↦ t(1 + log(y/t))` is monotone below `y`, so an upper bound
`L ≤ c·y·e^{−M}` converts directly into `L·(1 + log(y/L)) ≤ c·y·e^{−M}(1 + M − log c)`, which is the
`(1+M)e^{−M}` shape of the Halász exponent.  A standalone bound on `L` would lose the logarithm.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- `t ↦ t(1 + log(y/t))` is monotone on `(0, y]`. -/
theorem mul_one_add_log_div_mono {y s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (hty : t ≤ y) :
    s * (1 + Real.log (y / s)) ≤ t * (1 + Real.log (y / t)) := by
  have ht : (0 : ℝ) < t := lt_of_lt_of_le hs hst
  have hy : (0 : ℝ) < y := lt_of_lt_of_le ht hty
  set u : ℝ := s / t with hu
  have hu0 : (0 : ℝ) < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one ht]; exact hst
  have hv : (0 : ℝ) ≤ Real.log (y / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hsplit : Real.log (y / s) = Real.log (y / t) + Real.log (t / s) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlogu : Real.log (t / s) = -Real.log u := by
    rw [hu, Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]
    ring
  have hkey : -(u * Real.log u) ≤ 1 - u := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / u by positivity)
    have hlogi : Real.log (1 / u) = -Real.log u := by
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one]
      ring
    rw [hlogi] at h
    have hmul := mul_le_mul_of_nonneg_left h hu0.le
    have hid : u * (1 / u - 1) = 1 - u := by field_simp
    rw [hid] at hmul
    linarith
  have hstep : u * ((1 + Real.log (y / t)) - Real.log u) ≤ 1 + Real.log (y / t) := by
    have hone : 1 - u ≤ (1 + Real.log (y / t)) * (1 - u) := by
      nlinarith [hv, hu1]
    nlinarith [hkey, hone]
  have hs_eq : s = t * u := by rw [hu]; field_simp
  rw [hsplit, hlogu, hs_eq, mul_assoc]
  have := mul_le_mul_of_nonneg_left hstep ht.le
  calc t * (u * (1 + (Real.log (y / t) + -Real.log u)))
      = t * (u * ((1 + Real.log (y / t)) - Real.log u)) := by ring
    _ ≤ t * (1 + Real.log (y / t)) := this

/-- **Equation (H2): the Halász exponent.**  An exponential bound on the uniform shell factor
converts the shell cut's product into the `(1 + M)e^{−M}` shape. -/
theorem shell_cost_of_exp_bound {c y L M K₀ : ℝ} (hc : 0 < c) (hy : 0 < y) (hL : 0 < L)
    (hbound : L ≤ c * y * Real.exp (-M)) (hle : c * y * Real.exp (-M) ≤ y)
    (hK₀ : K₀ ≤ max 0 (Real.log (y / L)) + 1) :
    L * K₀ ≤ c * y * Real.exp (-M) * (1 + M - Real.log c) := by
  have hLy : L ≤ y := le_trans hbound hle
  have hlogpos : (0 : ℝ) ≤ Real.log (y / L) :=
    Real.log_nonneg (by rw [le_div_iff₀ hL]; linarith)
  have hmax : max 0 (Real.log (y / L)) = Real.log (y / L) := max_eq_right hlogpos
  rw [hmax] at hK₀
  have hstep1 : L * K₀ ≤ L * (1 + Real.log (y / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ hL.le
    linarith
  have ht0 : (0 : ℝ) < c * y * Real.exp (-M) := by positivity
  have hmono := mul_one_add_log_div_mono (y := y) (s := L) (t := c * y * Real.exp (-M))
    hL hbound hle
  have hlogt : Real.log (y / (c * y * Real.exp (-M))) = M - Real.log c := by
    have hid : y / (c * y * Real.exp (-M)) = Real.exp M / c := by
      rw [Real.exp_neg]
      field_simp
    rw [hid, Real.log_div (by positivity) hc.ne', Real.log_exp]
  rw [hlogt] at hmono
  calc L * K₀ ≤ L * (1 + Real.log (y / L)) := hstep1
    _ ≤ (c * y * Real.exp (-M)) * (1 + (M - Real.log c)) := hmono
    _ = c * y * Real.exp (-M) * (1 + M - Real.log c) := by ring

end

end RHTower.Sieve
