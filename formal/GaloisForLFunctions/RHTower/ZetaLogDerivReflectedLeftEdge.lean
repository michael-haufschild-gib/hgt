import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane
import GaloisForLFunctions.RHTower.ZetaLogDerivStripRange
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted
import GaloisForLFunctions.HTGeometry.GammaDigammaStirlingBound
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular

/-!
# The zeta logarithmic derivative just right of `Re s = 0`

Let `T ≥ 16` and `σ_L = A/(4 log⁹ T)`, with `A` the corpus zero-free-strip constant. On the line
`Re s = σ_L`, for `9 ≤ |y| ≤ T`, the residue unit `G(s) = (s − 1)ζ(s)` does not vanish and

`‖G'/G(σ_L + iy)‖ ≤ (2240/A) log⁹ T + log T + 8`
(`zetaResidueUnit_reflectedLeft_ne_zero_and_norm_logDeriv_le`).

The point `1 − s` lies in the zero-free strip at `Re = 1 − σ_L`, where `ζ'/ζ` is bounded by the
corpus strip estimate; the functional equation `ζ'/ζ(s) + ζ'/ζ(1 − s) = log π − ψ(s/2)/2 −
ψ((1−s)/2)/2` and the Stirling bound `‖ψ(z)‖ ≤ log ‖z‖ + 5` transport the bound to `s`.
-/

noncomputable section

open Complex

namespace RHTower

/-- The reflected abscissa `σ_L(T) = A/(4 log⁹ T)`. -/
def reflectedLeftAbscissa (T : ℝ) : ℝ := zetaLowerA / (4 * Real.log T ^ (9 : ℕ))

theorem zetaLowerA_le_half : zetaLowerA ≤ 1 / 2 := by
  rw [zetaLowerA]; norm_num

theorem log_ge_of_sixteen_le {T : ℝ} (hT : 16 ≤ T) : 2 ≤ Real.log T := by
  have h := Real.add_one_le_exp (2 : ℝ)
  have he : Real.exp 2 ≤ 16 := by
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc Real.exp 1 ^ 2 ≤ (2.72 : ℝ) ^ 2 := pow_le_pow_left₀ h0.le (by linarith) 2
      _ ≤ 16 := by norm_num
  rw [← Real.log_exp 2]
  exact Real.log_le_log (Real.exp_pos 2) (he.trans hT)

theorem reflectedLeftAbscissa_pos {T : ℝ} (hT : 16 ≤ T) : 0 < reflectedLeftAbscissa T := by
  have := log_ge_of_sixteen_le hT
  unfold reflectedLeftAbscissa
  exact div_pos zetaLowerA_pos (by positivity)

theorem reflectedLeftAbscissa_le {T : ℝ} (hT : 16 ≤ T) :
    reflectedLeftAbscissa T ≤ 1 / (8 * Real.log T ^ (9 : ℕ)) := by
  have hl := log_ge_of_sixteen_le hT
  unfold reflectedLeftAbscissa
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := zetaLowerA_le_half
  have hp : 0 < Real.log T ^ (9 : ℕ) := by positivity
  nlinarith

/-- `‖ψ(z)‖ ≤ log R + 5` for `Re z > 0`, `2 ≤ ‖z‖ ≤ R`. -/
theorem norm_digamma_le_log {z : ℂ} {R : ℝ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) (hR : ‖z‖ ≤ R) :
    ‖Complex.digamma z‖ ≤ Real.log R + 5 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    norm_num at h2
  have hD := GaloisForLFunctions.HTGeometry.norm_digammaStirlingDefect_le hz h2
  have hdef : Complex.digamma z =
      GaloisForLFunctions.HTGeometry.digammaStirlingDefect z + Complex.log z - 1 / (2 * z) := by
    rw [GaloisForLFunctions.HTGeometry.digammaStirlingDefect]; ring
  have hlog : ‖Complex.log z‖ ≤ Real.log R + Real.pi := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    have h1 : |Real.log ‖z‖| ≤ Real.log R := by
      rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
      exact Real.log_le_log (by linarith) hR
    linarith [Complex.abs_arg_le_pi z]
  have hinv : ‖1 / (2 * z)‖ ≤ 1 / 4 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, div_le_div_iff₀ (by positivity)
      (by norm_num)]
    linarith
  have hD' : 6 / ‖z‖ ^ (2 : ℕ) ≤ 3 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [hdef]
  have := norm_sub_le (GaloisForLFunctions.HTGeometry.digammaStirlingDefect z + Complex.log z) (1 / (2 * z))
  have := norm_add_le (GaloisForLFunctions.HTGeometry.digammaStirlingDefect z) (Complex.log z)
  linarith [Real.pi_lt_d2]

/-- For `Re s < 1`, `ζ(1 − s) ≠ 0` and `Im s ≠ 0` force `ζ(s) ≠ 0`. -/
theorem riemannZeta_ne_zero_of_reflect {s : ℂ} (h1 : s.re < 1)
    (him : s.im ≠ 0) (h : riemannZeta (1 - s) ≠ 0) : riemannZeta s ≠ 0 := by
  set u : ℂ := 1 - s with hu
  have hure : 0 < u.re := by rw [hu]; simp; linarith
  have huim : u.im ≠ 0 := by rw [hu]; simpa using him
  have hun : ∀ n : ℕ, u ≠ -(n : ℂ) := by
    intro n hn
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hu1 : u ≠ 1 := by
    intro h
    apply huim
    rw [h]; simp
  have hfe := riemannZeta_one_sub hun hu1
  have hs : 1 - u = s := by rw [hu]; ring
  rw [hs] at hfe
  rw [hfe]
  have hcos : Complex.cos (Real.pi * u / 2) ≠ 0 := by
    intro hc
    refine (Complex.cos_eq_zero_iff.mp hc).elim fun k hk => ?_
    have him := congrArg Complex.im hk
    have hl : (↑Real.pi * u / 2).im = Real.pi * u.im / 2 := by simp
    have hr : ((2 * (k : ℂ) + 1) * ↑Real.pi / 2).im = 0 := by simp
    rw [hl, hr] at him
    have : u.im = 0 := by
      have hπ := Real.pi_pos
      have h0 : Real.pi * u.im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h Real.pi_ne_zero
      · exact h
    exact huim this
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-u) ≠ 0 := by
    intro h0
    rw [Complex.cpow_eq_zero_iff] at h0
    exact h2π h0.1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow)
    (Complex.Gamma_ne_zero_of_re_pos hure)) hcos) h

/-- **The residue unit on the reflected left line.** -/
theorem zetaResidueUnit_reflectedLeft_ne_zero_and_norm_logDeriv_le {T y : ℝ} (hT : 16 ≤ T)
    (hy9 : 9 ≤ |y|) (hyT : |y| ≤ T) :
    zetaResidueUnit ((reflectedLeftAbscissa T : ℂ) + (y : ℂ) * I) ≠ 0 ∧
      ‖logDeriv zetaResidueUnit ((reflectedLeftAbscissa T : ℂ) + (y : ℂ) * I)‖ ≤
        2240 / zetaLowerA * Real.log T ^ (9 : ℕ) + Real.log T + 8 := by
  set σL : ℝ := reflectedLeftAbscissa T with hσL
  set s : ℂ := (σL : ℂ) + (y : ℂ) * I with hs
  have hl := log_ge_of_sixteen_le hT
  have hσ0 : 0 < σL := reflectedLeftAbscissa_pos hT
  have hσle := reflectedLeftAbscissa_le hT
  have hp9 : (2 : ℝ) ^ 9 ≤ Real.log T ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hl 9
  have hσ8 : σL ≤ 1 / 8 := hσle.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hsre : s.re = σL := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hy0 : y ≠ 0 := by
    intro h; rw [h, abs_zero] at hy9; norm_num at hy9
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [hs] at this
    exact hy0 this
  -- nonvanishing
  have h1s : riemannZeta (1 - s) ≠ 0 := by
    refine riemannZeta_ne_zero_of_lt_re (by simp [hs]; linarith) ?_
    have hre1 : (1 - s).re = 1 - σL := by simp [hs]
    have him1 : |(1 - s).im| = |y| := by simp [hs]
    rw [hre1, him1]
    have hlog4 : Real.log (|y| + 4) ≤ 2 * Real.log T := by
      have : |y| + 4 ≤ T ^ 2 := by nlinarith
      calc Real.log (|y| + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) this
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    have hlog4pos : 0 < Real.log (|y| + 4) := Real.log_pos (by linarith [abs_nonneg y])
    have hkey : σL < 1 / 58 / Real.log (|y| + 4) := by
      refine lt_of_le_of_lt hσle ?_
      rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      have h8 : (2 : ℝ) ^ 8 ≤ Real.log T ^ (8 : ℕ) := pow_le_pow_left₀ (by norm_num) hl 8
      have e9 : Real.log T ^ (9 : ℕ) = Real.log T ^ (8 : ℕ) * Real.log T := by ring
      rw [e9]
      nlinarith
    linarith
  have hζs : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_reflect (by rw [hsre]; linarith)
      (by rw [hsim]; exact hy0) h1s
  have hG : zetaResidueUnit s ≠ 0 := (Sieve.zetaResidueUnit_ne_zero_iff hs1).2 hζs
  refine ⟨hG, ?_⟩
  -- the logarithmic derivative
  rw [show logDeriv zetaResidueUnit s = logDeriv riemannZeta s + (s - 1)⁻¹ by
    rw [logDeriv_zeta_eq hs1 hG]; ring]
  have hrefl := logDeriv_riemannZeta_add_reflect_of_strip (s := s) (by rw [hsre]; exact hσ0)
    (by rw [hsre]; linarith) hζs h1s
  have hLz : logDeriv riemannZeta s = (Real.log Real.pi : ℂ) - Complex.digamma (s / 2) / 2 -
      Complex.digamma ((1 - s) / 2) / 2 - logDeriv riemannZeta (1 - s) := by
    rw [← hrefl]; ring
  rw [hLz]
  -- the reflected point is in the zero-free strip
  have hA := zetaLowerA_pos
  have hstrip : ‖logDeriv riemannZeta (1 - s)‖ ≤ 2240 / zetaLowerA * Real.log T ^ (9 : ℕ) := by
    have e : 1 - s = ((1 - σL : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [e, logDeriv_apply]
    have hσl : 1 - zetaLowerA / (2 * Real.log T ^ (9 : ℕ)) ≤ 1 - σL := by
      have : σL ≤ zetaLowerA / (2 * Real.log T ^ (9 : ℕ)) := by
        rw [hσL, reflectedLeftAbscissa]
        exact div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith)
      linarith
    have hσu : 1 - σL ≤ 1 + zetaLowerA / (2 * Real.log T ^ (9 : ℕ)) := by
      have : 0 ≤ zetaLowerA / (2 * Real.log T ^ (9 : ℕ)) := by positivity
      linarith
    exact norm_zeta_logDeriv_le_strip_range (by linarith) (by rwa [abs_neg])
      (by rwa [abs_neg]) hσl hσu
  -- digamma bounds
  have hψ1 : ‖Complex.digamma (s / 2)‖ ≤ Real.log T + 5 := by
    refine norm_digamma_le_log (by simp [hs]; linarith) ?_ ?_
    · have := Complex.abs_im_le_norm (s / 2)
      have him : (s / 2).im = y / 2 := by simp [hs]
      rw [him, abs_div, abs_two] at this
      linarith
    · have hn : ‖s / 2‖ ≤ (σL + |y|) / 2 := by
        rw [norm_div, Complex.norm_two, hs]
        have := Complex.norm_le_abs_re_add_abs_im ((σL : ℂ) + (y : ℂ) * I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, mul_one, zero_add] at this
        rw [abs_of_pos hσ0] at this
        linarith
      linarith
  have hψ2 : ‖Complex.digamma ((1 - s) / 2)‖ ≤ Real.log T + 5 := by
    refine norm_digamma_le_log (by simp [hs]; linarith) ?_ ?_
    · have := Complex.abs_im_le_norm ((1 - s) / 2)
      have him : ((1 - s) / 2).im = -y / 2 := by simp [hs]
      rw [him, abs_div, abs_neg, abs_two] at this
      linarith
    · have hn : ‖(1 - s) / 2‖ ≤ (1 + |y|) / 2 := by
        rw [norm_div, Complex.norm_two]
        have e : 1 - s = ((1 - σL : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by
          rw [hs]; push_cast; ring
        rw [e]
        have := Complex.norm_le_abs_re_add_abs_im (((1 - σL : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, mul_one, zero_add] at this
        rw [abs_of_pos (by linarith), abs_neg] at this
        linarith
      linarith
  have hlogπ : ‖((Real.log Real.pi : ℝ) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
      linarith [Real.pi_gt_three]))]
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d2])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have hinv : ‖(s - 1)⁻¹‖ ≤ 1 / 9 := by
    rw [norm_inv, one_div]
    refine inv_anti₀ (by norm_num) ?_
    have := Complex.abs_im_le_norm (s - 1)
    have him : (s - 1).im = y := by simp [hs]
    rw [him] at this
    linarith
  set a₁ : ℂ := ((Real.log Real.pi : ℝ) : ℂ) with ha₁
  set a₂ : ℂ := Complex.digamma (s / 2) with ha₂
  set a₃ : ℂ := Complex.digamma ((1 - s) / 2) with ha₃
  set a₄ : ℂ := logDeriv riemannZeta (1 - s) with ha₄
  have t4 := norm_add_le (a₁ - a₂ / 2 - a₃ / 2 - a₄) ((s - 1)⁻¹)
  have t1 := norm_sub_le (a₁ - a₂ / 2 - a₃ / 2) a₄
  have t2 := norm_sub_le (a₁ - a₂ / 2) (a₃ / 2)
  have t3 := norm_sub_le a₁ (a₂ / 2)
  have e2 : ‖a₂ / 2‖ = ‖a₂‖ / 2 := by rw [norm_div, Complex.norm_two]
  have e3 : ‖a₃ / 2‖ = ‖a₃‖ / 2 := by rw [norm_div, Complex.norm_two]
  rw [e2] at t3
  rw [e3] at t2
  linarith

end RHTower
