import GaloisForLFunctions.RHTower.XiHorizontalLogDerivativeModel
import GaloisForLFunctions.RHTower.Sieve.ZetaCrudeGrowth
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness

/-!
# Along a horizontal line, `ξ` in the strip is controlled by its value at `Re s = 5`

At height `Y ≥ 4` the digamma function has positive real part on the right half-plane
(`ψ(z) = log z − 1/(2z) + O(6/|z|²)`), so `x ↦ |Γ(x + iY)|` is nondecreasing on `x > 0`
(`monotoneOn_norm_Gamma_horizontal`). Writing `ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)` and using
`|ζ(s)| ≤ 2 + 2|s|` on `Re s ≥ ½` together with `|ζ(5 + iX) − 1| ≤ π²/6 − 1`, every point of the
horizontal segment `½ ≤ σ ≤ 5` at height `X ≥ 8` satisfies

`|ξ(σ + iX)| ≤ 200 (6 + X) |ξ(5 + iX)|`   (`norm_xi_horizontal_le_mul_norm_xi_five`).
-/

open Complex Set

namespace RHTower

noncomputable section

/-- `Re ψ(z) > 0` for `Re z > 0`, `|z| ≥ 4`. -/
theorem re_digamma_pos {z : ℂ} (hz : 0 < z.re) (h4 : 4 ≤ ‖z‖) : 0 < (Complex.digamma z).re := by
  have hz0 : 0 < ‖z‖ := by linarith
  have hD := GaloisForLFunctions.HTGeometry.norm_digammaStirlingDefect_le hz (by linarith)
  have hdig : Complex.digamma z = GaloisForLFunctions.HTGeometry.digammaStirlingDefect z +
      Complex.log z - 1 / (2 * z) := by
    rw [GaloisForLFunctions.HTGeometry.digammaStirlingDefect]; ring
  have hDre : -(6 / ‖z‖ ^ 2) ≤ (GaloisForLFunctions.HTGeometry.digammaStirlingDefect z).re := by
    have := Complex.abs_re_le_norm (GaloisForLFunctions.HTGeometry.digammaStirlingDefect z)
    have h2 : (6 : ℝ) / ‖z‖ ^ (2 : ℕ) = 6 / ‖z‖ ^ 2 := rfl
    rw [abs_le] at this
    linarith
  have hinv : (1 / (2 * z)).re ≤ 1 / 8 := by
    have := Complex.re_le_norm (1 / (2 * z))
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat] at this
    have : 1 / (2 * ‖z‖) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hlog : Real.log 4 ≤ (Complex.log z).re := by
    rw [Complex.log_re]; exact Real.log_le_log (by norm_num) h4
  have hlog4 : 1.38 < Real.log 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_gt_d9]
  have h6 : 6 / ‖z‖ ^ 2 ≤ 3 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  rw [hdig, Complex.sub_re, Complex.add_re]
  linarith

/-- **Monotonicity of `|Γ|` along horizontal lines** at height `|Y| ≥ 4`. -/
theorem monotoneOn_norm_Gamma_horizontal {Y : ℝ} (hY : 4 ≤ |Y|) :
    MonotoneOn (fun x : ℝ => ‖Complex.Gamma ((x : ℂ) + Y * I)‖) (Ioi 0) := by
  set f : ℝ → ℂ := fun x => Complex.Gamma ((x : ℂ) + Y * I) with hf
  have hre : ∀ x : ℝ, ((x : ℂ) + Y * I).re = x := by intro x; simp
  have hnorm : ∀ x : ℝ, 4 ≤ ‖(x : ℂ) + Y * I‖ := by
    intro x
    have := Complex.abs_im_le_norm ((x : ℂ) + Y * I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one, add_zero] at this
    linarith
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f
      (Complex.Gamma ((x : ℂ) + Y * I) * Complex.digamma ((x : ℂ) + Y * I)) x := by
    intro x hx
    have hpos : 0 < ((x : ℂ) + Y * I).re := by rw [hre]; exact hx
    have hne : ∀ m : ℕ, (x : ℂ) + Y * I ≠ -m := by
      intro m h
      have := congrArg Complex.re h
      rw [hre] at this
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hG := (Complex.differentiableAt_Gamma _ hne).hasDerivAt
    have hΓ0 := Complex.Gamma_ne_zero_of_re_pos hpos
    have hd : deriv Complex.Gamma ((x : ℂ) + Y * I) =
        Complex.Gamma ((x : ℂ) + Y * I) * Complex.digamma ((x : ℂ) + Y * I) := by
      rw [Complex.digamma_def, logDeriv_apply]; field_simp
    rw [hd] at hG
    have h2 := (hG.comp_add_const ((x : ℂ)) (Y * I))
    have h3 : HasDerivAt (fun y : ℂ => Complex.Gamma (y + Y * I))
        (Complex.Gamma ((x : ℂ) + Y * I) * Complex.digamma ((x : ℂ) + Y * I)) (x : ℂ) := h2
    exact h3.comp_ofReal
  set φ : ℝ → ℝ := fun x => ‖f x‖ ^ 2 with hφ
  have hφd : ∀ x : ℝ, 0 < x → HasDerivAt φ
      (2 * (‖f x‖ ^ 2 * (Complex.digamma ((x : ℂ) + Y * I)).re)) x := by
    intro x hx
    have h := (hderiv x hx).norm_sq
    convert h using 2
    rw [Complex.inner]
    simp only [hf]
    rw [mul_comm (Complex.Gamma _) _, mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal,
      Complex.normSq_eq_norm_sq]
    ring
  have hmono : MonotoneOn φ (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · exact fun x hx => (hφd x hx).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      exact fun x hx => (hφd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro x hx
      rw [(hφd x hx).deriv]
      have := re_digamma_pos (z := (x : ℂ) + Y * I) (by rw [hre]; exact hx) (hnorm x)
      positivity
  intro x hx x' hx' hxx'
  have := hmono hx hx' hxx'
  simp only [hφ] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- `ξ(s) = ½ s(s−1) Γℝ(s) ζ(s)` off `s = 0, 1`. -/
theorem xi_eq_mul_Gammaℝ_mul_riemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hre : 0 < s.re) :
    xi s = s * (s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) := by
  rw [xi_eq_half_mul hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  have := Complex.Gammaℝ_ne_zero_of_re_pos hre
  field_simp

private theorem norm_Gammaℝ_eq {s : ℂ} :
    ‖Complex.Gammaℝ s‖ = Real.pi ^ (-s.re / 2) * ‖Complex.Gamma (s / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp

/-- **The strip comparison.** For `½ ≤ σ ≤ 5` and `X ≥ 8`,
`|ξ(σ + iX)| ≤ 200 (6 + X) |ξ(5 + iX)|`. -/
theorem norm_xi_horizontal_le_mul_norm_xi_five {σ X : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ5 : σ ≤ 5)
    (hX : 8 ≤ X) :
    ‖xi ((σ : ℂ) + X * I)‖ ≤ 200 * (6 + X) * ‖xi ((5 : ℝ) + X * I)‖ := by
  have hX0 : 0 < X := by linarith
  have hne : ∀ τ : ℝ, (τ : ℂ) + X * I ≠ 0 ∧ (τ : ℂ) + X * I ≠ 1 := by
    intro τ
    constructor <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;> linarith
  set s : ℂ := (σ : ℂ) + X * I with hs
  set s5 : ℂ := ((5 : ℝ) : ℂ) + X * I with hs5
  have hsre : s.re = σ := by simp [hs]
  have hs5re : s5.re = 5 := by simp [hs5]
  have hs0 : s ≠ 0 := (hne σ).1
  have hs1 : s ≠ 1 := (hne σ).2
  have hs50 : s5 ≠ 0 := (hne 5).1
  have hs51 : s5 ≠ 1 := (hne 5).2
  rw [xi_eq_mul_Gammaℝ_mul_riemannZeta hs0 hs1 (by rw [hsre]; linarith),
    xi_eq_mul_Gammaℝ_mul_riemannZeta hs50 hs51 (by rw [hs5re]; norm_num)]
  simp only [norm_mul, norm_div, Complex.norm_ofNat, norm_Gammaℝ_eq, hsre, hs5re]
  -- the polynomial factors
  have hns : ‖s‖ ≤ ‖s5‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp [hs, hs5]
    nlinarith
  have hns1 : ‖s - 1‖ ≤ ‖s5 - 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp [hs, hs5]
    nlinarith
  -- the Gamma factors
  have hhalf : ∀ τ : ℝ, ((τ : ℂ) + X * I) / 2 = ((τ / 2 : ℝ) : ℂ) + (X / 2 : ℝ) * I := by
    intro τ; push_cast; ring
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ ‖Complex.Gamma (s5 / 2)‖ := by
    rw [hs, hs5, hhalf, hhalf]
    refine monotoneOn_norm_Gamma_horizontal (Y := X / 2) ?_ ?_ ?_ ?_
    · rw [abs_of_pos (by positivity)]; linarith
    · show (0 : ℝ) < σ / 2; linarith
    · show (0 : ℝ) < 5 / 2; norm_num
    · linarith
  -- the power of `π`
  have hpi : Real.pi ^ (-σ / 2) ≤ 32 * Real.pi ^ (-(5 : ℝ) / 2) := by
    have hsplit : Real.pi ^ (-σ / 2) = Real.pi ^ ((5 - σ) / 2) * Real.pi ^ (-(5 : ℝ) / 2) := by
      rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
    rw [hsplit]
    have h3 : Real.pi ^ ((5 - σ) / 2) ≤ Real.pi ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
    have h32 : Real.pi ^ (3 : ℝ) ≤ 32 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have := Real.pi_lt_d2
      have h0 := Real.pi_pos
      nlinarith [mul_pos h0 h0]
    have hp := Real.rpow_pos_of_pos Real.pi_pos (-(5 : ℝ) / 2)
    nlinarith
  -- the zeta factors
  have hζ : ‖riemannZeta s‖ ≤ 2 + 2 * (5 + X) := by
    refine (RHTower.Sieve.norm_riemannZeta_le_crude (by rw [hsre]; exact hσ1) ?_).trans ?_
    · simp [hs]; rw [abs_of_pos hX0]; linarith
    · have : ‖s‖ ≤ 5 + X := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul,
          Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
        linarith
      linarith
  have hζ5 : 1 / 3 ≤ ‖riemannZeta s5‖ := by
    have h := norm_riemannZeta_sub_one_le_zeta_two (s := s5) (by rw [hs5re]; norm_num)
    have hpi2 : Real.pi ^ 2 / 6 - 1 ≤ 2 / 3 := by
      have := Real.pi_lt_d2; have h0 := Real.pi_pos; nlinarith
    have := norm_sub_norm_le (1 : ℂ) (riemannZeta s5)
    rw [norm_one, norm_sub_rev] at this
    linarith
  -- assemble
  have hA : 0 ≤ ‖s5‖ * ‖s5 - 1‖ / 2 * Real.pi ^ (-(5 : ℝ) / 2) * ‖Complex.Gamma (s5 / 2)‖ := by
    positivity
  calc ‖s‖ * ‖s - 1‖ / 2 * (Real.pi ^ (-σ / 2) * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖)
      ≤ ‖s5‖ * ‖s5 - 1‖ / 2 *
          (32 * Real.pi ^ (-(5 : ℝ) / 2) * ‖Complex.Gamma (s5 / 2)‖ * (2 + 2 * (5 + X))) := by
        gcongr
    _ = (‖s5‖ * ‖s5 - 1‖ / 2 * Real.pi ^ (-(5 : ℝ) / 2) * ‖Complex.Gamma (s5 / 2)‖) *
          (64 * (6 + X)) := by ring
    _ ≤ (‖s5‖ * ‖s5 - 1‖ / 2 * Real.pi ^ (-(5 : ℝ) / 2) * ‖Complex.Gamma (s5 / 2)‖) *
          (200 * (6 + X) * ‖riemannZeta s5‖) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hA
    _ = 200 * (6 + X) * (‖s5‖ * ‖s5 - 1‖ / 2 *
          (Real.pi ^ (-(5 : ℝ) / 2) * ‖Complex.Gamma (s5 / 2)‖ * ‖riemannZeta s5‖)) := by ring

end

end RHTower
