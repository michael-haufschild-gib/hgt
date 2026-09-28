import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness
import GaloisForLFunctions.HTGeometry.GammaImaginaryShiftBounds
import GaloisForLFunctions.RHTower.EntireAutomorphism
import GaloisForLFunctions.RHTower.ResolventDivisionDecay

/-!
# The Hardy equality case for `ξ`: theta-rate `ξ`-divisible functions are `P · Φ`

`ThetaThresholdXiDivisibleUniqueness` shows that no function decaying at a rate `c > π`,
`|F(x)| ≤ C exp(−c e^{2|x|})`, has a centred Laplace transform `M_F(s) = ∫ F(x) e^{(s−½)x} dx`
divisible by `ξ`, while Riemann's kernel `Φ` (`M_Φ = ξ`) has every rate `c < π`. This file settles
the boundary case, in the form of Hardy's uncertainty theorem with polynomial factors
(`theta_rigidity_polynomial_quotient`):

> if `|F(x)| ≤ C e^{k|x|} exp(−π e^{2|x|})` and `M_F = ξ · h` with `h` entire, then `h` is a
> polynomial.

`Φ` satisfies the hypothesis with `k = 9/2` (`riemannPhiKernel_theta_rate`), with quotient `1`.

**Proof.**
* *Exact directional Stirling.* The imaginary-shift bound for `Γ` gives
  `|Γ(x+iy)| ≥ Γ(x)(1+y²/x²)^{−1/2}e^{−y²/x}` (`Gamma_mul_quadratic_le_norm_Gamma`). Against the
  theta-rate Legendre bound for `M_F`, this yields on `Re s ≥ 2`:
  `|h(σ+it)| ≤ B₀ (σ+K)^{(K+1)/2} √(1+t²/σ²) e^{t²/(2σ)}` (`norm_quotient_le_theta_right`).
  The growth is quadratic in the angle.
* *Sector Phragmén–Lindelöf.* On the rays `arg z = δ, π − δ` this gives
  `|h| ≤ B |z+i|^m e^{δ²|z|}`. Via `z = e^w` and the strip principle on `δ < Im w < π − δ`, it gives
  `|h(z)| ≤ B |z+i|^m e^{(δ²/sin δ) Im z}` on the sector (`norm_le_sector_of_rays`).
* *Limit.* `δ²/sin δ ≤ (π/2)δ → 0` with `B` independent of `δ`, so `|h(z)| ≤ B |z+i|^m` on the upper
  half-plane (`norm_le_upper_half_plane`). The lower half-plane follows by complex conjugation of
  `F`, and an entire function of polynomial growth is a polynomial.

Pointwise bounds at fixed height cannot see this: `h(s) = cos(b(s−½))` is bounded on the real axis,
but it grows like `e^{b|z| sin θ}`, which is linear in the angle and violates the quadratic
directional bound.
-/

open Complex Filter Topology MeasureTheory
open scoped Real

namespace RHTower

noncomputable section

/-! ## The Gamma floor with quadratic phase loss -/

/-- `2u arctan u − log(1+u²) ≤ 2u²`, hence the imaginary-shift integral is at most `2y²/x`. -/
theorem gammaShiftIntegral_le {x y : ℝ} (hx : 0 < x) :
    HTGeometry.gammaShiftIntegral x y ≤ 2 * y ^ 2 / x := by
  unfold HTGeometry.gammaShiftIntegral HTGeometry.gammaShiftPrimitive
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hY : 0 < |y| := abs_pos.mpr hy
  have harc : Real.arctan (x / |y|) = π / 2 - Real.arctan (|y| / x) := by
    rw [← Real.arctan_inv_of_pos (by positivity)]; congr 1; field_simp
  rw [harc]
  have hat : Real.arctan (|y| / x) ≤ |y| / x := by
    have h := Real.le_tan (Real.arctan_nonneg.mpr (by positivity : (0 : ℝ) ≤ |y| / x))
      (Real.arctan_lt_pi_div_two _)
    rwa [Real.tan_arctan] at h
  have hlog : 0 ≤ Real.log (1 + y ^ 2 / x ^ 2) := Real.log_nonneg (by
    have := div_nonneg (sq_nonneg y) (sq_nonneg x); linarith)
  have hy2 : |y| * |y| = y ^ 2 := by rw [← sq, sq_abs]
  have h1 : 2 * |y| * Real.arctan (|y| / x) ≤ 2 * |y| * (|y| / x) :=
    mul_le_mul_of_nonneg_left hat (by positivity)
  have h2 : 2 * |y| * (|y| / x) = 2 * y ^ 2 / x := by rw [← hy2]; ring
  nlinarith [mul_nonneg hx.le hlog]

/-- **Gamma floor with quadratic loss.** `|Γ(x+iy)| ≥ Γ(x) (1 + y²/x²)^{-1/2} e^{-y²/x}` for `x > 0`. -/
theorem Gamma_mul_quadratic_le_norm_Gamma {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.Gamma x * (Real.sqrt (1 + y ^ 2 / x ^ 2))⁻¹ * Real.exp (-(y ^ 2 / x)) ≤
      ‖Complex.Gamma ((x : ℂ) + y * I)‖ := by
  have hb := (HTGeometry.log_norm_Gamma_sub_log_Gamma_bounds hx y).1
  have hI := gammaShiftIntegral_le (y := y) hx
  have hΓ : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hw : HTGeometry.gammaShiftWeight x y 0 = Real.log (1 + y ^ 2 / x ^ 2) := by
    simp [HTGeometry.gammaShiftWeight]
  rw [hw] at hb
  have hq : 0 < 1 + y ^ 2 / x ^ 2 := by positivity
  have hnz : ‖Complex.Gamma ((x : ℂ) + y * I)‖ ≠ 0 := by
    intro h0
    rw [h0, Real.log_zero] at hb
    have : Real.log (Real.Gamma x) ≤ (1 / 2) * (Real.log (1 + y ^ 2 / x ^ 2) +
        HTGeometry.gammaShiftIntegral x y) := by linarith
    -- impossible: `log ‖Γ‖ = 0` would force `‖Γ‖ = 0`, but `Γ(x+iy) ≠ 0`
    exact absurd (norm_eq_zero.mp h0) (Complex.Gamma_ne_zero_of_re_pos (by simp [hx]))
  have hpos : 0 < ‖Complex.Gamma ((x : ℂ) + y * I)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnz)
  rw [← Real.exp_log hpos]
  have hsq : (Real.sqrt (1 + y ^ 2 / x ^ 2))⁻¹ = Real.exp (-(1 / 2) * Real.log (1 + y ^ 2 / x ^ 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hq.le, Real.rpow_def_of_pos hq]; ring_nf
  rw [hsq, ← Real.exp_log hΓ, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e : 2 * y ^ 2 / x = 2 * (y ^ 2 / x) := by ring
  rw [e] at hI
  linarith

/-- **`ξ` floor with quadratic loss.** For `σ ≥ 2`,
`|ξ(σ+it)| ≥ (1/3) π^{-σ/2} Γ(σ/2) (1 + t²/σ²)^{-1/2} e^{-t²/(2σ)}`. -/
theorem xi_floor_quadratic {σ t : ℝ} (hσ : 2 ≤ σ) :
    1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
      Real.exp (-(t ^ 2 / (2 * σ))) ≤ ‖xi ((σ : ℂ) + (t : ℂ) * I)‖ := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  rw [norm_xi_eq_factors (by rw [hsre]; linarith) hs1, hsre]
  have hpoly : 1 ≤ ‖s * (s - 1) / 2‖ := by
    rw [norm_mul_sub_one_div_two]
    have h1 : σ ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hsre, abs_of_pos (by linarith)] at this
      exact this
    have h2 : σ - 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, hsre, Complex.one_re, abs_of_pos (by linarith)] at this
      exact this
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hG := Gamma_mul_quadratic_le_norm_Gamma (x := σ / 2) (by linarith) (t / 2)
  have e1 : ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I = s / 2 := by rw [hs]; push_cast; ring
  rw [e1] at hG
  have e2 : (t / 2) ^ 2 / (σ / 2) ^ 2 = t ^ 2 / σ ^ 2 := by field_simp
  have e3 : (t / 2) ^ 2 / (σ / 2) = t ^ 2 / (2 * σ) := by field_simp
  rw [e2, e3] at hG
  have hZ := one_third_le_norm_riemannZeta (s := s) (by rw [hsre]; exact hσ)
  have hpi : 0 < Real.pi ^ (-(σ / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hq : 0 < (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ := by positivity
  have he : 0 < Real.exp (-(t ^ 2 / (2 * σ))) := Real.exp_pos _
  have hprod : 0 ≤ Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖ := by
    positivity
  calc 1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
        Real.exp (-(t ^ 2 / (2 * σ)))
      = (Real.pi ^ (-(σ / 2)) * (Real.Gamma (σ / 2) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
          Real.exp (-(t ^ 2 / (2 * σ))))) * (1 / 3) := by ring
    _ ≤ (Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖) * ‖riemannZeta s‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hG hpi.le) hZ (by norm_num) (by positivity)
    _ ≤ ‖s * (s - 1) / 2‖ * (Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖) *
          ‖riemannZeta s‖ := by nlinarith

/-! ## Growth of `M_F` at the exact theta rate -/

/-- At the exact rate `π` with prefactor `e^{k|x|}`:
`‖M_F(s)‖ ≤ C e^{G} ∫ e^{-|x|}` with `G = legendreMajorant π (|σ − ½| + k + 1)`. -/
theorem norm_centredLaplace_le_theta {F : ℝ → ℂ} {C k : ℝ}
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - π * Real.exp (2 * |x|))) (hk : 0 ≤ k) (s : ℂ) :
    ‖centredLaplace F s‖ ≤
      C * Real.exp (legendreMajorant π (|s.re - 1 / 2| + k + 1)) *
        ∫ x : ℝ, Real.exp (-|x|) := by
  have hC : 0 ≤ C := by
    have h1 := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (k * |(0 : ℝ)| - π * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  set G := legendreMajorant π (|s.re - 1 / 2| + k + 1) with hG
  have hpt : ∀ x : ℝ, ‖cexp ((s - 1 / 2) * x) * F x‖ ≤ C * Real.exp G * Real.exp (-|x|) := by
    intro x
    rw [norm_mul, Complex.norm_exp]
    have hre : ((s - 1 / 2) * (x : ℂ)).re = (s.re - 1 / 2) * x := by simp
    rw [hre]
    have hlin : (s.re - 1 / 2) * x ≤ |s.re - 1 / 2| * |x| := by
      calc (s.re - 1 / 2) * x ≤ |(s.re - 1 / 2) * x| := le_abs_self _
        _ = |s.re - 1 / 2| * |x| := abs_mul _ _
    have hleg := le_legendreMajorant (c := π) Real.pi_pos
      (by positivity : 0 ≤ |s.re - 1 / 2| + k + 1) |x|
    have hexp : (s.re - 1 / 2) * x + (k * |x| - π * Real.exp (2 * |x|)) ≤ G + -|x| := by
      rw [hG]; nlinarith
    calc Real.exp ((s.re - 1 / 2) * x) * ‖F x‖
        ≤ Real.exp ((s.re - 1 / 2) * x) * (C * Real.exp (k * |x| - π * Real.exp (2 * |x|))) :=
          mul_le_mul_of_nonneg_left (hF x) (Real.exp_pos _).le
      _ = C * Real.exp ((s.re - 1 / 2) * x + (k * |x| - π * Real.exp (2 * |x|))) := by
          rw [Real.exp_add]; ring
      _ ≤ C * Real.exp (G + -|x|) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
      _ = C * Real.exp G * Real.exp (-|x|) := by rw [Real.exp_add]; ring
  have hint : Integrable fun x : ℝ => C * Real.exp G * Real.exp (-|x|) :=
    integrable_exp_neg_abs.const_mul _
  unfold centredLaplace
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_const_mul]

/-- At the theta rate the Legendre majorant against `Γ(σ/2)` costs only a power:
`e^{G} π^{σ/2}/Γ(σ/2) ≤ e^π (σ+K)^{(K+1)/2}` with `K = k + ½` and `G = legendreMajorant π (σ − ½ + k + 1)`. -/
theorem legendre_theta_div_Gamma_le {k σ : ℝ} (hk : 0 ≤ k) (hσ : 2 ≤ σ) :
    Real.exp (legendreMajorant π (σ - 1 / 2 + k + 1)) * Real.pi ^ (σ / 2) / Real.Gamma (σ / 2) ≤
      Real.exp π * (σ + (k + 1 / 2)) ^ ((k + 1 / 2 + 1) / 2) := by
  set K := k + 1 / 2 with hK
  have hK0 : 0 ≤ K := by linarith
  set y := σ + K with hy
  have hy_eq : σ - 1 / 2 + k + 1 = y := by rw [hy, hK]; ring
  rw [hy_eq]
  have hσ0 : 0 < σ := by linarith
  have hy0 : 0 < y := by linarith
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hst := stirling_le_log_Gamma (a := σ / 2) (by linarith)
  set Ly := Real.log y
  set Lσ := Real.log σ
  set L2 := Real.log 2
  set Lπ := Real.log π
  have hL2 : 0 ≤ L2 := Real.log_nonneg (by norm_num)
  have hLπ : 0 ≤ Lπ := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog2π : Real.log (2 * π) = L2 + Lπ := Real.log_mul (by norm_num) Real.pi_pos.ne'
  have hlogσ2 : Real.log (σ / 2) = Lσ - L2 := Real.log_div hσ0.ne' (by norm_num)
  have hlogy2π : Real.log (y / (2 * π)) = Ly - (L2 + Lπ) := by
    rw [Real.log_div hy0.ne' (by positivity), hlog2π]
  -- the Legendre expression is at least `−π`
  have hE : -π ≤ y / 2 * (Real.log (y / (2 * π)) - 1) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < y / (2 * π) by positivity)
    have hinv : (y / (2 * π))⁻¹ = 2 * π / y := by rw [inv_div]
    rw [hinv] at h
    have : y / 2 * (Real.log (y / (2 * π)) - 1) ≥ y / 2 * (-(2 * π / y)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : y / 2 * (-(2 * π / y)) = -π := by field_simp
    linarith
  have hG : legendreMajorant π y ≤ y / 2 * (Real.log (y / (2 * π)) - 1) + π := by
    unfold legendreMajorant; exact max_le (by linarith) (by linarith [Real.pi_pos])
  -- `σ log(y/σ) ≤ K`
  have hratio : σ * (Ly - Lσ) ≤ K := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / σ by positivity)
    rw [Real.log_div hy0.ne' hσ0.ne'] at h
    have e : y / σ - 1 = K / σ := by rw [hy]; field_simp; ring
    rw [e] at h
    have := mul_le_mul_of_nonneg_left h hσ0.le
    rwa [mul_div_cancel₀ _ hσ0.ne'] at this
  have hσy : Lσ ≤ Ly := Real.log_le_log hσ0 (by linarith)
  rw [hlogσ2, hlog2π] at hst
  rw [hlogy2π] at hG
  have hkey : legendreMajorant π y + σ / 2 * Lπ - Real.log (Real.Gamma (σ / 2)) ≤
      π + (K + 1) / 2 * Ly := by
    have e : y / 2 * (Ly - (L2 + Lπ) - 1) + π + σ / 2 * Lπ -
        ((σ / 2 - 1 / 2) * (Lσ - L2) - σ / 2 + (L2 + Lπ) / 2)
        = σ / 2 * (Ly - Lσ) + K / 2 * (Ly - L2 - Lπ - 1) + π + 1 / 2 * Lσ - L2 - Lπ / 2 := by
      rw [hy]; ring
    nlinarith [mul_nonneg hK0 (add_nonneg hL2 hLπ)]
  rw [div_le_iff₀ hΓ, ← Real.exp_log hΓ]
  have hpi : Real.pi ^ (σ / 2) = Real.exp (σ / 2 * Lπ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]; congr 1; rw [mul_comm]
  have hyp : y ^ ((K + 1) / 2) = Real.exp ((K + 1) / 2 * Ly) := by
    rw [Real.rpow_def_of_pos hy0]; congr 1; rw [mul_comm]
  rw [hpi, hyp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **Right half-plane bound at the theta rate.** For `σ ≥ 2`,
`‖h(σ+it)‖ ≤ 3CJ e^π (σ+K)^{(K+1)/2} √(1+t²/σ²) e^{t²/(2σ)}`, `J = ∫ e^{−|x|}`, `K = k + ½`. -/
theorem norm_quotient_le_theta_right {F : ℝ → ℂ} {h : ℂ → ℂ} {C k : ℝ} (hk : 0 ≤ k)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - π * Real.exp (2 * |x|)))
    (hdiv : ∀ s : ℂ, 2 ≤ s.re → centredLaplace F s = xi s * h s) {σ t : ℝ} (hσ : 2 ≤ σ) :
    ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      3 * (C * ∫ x : ℝ, Real.exp (-|x|)) *
        (Real.exp π * (σ + (k + 1 / 2)) ^ ((k + 1 / 2 + 1) / 2)) *
        Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hMb := norm_centredLaplace_le_theta hF hk s
  have habs : |s.re - 1 / 2| + k + 1 = σ - 1 / 2 + k + 1 := by
    rw [hsre, abs_of_pos (by linarith)]
  rw [habs] at hMb
  have hC : 0 ≤ C := by
    have h1 := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (k * |(0 : ℝ)| - π * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  have hJ : 0 ≤ ∫ x : ℝ, Real.exp (-|x|) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hfl := xi_floor_quadratic (t := t) hσ
  set f := 1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
      Real.exp (-(t ^ 2 / (2 * σ))) with hf
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hsq : 0 < Real.sqrt (1 + t ^ 2 / σ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hfpos : 0 < f := by positivity
  have hnorm : ‖centredLaplace F s‖ = ‖xi s‖ * ‖h s‖ := by rw [hdiv s (by rw [hsre]; exact hσ), norm_mul]
  have h1 : f * ‖h s‖ ≤ C * Real.exp (legendreMajorant π (σ - 1 / 2 + k + 1)) *
      ∫ x : ℝ, Real.exp (-|x|) := by
    calc f * ‖h s‖ ≤ ‖xi s‖ * ‖h s‖ := mul_le_mul_of_nonneg_right hfl (norm_nonneg _)
      _ = _ := hnorm.symm
      _ ≤ _ := hMb
  rw [← le_div_iff₀' hfpos] at h1
  have hinv : 1 / f = 3 * (Real.pi ^ (σ / 2) / Real.Gamma (σ / 2)) *
      Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)) := by
    rw [hf, Real.rpow_neg Real.pi_pos.le, Real.exp_neg]
    field_simp
  have hl := legendre_theta_div_Gamma_le hk hσ
  calc ‖h s‖ ≤ C * Real.exp (legendreMajorant π (σ - 1 / 2 + k + 1)) *
        (∫ x : ℝ, Real.exp (-|x|)) / f := h1
    _ = 3 * (C * ∫ x : ℝ, Real.exp (-|x|)) *
        (Real.exp (legendreMajorant π (σ - 1 / 2 + k + 1)) * Real.pi ^ (σ / 2) /
          Real.Gamma (σ / 2)) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)) := by
        rw [div_eq_mul_one_div, hinv]; ring
    _ ≤ _ := by
        gcongr


/-! ## Phragmén–Lindelöf in a sector through the exponential map -/

theorem sin_ge_of_mem_Icc {δ x : ℝ} (hδ : 0 ≤ δ) (hx1 : δ ≤ x) (hx2 : x ≤ π - δ) :
    Real.sin δ ≤ Real.sin x := by
  rcases le_total x (π / 2) with h | h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h hx1
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)

theorem im_exp_ge {δ : ℝ} (hδ : 0 ≤ δ) {w : ℂ} (h1 : δ ≤ w.im) (h2 : w.im ≤ π - δ) :
    Real.exp w.re * Real.sin δ ≤ (cexp w).im := by
  rw [Complex.exp_im]
  exact mul_le_mul_of_nonneg_left (sin_ge_of_mem_Icc hδ h1 h2) (Real.exp_pos _).le

/-- **Sector Phragmén–Lindelöf.** Let `h` be entire of exponential type, and suppose that on the two
rays `arg z = δ` and `arg z = π − δ` (`z = e^w`, `Im w ∈ {δ, π − δ}`) it satisfies
`‖h z‖ ≤ B |z + i|^m e^{δ²|z|}`. Then on the sector `δ ≤ arg z ≤ π − δ`,
`‖h z‖ ≤ B |z + i|^m e^{(δ²/sin δ) Im z}`. -/
theorem norm_le_sector_of_rays {h : ℂ → ℂ} (hh : Differentiable ℂ h) {A τ B δ : ℝ} {m : ℕ}
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδ2 : δ < π / 2)
    (hgrow : ∀ z : ℂ, ‖h z‖ ≤ A * Real.exp (τ * ‖z‖))
    (hray : ∀ w : ℂ, (w.im = δ ∨ w.im = π - δ) →
      ‖h (cexp w)‖ ≤ B * ‖cexp w + I‖ ^ m * Real.exp (δ ^ 2 * ‖cexp w‖))
    {w : ℂ} (hw1 : δ ≤ w.im) (hw2 : w.im ≤ π - δ) :
    ‖h (cexp w)‖ ≤ B * ‖cexp w + I‖ ^ m * Real.exp (δ ^ 2 / Real.sin δ * (cexp w).im) := by
  have hsinδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  set β := δ ^ 2 / Real.sin δ with hβ
  have hβ0 : 0 ≤ β := by positivity
  set G : ℂ → ℂ := fun w => h (cexp w) * cexp (I * β * cexp w) / (cexp w + I) ^ m with hG
  -- `e^w + i` is nonzero with norm `≥ 1` on the closed strip
  have hnz : ∀ w : ℂ, δ ≤ w.im → w.im ≤ π - δ → 1 ≤ ‖cexp w + I‖ := by
    intro w h1 h2
    have him := im_exp_ge hδ.le h1 h2
    have hpos : 0 ≤ Real.exp w.re * Real.sin δ := by positivity
    have := Complex.abs_im_le_norm (cexp w + I)
    rw [Complex.add_im, Complex.I_im, abs_of_nonneg (by linarith)] at this
    linarith
  have hexpI : ∀ w : ℂ, ‖cexp (I * β * cexp w)‖ = Real.exp (-(β * (cexp w).im)) := by
    intro w
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  -- the key identity `‖G w‖ ‖e^w + i‖^m e^{β Im e^w} = ‖h(e^w)‖`
  have hGnorm : ∀ w : ℂ, δ ≤ w.im → w.im ≤ π - δ →
      ‖h (cexp w)‖ = ‖G w‖ * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im) := by
    intro w h1 h2
    have hn := hnz w h1 h2
    have hpow : 0 < ‖cexp w + I‖ ^ m := pow_pos (by linarith) m
    simp only [hG]
    rw [norm_div, norm_mul, norm_pow, hexpI]
    rw [div_mul_cancel₀ _ hpow.ne', mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      mul_one]
  -- differentiability on the closed strip
  have hdiff : DifferentiableOn ℂ G (closure (Complex.im ⁻¹' Set.Ioo δ (π - δ))) := by
    rw [Complex.closure_preimage_im, closure_Ioo (by linarith)]
    intro w hw
    have hn := hnz w hw.1 hw.2
    have hne : (cexp w + I) ^ m ≠ 0 := pow_ne_zero _ (by
      intro h0; rw [h0, norm_zero] at hn; linarith)
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun w : ℂ => h (cexp w) * cexp (I * β * cexp w)) w :=
      ((hh _).comp w (Complex.differentiableAt_exp)).mul
        ((differentiableAt_const _).mul Complex.differentiableAt_exp).cexp
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (cexp w + I) ^ m) w :=
      (Complex.differentiableAt_exp.add (differentiableAt_const _)).pow m
    exact h1.div h2 hne
  have hc : (1 : ℝ) < π / (π - δ - δ) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hGgrow : ∀ w : ℂ, w ∈ Complex.im ⁻¹' Set.Ioo δ (π - δ) →
      ‖G w‖ ≤ A * Real.exp (τ * Real.exp (1 * |w.re|)) := by
    intro w hw
    have h1 : δ ≤ w.im := hw.1.le
    have h2 : w.im ≤ π - δ := hw.2.le
    have hn := hnz w h1 h2
    have him := im_exp_ge hδ.le h1 h2
    have hpos : 0 ≤ β * (cexp w).im := mul_nonneg hβ0 (le_trans (by positivity) him)
    simp only [hG]
    rw [norm_div, norm_mul, norm_pow, hexpI]
    have hpow : 1 ≤ ‖cexp w + I‖ ^ m := one_le_pow₀ hn
    have hE : Real.exp (-(β * (cexp w).im)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hh1 := hgrow (cexp w)
    rw [Complex.norm_exp] at hh1
    have hre : Real.exp w.re ≤ Real.exp (1 * |w.re|) :=
      Real.exp_le_exp.mpr (by rw [one_mul]; exact le_abs_self _)
    have hhb : ‖h (cexp w)‖ ≤ A * Real.exp (τ * Real.exp (1 * |w.re|)) :=
      hh1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hre hτ)) hA)
    rw [div_le_iff₀ (by linarith)]
    calc ‖h (cexp w)‖ * Real.exp (-(β * (cexp w).im))
        ≤ A * Real.exp (τ * Real.exp (1 * |w.re|)) * 1 :=
          mul_le_mul hhb hE (Real.exp_pos _).le (by positivity)
      _ ≤ A * Real.exp (τ * Real.exp (1 * |w.re|)) * ‖cexp w + I‖ ^ m :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbound : ∀ w : ℂ, (w.im = δ ∨ w.im = π - δ) → ‖G w‖ ≤ B := by
    intro w hwi
    have h1 : δ ≤ w.im := by rcases hwi with h | h <;> linarith
    have h2 : w.im ≤ π - δ := by rcases hwi with h | h <;> linarith
    have hn := hnz w h1 h2
    have hpow : 0 < ‖cexp w + I‖ ^ m := pow_pos (by linarith) m
    have hr := hray w hwi
    have hid := hGnorm w h1 h2
    -- on the rays `Im e^w = |e^w| sin δ`, so `β Im e^w = δ² |e^w|`
    have hray_im : β * (cexp w).im = δ ^ 2 * ‖cexp w‖ := by
      rw [Complex.exp_im, Complex.norm_exp]
      have hs : Real.sin w.im = Real.sin δ := by
        rcases hwi with h | h
        · rw [h]
        · rw [h, Real.sin_pi_sub]
      rw [hs, hβ]; field_simp
    rw [hray_im] at hid
    have hEpos : 0 < Real.exp (δ ^ 2 * ‖cexp w‖) := Real.exp_pos _
    by_contra hcon
    push Not at hcon
    have : B * ‖cexp w + I‖ ^ m * Real.exp (δ ^ 2 * ‖cexp w‖) <
        ‖G w‖ * ‖cexp w + I‖ ^ m * Real.exp (δ ^ 2 * ‖cexp w‖) := by
      apply mul_lt_mul_of_pos_right _ hEpos
      exact mul_lt_mul_of_pos_right hcon hpow
    linarith
  have hPL := PhragmenLindelof.horizontal_strip (f := G) (a := δ) (b := π - δ) (C := B)
    hdiff.diffContOnCl
    ⟨1, hc, τ, Asymptotics.IsBigO.of_bound A (by
      filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with w hw
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hGgrow w hw)⟩
    (fun z hz => hbound z (Or.inl hz)) (fun z hz => hbound z (Or.inr hz)) hw1 hw2
  rw [hGnorm w hw1 hw2]
  have hpow : 0 ≤ ‖cexp w + I‖ ^ m := by positivity
  calc ‖G w‖ * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im)
      ≤ B * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right hPL hpow


/-! ## Rays, the limit `δ → 0`, and polynomial growth -/

theorem cos_ge_half {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : 1 / 2 ≤ Real.cos δ := by
  rw [← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi hδ (by linarith [Real.pi_gt_three])
    (by linarith [Real.pi_gt_three])

/-- `‖z‖ ≤ ‖z + i‖` and `1 ≤ ‖z + i‖` in the closed upper half-plane. -/
theorem norm_le_norm_add_I {z : ℂ} (hz : 0 ≤ z.im) : ‖z‖ ≤ ‖z + I‖ ∧ 1 ≤ ‖z + I‖ := by
  have h1 : ‖z + I‖ ^ 2 = ‖z‖ ^ 2 + (2 * z.im + 1) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp; ring
  have hsq : ‖z‖ ^ 2 ≤ ‖z + I‖ ^ 2 := by rw [h1]; linarith
  refine ⟨(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq, ?_⟩
  have : 1 ≤ ‖z + I‖ ^ 2 := by rw [h1]; nlinarith [norm_nonneg z]
  nlinarith [norm_nonneg (z + I)]

/-- The core estimate turning the right-region bound into a ray bound. -/
theorem ray_core {B₀ K σ t r δ N : ℝ} {m : ℕ} (hB₀ : 0 ≤ B₀) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hr : 0 ≤ r) (hσ : 2 ≤ σ) (hm : (K + 1) / 2 ≤ m) (hN : 1 ≤ N)
    (ht : |t| ≤ r * Real.sin δ) (hσr : r * Real.cos δ ≤ σ) (hσK : σ + K ≤ (2 + K) * N) :
    B₀ * (σ + K) ^ ((K + 1) / 2) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)) ≤
      3 * B₀ * (2 + K) ^ m * N ^ m * Real.exp (δ ^ 2 * r) := by
  have hcos := cos_ge_half hδ.le hδ1
  have hsin0 : 0 ≤ Real.sin δ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hδ.le (by linarith [Real.pi_gt_three])
  have hsinδ : Real.sin δ ≤ δ := Real.sin_le hδ.le
  have hsin1 : Real.sin δ ≤ 1 := Real.sin_le_one δ
  have hσ0 : 0 < σ := by linarith
  have hrσ : r ≤ 2 * σ := by nlinarith
  have ht2 : t ^ 2 ≤ r ^ 2 * δ ^ 2 := by
    have h1 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have h2 : |t| ≤ r * δ := ht.trans (mul_le_mul_of_nonneg_left hsinδ hr)
    rw [h1]; nlinarith [abs_nonneg t]
  have ht2' : t ^ 2 ≤ r ^ 2 := by
    have h1 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have h2 : |t| ≤ r := ht.trans (by nlinarith)
    rw [h1]; nlinarith [abs_nonneg t]
  -- the three factors
  have hpow : (σ + K) ^ ((K + 1) / 2) ≤ (2 + K) ^ m * N ^ m := by
    have hb : 1 ≤ σ + K := by linarith
    calc (σ + K) ^ ((K + 1) / 2) ≤ (σ + K) ^ (m : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb hm
      _ = (σ + K) ^ m := Real.rpow_natCast _ _
      _ ≤ ((2 + K) * N) ^ m := pow_le_pow_left₀ (by linarith) hσK m
      _ = (2 + K) ^ m * N ^ m := mul_pow _ _ _
  have hsq : Real.sqrt (1 + t ^ 2 / σ ^ 2) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have : t ^ 2 / σ ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hexp : t ^ 2 / (2 * σ) ≤ δ ^ 2 * r := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg δ, mul_nonneg hr (sq_nonneg δ)]
  have hP : 0 ≤ (2 + K) ^ m * N ^ m := by positivity
  calc B₀ * (σ + K) ^ ((K + 1) / 2) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ))
      ≤ B₀ * ((2 + K) ^ m * N ^ m) * 3 * Real.exp (δ ^ 2 * r) := by
        gcongr
    _ = 3 * B₀ * (2 + K) ^ m * N ^ m * Real.exp (δ ^ 2 * r) := by ring


/-- **Ray bounds.** From the right-region bounds for `h` and for `w ↦ h(1 − w)`, `h` satisfies
`‖h z‖ ≤ B |z + i|^m e^{δ²|z|}` on both rays `arg z = δ` and `arg z = π − δ`. -/
theorem ray_bound_of_right {h : ℂ → ℂ} {B₀ K A τ δ : ℝ} {m : ℕ} (hB₀ : 0 ≤ B₀) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : (K + 1) / 2 ≤ m)
    (hR : ∀ σ t : ℝ, 2 ≤ σ → ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      B₀ * (σ + K) ^ ((K + 1) / 2) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)))
    (hR' : ∀ σ t : ℝ, 2 ≤ σ → ‖h (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ≤
      B₀ * (σ + K) ^ ((K + 1) / 2) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)))
    (hgrow : ∀ z : ℂ, ‖h z‖ ≤ A * Real.exp (τ * ‖z‖)) :
    ∀ w : ℂ, (w.im = δ ∨ w.im = π - δ) →
      ‖h (cexp w)‖ ≤ (3 * B₀ * (2 + K) ^ m + A * Real.exp (4 * τ)) * ‖cexp w + I‖ ^ m *
        Real.exp (δ ^ 2 * ‖cexp w‖) := by
  intro w hw
  set z := cexp w with hz
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrexp : r = Real.exp w.re := by rw [hr, hz, Complex.norm_exp]
  have hzre : z.re = r * Real.cos w.im := by rw [hz, Complex.exp_re, hrexp]
  have hzim : z.im = r * Real.sin w.im := by rw [hz, Complex.exp_im, hrexp]
  have hcos := cos_ge_half hδ.le hδ1
  have hsin0 : 0 ≤ Real.sin δ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hδ.le (by linarith [Real.pi_gt_three])
  have hsinw : Real.sin w.im = Real.sin δ := by
    rcases hw with h | h
    · rw [h]
    · rw [h, Real.sin_pi_sub]
  have hzim' : z.im = r * Real.sin δ := by rw [hzim, hsinw]
  have hzimnn : 0 ≤ z.im := by rw [hzim']; positivity
  obtain ⟨hNr, hN1⟩ := norm_le_norm_add_I hzimnn
  set N := ‖z + I‖ with hN
  have hNm : 1 ≤ N ^ m := one_le_pow₀ hN1
  have hE1 : 1 ≤ Real.exp (δ ^ 2 * r) := Real.one_le_exp (by positivity)
  have hBc : 3 * B₀ * (2 + K) ^ m ≤ 3 * B₀ * (2 + K) ^ m + A * Real.exp (4 * τ) := by
    have : 0 ≤ A * Real.exp (4 * τ) := by positivity
    linarith
  have hBc' : A * Real.exp (4 * τ) ≤ 3 * B₀ * (2 + K) ^ m + A * Real.exp (4 * τ) := by
    have : 0 ≤ 3 * B₀ * (2 + K) ^ m := by positivity
    linarith
  -- the global bound handles small `r`
  have hsmall : r ≤ 4 → ‖h z‖ ≤ (3 * B₀ * (2 + K) ^ m + A * Real.exp (4 * τ)) * N ^ m *
      Real.exp (δ ^ 2 * r) := by
    intro hr4
    have hg := hgrow z
    rw [← hr] at hg
    have h1 : A * Real.exp (τ * r) ≤ A * Real.exp (4 * τ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hA
    calc ‖h z‖ ≤ A * Real.exp (4 * τ) := hg.trans h1
      _ ≤ (3 * B₀ * (2 + K) ^ m + A * Real.exp (4 * τ)) * 1 * 1 := by rw [mul_one, mul_one]; exact hBc'
      _ ≤ _ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hNm (by positivity)) hE1 zero_le_one
          positivity
  rcases hw with hwδ | hwδ
  · -- right ray
    have hzre' : z.re = r * Real.cos δ := by rw [hzre, hwδ]
    by_cases h2 : 2 ≤ z.re
    · have hzeq : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
      have hb := hR z.re z.im h2
      rw [← hzeq] at hb
      have hcore := ray_core (N := N) (m := m) (t := z.im) hB₀ hK hδ hδ1 hr0 h2 hm hN1
        (by rw [hzim', abs_of_nonneg (by positivity)]) (by rw [hzre']) (by
          have : r * Real.cos δ ≤ r := by nlinarith [Real.cos_le_one δ]
          nlinarith)
      calc ‖h z‖ ≤ _ := hb
        _ ≤ 3 * B₀ * (2 + K) ^ m * N ^ m * Real.exp (δ ^ 2 * r) := hcore
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right hBc (by positivity)
    · push Not at h2
      exact hsmall (by rw [hzre'] at h2; nlinarith)
  · -- left ray, through `w ↦ h(1 − w)`
    have hcosw : Real.cos w.im = -Real.cos δ := by rw [hwδ, Real.cos_pi_sub]
    have hzre' : z.re = -(r * Real.cos δ) := by rw [hzre, hcosw]; ring
    by_cases h2 : 2 ≤ 1 - z.re
    · have hzeq : 1 - ((((1 - z.re) : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I) = z := by
        conv_rhs => rw [← Complex.re_add_im z]
        push_cast; ring
      have hb := hR' (1 - z.re) (-z.im) h2
      rw [hzeq] at hb
      have hcore := ray_core (N := N) (m := m) (t := -z.im) hB₀ hK hδ hδ1 hr0 h2 hm hN1
        (by rw [abs_neg, hzim', abs_of_nonneg (by positivity)]) (by rw [hzre']; linarith)
        (by
          have : r * Real.cos δ ≤ r := by nlinarith [Real.cos_le_one δ]
          rw [hzre']; nlinarith)
      calc ‖h z‖ ≤ _ := hb
        _ ≤ 3 * B₀ * (2 + K) ^ m * N ^ m * Real.exp (δ ^ 2 * r) := hcore
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right hBc (by positivity)
    · push Not at h2
      exact hsmall (by rw [hzre'] at h2; nlinarith)

/-- `δ²/sin δ ≤ (π/2) δ` on `(0, 1]`. -/
theorem sq_div_sin_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : δ ^ 2 / Real.sin δ ≤ π / 2 * δ := by
  have hs := Real.mul_le_sin hδ.le (by linarith [Real.pi_gt_three])
  have hspos : 0 < Real.sin δ := by
    have : 0 < 2 / π * δ := by positivity
    linarith
  rw [div_le_iff₀ hspos]
  have e : π / 2 * δ * (2 / π * δ) = δ ^ 2 := by field_simp
  have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ π / 2 * δ)
  linarith

/-- **Polynomial growth in the closed upper half-plane.** Letting `δ → 0` in the sector bound. -/
theorem norm_le_upper_half_plane {h : ℂ → ℂ} (hh : Differentiable ℂ h) {B₀ K A τ : ℝ} {m : ℕ}
    (hB₀ : 0 ≤ B₀) (hK : 0 ≤ K) (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hm : (K + 1) / 2 ≤ m)
    (hR : ∀ σ t : ℝ, 2 ≤ σ → ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      B₀ * (σ + K) ^ ((K + 1) / 2) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)))
    (hR' : ∀ σ t : ℝ, 2 ≤ σ → ‖h (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ≤
      B₀ * (σ + K) ^ ((K + 1) / 2) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)))
    (hgrow : ∀ z : ℂ, ‖h z‖ ≤ A * Real.exp (τ * ‖z‖)) :
    ∀ z : ℂ, 0 ≤ z.im →
      ‖h z‖ ≤ (3 * B₀ * (2 + K) ^ m + A * Real.exp (4 * τ)) * ‖z + I‖ ^ m := by
  set B := 3 * B₀ * (2 + K) ^ m + A * Real.exp (4 * τ) with hB
  have hBnn : 0 ≤ B := by positivity
  -- open upper half-plane
  have hopen : ∀ z : ℂ, 0 < z.im → ‖h z‖ ≤ B * ‖z + I‖ ^ m := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
    set a := z.arg with ha
    have hsa : 0 < Real.sin a := by
      rw [ha, Complex.sin_arg]; exact div_pos hz (norm_pos_iff.mpr hz0)
    have ha0 : 0 < a := by
      refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) (fun h0 => ?_)
      rw [← h0, Real.sin_zero] at hsa; linarith
    have haπ : a < π := by
      rcases lt_or_ge a π with h | h
      · exact h
      · exfalso
        have hle := Complex.arg_le_pi z
        have : a = π := le_antisymm hle h
        rw [this, Real.sin_pi] at hsa; linarith
    -- for every small `δ` the sector bound holds at `z`
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ‖h z‖ ≤ B * ‖z + I‖ ^ m * Real.exp (π / 2 * δ * z.im) := by
      have hpos : 0 < min (min a (π - a)) 1 := lt_min (lt_min ha0 (by linarith)) one_pos
      filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
      have hδ0 : 0 < δ := hδ.1
      have hδa : δ < a := lt_of_lt_of_le hδ.2 ((min_le_left _ _).trans (min_le_left _ _))
      have hδπ : δ < π - a := lt_of_lt_of_le hδ.2 ((min_le_left _ _).trans (min_le_right _ _))
      have hδ1 : δ ≤ 1 := (lt_of_lt_of_le hδ.2 (min_le_right _ _)).le
      have hδ2 : δ < π / 2 := by linarith [Real.pi_gt_three]
      have hrays := ray_bound_of_right hB₀ hK hA hτ hδ0 hδ1 hm hR hR' hgrow
      have hsec := norm_le_sector_of_rays (w := Complex.log z) hh hA hτ hδ0 hδ2 hgrow hrays
        (by rw [Complex.log_im]; linarith) (by rw [Complex.log_im]; linarith)
      rw [Complex.exp_log hz0] at hsec
      have hβ := sq_div_sin_le hδ0 hδ1
      calc ‖h z‖ ≤ _ := hsec
        _ ≤ B * ‖z + I‖ ^ m * Real.exp (π / 2 * δ * z.im) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ hz.le)
    have hlim : Tendsto (fun δ : ℝ => B * ‖z + I‖ ^ m * Real.exp (π / 2 * δ * z.im))
        (𝓝[>] (0 : ℝ)) (𝓝 (B * ‖z + I‖ ^ m)) := by
      have hc : Continuous fun δ : ℝ => B * ‖z + I‖ ^ m * Real.exp (π / 2 * δ * z.im) := by
        fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact ge_of_tendsto hlim hev
  intro z hz
  rcases hz.lt_or_eq with hz | hz
  · exact hopen z hz
  -- the real axis, by continuity
  have hseq : Tendsto (fun n : ℕ => z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 z) := by
    have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).mul_const I
    simpa using (tendsto_const_nhds (x := z)).add h2
  have hcont : Continuous fun w : ℂ => B * ‖w + I‖ ^ m - ‖h w‖ := by
    have := hh.continuous; fun_prop
  have hge : ∀ n : ℕ, 0 ≤ B * ‖(z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) + I‖ ^ m -
      ‖h (z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)‖ := by
    intro n
    have him : 0 < (z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I).im := by
      have e : (z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I).im = z.im + 1 / ((n : ℝ) + 1) := by
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      rw [e, ← hz]
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    linarith [hopen _ him]
  have hlim := (hcont.tendsto z).comp hseq
  have := ge_of_tendsto hlim (Eventually.of_forall hge)
  linarith


/-! ## The Hardy equality case -/

/-- Theta-rate decay implies rate-`π/2` decay, the input of the exponential-type machinery. -/
theorem decay_half_of_theta {F : ℝ → ℂ} {C k : ℝ} (hk : 0 ≤ k)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - π * Real.exp (2 * |x|))) :
    ∀ x, ‖F x‖ ≤ C * Real.exp (legendreMajorant (π / 2) k) *
      Real.exp (-(π / 2 * Real.exp (2 * |x|))) := by
  have hC : 0 ≤ C := by
    have h1 := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (k * |(0 : ℝ)| - π * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  intro x
  have hleg := le_legendreMajorant (c := π / 2) (by positivity) hk |x|
  refine (hF x).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  linarith

/-- Upper half-plane polynomial growth for the quotient of any theta-rate `F`. -/
theorem exists_upper_half_plane_bound {F : ℝ → ℂ} {C k : ℝ} (hk : 0 ≤ k)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - π * Real.exp (2 * |x|)))
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (hdiv : ∀ s, centredLaplace F s = xi s * h s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 0 ≤ z.im →
      ‖h z‖ ≤ B * ‖z + I‖ ^ (⌈(k + 1 / 2 + 1) / 2⌉₊) := by
  have hC : 0 ≤ C := by
    have h1 := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (k * |(0 : ℝ)| - π * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  obtain ⟨A, τ, hA, hτ, hgrow⟩ := exists_quotient_exponential_type (c := π / 2) (δ := π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (decay_half_of_theta hk hF) hh hdiv
  set J := ∫ x : ℝ, Real.exp (-|x|) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  set B₀ := 3 * (C * J) * Real.exp π with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  set K := k + 1 / 2 with hK
  have hK0 : 0 ≤ K := by linarith
  have hR : ∀ σ t : ℝ, 2 ≤ σ → ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      B₀ * (σ + K) ^ ((K + 1) / 2) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)) := by
    intro σ t hσ
    have := norm_quotient_le_theta_right hk hF (fun s _ => hdiv s) (t := t) hσ
    calc ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤ _ := this
      _ = _ := by rw [hB₀, hK]; ring
  have hFrefl : ∀ x, ‖(fun y => F (-y)) x‖ ≤ C * Real.exp (k * |x| - π * Real.exp (2 * |x|)) := by
    intro x; simpa [abs_neg] using hF (-x)
  have hR' : ∀ σ t : ℝ, 2 ≤ σ → ‖h (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ≤
      B₀ * (σ + K) ^ ((K + 1) / 2) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (t ^ 2 / (2 * σ)) := by
    intro σ t hσ
    have := norm_quotient_le_theta_right (h := fun w => h (1 - w)) hk hFrefl
      (fun w _ => centredLaplace_reflect_eq hdiv w) (t := t) hσ
    calc ‖h (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ≤ _ := this
      _ = _ := by rw [hB₀, hK]; ring
  have hm : (K + 1) / 2 ≤ (⌈(k + 1 / 2 + 1) / 2⌉₊ : ℝ) := by rw [hK]; exact Nat.le_ceil _
  exact ⟨_, by positivity, norm_le_upper_half_plane hh hB₀0 hK0 hA hτ hm hR hR' hgrow⟩

/-- Complex conjugation of `F` conjugates the transform: `M_{F̄}(s) = conj M_F(s̄)`. -/
theorem centredLaplace_conj (F : ℝ → ℂ) (s : ℂ) :
    centredLaplace (fun x => (starRingEnd ℂ) (F x)) s =
      (starRingEnd ℂ) (centredLaplace F ((starRingEnd ℂ) s)) := by
  unfold centredLaplace
  rw [← integral_conj]
  congr 1; funext x
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp [map_sub, map_mul, Complex.conj_ofReal, map_ofNat]

/-- **Hardy equality case for `ξ` (theta rigidity).** If `|F(x)| ≤ C e^{k|x|} exp(−π e^{2|x|})`
and the centred Laplace transform `M_F` is divisible by `ξ` among entire functions, then the
quotient is a polynomial: `M_F = P · ξ`.

At the theta rate the quotient has polynomial size on the real axis and grows at most like
`exp(t²/(2σ))` near it (exact imaginary-shift bound for `Γ`). This growth is quadratic in the
angle, so a sector Phragmén–Lindelöf argument with vanishing opening loss gives polynomial growth
in each half-plane. -/
theorem theta_rigidity_polynomial_quotient {F : ℝ → ℂ} {C k : ℝ} (hk : 0 ≤ k)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - π * Real.exp (2 * |x|)))
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (hdiv : ∀ s, centredLaplace F s = xi s * h s) :
    ∃ P : Polynomial ℂ, ∀ s, h s = P.eval s := by
  set m := ⌈(k + 1 / 2 + 1) / 2⌉₊ with hm
  obtain ⟨B, hB, hup⟩ := exists_upper_half_plane_bound hk hF hh hdiv
  -- the conjugate problem
  set F' : ℝ → ℂ := fun x => (starRingEnd ℂ) (F x) with hF'
  set h' : ℂ → ℂ := fun s => (starRingEnd ℂ) (h ((starRingEnd ℂ) s)) with hh'
  have hF'd : ∀ x, ‖F' x‖ ≤ C * Real.exp (k * |x| - π * Real.exp (2 * |x|)) := by
    intro x; rw [hF', Complex.norm_conj]; exact hF x
  have hh'd : Differentiable ℂ h' := by
    intro s
    have := (hh ((starRingEnd ℂ) s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hdiv' : ∀ s, centredLaplace F' s = xi s * h' s := by
    intro s
    rw [hF', centredLaplace_conj, hdiv, map_mul, xi_conj, Complex.conj_conj]
  obtain ⟨B', hB', hup'⟩ := exists_upper_half_plane_bound hk hF'd hh'd hdiv'
  refine exists_polynomial_of_polyGrowth hh (M := max B B') (d := m) fun z => ?_
  have hmax : 0 ≤ max B B' := le_trans hB (le_max_left _ _)
  rcases le_total 0 z.im with hz | hz
  · have h1 := hup z hz
    have h2 : ‖z + I‖ ≤ ‖z‖ + 1 := by
      have := norm_add_le z I; rwa [Complex.norm_I] at this
    calc ‖h z‖ ≤ B * ‖z + I‖ ^ m := h1
      _ ≤ max B B' * (‖z‖ + 1) ^ m :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (norm_nonneg _) h2 m)
            (by positivity) hmax
  · have hzc : 0 ≤ ((starRingEnd ℂ) z).im := by simp; linarith
    have h1 := hup' ((starRingEnd ℂ) z) hzc
    have e : h' ((starRingEnd ℂ) z) = (starRingEnd ℂ) (h z) := by
      rw [hh']; simp only [Complex.conj_conj]
    rw [e, Complex.norm_conj] at h1
    have h2 : ‖(starRingEnd ℂ) z + I‖ ≤ ‖z‖ + 1 := by
      have := norm_add_le ((starRingEnd ℂ) z) I
      rwa [Complex.norm_I, Complex.norm_conj] at this
    calc ‖h z‖ ≤ B' * ‖(starRingEnd ℂ) z + I‖ ^ m := h1
      _ ≤ max B B' * (‖z‖ + 1) ^ m :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (norm_nonneg _) h2 m)
            (by positivity) hmax


open Bottcher Zeta23 in
/-- Riemann's kernel attains the theta rate: `|Φ(x)| ≤ C e^{9|x|/2} exp(−π e^{2|x|})`. So the Hardy
equality case is not vacuous: `Φ` realizes the quotient `P = 1`. -/
theorem riemannPhiKernel_theta_rate :
    ∃ C : ℝ, ∀ x : ℝ, ‖riemannPhiKernel x‖ ≤
      C * Real.exp (9 / 2 * |x| - π * Real.exp (2 * |x|)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_norm_riemannPhiKernel_le_exp (B := 0) le_rfl
  have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
  refine ⟨C₀ * Real.exp (3 * π) + 20 * jacobiThetaTailConstant * Real.exp π, fun x => ?_⟩
  have hsym : ‖riemannPhiKernel x‖ = ‖riemannPhiKernel |x|‖ := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, riemannPhiKernel_neg]
  set u := Real.exp (2 * |x|) with hu
  have hu1 : 1 ≤ u := Real.one_le_exp (by positivity)
  have hE : 0 < Real.exp (9 / 2 * |x| - π * u) := Real.exp_pos _
  have hpos2 : 0 ≤ 20 * jacobiThetaTailConstant * Real.exp π := by positivity
  rcases lt_or_ge u 3 with hu3 | hu3
  · have h1 := hb x
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at h1
    have h2 : 1 ≤ Real.exp (3 * π) * Real.exp (9 / 2 * |x| - π * u) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [abs_nonneg x, Real.pi_pos])
    calc ‖riemannPhiKernel x‖ ≤ C₀ := h1
      _ ≤ C₀ * (Real.exp (3 * π) * Real.exp (9 / 2 * |x| - π * u)) := by nlinarith
      _ ≤ _ := by nlinarith
  · have h1 := norm_riemannPhiKernel_le (x := |x|) hu3
    rw [← hsym] at h1
    have hfac : Real.exp (|x| / 2) * (3 * u + 2 * u ^ 2) ≤ 5 * Real.exp (9 / 2 * |x|) := by
      have hu2 : u ^ 2 = Real.exp (4 * |x|) := by rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
      have h3 : 3 * u + 2 * u ^ 2 ≤ 5 * u ^ 2 := by nlinarith
      calc Real.exp (|x| / 2) * (3 * u + 2 * u ^ 2) ≤ Real.exp (|x| / 2) * (5 * u ^ 2) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = 5 * Real.exp (9 / 2 * |x|) := by rw [hu2, mul_left_comm, ← Real.exp_add]; ring_nf
    calc ‖riemannPhiKernel x‖
        ≤ 4 * jacobiThetaTailConstant * Real.exp π * Real.exp (|x| / 2) * (3 * u + 2 * u ^ 2) *
            Real.exp (-π * u) := h1
      _ = 4 * jacobiThetaTailConstant * Real.exp π * (Real.exp (|x| / 2) * (3 * u + 2 * u ^ 2)) *
            Real.exp (-π * u) := by ring
      _ ≤ 4 * jacobiThetaTailConstant * Real.exp π * (5 * Real.exp (9 / 2 * |x|)) *
            Real.exp (-π * u) := by gcongr
      _ = 20 * jacobiThetaTailConstant * Real.exp π * Real.exp (9 / 2 * |x| - π * u) := by
          rw [show 9 / 2 * |x| - π * u = 9 / 2 * |x| + -π * u by ring, Real.exp_add]; ring
      _ ≤ _ := by
          have : 0 ≤ C₀ * Real.exp (3 * π) := by positivity
          nlinarith


end

end RHTower
