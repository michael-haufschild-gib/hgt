import GaloisForLFunctions.RHTower.ThetaRigidityHardyEqualityCase

/-!
# The theta-window law for `ξ`-divisible transforms

Let `M_F(s) = ∫ F(x) e^{(s−½)x} dx`. A function decaying at rate `c`,
`|F(x)| ≤ C e^{k|x|} exp(−c e^{2|x|})`, whose transform is divisible by `ξ`, `M_F = ξ · h`, has a
quotient of controlled growth in every direction (`theta_window_directional_law`): on `Re s ≥ 2`,

`|h(σ+it)| ≲ exp((σ/2) log(π/c) + ½|t| arctan(|t|/σ) − (σ/4) log(1+t²/σ²))`.

In polar coordinates `s = re^{iφ}` the exponent is `r J_c(φ)`,
`J_c(φ) = ½[cos φ · log(π cos φ / c) + φ sin φ]`.

Compare with the **theta window** `D_c = {v + iθ : π e^{−2|v|} cos 2θ ≥ c}`:
* every `w = v + iθ ∈ D_c` satisfies `vσ − θt ≤` the exponent (`theta_window_le`, a tangent-line
  inequality for `cos`), so `J_c` dominates the support function of `D_c` in every direction;
* in each direction with `c ≤ π cos φ` equality holds at `θ = −φ/2`, `v = ½ log(π cos φ/c)`
  (`theta_window_attained`), so there `J_c` is exactly the support function.

In the steep directions `π cos φ < c` the window's support function is `½ arccos(c/π) sin φ`,
which is smaller than `J_c(φ)`; whether the law can be sharpened there is not decided here.

The complex shift `Φ(· − w)` of Riemann's kernel has transform `e^{w(s−½)} ξ` and decay rate
`π e^{−2|Re w|} cos(2 Im w)`. So the window describes exactly the shifts of `Φ` that remain at rate
`c`. Along the real axis the law is attained by the real shift `Φ(· − ½ log(π/c))`
(`theta_window_real_axis_attained`). The endpoints are `D_π = {0}` (Hardy equality case,
`theta_rigidity_polynomial_quotient`) and `D_c = ∅` for `c > π`
(`ae_eq_zero_of_centredLaplace_xi_dvd`).

The exponent is exact. The imaginary-shift integral of `Γ` equals
`|t| arctan(|t|/σ) − (σ/2) log(1+t²/σ²)` at `(σ/2, t/2)` (`gammaShiftIntegral_half_eq`). Against
the rate-`c` Legendre transform this leaves exactly `(σ/2) log(π/c)`
(`legendre_rate_div_Gamma_le`).
-/

open Complex Filter Topology MeasureTheory
open scoped Real

namespace RHTower

noncomputable section

/-! ## The window inequality -/

/-- Tangent line of the concave cosine: `cos α ≤ cos φ + (φ − α) sin φ` on `[0, π/2]`. -/
theorem cos_le_tangent {α φ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ π / 2) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) :
    Real.cos α ≤ Real.cos φ + (φ - α) * Real.sin φ := by
  have hconc := strictConcaveOn_cos_Icc.concaveOn
  have hαS : α ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith [Real.pi_pos], hα1⟩
  have hφS : φ ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith [Real.pi_pos], hφ1⟩
  rcases lt_trichotomy α φ with h | h | h
  · have hs := hconc.le_slope_of_hasDerivAt hαS hφS h (Real.hasDerivAt_cos φ)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at hs
    nlinarith
  · subst h; linarith
  · have hs := hconc.slope_le_of_hasDerivAt hφS hαS h (Real.hasDerivAt_cos φ)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at hs
    nlinarith

/-- `log(1 + t²/σ²) = −2 log cos(arctan(|t|/σ))`. -/
theorem log_one_add_sq_div_eq {σ t : ℝ} (hσ : 0 < σ) :
    Real.log (1 + t ^ 2 / σ ^ 2) = -2 * Real.log (Real.cos (Real.arctan (|t| / σ))) := by
  rw [Real.cos_arctan, div_pow, sq_abs, Real.log_div one_ne_zero (by positivity), Real.log_one,
    Real.log_sqrt (by positivity)]
  ring

/-- **The theta window dominates.** If `w = v + iθ` lies in the window
`c ≤ π e^{−2|v|} cos 2θ`, `|θ| < π/4`, then for `σ > 0`
`vσ − θt ≤ (σ/2) log(π/c) + ½|t| arctan(|t|/σ) − (σ/4) log(1 + t²/σ²)`: the exponential
`e^{w(s−½)}` is dominated by the directional law at `s = σ + it`. -/
theorem theta_window_le {c σ t v θ : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hθ : |θ| < π / 4)
    (hw : c ≤ π * Real.exp (-(2 * |v|)) * Real.cos (2 * θ)) :
    v * σ - θ * t ≤ σ / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ) -
      σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2) := by
  set φ := Real.arctan (|t| / σ) with hφ
  set α := 2 * |θ| with hα
  have hα0 : 0 ≤ α := by positivity
  have hα1 : α < π / 2 := by rw [hα]; linarith
  have hφ0 : 0 ≤ φ := Real.arctan_nonneg.mpr (by positivity)
  have hφ1 : φ < π / 2 := Real.arctan_lt_pi_div_two _
  have hcos2θ : Real.cos (2 * θ) = Real.cos α := by
    rw [hα]; rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, show 2 * -θ = -(2 * θ) by ring, Real.cos_neg]
  have hcosα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα1⟩
  have hcosφ : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ1⟩
  rw [hcos2θ] at hw
  -- `|v| ≤ ½ log(π cos α / c)`
  have hv : |v| ≤ (Real.log (π / c) + Real.log (Real.cos α)) / 2 := by
    have h1 : c / (π * Real.cos α) ≤ Real.exp (-(2 * |v|)) := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_exp, Real.log_div hc.ne' (by positivity), Real.log_mul Real.pi_pos.ne'
      hcosα.ne'] at h2
    rw [Real.log_div Real.pi_pos.ne' hc.ne']
    linarith
  have hvσ : v * σ ≤ σ / 2 * (Real.log (π / c) + Real.log (Real.cos α)) := by
    have := mul_le_mul_of_nonneg_right ((le_abs_self v).trans hv) hσ.le
    linarith
  have hθt : -(θ * t) ≤ α / 2 * |t| := by
    have := neg_abs_le (θ * t); rw [abs_mul] at this; rw [hα]; linarith
  -- the key step: `(σ/2) log(cos α / cos φ) ≤ (|t|/2)(φ − α)`
  have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.cos α / Real.cos φ by positivity)
  rw [Real.log_div hcosα.ne' hcosφ.ne'] at hlog
  have htan := cos_le_tangent hα0 hα1.le hφ0 hφ1.le
  -- `σ / cos φ = r` and `|t| = r sin φ`
  have hr : σ * Real.sin φ = |t| * Real.cos φ := by
    rw [hφ, Real.sin_arctan, Real.cos_arctan]
    field_simp
  have hkey : σ * (Real.log (Real.cos α) - Real.log (Real.cos φ)) ≤ |t| * (φ - α) := by
    have h1 : σ * (Real.log (Real.cos α) - Real.log (Real.cos φ)) ≤
        σ * (Real.cos α / Real.cos φ - 1) := mul_le_mul_of_nonneg_left hlog hσ.le
    have h2 : σ * (Real.cos α / Real.cos φ - 1) * Real.cos φ = σ * (Real.cos α - Real.cos φ) := by
      field_simp
    have h3 : σ * (Real.cos α - Real.cos φ) ≤ σ * ((φ - α) * Real.sin φ) :=
      mul_le_mul_of_nonneg_left (by linarith) hσ.le
    have h4 : σ * ((φ - α) * Real.sin φ) = |t| * (φ - α) * Real.cos φ := by
      rw [show σ * ((φ - α) * Real.sin φ) = (σ * Real.sin φ) * (φ - α) by ring, hr]; ring
    have h5 : σ * (Real.cos α / Real.cos φ - 1) ≤ |t| * (φ - α) := by
      have := h2 ▸ h3.trans h4.le
      nlinarith
    linarith
  have hlog1 := log_one_add_sq_div_eq (t := t) hσ
  rw [← hφ] at hlog1
  rw [hlog1]
  nlinarith

/-- **The window is attained.** In every direction with `c ≤ π cos φ`, `φ = arctan(t/σ)`, `t ≥ 0`,
the shift `v = ½ log(π cos φ/c)`, `θ = −φ/2` lies on the boundary of the window and realizes the
directional exponent exactly. -/
theorem theta_window_attained {c σ t : ℝ} (hc : 0 < c) (hσ : 0 < σ) (ht : 0 ≤ t)
    (hdir : c ≤ π * Real.cos (Real.arctan (t / σ))) :
    let φ := Real.arctan (t / σ)
    let v := Real.log (π * Real.cos φ / c) / 2
    let θ := -(φ / 2)
    |θ| < π / 4 ∧ c = π * Real.exp (-(2 * |v|)) * Real.cos (2 * θ) ∧
      v * σ - θ * t = σ / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ) -
        σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2) := by
  intro φ v θ
  have hφ0 : 0 ≤ φ := Real.arctan_nonneg.mpr (by positivity)
  have hφ1 : φ < π / 2 := Real.arctan_lt_pi_div_two _
  have hcosφ : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ1⟩
  have hq : 1 ≤ π * Real.cos φ / c := by rw [le_div_iff₀ hc]; linarith
  have hv0 : 0 ≤ v := by
    show 0 ≤ Real.log (π * Real.cos φ / c) / 2
    have := Real.log_nonneg hq; linarith
  have habs_t : |t| = t := abs_of_nonneg ht
  refine ⟨?_, ?_, ?_⟩
  · show |-(φ / 2)| < π / 4
    rw [abs_neg, abs_of_nonneg (by positivity)]; linarith
  · show c = π * Real.exp (-(2 * |v|)) * Real.cos (2 * -(φ / 2))
    rw [abs_of_nonneg hv0, show 2 * -(φ / 2) = -φ by ring, Real.cos_neg]
    have he : Real.exp (-(2 * v)) = c / (π * Real.cos φ) := by
      show Real.exp (-(2 * (Real.log (π * Real.cos φ / c) / 2))) = c / (π * Real.cos φ)
      rw [show -(2 * (Real.log (π * Real.cos φ / c) / 2)) = -Real.log (π * Real.cos φ / c) by ring,
        Real.exp_neg, Real.exp_log (by positivity), inv_div]
    rw [he]; field_simp
  · show Real.log (π * Real.cos φ / c) / 2 * σ - -(φ / 2) * t =
      σ / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ) - σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2)
    have hlog1 := log_one_add_sq_div_eq (t := t) hσ
    rw [habs_t] at hlog1 ⊢
    rw [hlog1, Real.log_div (by positivity) hc.ne', Real.log_mul Real.pi_pos.ne' hcosφ.ne',
      Real.log_div Real.pi_pos.ne' hc.ne']
    ring

/-! ## The directional law -/

/-- The imaginary-shift integral in coordinates:
`I(σ/2, t/2) = |t| arctan(|t|/σ) − (σ/2) log(1 + t²/σ²)`. -/
theorem gammaShiftIntegral_half_eq {σ t : ℝ} (hσ : 0 < σ) :
    HTGeometry.gammaShiftIntegral (σ / 2) (t / 2) =
      |t| * Real.arctan (|t| / σ) - σ / 2 * Real.log (1 + t ^ 2 / σ ^ 2) := by
  unfold HTGeometry.gammaShiftIntegral HTGeometry.gammaShiftPrimitive
  have e1 : (t / 2) ^ 2 / (σ / 2) ^ 2 = t ^ 2 / σ ^ 2 := by field_simp
  rw [e1]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hT : 0 < |t / 2| := abs_pos.mpr (by positivity)
  have harc : Real.arctan (σ / 2 / |t / 2|) = π / 2 - Real.arctan (|t| / σ) := by
    rw [← Real.arctan_inv_of_pos (by positivity : 0 < |t| / σ)]
    congr 1
    rw [abs_div, abs_two]; field_simp
  rw [harc, abs_div, abs_two]
  ring

/-- Rate-`c` growth of `M_F` with prefactor `e^{k|x|}`. -/
theorem norm_centredLaplace_le_rate {F : ℝ → ℂ} {C k c : ℝ} (hc : 0 < c)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - c * Real.exp (2 * |x|))) (hk : 0 ≤ k) (s : ℂ) :
    ‖centredLaplace F s‖ ≤
      C * Real.exp (legendreMajorant c (|s.re - 1 / 2| + k + 1)) * ∫ x : ℝ, Real.exp (-|x|) := by
  have hC : 0 ≤ C := by
    have h1 := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (k * |(0 : ℝ)| - c * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  set G := legendreMajorant c (|s.re - 1 / 2| + k + 1) with hG
  have hpt : ∀ x : ℝ, ‖cexp ((s - 1 / 2) * x) * F x‖ ≤ C * Real.exp G * Real.exp (-|x|) := by
    intro x
    rw [norm_mul, Complex.norm_exp]
    have hre : ((s - 1 / 2) * (x : ℂ)).re = (s.re - 1 / 2) * x := by simp
    rw [hre]
    have hlin : (s.re - 1 / 2) * x ≤ |s.re - 1 / 2| * |x| := by
      calc (s.re - 1 / 2) * x ≤ |(s.re - 1 / 2) * x| := le_abs_self _
        _ = |s.re - 1 / 2| * |x| := abs_mul _ _
    have hleg := le_legendreMajorant (c := c) hc (by positivity : 0 ≤ |s.re - 1 / 2| + k + 1) |x|
    have hexp : (s.re - 1 / 2) * x + (k * |x| - c * Real.exp (2 * |x|)) ≤ G + -|x| := by
      rw [hG]; nlinarith
    calc Real.exp ((s.re - 1 / 2) * x) * ‖F x‖
        ≤ Real.exp ((s.re - 1 / 2) * x) * (C * Real.exp (k * |x| - c * Real.exp (2 * |x|))) :=
          mul_le_mul_of_nonneg_left (hF x) (Real.exp_pos _).le
      _ = C * Real.exp ((s.re - 1 / 2) * x + (k * |x| - c * Real.exp (2 * |x|))) := by
          rw [Real.exp_add]; ring
      _ ≤ C * Real.exp (G + -|x|) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
      _ = C * Real.exp G * Real.exp (-|x|) := by rw [Real.exp_add]; ring
  have hint : Integrable fun x : ℝ => C * Real.exp G * Real.exp (-|x|) :=
    integrable_exp_neg_abs.const_mul _
  unfold centredLaplace
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_const_mul]

/-- Rate-`c` Legendre majorant against `Γ(σ/2)`:
`e^{G} π^{σ/2}/Γ(σ/2) ≤ exp(c + ((K+1)/2) log(σ+K) + ((σ+K)/2) log(π/c))`. -/
theorem legendre_rate_div_Gamma_le {c k σ : ℝ} (hc : 0 < c) (hk : 0 ≤ k) (hσ : 2 ≤ σ) :
    Real.exp (legendreMajorant c (σ - 1 / 2 + k + 1)) * Real.pi ^ (σ / 2) / Real.Gamma (σ / 2) ≤
      Real.exp (c + (k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2)) +
        (σ + (k + 1 / 2)) / 2 * Real.log (π / c)) := by
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
  set Lc := Real.log c
  have hL2 : 0 ≤ L2 := Real.log_nonneg (by norm_num)
  have hLπ : 0 ≤ Lπ := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog2π : Real.log (2 * π) = L2 + Lπ := Real.log_mul (by norm_num) Real.pi_pos.ne'
  have hlogσ2 : Real.log (σ / 2) = Lσ - L2 := Real.log_div hσ0.ne' (by norm_num)
  have hlogy2c : Real.log (y / (2 * c)) = Ly - (L2 + Lc) := by
    rw [Real.log_div hy0.ne' (by positivity), Real.log_mul (by norm_num) hc.ne']
  have hlogπc : Real.log (π / c) = Lπ - Lc := Real.log_div Real.pi_pos.ne' hc.ne'
  have hE : -c ≤ y / 2 * (Real.log (y / (2 * c)) - 1) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < y / (2 * c) by positivity)
    have hinv : (y / (2 * c))⁻¹ = 2 * c / y := by rw [inv_div]
    rw [hinv] at h
    have : y / 2 * (Real.log (y / (2 * c)) - 1) ≥ y / 2 * (-(2 * c / y)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : y / 2 * (-(2 * c / y)) = -c := by field_simp
    linarith
  have hG : legendreMajorant c y ≤ y / 2 * (Real.log (y / (2 * c)) - 1) + c := by
    unfold legendreMajorant; exact max_le (by linarith) (by linarith)
  have hratio : σ * (Ly - Lσ) ≤ K := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / σ by positivity)
    rw [Real.log_div hy0.ne' hσ0.ne'] at h
    have e : y / σ - 1 = K / σ := by rw [hy]; field_simp; ring
    rw [e] at h
    have := mul_le_mul_of_nonneg_left h hσ0.le
    rwa [mul_div_cancel₀ _ hσ0.ne'] at this
  have hσy : Lσ ≤ Ly := Real.log_le_log hσ0 (by linarith)
  rw [hlogσ2, hlog2π] at hst
  rw [hlogy2c] at hG
  rw [hlogπc]
  have hkey : legendreMajorant c y + σ / 2 * Lπ - Real.log (Real.Gamma (σ / 2)) ≤
      c + (K + 1) / 2 * Ly + y / 2 * (Lπ - Lc) := by
    have e : y / 2 * (Ly - (L2 + Lc) - 1) + c + σ / 2 * Lπ -
        ((σ / 2 - 1 / 2) * (Lσ - L2) - σ / 2 + (L2 + Lπ) / 2)
        = σ / 2 * (Ly - Lσ) + K / 2 * (Ly - L2 - Lπ - 1) + c + 1 / 2 * Lσ - L2 - Lπ / 2 +
          y / 2 * (Lπ - Lc) := by
      rw [hy]; ring
    nlinarith [mul_nonneg hK0 (add_nonneg hL2 hLπ)]
  rw [div_le_iff₀ hΓ, ← Real.exp_log hΓ]
  have hpi : Real.pi ^ (σ / 2) = Real.exp (σ / 2 * Lπ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]; congr 1; rw [mul_comm]
  rw [hpi, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The full `ξ` floor on `Re s ≥ 2` with the exact imaginary-shift integral. -/
theorem xi_floor_exact {σ t : ℝ} (hσ : 2 ≤ σ) :
    1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
      Real.exp (-(HTGeometry.gammaShiftIntegral (σ / 2) (t / 2) / 2)) ≤
        ‖xi ((σ : ℂ) + (t : ℂ) * I)‖ := by
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
  -- `‖Γ(σ/2 + it/2)‖ ≥ Γ(σ/2) (1+t²/σ²)^{-1/2} e^{-I/2}`
  have hx : 0 < σ / 2 := by linarith
  have hb := (HTGeometry.log_norm_Gamma_sub_log_Gamma_bounds hx (t / 2)).1
  have hw : HTGeometry.gammaShiftWeight (σ / 2) (t / 2) 0 = Real.log (1 + t ^ 2 / σ ^ 2) := by
    simp only [HTGeometry.gammaShiftWeight, add_zero]
    congr 2; field_simp
  rw [hw] at hb
  have e1 : ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I = s / 2 := by rw [hs]; push_cast; ring
  rw [e1] at hb
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos hx
  have hq : 0 < 1 + t ^ 2 / σ ^ 2 := by positivity
  have hGpos : 0 < ‖Complex.Gamma (s / 2)‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.div_re]; simp [hsre]; nlinarith)
  have hG : Real.Gamma (σ / 2) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
      Real.exp (-(HTGeometry.gammaShiftIntegral (σ / 2) (t / 2) / 2)) ≤ ‖Complex.Gamma (s / 2)‖ := by
    rw [← Real.exp_log hGpos]
    have hsq : (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ =
        Real.exp (-(1 / 2) * Real.log (1 + t ^ 2 / σ ^ 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hq.le, Real.rpow_def_of_pos hq]; ring_nf
    rw [hsq, ← Real.exp_log hΓ, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hZ := one_third_le_norm_riemannZeta (s := s) (by rw [hsre]; exact hσ)
  have hpi : 0 < Real.pi ^ (-(σ / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  calc 1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
        Real.exp (-(HTGeometry.gammaShiftIntegral (σ / 2) (t / 2) / 2))
      = (Real.pi ^ (-(σ / 2)) * (Real.Gamma (σ / 2) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
          Real.exp (-(HTGeometry.gammaShiftIntegral (σ / 2) (t / 2) / 2)))) * (1 / 3) := by ring
    _ ≤ (Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖) * ‖riemannZeta s‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hG hpi.le) hZ (by norm_num) (by positivity)
    _ ≤ ‖s * (s - 1) / 2‖ * (Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖) *
          ‖riemannZeta s‖ := by
        have : 0 ≤ Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖ := by positivity
        nlinarith


/-- **Theta-window directional law.** Let `|F(x)| ≤ C e^{k|x|} exp(−c e^{2|x|})` with `0 < c`, and
`M_F = ξ · h` on `Re s ≥ 2`. Then for `σ ≥ 2`,
`‖h(σ+it)‖ ≤ B (σ+K)^{…} √(1+t²/σ²) · exp((σ/2) log(π/c) + ½|t| arctan(|t|/σ) − (σ/4) log(1+t²/σ²))`.
In polar coordinates the exponent is `r J_c(φ)`, `J_c(φ) = ½[cos φ log(π cos φ/c) + φ sin φ]`. By
`theta_window_le` and `theta_window_attained` it dominates the support function of the shift window
`{v + iθ : π e^{−2|v|} cos 2θ ≥ c}` of Riemann's kernel, with equality where `π cos φ ≥ c`. -/
theorem theta_window_directional_law {F : ℝ → ℂ} {C k c : ℝ} (hk : 0 ≤ k) (hc : 0 < c)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - c * Real.exp (2 * |x|)))
    {h : ℂ → ℂ} (hdiv : ∀ s : ℂ, 2 ≤ s.re → centredLaplace F s = xi s * h s) {σ t : ℝ}
    (hσ : 2 ≤ σ) :
    ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      3 * (C * ∫ x : ℝ, Real.exp (-|x|)) *
        Real.exp (c + (k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2)) +
          (k + 1 / 2) / 2 * Real.log (π / c)) *
        Real.sqrt (1 + t ^ 2 / σ ^ 2) *
        Real.exp (σ / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ) -
          σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hσ0 : 0 < σ := by linarith
  have hC : 0 ≤ C := by
    have h1 := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (k * |(0 : ℝ)| - c * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  have hJ : 0 ≤ ∫ x : ℝ, Real.exp (-|x|) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hMb := norm_centredLaplace_le_rate hc hF hk s
  have habs : |s.re - 1 / 2| + k + 1 = σ - 1 / 2 + k + 1 := by
    rw [hsre, abs_of_pos (by linarith)]
  rw [habs] at hMb
  set Ish := HTGeometry.gammaShiftIntegral (σ / 2) (t / 2) with hIsh
  have hfl := xi_floor_exact (t := t) hσ
  rw [← hIsh] at hfl
  set f := 1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * (Real.sqrt (1 + t ^ 2 / σ ^ 2))⁻¹ *
      Real.exp (-(Ish / 2)) with hf
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hsq : 0 < Real.sqrt (1 + t ^ 2 / σ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hfpos : 0 < f := by positivity
  have hnorm : ‖centredLaplace F s‖ = ‖xi s‖ * ‖h s‖ := by
    rw [hdiv s (by rw [hsre]; exact hσ), norm_mul]
  have h1 : f * ‖h s‖ ≤ C * Real.exp (legendreMajorant c (σ - 1 / 2 + k + 1)) *
      ∫ x : ℝ, Real.exp (-|x|) := by
    calc f * ‖h s‖ ≤ ‖xi s‖ * ‖h s‖ := mul_le_mul_of_nonneg_right hfl (norm_nonneg _)
      _ = _ := hnorm.symm
      _ ≤ _ := hMb
  rw [← le_div_iff₀' hfpos] at h1
  have hinv : 1 / f = 3 * (Real.pi ^ (σ / 2) / Real.Gamma (σ / 2)) *
      Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (Ish / 2) := by
    rw [hf, Real.rpow_neg Real.pi_pos.le, Real.exp_neg]
    field_simp
  have hl := legendre_rate_div_Gamma_le hc hk hσ
  have hI := gammaShiftIntegral_half_eq (t := t) hσ0
  rw [← hIsh] at hI
  have hsplit : Real.exp (c + (k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2)) +
        (σ + (k + 1 / 2)) / 2 * Real.log (π / c)) * Real.exp (Ish / 2) =
      Real.exp (c + (k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2)) +
          (k + 1 / 2) / 2 * Real.log (π / c)) *
        Real.exp (σ / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ) -
          σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, hI]; congr 1; ring
  have hK : 0 ≤ 3 * (C * ∫ x : ℝ, Real.exp (-|x|)) := by positivity
  calc ‖h s‖ ≤ C * Real.exp (legendreMajorant c (σ - 1 / 2 + k + 1)) *
        (∫ x : ℝ, Real.exp (-|x|)) / f := h1
    _ = 3 * (C * ∫ x : ℝ, Real.exp (-|x|)) *
        (Real.exp (legendreMajorant c (σ - 1 / 2 + k + 1)) * Real.pi ^ (σ / 2) /
          Real.Gamma (σ / 2)) * Real.sqrt (1 + t ^ 2 / σ ^ 2) * Real.exp (Ish / 2) := by
        rw [div_eq_mul_one_div, hinv]; ring
    _ ≤ 3 * (C * ∫ x : ℝ, Real.exp (-|x|)) *
        Real.exp (c + (k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2)) +
          (σ + (k + 1 / 2)) / 2 * Real.log (π / c)) * Real.sqrt (1 + t ^ 2 / σ ^ 2) *
          Real.exp (Ish / 2) := by
        gcongr
    _ = _ := by
        rw [mul_assoc (3 * (C * ∫ x : ℝ, Real.exp (-|x|)) * _), mul_comm (Real.sqrt _),
          ← mul_assoc, mul_assoc (3 * (C * ∫ x : ℝ, Real.exp (-|x|))), hsplit]
        ring


/-! ## Attainment by real shifts of `Φ` -/

/-- A real shift multiplies the transform: `M_{F(·−v)}(s) = e^{(s−½)v} M_F(s)`. -/
theorem centredLaplace_shift (F : ℝ → ℂ) (v : ℝ) (s : ℂ) :
    centredLaplace (fun x => F (x - v)) s = cexp ((s - 1 / 2) * v) * centredLaplace F s := by
  unfold centredLaplace
  rw [← integral_const_mul, ← integral_add_right_eq_self
    (fun x : ℝ => cexp ((s - 1 / 2) * x) * F (x - v)) v]
  congr 1; funext x
  simp only [add_sub_cancel_right]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- The real shift `Φ(· − v)` decays at the rate `π e^{−2|v|}`, with prefactor `e^{9|x|/2}`. -/
theorem riemannPhiKernel_shift_rate (v : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, ‖riemannPhiKernel (x - v)‖ ≤
      C * Real.exp (9 / 2 * |x| - π * Real.exp (-(2 * |v|)) * Real.exp (2 * |x|)) := by
  obtain ⟨C₀, hC₀⟩ := riemannPhiKernel_theta_rate
  have hC₀nn : 0 ≤ C₀ := by
    have h1 := hC₀ 0
    have := norm_nonneg (riemannPhiKernel 0)
    have h3 := Real.exp_pos (9 / 2 * |(0 : ℝ)| - π * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  refine ⟨C₀ * Real.exp (9 / 2 * |v|), fun x => ?_⟩
  refine (hC₀ (x - v)).trans ?_
  have h1 : |x - v| ≤ |x| + |v| := abs_sub _ _
  have h2 : |x| - |v| ≤ |x - v| := abs_sub_abs_le_abs_sub x v
  have h3 : Real.exp (-(2 * |v|)) * Real.exp (2 * |x|) ≤ Real.exp (2 * |x - v|) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC₀nn
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
  nlinarith

/-- **Attainment on the real axis.** For every `c ∈ (0, π]` the shift `Φ(· − v)` with
`v = ½ log(π/c)` has rate `c` and quotient `h(s) = e^{v(s−½)}`, so `|h(σ)| = e^{v(σ−½)}` meets the
directional law at `t = 0`, `(σ/2) log(π/c) = vσ`, up to the constant factor `e^{−v/2}`. -/
theorem theta_window_real_axis_attained {c : ℝ} (hc : 0 < c) (hcπ : c ≤ π) :
    let v := Real.log (π / c) / 2
    (∃ C : ℝ, ∀ x : ℝ, ‖riemannPhiKernel (x - v)‖ ≤
      C * Real.exp (9 / 2 * |x| - c * Real.exp (2 * |x|))) ∧
    (∀ s : ℂ, centredLaplace (fun x => riemannPhiKernel (x - v)) s =
      xi s * cexp ((s - 1 / 2) * v)) ∧
    ∀ σ : ℝ, v * σ = σ / 2 * Real.log (π / c) := by
  intro v
  have hv0 : 0 ≤ v := by
    show 0 ≤ Real.log (π / c) / 2
    have := Real.log_nonneg (show 1 ≤ π / c by rw [le_div_iff₀ hc]; linarith); linarith
  refine ⟨?_, fun s => ?_, fun σ => by show Real.log (π / c) / 2 * σ = _; ring⟩
  · obtain ⟨C, hC⟩ := riemannPhiKernel_shift_rate v
    refine ⟨C, fun x => (hC x).trans_eq ?_⟩
    congr 3
    rw [abs_of_nonneg hv0]
    have : Real.exp (-(2 * v)) = c / π := by
      show Real.exp (-(2 * (Real.log (π / c) / 2))) = c / π
      rw [show -(2 * (Real.log (π / c) / 2)) = -Real.log (π / c) by ring, Real.exp_neg,
        Real.exp_log (by positivity), inv_div]
    rw [this]; field_simp
  · rw [centredLaplace_shift, centredLaplace_riemannPhiKernel, mul_one, mul_comm]


end

end RHTower
