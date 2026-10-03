import GaloisForLFunctions.RHTower.HamburgerTwistedRadialDefect
import GaloisForLFunctions.RHTower.WeilFractionalMassPolynomialTailRigidity

/-!
# Truncated radial integrals of a Herglotz producer are uniformly bounded

Let `G` be continuous on `Re s ≥ ½` with `G' = ΦG`, where `Φ` is the Herglotz form of Weil
positivity for weights `lam`, and let `F = G/(s(s−1)Γ_ℝ)` be the producer zeta function, whose
boundary value on the critical line is `phiG G t = F(½ + 2it)`.  Put `τ_ε = ε + i m` with `m ≥ 1`.

**Theorem** (`exists_bound_truncated_radial`).  There is `B` with
`‖ε ∫_a^0 F(½ + 2it) k(2t, τ_ε) dt‖ ≤ B` for all `0 < ε ≤ 1` and all `a ≤ 0`, where `k` is
Hamburger's Laplace kernel.

The absolute integral `ε ∫_a^0 ‖F k‖` is not bounded in general: it is the Abel mean of `‖F‖`.
The bound comes from cancellation, through a contour shift.

**Proof.**
* `k(v, τ)` is the value at `s = ½ + iv` of
  `k_τ(s) = π^{1−s/2} τ (πτ²)^{s/2−1}/sin(πs/2)`, holomorphic on `0 < Re s < 2`
  (`pairKernel_eq_offKernel`).  On `½ ≤ Re s ≤ 3/2`, `Im s = y ≤ −1`, it satisfies
  `‖k_τ(s)‖ ≤ 4π^{3/4} ‖τ‖ e^{−δ|y|}` with `δ = Re τ/‖τ‖ = ε/‖τ‖` (`norm_offKernel_le`), because
  `|sin(πs/2)| ≥ e^{π|y|/2}/4` and `|arg(πτ²)| ≤ π − 2δ`.
* Cauchy's theorem on `[½, 3/2] × [2a, −2]` moves the integral of `F k_τ` from the critical line to
  `Re s = 3/2`, plus two horizontal segments.
  - On `Re s = 3/2`, `F = exp(Σ lam(n) n^{−s}/log n)` is bounded, and `ε ∫ e^{−δ|y|} dy ≤ ε/δ = ‖τ‖`.
  - On a horizontal segment, horizontal monotonicity of `|G|` and a uniform vertical `Γ`-ratio
    bound give `|F(x + iy)| ≤ C (1 + |y|)^{1/2}` (`exists_norm_prodF_le`).  Then
    `ε (1 + |y|) e^{−δ|y|} ≤ ε + ‖τ‖` is bounded.
* The piece `[−1, 0]` is bounded trivially.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace TruncatedRadial

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability

noncomputable section

/-! ### The Laplace kernel off the critical line -/

/-- Hamburger's Laplace kernel as a function of `s`:
`k_τ(s) = π^{1−s/2} τ (πτ²)^{s/2−1} / sin(πs/2)`. -/
def offKernel (τ s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (1 - s / 2) * τ * ((Real.pi : ℂ) * τ ^ 2) ^ (s / 2 - 1) /
    Complex.sin (Real.pi * s / 2)

theorem pairKernel_eq_offKernel (v : ℝ) (τ : ℂ) :
    pairKernel v τ = offKernel τ (HamburgerStability.linePt v) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set ρ := HamburgerStability.linePt v with hρ
  unfold pairKernel gammaPair offKernel
  rw [← hρ, Complex.Gamma_mul_Gamma_one_sub]
  have h1 : (Real.pi : ℂ) ^ (1 - ρ / 2) = (Real.pi : ℂ) * (Real.pi : ℂ) ^ (-ρ / 2) := by
    rw [show (1 : ℂ) - ρ / 2 = 1 + -ρ / 2 by ring, Complex.cpow_add _ _ hpi, Complex.cpow_one]
  rw [h1, show -(1 - ρ / 2) = ρ / 2 - 1 by ring,
    show (Real.pi : ℂ) * (ρ / 2) = Real.pi * ρ / 2 by ring]
  ring

/-- `sin(πs/2) ≠ 0` on `0 < Re s < 2`. -/
theorem sin_pi_mul_half_ne_zero {s : ℂ} (h0 : 0 < s.re) (h2 : s.re < 2) :
    Complex.sin (Real.pi * s / 2) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp only [Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.intCast_re, Complex.intCast_im, mul_zero] at hre
  norm_num at hre
  have hpi := Real.pi_pos
  have hk' : s.re = 2 * k := by
    field_simp at hre
    nlinarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (k : ℝ) < 1 := by linarith
  have h1 : (0 : ℤ) < k := by exact_mod_cast hk0
  have h2' : k < (1 : ℤ) := by exact_mod_cast hk1
  omega

theorem differentiableAt_offKernel {τ s : ℂ} (hτ : τ ≠ 0) (h0 : 0 < s.re) (h2 : s.re < 2) :
    DifferentiableAt ℂ (offKernel τ) s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : (Real.pi : ℂ) * τ ^ 2 ≠ 0 := mul_ne_zero hpi (pow_ne_zero 2 hτ)
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (1 - z / 2)) s :=
    ((differentiableAt_const _).sub (differentiableAt_id.div_const _)).const_cpow (Or.inl hpi)
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => ((Real.pi : ℂ) * τ ^ 2) ^ (z / 2 - 1)) s :=
    ((differentiableAt_id.div_const _).sub (differentiableAt_const _)).const_cpow (Or.inl hz)
  have hd3 : DifferentiableAt ℂ (fun z : ℂ => Complex.sin (Real.pi * z / 2)) s :=
    Complex.differentiableAt_sin.comp _ ((differentiableAt_id.const_mul _).div_const _)
  exact ((hd1.mul (differentiableAt_const _)).mul hd2).div hd3 (sin_pi_mul_half_ne_zero h0 h2)

/-- `|sin(x + iy)| ≥ |sinh y|`. -/
theorem abs_sinh_le_norm_sin (x y : ℝ) :
    |Real.sinh y| ≤ ‖Complex.sin ((x : ℂ) + (y : ℂ) * I)‖ := by
  have hz : Complex.sin ((x : ℂ) + (y : ℂ) * I) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * I := by
    rw [Complex.sin_add_mul_I]
    push_cast [Complex.ofReal_sin, Complex.ofReal_cos, Complex.ofReal_cosh, Complex.ofReal_sinh]
    ring
  have hsq : Real.sinh y ^ 2 ≤ ‖Complex.sin ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hz]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.add_im, Complex.mul_im,
      zero_add]
    have hc := Real.cosh_sq y
    have hsc := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.sin x * Real.sinh y), sq_nonneg (Real.sin x), sq_nonneg (Real.cos x)]
  rw [← abs_norm]
  exact sq_le_sq.mp (by simpa using hsq)

/-- `sinh u ≥ e^u/4` for `u ≥ 1`. -/
theorem exp_div_four_le_sinh {u : ℝ} (hu : 1 ≤ u) : Real.exp u / 4 ≤ Real.sinh u := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-u) ≤ Real.exp u / 2 := by
    have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h3 : 2 ≤ Real.exp u * Real.exp u := by
      have := Real.add_one_le_exp u
      nlinarith
    nlinarith [Real.exp_pos u, Real.exp_pos (-u)]
  linarith

/-- **Damping of the kernel off the critical line.**  For `½ ≤ x ≤ 3/2`, `|y| ≥ 1`, `Re τ > 0` and
`‖τ‖ ≥ 1`: `‖k_τ(x + iy)‖ ≤ 4 π^{3/4} ‖τ‖ e^{−|y| Re τ/‖τ‖}`. -/
theorem norm_offKernel_le {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {x y : ℝ} (hx1 : 1 / 2 ≤ x)
    (hx2 : x ≤ 3 / 2) (hy : 1 ≤ |y|) :
    ‖offKernel τ ((x : ℂ) + (y : ℂ) * I)‖ ≤
      4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖))) := by
  have hpi := Real.pi_pos
  have hτ : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  have hz : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hpi.ne') (pow_ne_zero 2 hτ)
  set s : ℂ := (x : ℂ) + (y : ℂ) * I with hs
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  -- the three factors
  have hA : ‖(Real.pi : ℂ) ^ (1 - s / 2)‖ ≤ Real.pi ^ (3 / 4 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) ?_
    simp [hs]; linarith
  have hnorm : ‖(Real.pi : ℂ) * τ ^ 2‖ = Real.pi * ‖τ‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have hbase : 1 ≤ Real.pi * ‖τ‖ ^ 2 := by nlinarith [Real.pi_gt_three]
  have hB : ‖((Real.pi : ℂ) * τ ^ 2) ^ (s / 2 - 1)‖ ≤
      Real.exp ((Real.pi - 2 * δ) * (|y| / 2)) := by
    rw [Complex.norm_cpow_of_ne_zero hz, hnorm]
    have hre : (s / 2 - 1).re = x / 2 - 1 := by simp [hs]
    have him : (s / 2 - 1).im = y / 2 := by simp [hs]
    rw [hre, him]
    have h1 : (Real.pi * ‖τ‖ ^ 2) ^ (x / 2 - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    have harg := abs_arg_pi_mul_sq_le hτre
    have h2 : Real.exp (-((Real.pi - 2 * δ) * (|y| / 2))) ≤
        Real.exp (((Real.pi : ℂ) * τ ^ 2).arg * (y / 2)) := by
      apply Real.exp_le_exp.mpr
      have h3 := neg_abs_le (((Real.pi : ℂ) * τ ^ 2).arg * (y / 2))
      rw [abs_mul, abs_div, abs_two] at h3
      have h4 : |((Real.pi : ℂ) * τ ^ 2).arg| * (|y| / 2) ≤ (Real.pi - 2 * δ) * (|y| / 2) :=
        mul_le_mul_of_nonneg_right harg (by positivity)
      linarith
    rw [div_le_iff₀ (Real.exp_pos _)]
    calc (Real.pi * ‖τ‖ ^ 2) ^ (x / 2 - 1) ≤ 1 := h1
      _ = Real.exp ((Real.pi - 2 * δ) * (|y| / 2)) *
          Real.exp (-((Real.pi - 2 * δ) * (|y| / 2))) := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp ((Real.pi - 2 * δ) * (|y| / 2)) *
          Real.exp (((Real.pi : ℂ) * τ ^ 2).arg * (y / 2)) := by gcongr
  have hC : Real.exp (Real.pi * |y| / 2) / 4 ≤ ‖Complex.sin (Real.pi * s / 2)‖ := by
    have harg : (Real.pi : ℂ) * s / 2 = ((Real.pi * x / 2 : ℝ) : ℂ) + ((Real.pi * y / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [harg]
    refine le_trans ?_ (abs_sinh_le_norm_sin _ _)
    have hu : 1 ≤ |Real.pi * y / 2| := by
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
      nlinarith [Real.pi_gt_three]
    have habs : |Real.pi * y / 2| = Real.pi * |y| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
    rw [← habs, Real.abs_sinh]
    exact exp_div_four_le_sinh hu
  have hCpos : 0 < Real.exp (Real.pi * |y| / 2) / 4 := by positivity
  unfold offKernel
  rw [norm_div, norm_mul, norm_mul, div_le_iff₀ (lt_of_lt_of_le hCpos hC)]
  calc ‖(Real.pi : ℂ) ^ (1 - s / 2)‖ * ‖τ‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ (s / 2 - 1)‖
      ≤ Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp ((Real.pi - 2 * δ) * (|y| / 2)) := by
        gcongr
    _ = 4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * δ)) *
          (Real.exp (Real.pi * |y| / 2) / 4) := by
        have : Real.exp ((Real.pi - 2 * δ) * (|y| / 2)) =
            Real.exp (-(|y| * δ)) * Real.exp (Real.pi * |y| / 2) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]; ring
    _ ≤ 4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * δ)) *
          ‖Complex.sin (Real.pi * s / 2)‖ := by gcongr

/-! ### A uniform vertical shift of `Γ` -/

/-- **Uniform vertical shift of `Γ`.**  For `0 ≤ a ≤ b` and `τ > 0`,
`‖Γ(b + iτ)‖ ≤ ‖Γ(a + iτ)‖ exp((b − a)(½ log(b² + τ²) + 1/τ² + π/(2τ)))`, by integrating the
vertical digamma bound. -/
theorem norm_Gamma_shift_le_uniform {a b τ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hτ : 0 < τ) :
    ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * I)‖ ≤ ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ *
      Real.exp ((b - a) * (1 / 2 * Real.log (b ^ 2 + τ ^ 2) + (1 / τ ^ 2 + Real.pi / (2 * τ)))) := by
  have hint := integral_re_digamma_vertical (a := a) (δ := b - a) hτ
  rw [show a + (b - a) = b by ring] at hint
  set K := 1 / 2 * Real.log (b ^ 2 + τ ^ 2) + (1 / τ ^ 2 + Real.pi / (2 * τ)) with hK
  have hle : ∫ x in a..b, (Complex.digamma ((x : ℂ) + (τ : ℂ) * I)).re ≤ (b - a) * K := by
    have h := intervalIntegral.integral_mono_on (g := fun _ => K) hab
      ((continuous_re_digamma_line hτ).intervalIntegrable a b)
      (continuous_const.intervalIntegrable (μ := volume) a b) (fun x hx => ?_)
    · rw [intervalIntegral.integral_const, smul_eq_mul] at h; linarith
    · have hx0 : 0 ≤ x := ha.trans hx.1
      have hb := (abs_le.mp (re_digamma_vertical_bound_uncond hx0 hτ)).2
      have hlog : Real.log (x ^ 2 + τ ^ 2) ≤ Real.log (b ^ 2 + τ ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith [hx.1, hx.2])
      linarith
  have hG0 : 0 < ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero hτ a)
  have hG1 : 0 < ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero hτ b)
  rw [← Real.exp_log hG1, ← Real.exp_log hG0, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **`Γ_ℝ` between `Re s = x` and `Re s = 3/2`.**  For `½ ≤ x ≤ 3/2` and `|y| ≥ 2`,
`‖Γ_ℝ(3/2 + iy)‖ ≤ e³ (1 + |y|)^{1/2} ‖Γ_ℝ(x + iy)‖`. -/
theorem norm_Gammaℝ_three_halves_le {x y : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 3 / 2) (hy : 2 ≤ |y|) :
    ‖Complex.Gammaℝ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp 3 * (1 + |y|) ^ (1 / 2 : ℝ) * ‖Complex.Gammaℝ ((x : ℂ) + (y : ℂ) * I)‖ := by
  have hpi := Real.pi_pos
  have hnorm : ∀ σ : ℝ, ‖Complex.Gammaℝ ((σ : ℂ) + (y : ℂ) * I)‖ =
      Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((|y| / 2 : ℝ) : ℂ) * I)‖ := by
    intro σ
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    congr 1
    · congr 1; simp; ring
    · rcases le_total 0 y with h | h
      · rw [abs_of_nonneg h]; congr 1; push_cast; ring_nf
      · rw [abs_of_nonpos h, ← FractionalMassPolynomialTailRigidity.norm_Gamma_conj_line]
        congr 1; push_cast; ring_nf
  rw [hnorm, hnorm]
  set τ : ℝ := |y| / 2 with hτ
  have hτ1 : 1 ≤ τ := by rw [hτ]; linarith
  have hτ0 : 0 < τ := by linarith
  have hsh := norm_Gamma_shift_le_uniform (a := x / 2) (b := 3 / 2 / 2) (τ := τ) (by linarith)
    (by linarith) hτ0
  have hE : (3 / 2 / 2 - x / 2) * (1 / 2 * Real.log ((3 / 2 / 2) ^ 2 + τ ^ 2) +
      (1 / τ ^ 2 + Real.pi / (2 * τ))) ≤ 1 / 2 * Real.log (1 + |y|) + 3 / 2 := by
    have hd0 : 0 ≤ 3 / 2 / 2 - x / 2 := by linarith
    have hd1 : 3 / 2 / 2 - x / 2 ≤ 1 / 2 := by linarith
    have hl0 : 0 ≤ 1 / 2 * Real.log ((3 / 2 / 2) ^ 2 + τ ^ 2) :=
      mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith))
    have hl1 : 1 / 2 * Real.log ((3 / 2 / 2) ^ 2 + τ ^ 2) ≤ Real.log (1 + |y|) := by
      have h1 : (3 / 2 / 2) ^ 2 + τ ^ 2 ≤ (1 + |y|) ^ 2 := by rw [hτ]; nlinarith [abs_nonneg y]
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    have he0 : 0 ≤ 1 / τ ^ 2 + Real.pi / (2 * τ) := by positivity
    have he1 : 1 / τ ^ 2 + Real.pi / (2 * τ) ≤ 3 := by
      have h1 : 1 / τ ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      have h2 : Real.pi / (2 * τ) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
      linarith
    nlinarith
  have hexp : Real.exp ((3 / 2 / 2 - x / 2) * (1 / 2 * Real.log ((3 / 2 / 2) ^ 2 + τ ^ 2) +
      (1 / τ ^ 2 + Real.pi / (2 * τ)))) ≤ Real.exp 3 * (1 + |y|) ^ (1 / 2 : ℝ) := by
    calc _ ≤ Real.exp (1 / 2 * Real.log (1 + |y|) + 3 / 2) := Real.exp_le_exp.mpr hE
      _ = Real.exp (3 / 2) * (1 + |y|) ^ (1 / 2 : ℝ) := by
          rw [Real.exp_add, Real.rpow_def_of_pos (by positivity)]; ring_nf
      _ ≤ Real.exp 3 * (1 + |y|) ^ (1 / 2 : ℝ) := by
          gcongr; norm_num
  have hpow : Real.pi ^ (-((3 / 2 : ℝ) / 2)) ≤ Real.pi ^ (-(x / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  have e1 : (((3 / 2 : ℝ) / 2 : ℝ) : ℂ) = ((3 / 2 / 2 : ℝ) : ℂ) := by norm_num
  rw [e1]
  calc Real.pi ^ (-((3 / 2 : ℝ) / 2)) * ‖Complex.Gamma (((3 / 2 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖
      ≤ Real.pi ^ (-(x / 2)) * (‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ *
          (Real.exp 3 * (1 + |y|) ^ (1 / 2 : ℝ))) :=
        mul_le_mul hpow (hsh.trans (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-! ### The producer zeta function in the strip -/

/-- The producer zeta function `F = G/(s(s−1)Γ_ℝ(s))`; on the critical line
`phiG G t = F(½ + 2it)`. -/
def prodF (G : ℂ → ℂ) (s : ℂ) : ℂ := G s / (s * (s - 1) * Complex.Gammaℝ s)

theorem phiG_eq_prodF (G : ℂ → ℂ) (t : ℝ) : phiG G t = prodF G (lineS t) := rfl

/-- `‖exp(Σ lam(n) n^{−s}/log n)‖ ≤ exp(Σ ‖lam(n) n^{−σ}/log n‖)` on `Re s = σ > 1`. -/
theorem norm_zetaOf_le {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ} (hs : 1 < s.re) :
    ‖zetaOf lam s‖ ≤ Real.exp (∑' n, ‖LSeries.term (lamLog lam) (s.re : ℂ) n‖) := by
  have hsumm : LSeriesSummable (lamLog lam) s := lseriesSummable_of_le (norm_lamLog_le lam) hsl hs
  have hL : ‖LSeries (lamLog lam) s‖ ≤ ∑' n, ‖LSeries.term (lamLog lam) (s.re : ℂ) n‖ := by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hsumm.norm).trans (le_of_eq (tsum_congr fun n => ?_))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  unfold zetaOf
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hL)

theorem prodF_eq_zetaOf {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {s : ℂ} (hs : 1 < s.re) : prodF G s = zetaOf lam s := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1 : s - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  unfold prodF
  rw [G_eq_bigG hsl hid hGd hG2 hs]
  unfold bigG
  field_simp

/-- **The producer zeta function grows at most like `|y|^{1/2}` in the strip.**  For
`½ ≤ x ≤ 3/2` and `|y| ≥ 2`, `‖F(x + iy)‖ ≤ C (1 + |y|)^{1/2}`: horizontal monotonicity of `|G|`
up to `Re s = 3/2` and the uniform `Γ_ℝ` ratio. -/
theorem exists_norm_prodF_le {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (1 / 2 : ℝ) := by
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  refine ⟨4 * Real.exp 3 * Real.exp S, by positivity, fun x y hx1 hx2 hy => ?_⟩
  set s : ℂ := (x : ℂ) + (y : ℂ) * I with hs
  set s₃ : ℂ := ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hs₃
  have hs₃re : 1 < s₃.re := by simp [hs₃]; norm_num
  have hmono : ‖G s‖ ≤ ‖G s₃‖ :=
    FractionalMassPolynomialTailRigidity.norm_G_le_of_le hΦre hGc hGd y hx1 hx2
  have hG3 : ‖G s₃‖ = ‖s₃‖ * ‖s₃ - 1‖ * ‖Complex.Gammaℝ s₃‖ * ‖zetaOf lam s₃‖ := by
    rw [G_eq_bigG hsl hid hGd hG2 hs₃re]; unfold bigG; rw [norm_mul, norm_mul, norm_mul]
  have hz : ‖zetaOf lam s₃‖ ≤ Real.exp S := by
    have h := norm_zetaOf_le hsl hs₃re
    have hre : (s₃.re : ℂ) = ((3 / 2 : ℝ) : ℂ) := by simp [hs₃]
    rwa [hre] at h
  have hΓ := norm_Gammaℝ_three_halves_le hx1 hx2 hy
  have hyabs : 0 < |y| := by linarith
  have hsy : |y| ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s; simpa [hs] using this
  have hs1y : |y| ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1); simpa [hs] using this
  have hs₃n : ‖s₃‖ ≤ 2 * ‖s‖ := by
    have h := norm_add_le (((3 / 2 : ℝ) : ℂ)) ((y : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
    linarith
  have hs₃1 : ‖s₃ - 1‖ ≤ 2 * ‖s - 1‖ := by
    have e : s₃ - 1 = ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by rw [hs₃]; push_cast; ring
    have h := norm_add_le (((1 / 2 : ℝ) : ℂ)) ((y : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
    rw [e]; linarith
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hyabs hsy
  have hs10 : 0 < ‖s - 1‖ := lt_of_lt_of_le hyabs hs1y
  have hΓ0 : 0 < ‖Complex.Gammaℝ s‖ :=
    norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by simp [hs]; linarith))
  unfold prodF
  rw [norm_div, norm_mul, norm_mul, div_le_iff₀ (by positivity)]
  calc ‖G s‖ ≤ ‖G s₃‖ := hmono
    _ = ‖s₃‖ * ‖s₃ - 1‖ * ‖Complex.Gammaℝ s₃‖ * ‖zetaOf lam s₃‖ := hG3
    _ ≤ (2 * ‖s‖) * (2 * ‖s - 1‖) *
          (Real.exp 3 * (1 + |y|) ^ (1 / 2 : ℝ) * ‖Complex.Gammaℝ s‖) * Real.exp S := by
        gcongr
    _ = 4 * Real.exp 3 * Real.exp S * (1 + |y|) ^ (1 / 2 : ℝ) *
          (‖s‖ * ‖s - 1‖ * ‖Complex.Gammaℝ s‖) := by ring

/-! ### Regularity of the integrand -/

theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h : Complex.Gammaℝ = fun z => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) :=
    funext Complex.Gammaℝ_def
  rw [h]
  have h1 : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
  have h2 : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
  refine (h1.const_cpow (Or.inl hpi)).mul ?_
  refine (Complex.differentiableAt_Gamma _ fun k hk => ?_).comp s h2
  have := congrArg Complex.re hk
  simp at this
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem denom_ne_zero {s : ℂ} (hs : 0 < s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    s * (s - 1) * Complex.Gammaℝ s ≠ 0 :=
  mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (Complex.Gammaℝ_ne_zero_of_re_pos hs)

theorem continuousAt_prodF {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) : ContinuousAt (prodF G) s := by
  have hc : ContinuousAt (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s :=
    (continuousAt_id.mul (continuousAt_id.sub continuousAt_const)).mul
      (differentiableAt_Gammaℝ_of_re_pos (by linarith)).continuousAt
  exact (hGc s hs).div hc (denom_ne_zero (by linarith) h0 h1)

theorem differentiableAt_prodF {Φ G : ℂ → ℂ}
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) {s : ℂ} (hs : 1 / 2 < s.re)
    (h0 : s ≠ 0) (h1 : s ≠ 1) : DifferentiableAt ℂ (prodF G) s := by
  have hc : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s :=
    (differentiableAt_id.mul (differentiableAt_id.sub (differentiableAt_const _))).mul
      (differentiableAt_Gammaℝ_of_re_pos (by linarith))
  exact (hGd s hs).differentiableAt.div hc (denom_ne_zero (by linarith) h0 h1)

theorem continuous_pairKernel_two_mul {τ : ℂ} (hτ : τ ≠ 0) :
    Continuous fun t : ℝ => pairKernel (2 * t) τ := by
  have e : (fun t : ℝ => pairKernel (2 * t) τ) =
      fun t : ℝ => offKernel τ ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) := by
    funext t; rw [pairKernel_eq_offKernel]; rfl
  rw [e, continuous_iff_continuousAt]
  intro t
  have hre : ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I).re = 1 / 2 := by simp
  have hd := differentiableAt_offKernel hτ (s := (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)
    (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  exact hd.continuousAt.comp (f := fun t : ℝ => (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)
    (by fun_prop)

/-! ### Elementary integrals -/

/-- `u e^{−uδ} ≤ 1/δ`. -/
theorem mul_exp_neg_mul_le {u δ : ℝ} (hδ : 0 < δ) : u * Real.exp (-(u * δ)) ≤ δ⁻¹ := by
  have h : u * δ ≤ Real.exp (u * δ) := by linarith [Real.add_one_le_exp (u * δ)]
  have he : Real.exp (u * δ) * Real.exp (-(u * δ)) = 1 := by rw [← Real.exp_add]; simp
  calc u * Real.exp (-(u * δ)) = (u * δ) * Real.exp (-(u * δ)) * δ⁻¹ := by
        field_simp
    _ ≤ Real.exp (u * δ) * Real.exp (-(u * δ)) * δ⁻¹ := by gcongr
    _ = δ⁻¹ := by rw [he, one_mul]

theorem integral_exp_mul_le {A B δ : ℝ} (hB : B ≤ 0) (hδ : 0 < δ) :
    ∫ y in A..B, Real.exp (δ * y) ≤ δ⁻¹ := by
  rw [intervalIntegral.integral_comp_mul_left (fun y => Real.exp y) hδ.ne', integral_exp,
    smul_eq_mul]
  have h1 : Real.exp (δ * B) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 := Real.exp_pos (δ * A)
  have h3 : 0 < δ⁻¹ := inv_pos.mpr hδ
  nlinarith

/-- `ε (1 + u)^{1/2} e^{−uδ} ≤ ε + ε/δ`. -/
theorem mul_rpow_half_exp_le {ε u δ : ℝ} (hε : 0 ≤ ε) (hu : 0 ≤ u) (hδ : 0 < δ) :
    ε * ((1 + u) ^ (1 / 2 : ℝ) * Real.exp (-(u * δ))) ≤ ε + ε * δ⁻¹ := by
  have h1 : (1 + u) ^ (1 / 2 : ℝ) ≤ 1 + u := by
    calc (1 + u) ^ (1 / 2 : ℝ) ≤ (1 + u) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 1 + u := Real.rpow_one _
  have h2 : Real.exp (-(u * δ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h3 := mul_exp_neg_mul_le (u := u) hδ
  have he := Real.exp_pos (-(u * δ))
  calc ε * ((1 + u) ^ (1 / 2 : ℝ) * Real.exp (-(u * δ)))
      ≤ ε * ((1 + u) * Real.exp (-(u * δ))) := by gcongr
    _ = ε * Real.exp (-(u * δ)) + ε * (u * Real.exp (-(u * δ))) := by ring
    _ ≤ ε * 1 + ε * δ⁻¹ := by gcongr
    _ = ε + ε * δ⁻¹ := by ring

/-! ### The truncated radial integrals -/

/-- **Uniformly bounded truncated radial integrals.**  For `m ≥ 1` there is `B` with
`‖ε ∫_a^0 F(½ + 2it) k(2t, ε + i m) dt‖ ≤ B` for all `0 < ε ≤ 1` and `a ≤ 0`. -/
theorem exists_bound_truncated_radial {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ a : ℝ, a ≤ 0 →
      ‖(ε : ℂ) * ∫ t in a..0, phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)‖ ≤ B := by
  have hpi := Real.pi_pos
  obtain ⟨CF, hCF, hF⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  obtain ⟨CB, N, hCB, hB⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set K₀ : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set M : ℝ := (m : ℝ) + 1 with hM
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set B₀ : ℝ := 3 * CB * 2 ^ N with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  set B₁ : ℝ := Real.exp S * K₀ * M ^ 2 + 2 * (CF * K₀ * M * (1 + M)) with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  refine ⟨B₁ / 2 + B₀, fun ε hε hε1 a ha => ?_⟩
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτim : τ.im = m := by simp [hτ]
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    rw [hτim, abs_of_nonneg (Nat.cast_nonneg m)] at h
    linarith
  have hτM : ‖τ‖ ≤ M := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    rw [hM]; linarith
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ1; norm_num at hτ1
  have hτpos : 0 < ‖τ‖ := by linarith
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre0 hτpos
  have hεδ : ε * δ⁻¹ = ‖τ‖ := by rw [hδ, hτre]; field_simp
  set f : ℝ → ℂ := fun t => phiG G t * pairKernel (2 * t) τ with hf
  have hfc : Continuous f := (continuous_phiG hGc).mul (continuous_pairKernel_two_mul hτ0)
  -- the piece near `0`
  have hnear : ∀ b : ℝ, -1 ≤ b → b ≤ 0 → ‖∫ t in b..0, f t‖ ≤ B₀ := by
    intro b hb1 hb0
    have hbd : ∀ t ∈ Set.uIoc b 0, ‖f t‖ ≤ B₀ := by
      intro t ht
      rw [Set.uIoc_of_le hb0] at ht
      have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h1 := (hB t).1
      have h2 := norm_pairKernel_two_mul_le t hτre0
      have h3 : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
      have h4 : Real.exp (-(2 * (τ.re / ‖τ‖) * |t|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      have h5 : (1 + |t|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      have h6 : ‖pairKernel (2 * t) τ‖ ≤ 3 := by
        calc ‖pairKernel (2 * t) τ‖ ≤ 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
              Real.exp (-(2 * (τ.re / ‖τ‖) * |t|)) := h2
          _ ≤ 3 * 1 * 1 := by gcongr
          _ = 3 := by norm_num
      simp only [hf]
      rw [norm_mul]
      calc ‖phiG G t‖ * ‖pairKernel (2 * t) τ‖ ≤ (CB * 2 ^ N) * 3 :=
            mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h5 hCB)) h6 (norm_nonneg _)
              (by positivity)
        _ = B₀ := by rw [hB₀]; ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hab : |0 - b| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc ‖∫ t in b..0, f t‖ ≤ B₀ * |0 - b| := h
      _ ≤ B₀ * 1 := mul_le_mul_of_nonneg_left hab hB₀0
      _ = B₀ := mul_one _
  have hεn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  rcases le_or_gt (-1) a with ha1 | ha1
  · rw [norm_mul, hεn]
    calc ε * ‖∫ t in a..0, f t‖ ≤ 1 * B₀ := mul_le_mul hε1 (hnear a ha1 ha) (norm_nonneg _)
          zero_le_one
      _ ≤ B₁ / 2 + B₀ := by linarith
  -- `a < −1`: split at `−1`, shift the contour on `[a, −1]`
  have hsplit : ∫ t in a..0, f t = (∫ t in a..(-1), f t) + ∫ t in (-1 : ℝ)..0, f t :=
    (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)).symm
  set h : ℂ → ℂ := fun s => prodF G s * offKernel τ s with hh
  set g : ℝ → ℂ := fun y => h (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) with hg
  have hfg : ∀ t : ℝ, f t = g (2 * t) := by
    intro t
    simp only [hf, hg, hh]
    rw [phiG_eq_prodF, pairKernel_eq_offKernel, lineS_eq]
    have e : HamburgerStability.linePt (2 * t) = ((1 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
      unfold HamburgerStability.linePt; push_cast; ring
    rw [e]; push_cast; ring_nf
  have hchange : ∫ t in a..(-1), f t = (2 : ℝ)⁻¹ • ∫ y in (2 * a)..(-2), g y := by
    have h := intervalIntegral.integral_comp_mul_left g (a := a) (b := -1) (two_ne_zero' ℝ)
    rw [show (2 : ℝ) * -1 = -2 by norm_num] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun t _ => hfg t
  have h2a : 2 * a < -2 := by linarith
  -- the rectangle `[½, 3/2] × [2a, −2]`
  have hne : ∀ s : ℂ, s.im ≤ -2 → s ≠ 0 ∧ s ≠ 1 := by
    intro s hs
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · rw [h0] at hs; simp at hs; linarith
    · rw [h1] at hs; simp at hs; linarith
  have hcont : ContinuousOn h (Set.uIcc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.uIcc (2 * a) (-2)) := by
    intro s hs
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le h2a.le] at hs
    obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
    obtain ⟨h0, h1⟩ := hne s hi2
    exact ((continuousAt_prodF hGc hr1 h0 h1).mul
      (differentiableAt_offKernel hτ0 (by linarith) (by linarith)).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℂ h (Set.Ioo (min (1 / 2 : ℝ) (3 / 2)) (max (1 / 2 : ℝ) (3 / 2)) ×ℂ
      Set.Ioo (min (2 * a) (-2)) (max (2 * a) (-2))) := by
    intro s hs
    rw [Complex.mem_reProdIm, min_eq_left (by norm_num), max_eq_right (by norm_num),
      min_eq_left h2a.le, max_eq_right h2a.le] at hs
    obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
    obtain ⟨h0, h1⟩ := hne s hi2.le
    exact ((differentiableAt_prodF hGd hr1 h0 h1).mul
      (differentiableAt_offKernel hτ0 (by linarith) (by linarith))).differentiableWithinAt
  set z : ℂ := ((1 / 2 : ℝ) : ℂ) + ((2 * a : ℝ) : ℂ) * I with hz
  set w : ℂ := ((3 / 2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * I with hw
  have hzre : z.re = 1 / 2 := by simp [hz]
  have hzim : z.im = 2 * a := by simp [hz]
  have hwre : w.re = 3 / 2 := by simp [hw]
  have hwim : w.im = -2 := by simp [hw]
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn h z w
    (by rw [hzre, hwre, hzim, hwim]; exact hcont) (by rw [hzre, hwre, hzim, hwim]; exact hdiff)
  rw [hzre, hwre, hzim, hwim] at hrect
  set L : ℂ := ∫ y in (2 * a)..(-2), g y with hL
  set R : ℂ := ∫ y in (2 * a)..(-2), h (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) with hR
  set Bot : ℂ := ∫ x in (1 / 2 : ℝ)..(3 / 2), h ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I) with hBot
  set Top : ℂ := ∫ x in (1 / 2 : ℝ)..(3 / 2), h ((x : ℂ) + ((-2 : ℝ) : ℂ) * I) with hTop
  have hLnorm : ‖L‖ ≤ ‖Bot‖ + ‖Top‖ + ‖R‖ := by
    have e : I * L = Bot - Top + I * R := by
      simp only [smul_eq_mul] at hrect
      linear_combination (-1 : ℂ) * hrect
    have hIL : ‖I * L‖ = ‖L‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [← hIL, e]
    calc ‖Bot - Top + I * R‖ ≤ ‖Bot - Top‖ + ‖I * R‖ := norm_add_le _ _
      _ ≤ ‖Bot‖ + ‖Top‖ + ‖R‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le Bot Top]
  -- the right edge
  have hRb : ε * ‖R‖ ≤ Real.exp S * K₀ * M ^ 2 := by
    have hbd : ∀ᵐ y ∂volume, y ∈ Set.Ioc (2 * a) (-2) →
        ‖h (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp S * K₀ * ‖τ‖ * Real.exp (δ * y) := by
      refine Eventually.of_forall fun y hy => ?_
      have hy0 : y < 0 := by linarith [hy.2]
      have hy2 : 1 ≤ |y| := by rw [abs_of_neg hy0]; linarith [hy.2]
      have hre : 1 < (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp; norm_num
      have hz1 := prodF_eq_zetaOf hsl hid hGd hG2 hre
      have hz2 := norm_zetaOf_le hsl hre
      have hre' : ((((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re : ℂ) = ((3 / 2 : ℝ) : ℂ) := by simp
      rw [hre'] at hz2
      have hk := norm_offKernel_le hτre0 hτ1 (x := 3 / 2) (y := y) (by norm_num) (by norm_num) hy2
      rw [abs_of_neg hy0] at hk
      simp only [hh]
      rw [norm_mul, hz1]
      calc ‖zetaOf lam (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ *
            ‖offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
          ≤ Real.exp S * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(-y * (τ.re / ‖τ‖)))) :=
            mul_le_mul hz2 hk (norm_nonneg _) (by positivity)
        _ = Real.exp S * K₀ * ‖τ‖ * Real.exp (δ * y) := by
            rw [hK₀, hδ]; ring_nf
    have hint : IntervalIntegrable (fun y => Real.exp S * K₀ * ‖τ‖ * Real.exp (δ * y)) volume
        (2 * a) (-2) := by
      exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        continuous_id))).intervalIntegrable _ _
    have h1 := intervalIntegral.norm_integral_le_of_norm_le h2a.le hbd hint
    rw [intervalIntegral.integral_const_mul] at h1
    have h2 := integral_exp_mul_le (A := 2 * a) (B := -2) (by norm_num) hδ0
    have hc : 0 ≤ Real.exp S * K₀ * ‖τ‖ := by positivity
    calc ε * ‖R‖ ≤ ε * (Real.exp S * K₀ * ‖τ‖ * δ⁻¹) := by
          gcongr; exact h1.trans (mul_le_mul_of_nonneg_left h2 hc)
      _ = Real.exp S * K₀ * ‖τ‖ * (ε * δ⁻¹) := by ring
      _ = Real.exp S * K₀ * ‖τ‖ ^ 2 := by rw [hεδ]; ring
      _ ≤ Real.exp S * K₀ * M ^ 2 := by gcongr
  -- the horizontal edges
  have hedge : ∀ y : ℝ, y ≤ -2 →
      ε * ‖∫ x in (1 / 2 : ℝ)..(3 / 2), h ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * K₀ * M * (1 + M) := by
    intro y hy
    have hy0 : y < 0 := by linarith
    have hy2 : 2 ≤ |y| := by rw [abs_of_neg hy0]; linarith
    have hbd : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) (3 / 2), ‖h ((x : ℂ) + (y : ℂ) * I)‖ ≤
        CF * (1 + |y|) ^ (1 / 2 : ℝ) * (K₀ * ‖τ‖ * Real.exp (-(|y| * δ))) := by
      intro x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      have hF' := hF x y (by linarith [hx.1]) hx.2 hy2
      have hk := norm_offKernel_le hτre0 hτ1 (x := x) (y := y) (by linarith [hx.1]) hx.2
        (by linarith)
      simp only [hh]
      rw [norm_mul]
      exact mul_le_mul hF' hk (norm_nonneg _) (by positivity)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [show |(3 / 2 : ℝ) - 1 / 2| = 1 by norm_num, mul_one] at h1
    have h2 := mul_rpow_half_exp_le (ε := ε) (u := |y|) hε.le (abs_nonneg y) hδ0
    calc ε * ‖∫ x in (1 / 2 : ℝ)..(3 / 2), h ((x : ℂ) + (y : ℂ) * I)‖
        ≤ ε * (CF * (1 + |y|) ^ (1 / 2 : ℝ) * (K₀ * ‖τ‖ * Real.exp (-(|y| * δ)))) := by gcongr
      _ = CF * K₀ * ‖τ‖ * (ε * ((1 + |y|) ^ (1 / 2 : ℝ) * Real.exp (-(|y| * δ)))) := by ring
      _ ≤ CF * K₀ * ‖τ‖ * (ε + ε * δ⁻¹) := by gcongr
      _ ≤ CF * K₀ * M * (1 + M) := by
          rw [hεδ]
          have : ε + ‖τ‖ ≤ 1 + M := by linarith
          gcongr
  have hBot' := hedge (2 * a) h2a.le
  have hTop' := hedge (-2) le_rfl
  have hLb : ε * ‖L‖ ≤ B₁ := by
    calc ε * ‖L‖ ≤ ε * ‖Bot‖ + ε * ‖Top‖ + ε * ‖R‖ := by
          have := mul_le_mul_of_nonneg_left hLnorm hε.le; linarith
      _ ≤ CF * K₀ * M * (1 + M) + CF * K₀ * M * (1 + M) + Real.exp S * K₀ * M ^ 2 := by
          gcongr
      _ = B₁ := by rw [hB₁]; ring
  rw [hsplit, hchange, norm_mul, hεn]
  calc ε * ‖(2 : ℝ)⁻¹ • L + ∫ t in (-1 : ℝ)..0, f t‖
      ≤ ε * (‖L‖ / 2 + B₀) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add ?_ (hnear (-1) le_rfl (by norm_num)))
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]; ring_nf; rfl
    _ = (ε * ‖L‖) / 2 + ε * B₀ := by ring
    _ ≤ B₁ / 2 + 1 * B₀ := by gcongr
    _ = B₁ / 2 + B₀ := by ring

end

end TruncatedRadial

end RHTower
