import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversionGeneralLine

/-!
# The Gaussian Mellin–Barnes kernel

`K(y, w) = ½ Γ(w/2) y^{-w/2}` is the Mellin–Barnes kernel of the Gaussian: on every vertical line
`w = c + iv`, `c > 0`,

* `v ↦ ‖K(y, c + iv)‖ (1 + |v|)^N` is integrable (`integrable_norm_gaussianMBKernel_mul_pow`), by
  Stirling-type decay of `Γ` on vertical lines;
* `(1/2π) ∫ K(y, c + iv) dv = e^{-y}` (`gaussianMBKernel_line_integral`), Cahen–Mellin after
  `w = 2u`.

Consequences:

* **Incomplete Gaussian Mellin transform** (`gaussianIncompleteMellin_eq_line_integral`): for
  `Re a < c`, `∫_1^∞ e^{-y u²} u^{a-1} du = (1/2π) ∫ K(y, c + iv) / (c + iv − a) dv`.  Proof:
  `1/(w − a) = ∫_1^∞ u^{a-w-1} du`, Fubini, and `K(y, w) u^{-w} = K(y u², w)`.
* **Dirichlet series** (`tsum_term_mul_exp_neg_eq_line_integral`):
  `Σ_{n≥1} f(n) n^{-s} e^{-y n²} = (1/2π) ∫ K(y, c + iv) L(f, s + c + iv) dv` when
  `Σ ‖f(n)‖ n^{-(Re s + c)} < ∞`.
* `a ↦ ∫_1^∞ e^{-y u²} u^{a-1} du` is entire (`differentiable_gaussianIncompleteMellin`), being the
  Mellin transform of a function vanishing near `0` and decaying faster than `e^{-u}`.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- The Gaussian Mellin–Barnes kernel `½ Γ(w/2) y^{-w/2}`. -/
def gaussianMBKernel (y : ℝ) (w : ℂ) : ℂ :=
  (1 / 2) * Complex.Gamma (w / 2) * (y : ℂ) ^ (-(w / 2))

/-- The incomplete Gaussian Mellin transform `∫_1^∞ e^{-y u²} u^{a-1} du`. -/
def gaussianIncompleteMellin (y : ℝ) (a : ℂ) : ℂ :=
  ∫ u in Set.Ici (1 : ℝ), (Real.exp (-y * u ^ 2) : ℂ) * (u : ℂ) ^ (a - 1)

/-! ## Decay of `Γ` on a vertical line -/

/-- `‖Γ(c + it)‖ ≤ B (1 + |t|)^N e^{-π|t|/2}` on the line `Re = c > 0`. -/
theorem exists_norm_Gamma_line_le {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, ∃ N : ℕ, 0 ≤ B ∧ ∀ t : ℝ,
      ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ ≤
        B * ((1 + |t|) ^ N * Real.exp (-(Real.pi / 2) * |t|)) := by
  obtain ⟨C, N, hC0, hGamma⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip (a := c) hc c
  set r : ℝ := Real.pi / 2 with hr
  refine ⟨max C (Real.Gamma c * Real.exp r), N, le_trans hC0 (le_max_left _ _), fun t => ?_⟩
  set B := max C (Real.Gamma c * Real.exp r)
  have hE : 0 < Real.exp (-r * |t|) := Real.exp_pos _
  by_cases ht : 1 ≤ |t|
  · have hΓ := hGamma c t le_rfl le_rfl ht
    have hpow : |t| ^ N ≤ (1 + |t|) ^ N :=
      pow_le_pow_left₀ (abs_nonneg t) (by linarith [abs_nonneg t]) N
    have hexp : Real.exp (-(Real.pi * |t| / 2)) = Real.exp (-r * |t|) := by
      rw [hr]; ring_nf
    calc ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖
        ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := hΓ
      _ ≤ B * ((1 + |t|) ^ N * Real.exp (-r * |t|)) := by
        rw [hexp]
        have hCB : C ≤ B := le_max_left _ _
        have h1 : C * |t| ^ N ≤ B * (1 + |t|) ^ N :=
          mul_le_mul hCB hpow (pow_nonneg (abs_nonneg t) N) (le_trans hC0 hCB)
        nlinarith
  · have htlt : |t| < 1 := lt_of_not_ge ht
    have hΓc : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ ≤ Real.Gamma c := by
      have hΓ := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re
        (s := (c : ℂ) + (t : ℂ) * I) (by simpa using hc)
      simpa using hΓ
    have hrecover : 1 ≤ Real.exp r * Real.exp (-r * |t|) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ r := by rw [hr]; positivity
      nlinarith [abs_nonneg t]
    have hbase : 1 ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
    have hg0 : 0 ≤ Real.Gamma c := (Real.Gamma_pos_of_pos hc).le
    have hBB : Real.Gamma c * Real.exp r ≤ B := le_max_right _ _
    calc ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ ≤ Real.Gamma c := hΓc
      _ ≤ Real.Gamma c * (Real.exp r * Real.exp (-r * |t|)) := le_mul_of_one_le_right hg0 hrecover
      _ ≤ Real.Gamma c * Real.exp r * ((1 + |t|) ^ N * Real.exp (-r * |t|)) := by
        have := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE.le hbase)
          (mul_nonneg hg0 (Real.exp_pos r).le)
        nlinarith
      _ ≤ B * ((1 + |t|) ^ N * Real.exp (-r * |t|)) :=
        mul_le_mul_of_nonneg_right hBB (by positivity)

theorem half_line (c v : ℝ) : ((c : ℂ) + (v : ℂ) * I) / 2 = ((c / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I := by
  push_cast; ring

theorem norm_gaussianMBKernel_line {y : ℝ} (hy : 0 < y) (c v : ℝ) :
    ‖gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I)‖ =
      1 / 2 * ‖Complex.Gamma (((c / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖ * y ^ (-(c / 2)) := by
  rw [gaussianMBKernel, norm_mul, norm_mul, half_line, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  norm_num

theorem continuous_gaussianMBKernel_line {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Continuous fun v : ℝ => gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) := by
  unfold gaussianMBKernel
  refine (continuous_const.mul ?_).mul ?_
  · rw [continuous_iff_continuousAt]
    intro v
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).continuousAt.comp (by fun_prop)
    have hre := congrArg Complex.re hm
    simp at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne'))

/-- **(K1)** Polynomially weighted integrability of the kernel on a vertical line. -/
theorem integrable_norm_gaussianMBKernel_mul_pow {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (N : ℕ) :
    Integrable fun v : ℝ => ‖gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I)‖ * (1 + |v|) ^ N := by
  obtain ⟨B, N₀, hB, hΓ⟩ := exists_norm_Gamma_line_le (by linarith : 0 < c / 2)
  have hmaj : Integrable fun v : ℝ =>
      (1 / 2 * y ^ (-(c / 2)) * B) * ((1 + |v|) ^ (N₀ + N) * Real.exp (-(Real.pi / 4) * |v|)) :=
    (GaloisForLFunctions.SelbergClass.integrable_one_add_abs_pow_mul_exp_neg_abs (N₀ + N)
      (by positivity : 0 < Real.pi / 4)).const_mul _
  refine hmaj.mono' (((continuous_gaussianMBKernel_line hy hc).norm.mul
    (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_gaussianMBKernel_line hy]
  have h1 := hΓ (v / 2)
  have hv2 : |v / 2| ≤ |v| := by rw [abs_div, abs_two]; linarith [abs_nonneg v]
  have hpow : (1 + |v / 2|) ^ N₀ ≤ (1 + |v|) ^ N₀ :=
    pow_le_pow_left₀ (by positivity) (by linarith) N₀
  have hexp : Real.exp (-(Real.pi / 2) * |v / 2|) = Real.exp (-(Real.pi / 4) * |v|) := by
    rw [abs_div, abs_two]; ring_nf
  have hyc : 0 < y ^ (-(c / 2)) := Real.rpow_pos_of_pos hy _
  have hΓ' : ‖Complex.Gamma (((c / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖ ≤
      B * ((1 + |v|) ^ N₀ * Real.exp (-(Real.pi / 4) * |v|)) := by
    rw [← hexp]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) hB)
  have hsplit : (1 + |v|) ^ (N₀ + N) = (1 + |v|) ^ N₀ * (1 + |v|) ^ N := pow_add _ _ _
  rw [hsplit]
  have hN : 0 ≤ (1 + |v|) ^ N := by positivity
  calc 1 / 2 * ‖Complex.Gamma (((c / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖ * y ^ (-(c / 2)) *
        (1 + |v|) ^ N
      ≤ 1 / 2 * (B * ((1 + |v|) ^ N₀ * Real.exp (-(Real.pi / 4) * |v|))) * y ^ (-(c / 2)) *
        (1 + |v|) ^ N := by gcongr
    _ = _ := by ring

theorem integrable_gaussianMBKernel_line {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Integrable fun v : ℝ => gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) := by
  refine (integrable_norm_gaussianMBKernel_mul_pow hy hc 0).mono'
    (continuous_gaussianMBKernel_line hy hc).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  simp

/-- **(K2)** Cahen–Mellin on the line `Re w = c`: `(1/2π) ∫ K(y, c + iv) dv = e^{-y}`. -/
theorem gaussianMBKernel_line_integral {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) =
      (Real.exp (-y) : ℂ) := by
  set g : ℝ → ℂ := fun t => (y : ℂ) ^ (-(((c / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
    Complex.Gamma (((c / 2 : ℝ) : ℂ) + (t : ℂ) * I) with hg
  have hK : ∀ v : ℝ, gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) = (1 / 2 : ℂ) * g ((1 / 2) * v) := by
    intro v
    rw [gaussianMBKernel, half_line, hg]
    simp only
    rw [show (v / 2 : ℝ) = 1 / 2 * v by ring]
    ring
  simp_rw [hK]
  rw [integral_const_mul, Measure.integral_comp_mul_left g (1 / 2)]
  have hinv := GaloisForLFunctions.SelbergClass.mellinInv_line_Gamma_eq_exp_neg
    (by linarith : 0 < c / 2) hy
  unfold mellinInv at hinv
  have hIg : (∫ t : ℝ, (y : ℂ) ^ (-(((c / 2 : ℝ) : ℂ) + (t : ℂ) * I)) •
      Complex.Gamma (((c / 2 : ℝ) : ℂ) + (t : ℂ) * I)) = ∫ t : ℝ, g t := rfl
  rw [hIg, Complex.real_smul] at hinv
  obtain ⟨Ig, hIgdef⟩ : ∃ Ig : ℂ, Ig = ∫ t : ℝ, g t := ⟨_, rfl⟩
  rw [← hIgdef] at hinv ⊢
  rw [Complex.ofReal_exp, Complex.ofReal_neg, ← hinv,
    show |(1 / 2 : ℝ)⁻¹| = 2 by norm_num, Complex.real_smul]
  push_cast
  ring

/-! ## Dilation by `u²` -/

theorem ofReal_sq_cpow {u : ℝ} (hu : 0 < u) (w : ℂ) :
    (((u ^ 2 : ℝ)) : ℂ) ^ (-(w / 2)) = (u : ℂ) ^ (-w) := by
  have hu2 : (((u ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hu 2).ne'
  have hu1 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [Complex.cpow_def_of_ne_zero hu2, Complex.cpow_def_of_ne_zero hu1,
    ← Complex.ofReal_log (pow_pos hu 2).le, ← Complex.ofReal_log hu.le, Real.log_pow]
  push_cast
  ring_nf

/-- `K(y, w) u^{-w} = K(y u², w)` for `u > 0`. -/
theorem gaussianMBKernel_mul_cpow_neg {y u : ℝ} (hy : 0 < y) (hu : 0 < u) (w : ℂ) :
    gaussianMBKernel y w * (u : ℂ) ^ (-w) = gaussianMBKernel (y * u ^ 2) w := by
  unfold gaussianMBKernel
  rw [show (((y * u ^ 2 : ℝ)) : ℂ) = (y : ℂ) * (((u ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg hy.le (pow_pos hu 2).le, ofReal_sq_cpow hu]
  ring

/-- `(1/2π) ∫ K(y, c + iv) u^{-(c+iv)} dv = e^{-y u²}` for `u > 0`. -/
theorem gaussianMBKernel_line_integral_mul_cpow {y c u : ℝ} (hy : 0 < y) (hc : 0 < c)
    (hu : 0 < u) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) * (u : ℂ) ^ (-((c : ℂ) + (v : ℂ) * I)) =
      (Real.exp (-(y * u ^ 2)) : ℂ) := by
  simp_rw [gaussianMBKernel_mul_cpow_neg hy hu]
  exact gaussianMBKernel_line_integral (by positivity) hc

/-! ## The incomplete Gaussian Mellin transform -/

theorem one_div_sub_eq_integral_cpow {w a : ℂ} (h : a.re < w.re) :
    1 / (w - a) = ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (a - w - 1) := by
  have hre : (a - w - 1).re < -1 := by simp; linarith
  rw [integral_Ioi_cpow_of_lt hre one_pos]
  have hne : w - a ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp at this
    linarith
  rw [Complex.ofReal_one, Complex.one_cpow, show a - w - 1 + 1 = -(w - a) by ring]
  field_simp

theorem continuousOn_line_cpow {a : ℂ} {c : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (a - ((c : ℂ) + (p.1 : ℂ) * I) - 1))
      (univ ×ˢ Ioi (1 : ℝ)) := by
  intro p hp
  have hp2 : (1 : ℝ) < p.2 := hp.2
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.cpow (by fun_prop) (by fun_prop) ?_
  exact Or.inl (by simp; linarith)

/-- **(K3)** The incomplete Gaussian Mellin transform as a Mellin–Barnes integral: for `y > 0`,
`c > 0` and `Re a < c`, `∫_1^∞ e^{-yu²} u^{a-1} du = (1/2π) ∫ K(y, c + iv)/(c + iv − a) dv`. -/
theorem gaussianIncompleteMellin_eq_line_integral {y c : ℝ} (hy : 0 < y) (hc : 0 < c) {a : ℂ}
    (ha : a.re < c) :
    gaussianIncompleteMellin y a =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) / (((c : ℂ) + (v : ℂ) * I) - a) := by
  set K : ℝ → ℂ := fun v => gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) with hKdef
  set F : ℝ → ℝ → ℂ := fun v u => K v * (u : ℂ) ^ (a - ((c : ℂ) + (v : ℂ) * I) - 1) with hF
  have hw : ∀ v : ℝ, a.re < ((c : ℂ) + (v : ℂ) * I).re := fun v => by simpa using ha
  -- the integrand as an inner integral
  have hinner : ∀ v : ℝ, gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) / (((c : ℂ) + (v : ℂ) * I) - a) =
      ∫ u in Ioi (1 : ℝ), F v u := by
    intro v
    rw [div_eq_mul_one_div, one_div_sub_eq_integral_cpow (hw v), ← integral_const_mul]
  simp_rw [hinner]
  -- Fubini
  have hprod : (volume : Measure ℝ).prod (volume.restrict (Ioi (1 : ℝ))) =
      ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi (1 : ℝ)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hG : Integrable (fun p : ℝ × ℝ => ‖K p.1‖ * p.2 ^ (a.re - c - 1))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (1 : ℝ)))) :=
    Integrable.mul_prod (by simpa using integrable_norm_gaussianMBKernel_mul_pow hy hc 0)
      (integrableOn_Ioi_rpow_of_lt (a := a.re - c - 1) (by linarith) one_pos)
  have hFint : Integrable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (1 : ℝ)))) := by
    refine hG.mono' ?_ ?_
    · rw [hprod]
      refine ContinuousOn.aestronglyMeasurable ?_ (MeasurableSet.univ.prod measurableSet_Ioi)
      exact ((continuous_gaussianMBKernel_line hy hc).comp continuous_fst).continuousOn.mul
        continuousOn_line_cpow
    · rw [hprod, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioi)]
      refine Eventually.of_forall fun p hp => ?_
      have hp2 : (0 : ℝ) < p.2 := lt_trans one_pos hp.2
      show ‖K p.1 * (p.2 : ℂ) ^ (a - ((c : ℂ) + (p.1 : ℂ) * I) - 1)‖ ≤ _
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp2]
      simp
  rw [integral_integral_swap hFint]
  -- the inner `v`-integral
  have hcol : ∀ u ∈ Ioi (1 : ℝ),
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, F v u =
        (Real.exp (-(y * u ^ 2)) : ℂ) * (u : ℂ) ^ (a - 1) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hu1 : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have hsplit : ∀ v : ℝ, F v u =
        (u : ℂ) ^ (a - 1) * (K v * (u : ℂ) ^ (-((c : ℂ) + (v : ℂ) * I))) := by
      intro v
      simp only [hF]
      rw [show a - ((c : ℂ) + (v : ℂ) * I) - 1 = (a - 1) + -((c : ℂ) + (v : ℂ) * I) by ring,
        Complex.cpow_add _ _ hu1]
      ring
    simp_rw [hsplit]
    rw [integral_const_mul, mul_left_comm, gaussianMBKernel_line_integral_mul_cpow hy hc hu0]
    ring
  rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi hcol, gaussianIncompleteMellin,
    integral_Ici_eq_integral_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  congr 2
  ring_nf

/-! ## The Dirichlet-series version -/

/-- **(K4)** For `Σ ‖f(n)‖ n^{-(Re s + c)} < ∞`,
`Σ_{n ≥ 1} f(n) n^{-s} e^{-y n²} = (1/2π) ∫ K(y, c + iv) L(f, s + c + iv) dv`.  The left side is
written with mathlib's `LSeries.term`, which is `0` at `n = 0`. -/
theorem tsum_term_mul_exp_neg_eq_line_integral {y c : ℝ} (hy : 0 < y) (hc : 0 < c)
    (f : ℕ → ℂ) (s : ℂ) (hf : Summable fun n : ℕ => ‖f n‖ * (n : ℝ) ^ (-(s.re + c))) :
    ∑' n : ℕ, LSeries.term f s n * (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) *
          LSeries f (s + ((c : ℂ) + (v : ℂ) * I)) := by
  set K : ℝ → ℂ := fun v => gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) with hKdef
  set G : ℕ → ℝ → ℂ := fun n v => K v * LSeries.term f (s + ((c : ℂ) + (v : ℂ) * I)) n with hG
  have hnorm : ∀ n : ℕ, ∀ v : ℝ, ‖G n v‖ = ‖K v‖ * (if n = 0 then 0 else ‖f n‖ * (n : ℝ) ^ (-(s.re + c))) := by
    intro n v
    simp only [hG, norm_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_def]
    · rw [LSeries.term_of_ne_zero hn, if_neg hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hKint : Integrable K := integrable_gaussianMBKernel_line hy hc
  have hKnorm : Integrable fun v => ‖K v‖ := hKint.norm
  have hGint : ∀ n, Integrable (G n) := by
    intro n
    refine (hKnorm.mul_const (if n = 0 then 0 else ‖f n‖ * (n : ℝ) ^ (-(s.re + c)))).mono' ?_
      (Eventually.of_forall fun v => (hnorm n v).le)
    exact hKint.aestronglyMeasurable.mul (by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_def, if_pos]; exact aestronglyMeasurable_const
      · simp only [LSeries.term_of_ne_zero hn]
        exact (continuous_const.div (Continuous.const_cpow (by fun_prop)
          (Or.inl (by exact_mod_cast hn))) fun v => by
            simp [hn]).aestronglyMeasurable)
  have hsumm : Summable fun n => ∫ v, ‖G n v‖ := by
    simp_rw [hnorm]
    simp_rw [integral_mul_const]
    refine (hf.mul_left (∫ v, ‖K v‖)).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (integral_nonneg fun v => norm_nonneg _) (by split_ifs <;> positivity)
    · split_ifs with hn
      · rw [mul_zero]; positivity
      · exact le_rfl
  have hLS : ∀ v : ℝ, gaussianMBKernel y ((c : ℂ) + (v : ℂ) * I) *
      LSeries f (s + ((c : ℂ) + (v : ℂ) * I)) = ∑' n, G n v := by
    intro v
    rw [LSeries, ← tsum_mul_left]
  simp_rw [hLS]
  rw [← integral_tsum_of_summable_integral_norm hGint hsumm, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hG, LSeries.term_def]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hsplit : ∀ v : ℝ, G n v =
        LSeries.term f s n * (K v * ((n : ℝ) : ℂ) ^ (-((c : ℂ) + (v : ℂ) * I))) := by
      intro v
      show K v * LSeries.term f (s + ((c : ℂ) + (v : ℂ) * I)) n = _
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hn1,
        Complex.ofReal_natCast, Complex.cpow_neg]
      have h1 : (n : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hn1]; exact Complex.exp_ne_zero _
      field_simp
    simp_rw [hsplit]
    rw [integral_const_mul, mul_left_comm, gaussianMBKernel_line_integral_mul_cpow hy hc hn0]

/-! ## Holomorphy in the exponent -/

/-- **(K5)** `a ↦ ∫_1^∞ e^{-yu²} u^{a-1} du` is entire for `y > 0`. -/
theorem differentiable_gaussianIncompleteMellin {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (gaussianIncompleteMellin y) := by
  set g : ℝ → ℂ := (Ici (1 : ℝ)).indicator fun u => (Real.exp (-y * u ^ 2) : ℂ) with hg
  have hmellin : gaussianIncompleteMellin y = mellin g := by
    funext a
    rw [gaussianIncompleteMellin, mellin, hg]
    simp_rw [smul_eq_mul]
    rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext u
    by_cases hu : (1 : ℝ) ≤ u
    · have hu0 : u ∈ Ioi (0 : ℝ) := lt_of_lt_of_le one_pos hu
      simp [Set.indicator, hu, hu0, mem_Ici, mul_comm]
    · simp [Set.indicator, hu, mem_Ici]
  rw [hmellin]
  intro a
  refine mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := a.re - 1) one_pos ?_ ?_ ?_
    (by linarith)
  · have hcont : Continuous fun u : ℝ => (Real.exp (-y * u ^ 2) : ℂ) := by fun_prop
    exact ((hcont.locallyIntegrable (μ := volume)).indicator measurableSet_Ici).locallyIntegrableOn _
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (max 1 (1 / y))] with u hu
    have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
    have huy : 1 / y ≤ u := le_trans (le_max_right _ _) hu
    simp only [hg, Set.indicator, mem_Ici, if_pos hu1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), one_mul]
    apply Real.exp_le_exp.2
    have : 1 ≤ y * u := by
      rw [div_le_iff₀ hy] at huy; linarith
    nlinarith
  · rw [Asymptotics.isBigO_iff]
    refine ⟨0, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    simp [hg, mem_Ici, not_le.2 hu.2]

end

end RHTower
