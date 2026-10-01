import GaloisForLFunctions.RHTower.SuzukiMellinConvolution
import GaloisForLFunctions.RHTower.ThetaSymmetryMellinConverse

/-!
# The inverse Mellin kernels of `Γℝ(s)^{d+1}` and Hecke's converse step in every degree

`K₀(x) = 2e^{-πx²}` has Mellin transform `Γℝ(s)`, and `K_{d+1} = K_d ⋆ K₀` (multiplicative
convolution on `(0, ∞)`) has Mellin transform `Γℝ(s)^{d+2}` on `Re s > 0`
(`hasMellin_gammaRPowKernel`). Each `K_d` is continuous on `(0, ∞)` and satisfies
`|K_d(x)| ≤ C_c x^{-c}` for every `c > 0`: the Gaussian bound
`x^c e^{-πx²} ≤ (c/2πe)^{c/2}` propagates through the convolution because the Mellin integrals
`∫ y^{c-1}|K_d(y)| dy` converge.

With these bounds, a theta series `θ(y) = Σ_{n≥1} e_n K_d(n y)` with polynomially bounded
coefficients and the symmetry `θ(1/y) = y θ(y)` has an entire Mellin transform
`Λ(s) = Γℝ(s)^{d+1} Σ e_n n^{-s}` (on `Re s > A + 1`) with `Λ(1 - s) = Λ(s)`
(`gammaRPow_theta_converse`). For `d = 2` this is the final step of the proof that the functional
equation of `ζ(s)³` has infinitely many independent Dirichlet-series solutions.
-/

open Complex MeasureTheory Set Asymptotics Filter Topology

noncomputable section

namespace RHTower

/-- The Gaussian `2e^{-πx²}`, whose Mellin transform is `Γℝ`. -/
def gaussKernel (x : ℝ) : ℂ := 2 * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)

/-- The Gaussian kernel is continuous. -/
theorem continuous_gaussKernel : Continuous gaussKernel := by
  unfold gaussKernel; fun_prop

/-- `|2e^{-πx²}| = 2e^{-πx²}`. -/
theorem norm_gaussKernel (x : ℝ) : ‖gaussKernel x‖ = 2 * Real.exp (-Real.pi * x ^ 2) := by
  unfold gaussKernel
  rw [norm_mul, Complex.norm_exp]
  have h : (-(Real.pi : ℂ) * (x : ℂ) ^ 2).re = -Real.pi * x ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h]; norm_num

/-- The Gaussian kernel has absolutely convergent Mellin transform on `Re s > 0`. -/
theorem mellinConvergent_gaussKernel {s : ℂ} (hs : 0 < s.re) : MellinConvergent gaussKernel s := by
  refine mellinConvergent_of_isBigO_rpow_exp (a := Real.pi) (b := 0) Real.pi_pos
    (continuous_gaussKernel.continuousOn.locallyIntegrableOn measurableSet_Ioi) ?_ ?_ hs
  · rw [isBigO_iff]
    refine ⟨2, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [norm_gaussKernel, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : -Real.pi * x ^ 2 ≤ -Real.pi * x := by
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith : (0 : ℝ) ≤ x))
        (by linarith : (0 : ℝ) ≤ x - 1)]
    have h2 := Real.exp_le_exp.mpr h1
    linarith
  · rw [isBigO_iff]
    refine ⟨2, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [norm_gaussKernel, neg_zero, Real.rpow_zero, norm_one, mul_one]
    have : Real.exp (-Real.pi * x ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, sq_nonneg x]
    linarith

/-- `∫₀^∞ 2e^{-πx²} x^{s-1} dx = Γℝ(s)`. -/
theorem mellin_gaussKernel {s : ℂ} (hs : 0 < s.re) : mellin gaussKernel s = Gammaℝ s := by
  set f : ℝ → ℂ := fun u => 2 * Complex.exp (-(Real.pi : ℂ) * (u : ℂ)) with hf
  have h1 : mellin gaussKernel s = mellin (fun t : ℝ => f (t ^ (2 : ℝ))) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    simp only [hf, gaussKernel, Real.rpow_two]
    push_cast
    ring_nf
  have h2 := mellin_comp_rpow f s 2
  have hs2 : 0 < (s / 2).re := by
    rw [show (s / 2).re = s.re / 2 by simp]; linarith
  have h3 : mellin f (s / ((2 : ℝ) : ℂ))
      = 2 * ((1 / (Real.pi : ℂ)) ^ (s / 2) * Complex.Gamma (s / 2)) := by
    rw [show (s / ((2 : ℝ) : ℂ)) = s / 2 by push_cast; ring]
    rw [← integral_cpow_mul_exp_neg_mul_Ioi hs2 Real.pi_pos, ← integral_const_mul]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [hf, smul_eq_mul]
    ring_nf
  rw [h1, h2, h3, Gammaℝ_def]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  rw [one_div, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.real_smul,
    show |(2 : ℝ)|⁻¹ = (1 / 2 : ℝ) by norm_num]
  push_cast
  ring_nf

/-- `HasMellin` form of the Gaussian identity. -/
theorem hasMellin_gaussKernel {s : ℂ} (hs : 0 < s.re) : HasMellin gaussKernel s (Gammaℝ s) :=
  ⟨mellinConvergent_gaussKernel hs, mellin_gaussKernel hs⟩

/-- Power bound `|2e^{-πx²}| ≤ 2 (c/(2πe))^{c/2} x^{-c}` for every `c > 0`. -/
theorem norm_gaussKernel_le_rpow {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    ‖gaussKernel x‖ ≤ 2 * Real.exp (-(c / 2) - (c / 2) * Real.log (2 * Real.pi / c)) * x ^ (-c) := by
  rw [norm_gaussKernel]
  have hk : 0 < 2 * Real.pi / c := by positivity
  have hlog := Real.log_le_sub_one_of_pos (mul_pos hk (pow_pos hx 2))
  rw [Real.log_mul hk.ne' (pow_pos hx 2).ne', Real.log_pow] at hlog
  have hkey : c * Real.log x - Real.pi * x ^ 2 ≤ -(c / 2) - (c / 2) * Real.log (2 * Real.pi / c) := by
    have : (2 * Real.pi / c) * x ^ 2 * c = 2 * Real.pi * x ^ 2 := by field_simp
    nlinarith [this]
  have hxc : x ^ (-c) = Real.exp (-(c * Real.log x)) := by
    rw [Real.rpow_def_of_pos hx]; ring_nf
  rw [hxc, mul_assoc, ← Real.exp_add]
  gcongr
  linarith

/-- The kernels `K₀ = 2e^{-πx²}`, `K_{d+1} = K_d ⋆ K₀` (multiplicative convolution on `(0,∞)`). -/
def gammaRPowKernel : ℕ → ℝ → ℂ
  | 0 => gaussKernel
  | d + 1 => positiveMellinConvolution (gammaRPowKernel d) gaussKernel

/-- Each kernel is measurable. -/
theorem measurable_gammaRPowKernel (d : ℕ) : Measurable (gammaRPowKernel d) := by
  induction d with
  | zero => exact continuous_gaussKernel.measurable
  | succ d ih =>
    show Measurable (fun x : ℝ => ∫ y in Ioi (0 : ℝ), gammaRPowKernel d y * gaussKernel (x / y) / y)
    have hF : StronglyMeasurable (Function.uncurry fun (x y : ℝ) =>
        gammaRPowKernel d y * gaussKernel (x / y) / (y : ℂ)) := by
      apply Measurable.stronglyMeasurable
      have h1 : Measurable fun p : ℝ × ℝ => gammaRPowKernel d p.2 := ih.comp measurable_snd
      have h2 : Measurable fun p : ℝ × ℝ => gaussKernel (p.1 / p.2) :=
        continuous_gaussKernel.measurable.comp (measurable_fst.div measurable_snd)
      have h3 : Measurable fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp measurable_snd
      exact (h1.mul h2).div h3
    exact (hF.integral_prod_right (ν := volume.restrict (Ioi 0))).measurable

/-- `K_d` has Mellin transform `Γℝ(s)^{d+1}` on `Re s > 0`. -/
theorem hasMellin_gammaRPowKernel (d : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (gammaRPowKernel d) s (Gammaℝ s ^ (d + 1)) := by
  induction d with
  | zero =>
    rw [zero_add, pow_one]
    exact hasMellin_gaussKernel hs
  | succ d ih =>
    have h := hasMellin_positiveMellinConvolution (measurable_gammaRPowKernel d)
      continuous_gaussKernel.measurable ih.1 (mellinConvergent_gaussKernel hs)
    rw [ih.2, mellin_gaussKernel hs, ← pow_succ] at h
    exact h

private theorem integrableOn_rpow_mul_norm_of_mellinConvergent {f : ℝ → ℂ} {c : ℝ}
    (h : MellinConvergent f (c : ℂ)) :
    IntegrableOn (fun y : ℝ => y ^ (c - 1) * ‖f y‖) (Ioi 0) := by
  have h' : IntegrableOn (fun y : ℝ => ‖(y : ℂ) ^ ((c : ℂ) - 1) • f y‖) (Ioi 0) := h.norm
  refine h'.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy' : (0 : ℝ) < y := hy
  show ‖(y : ℂ) ^ ((c : ℂ) - 1) • f y‖ = y ^ (c - 1) * ‖f y‖
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hy']
  simp

/-- Pointwise power bounds: for every `c > 0`, `|K_d(x)| ≤ C x^{-c}` on `x > 0`. -/
theorem exists_norm_gammaRPowKernel_le (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → ‖gammaRPowKernel d x‖ ≤ C * x ^ (-c) := by
  cases d with
  | zero => exact ⟨_, fun x hx => norm_gaussKernel_le_rpow hc hx⟩
  | succ d =>
    set C₀ := 2 * Real.exp (-(c / 2) - (c / 2) * Real.log (2 * Real.pi / c)) with hC₀
    have hconv : MellinConvergent (gammaRPowKernel d) (c : ℂ) :=
      (hasMellin_gammaRPowKernel d (s := (c : ℂ)) (by simpa using hc)).1
    have hint := integrableOn_rpow_mul_norm_of_mellinConvergent hconv
    set M := ∫ y in Ioi (0 : ℝ), y ^ (c - 1) * ‖gammaRPowKernel d y‖ with hM
    refine ⟨C₀ * M, fun x hx => ?_⟩
    show ‖∫ y in Ioi (0 : ℝ), gammaRPowKernel d y * gaussKernel (x / y) / y‖ ≤ _
    calc _ ≤ ∫ y in Ioi (0 : ℝ), ‖gammaRPowKernel d y * gaussKernel (x / y) / y‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y in Ioi (0 : ℝ), C₀ * x ^ (-c) * (y ^ (c - 1) * ‖gammaRPowKernel d y‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          (hint.const_mul _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy' : (0 : ℝ) < y := hy
        have hg := norm_gaussKernel_le_rpow hc (div_pos hx hy')
        rw [← hC₀] at hg
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy']
        have hxy : (x / y) ^ (-c) = x ^ (-c) * y ^ c := by
          rw [Real.div_rpow hx.le hy'.le, Real.rpow_neg hx.le, Real.rpow_neg hy'.le]; field_simp
        have hyc : y ^ c = y ^ (c - 1) * y := by
          rw [Real.rpow_sub_one hy'.ne']; field_simp
        calc ‖gammaRPowKernel d y‖ * ‖gaussKernel (x / y)‖ / y
            ≤ ‖gammaRPowKernel d y‖ * (C₀ * (x / y) ^ (-c)) / y := by gcongr
          _ = C₀ * x ^ (-c) * (y ^ (c - 1) * ‖gammaRPowKernel d y‖) := by
            rw [hxy, hyc]; field_simp
      _ = C₀ * M * x ^ (-c) := by rw [integral_const_mul]; ring

/-- Each kernel is continuous on `(0, ∞)`. -/
theorem continuousOn_gammaRPowKernel (d : ℕ) : ContinuousOn (gammaRPowKernel d) (Ioi 0) := by
  cases d with
  | zero => exact continuous_gaussKernel.continuousOn
  | succ d =>
    intro x₀ hx₀
    have hx₀' : (0 : ℝ) < x₀ := hx₀
    set a := x₀ / 2 with ha
    have ha0 : 0 < a := by positivity
    set C₁ := 2 * Real.exp (-(1 / 2) - (1 / 2) * Real.log (2 * Real.pi / 1)) with hC₁
    have hconv : MellinConvergent (gammaRPowKernel d) ((1 : ℝ) : ℂ) :=
      (hasMellin_gammaRPowKernel d (s := ((1 : ℝ) : ℂ)) (by simp)).1
    have hint := integrableOn_rpow_mul_norm_of_mellinConvergent hconv
    simp only [sub_self, Real.rpow_zero, one_mul] at hint
    have hcont : ContinuousOn (fun x : ℝ => ∫ y in Ioi (0 : ℝ),
        gammaRPowKernel d y * gaussKernel (x / y) / y) (Icc a (2 * x₀)) := by
      refine continuousOn_of_dominated (bound := fun y => C₁ * a⁻¹ * ‖gammaRPowKernel d y‖)
        (fun x _ => ?_) (fun x hx => ?_) (hint.const_mul _) ?_
      · exact (((measurable_gammaRPowKernel d).mul
          (continuous_gaussKernel.measurable.comp (measurable_const.div measurable_id))).div
          Complex.measurable_ofReal).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy' : (0 : ℝ) < y := hy
        have hxpos : 0 < x := lt_of_lt_of_le ha0 hx.1
        have hg := norm_gaussKernel_le_rpow (c := 1) one_pos (div_pos hxpos hy')
        rw [← hC₁] at hg
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy']
        have hxy : (x / y) ^ (-(1 : ℝ)) = y / x := by
          rw [Real.rpow_neg_one, inv_div]
        rw [hxy] at hg
        have hC₁0 : 0 ≤ C₁ := by positivity
        calc ‖gammaRPowKernel d y‖ * ‖gaussKernel (x / y)‖ / y
            ≤ ‖gammaRPowKernel d y‖ * (C₁ * (y / x)) / y := by gcongr
          _ = C₁ * x⁻¹ * ‖gammaRPowKernel d y‖ := by field_simp
          _ ≤ C₁ * a⁻¹ * ‖gammaRPowKernel d y‖ := by
            gcongr
            exact hx.1
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy' : (0 : ℝ) < y := hy
        refine ContinuousOn.div_const (ContinuousOn.mul continuousOn_const ?_) _
        exact (continuous_gaussKernel.comp (continuous_id.div_const y)).continuousOn
    have hnhds : Icc a (2 * x₀) ∈ 𝓝 x₀ := Icc_mem_nhds (by rw [ha]; linarith) (by linarith)
    exact (hcont.continuousAt hnhds).continuousWithinAt

private theorem summable_succ_rpow {p : ℝ} (hp : p < -1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ p := by
  have := (Real.summable_nat_rpow (p := p)).mpr hp
  exact ((summable_nat_add_iff 1).mpr this).congr (fun n => by push_cast; ring_nf)

/-- Termwise bound for the theta series of `K_d`: `|e_n K_d((n+1)y)| ≤ C' y^{-c} (n+1)^{A-c}`. -/
private theorem norm_theta_term_le (d : ℕ) {e : ℕ → ℂ} {A C c : ℝ} (_hc : 0 < c)
    (he : ∀ n : ℕ, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ A) {K : ℝ}
    (hK : ∀ x : ℝ, 0 < x → ‖gammaRPowKernel d x‖ ≤ K * x ^ (-c)) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖e n * gammaRPowKernel d (((n : ℝ) + 1) * y)‖ ≤ C * K * y ^ (-c) * ((n : ℝ) + 1) ^ (A - c) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hK0 : 0 ≤ K := by
    have := hK 1 one_pos; rw [Real.one_rpow, mul_one] at this; exact le_trans (norm_nonneg _) this
  rw [norm_mul]
  have h1 := hK _ (mul_pos hn hy)
  rw [Real.mul_rpow hn.le hy.le] at h1
  have hC0 : 0 ≤ C := by
    have := he 0; simp at this; exact le_trans (norm_nonneg _) this
  calc ‖e n‖ * ‖gammaRPowKernel d (((n : ℝ) + 1) * y)‖
      ≤ (C * ((n : ℝ) + 1) ^ A) * (K * (((n : ℝ) + 1) ^ (-c) * y ^ (-c))) :=
        mul_le_mul (he n) h1 (norm_nonneg _) (by positivity)
    _ = C * K * y ^ (-c) * ((n : ℝ) + 1) ^ (A - c) := by
        rw [Real.rpow_sub hn, Real.rpow_neg hn.le]; field_simp

/-- **Claim 0 for `Γℝ(s)^{d+1}`.** Let `θ(y) = Σ_{n≥1} e_n K_d(n y)` with `|e_n| ≤ C n^A` satisfy
`θ(1/y) = y θ(y)`. Then `Λ = mellin θ` is entire, `Λ(1 - s) = Λ(s)`, and
`Λ(s) = Γℝ(s)^{d+1} Σ e_n n^{-s}` for `Re s > A + 1`. -/
theorem gammaRPow_theta_converse (d : ℕ) {e : ℕ → ℂ} {A C : ℝ} (hA : 0 ≤ A)
    (he : ∀ n : ℕ, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    (hsym : ∀ y : ℝ, 0 < y →
      (∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * (1 / y)))
        = (y : ℂ) * ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) :
    Differentiable ℂ (mellin fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) ∧
    (∀ s : ℂ, mellin (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) (1 - s)
      = mellin (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) s) ∧
    (∀ s : ℂ, A + 1 < s.re →
      mellin (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) s
        = (∑' n : ℕ, e n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * Gammaℝ s ^ (d + 1)) := by
  -- continuity on `(0, ∞)`
  have hθc : ContinuousOn (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y))
      (Ioi 0) := by
    intro y₀ hy₀
    have hy₀' : (0 : ℝ) < y₀ := hy₀
    set c : ℝ := max (A + 2) 1 with hc
    have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨K, hK⟩ := exists_norm_gammaRPowKernel_le d hc0
    have hK0 : 0 ≤ K := by
      have := hK 1 one_pos; rw [Real.one_rpow, mul_one] at this; exact le_trans (norm_nonneg _) this
    have hC0 : 0 ≤ C := by
      have := he 0; simp at this; exact le_trans (norm_nonneg _) this
    set a := y₀ / 2 with ha
    have ha0 : 0 < a := by positivity
    have hon : ContinuousOn (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y))
        (Ici a) := by
      refine continuousOn_tsum (u := fun n : ℕ => C * K * a ^ (-c) * ((n : ℝ) + 1) ^ (A - c))
        (f := fun (n : ℕ) (y : ℝ) => e n * gammaRPowKernel d (((n : ℝ) + 1) * y))
        (fun n => ?_) ?_ (fun n y hy => ?_)
      · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        refine ContinuousOn.mul continuousOn_const ?_
        have hlin : ContinuousOn (fun y : ℝ => ((n : ℝ) + 1) * y) (Ici a) :=
          (continuous_const.mul continuous_id).continuousOn
        refine (continuousOn_gammaRPowKernel d).comp hlin (fun y hy => ?_)
        exact mul_pos hn (lt_of_lt_of_le ha0 hy)
      · exact (summable_succ_rpow (by rw [hc]; have := le_max_left (A + 2) 1; linarith)).mul_left _
      · have hy' : 0 < y := lt_of_lt_of_le ha0 hy
        refine (norm_theta_term_le d hc0 he hK n hy').trans ?_
        have hyc : y ^ (-c) ≤ a ^ (-c) :=
          Real.rpow_le_rpow_of_nonpos ha0 hy (by linarith)
        have hnn : 0 ≤ ((n : ℝ) + 1) ^ (A - c) := by positivity
        have hCK : 0 ≤ C * K := mul_nonneg hC0 hK0
        calc C * K * y ^ (-c) * ((n : ℝ) + 1) ^ (A - c)
            ≤ C * K * a ^ (-c) * ((n : ℝ) + 1) ^ (A - c) := by gcongr
          _ = _ := rfl
    have hnhds : Ici a ∈ 𝓝 y₀ := Ici_mem_nhds (by rw [ha]; linarith)
    exact (hon.continuousAt hnhds).continuousWithinAt
  -- rapid decay at infinity
  have hθdec : ∀ a : ℝ, (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y))
      =O[atTop] fun x : ℝ => x ^ (-a) := by
    intro a
    set c : ℝ := max (A + 2) (max a 1) with hc
    have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
    have hca : a ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
    obtain ⟨K, hK⟩ := exists_norm_gammaRPowKernel_le d hc0
    have hsum := summable_succ_rpow (p := A - c) (by have := le_max_left (A + 2) (max a 1); linarith)
    rw [Asymptotics.isBigO_iff]
    refine ⟨C * K * ∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c), ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hbound := tsum_of_norm_bounded ((hsum.mul_left (C * K * y ^ (-c))).hasSum)
      (fun n => norm_theta_term_le d hc0 he hK n hy0)
    rw [tsum_mul_left] at hbound
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
    have hyc : y ^ (-c) ≤ y ^ (-a) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    have hS : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c) := tsum_nonneg (fun n => by positivity)
    have hK0 : 0 ≤ K := by
      have := hK 1 one_pos; rw [Real.one_rpow, mul_one] at this; exact le_trans (norm_nonneg _) this
    have hC0 : 0 ≤ C := by
      have := he 0; simp at this; exact le_trans (norm_nonneg _) this
    calc ‖∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)‖
        ≤ C * K * y ^ (-c) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c) := hbound
      _ ≤ C * K * y ^ (-a) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c) := by gcongr
      _ = C * K * (∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c)) * y ^ (-a) := by ring
  obtain ⟨h1, h2, h3⟩ := hecke_theta_converse (continuousOn_gammaRPowKernel d) he hθc hθdec hsym
  refine ⟨h1, h2, fun s hs => ?_⟩
  have hs0 : 0 < s.re := by linarith
  have hmel := hasMellin_gammaRPowKernel d hs0
  have hKint : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖gammaRPowKernel d t‖) (Ioi 0) :=
    integrableOn_rpow_mul_norm_of_mellinConvergent
      (hasMellin_gammaRPowKernel d (s := ((s.re : ℝ) : ℂ)) (by simpa using hs0)).1
  rw [h3 s hs hKint, hmel.2]

end RHTower
