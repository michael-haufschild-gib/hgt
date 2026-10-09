import GaloisForLFunctions.RHTower.XiSecondOrderLaguerrePolyaPreimage
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity

/-!
# Strong first-order filters do not produce `Ξ` from the Laguerre–Pólya class

Let `b` be real with `|b| > 4/π`, and let `ψ` be Laguerre–Pólya with `Ξ = ψ − bψ′`.

Then `H(x) = e^{−x/b}ψ(x)` satisfies `H′ = −(1/b)e^{−x/b}Ξ`.  The Laplace weight `e^{−t/b}` grows
more slowly than `Ξ` decays (`|Ξ(t)| ≪ e^{−r|t|}` for every `r < π/4`,
`exists_abs_Xi_le_exp`), so `H` has limits at `±∞`.  By Hardy's theorem `Ξ` has real zeros
arbitrarily far out, and interlacing puts zeros of `ψ` between them.  Hence `H` vanishes along
sequences going to both ends, and

  `∫ e^{−t/b} Ξ(t) dt = 0`   (`integral_exp_mul_Xi_eq_zero_of_sub_smul_deriv`).

The value at `b = ∞` is `∫Ξ = 2πΦ(0) > 0` (Fourier inversion, `integral_Xi_pos`), and the
Laplace integral is continuous in `1/b`.  So for `0 < |a| < a₀` no Laguerre–Pólya `ψ` has
`(1 − D/a)ψ = Ξ` (`exists_pos_not_laguerrePolya_firstOrder_preimage`), and the same holds for any
operator with such a first-order factor (`not_laguerrePolya_secondOrder_preimage_of_small`).
No RH and no zero-density input is used.
-/

open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform Real
open Zeta23
open GaloisForLFunctions.HTGeometry

namespace RHTower.Littlewood

noncomputable section

theorem Xi_neg (t : ℝ) : Xi (-t) = Xi t := by
  have h := XiC_even (t : ℂ)
  rw [← Complex.ofReal_neg, XiC_ofReal, XiC_ofReal] at h
  exact_mod_cast h

theorem continuous_Xi : Continuous Xi := by
  have h : Continuous fun t : ℝ => XiC (t : ℂ) :=
    XiC_differentiable.continuous.comp Complex.continuous_ofReal
  have e : Xi = fun t : ℝ => (XiC (t : ℂ)).re := funext fun t => by rw [XiC_ofReal]; simp
  rw [e]
  exact Complex.continuous_re.comp h

/-- **Decay of `Ξ` on the real line.**  `|Ξ(t)| ≤ K e^{−r|t|}` for `0 ≤ r < π/4`. -/
theorem exists_abs_Xi_le_exp {r : ℝ} (hr0 : 0 ≤ r) (hr : r < π / 4) :
    ∃ K : ℝ, ∀ t : ℝ, |Xi t| ≤ K * Real.exp (-(r * |t|)) := by
  set m : ℂ → ℂ := fun _ => 1 with hmdef
  have hm : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ r → DifferentiableAt ℂ m z :=
    fun _ _ _ => differentiableAt_const _
  have hmb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ r → ‖m z‖ ≤ 1 := fun _ _ _ => by simp [hmdef]
  set K := ∫ u, ‖KernelStrip.shiftedProfile m r u‖
  have hpos : ∀ t : ℝ, 0 ≤ t → |Xi t| ≤ K * Real.exp (-(r * t)) := by
    intro t _
    have he := KernelStrip.exp_mul_kernelPsi_eq hr0 hr hm hmb t
    have hk : KernelStrip.kernelPsi m t = (Xi t : ℂ) := by
      rw [← XiC_ofReal, ← paperFT_riemannPhiKernel_eq_XiC]
      unfold KernelStrip.kernelPsi paperFT
      simp [hmdef]
    rw [hk] at he
    have hb : ‖paperFT (KernelStrip.shiftedProfile m r) t‖ ≤ K := by
      unfold paperFT
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (Eventually.of_forall fun u => ?_)))
      simp only
      rw [norm_mul, show I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_real, Real.norm_eq_abs] at hb
    calc |Xi t| = Real.exp (-(r * t)) * (Real.exp (r * t) * |Xi t|) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp (-(r * t)) * K := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = K * Real.exp (-(r * t)) := mul_comm _ _
  refine ⟨K, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]; exact hpos t ht
  · rw [abs_of_neg ht, ← Xi_neg]; exact hpos (-t) (by linarith)

/-- `t ↦ e^{st}Ξ(t)` is integrable for `|s| < π/4`. -/
theorem integrable_exp_mul_Xi {s : ℝ} (hs : |s| < π / 4) :
    Integrable (fun t => Real.exp (s * t) * Xi t) := by
  set r := (|s| + π / 4) / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hrlt : r < π / 4 := by rw [hr]; linarith
  obtain ⟨K, hK⟩ := exists_abs_Xi_le_exp hr0 hrlt
  have hgap : 0 < r - |s| := by rw [hr]; linarith
  refine ((RHTower.integrable_exp_neg_mul_abs' hgap).const_mul K).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      continuous_Xi).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := hK t
  have hK0 : 0 ≤ K := by
    have := hK 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  calc Real.exp (s * t) * |Xi t| ≤ Real.exp (s * t) * (K * Real.exp (-(r * |t|))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = K * Real.exp (s * t - r * |t|) := by rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ K * Real.exp (-((r - |s|) * |t|)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
        have : s * t ≤ |s| * |t| := by rw [← abs_mul]; exact le_abs_self _
        nlinarith

/-- Hardy's theorem, twice: two real zeros of `Ξ` beyond any height. -/
theorem exists_two_Xi_zeros_gt (T : ℝ) :
    ∃ γ γ' : ℝ, T < γ ∧ γ < γ' ∧ Xi γ = 0 ∧ Xi γ' = 0 := by
  obtain ⟨γ, hγ, h0⟩ := exists_Xi_zero_gt T
  obtain ⟨γ', hγ', h1⟩ := exists_Xi_zero_gt γ
  exact ⟨γ, γ', hγ, hγ', h0, h1⟩

theorem XiC_neg_I_div_two_ne_zero : XiC (-I / 2) ≠ 0 := by
  have e : (1 / 2 : ℂ) + -I / 2 * I = 1 := by ring_nf; rw [Complex.I_sq]; ring
  rw [XiC, e, xi_one]; norm_num

/-- **First-order preimages vanish at both ends.**  If `Ξ = ψ − bψ′` with `ψ` Laguerre–Pólya, then
`ψ` has real zeros beyond every height and below every depth. -/
theorem laguerrePolya_preimage_zeros {ψ : ℂ → ℂ} (hψ : GaloisForLFunctions.HTGeometry.LaguerrePolya ψ) (b : ℝ)
    (h : ∀ z, XiC z = ψ z - (b : ℂ) * deriv ψ z) :
    (∀ T : ℝ, ∃ x : ℝ, T < x ∧ ψ x = 0) ∧ (∀ T : ℝ, ∃ x : ℝ, x < -T ∧ ψ x = 0) := by
  have hnz : ∃ z₀, ψ z₀ - (b : ℂ) * deriv ψ z₀ ≠ 0 :=
    ⟨-I / 2, by rw [← h]; exact XiC_neg_I_div_two_ne_zero⟩
  have hzero : ∀ γ : ℝ, Xi γ = 0 → ψ γ - (b : ℂ) * deriv ψ γ = 0 := by
    intro γ hγ
    rw [← h, XiC_ofReal, hγ, Complex.ofReal_zero]
  constructor
  · intro T
    obtain ⟨γ, γ', hT, hγγ', z, z'⟩ := exists_two_Xi_zeros_gt T
    obtain ⟨x, hx, hψx⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hψ b hnz hγγ'
      (hzero γ z) (hzero γ' z')
    exact ⟨x, by linarith [hx.1], hψx⟩
  · intro T
    obtain ⟨γ, γ', hT, hγγ', z, z'⟩ := exists_two_Xi_zeros_gt T
    have hlt : -γ' < -γ := by linarith
    obtain ⟨x, hx, hψx⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hψ b hnz hlt
      (hzero (-γ') (by rw [Xi_neg]; exact z')) (hzero (-γ) (by rw [Xi_neg]; exact z))
    exact ⟨x, by linarith [hx.2], hψx⟩

/-- **The Laplace obstruction.**  If `Ξ = ψ − bψ′` with `ψ` Laguerre–Pólya, `b ≠ 0` and
`1/|b| < π/4`, then `∫ e^{−t/b} Ξ(t) dt = 0`. -/
theorem integral_exp_mul_Xi_eq_zero_of_sub_smul_deriv {b : ℝ} (hb0 : b ≠ 0)
    (hb : 1 / |b| < π / 4) {ψ : ℂ → ℂ} (hψ : GaloisForLFunctions.HTGeometry.LaguerrePolya ψ)
    (h : ∀ z, XiC z = ψ z - (b : ℂ) * deriv ψ z) :
    ∫ t, Real.exp ((-1 / b) * t) * Xi t = 0 := by
  have hψd : Differentiable ℂ ψ := GaloisForLFunctions.HTGeometry.LaguerrePolya.differentiable hψ
  -- the real restriction and its equation
  set ψr : ℝ → ℝ := fun x => (ψ x).re with hψr
  set ψ1 : ℝ → ℝ := fun x => (deriv ψ x).re with hψ1
  have hd0 : ∀ x : ℝ, HasDerivAt ψr (ψ1 x) x := fun x => (hψd x).hasDerivAt.real_of_complex
  have hode : ∀ x : ℝ, Xi x = ψr x - b * ψ1 x := by
    intro x
    have hx := congrArg Complex.re (h x)
    rw [XiC_ofReal, Complex.ofReal_re, Complex.sub_re, Complex.re_ofReal_mul] at hx
    exact hx
  -- `H(x) = e^{−x/b}ψ(x)` and `H′ = −(1/b)e^{−x/b}Ξ`
  set H : ℝ → ℝ := fun x => Real.exp ((-1 / b) * x) * ψr x with hH
  have hHd : ∀ x : ℝ, HasDerivAt H (-(1 / b) * (Real.exp ((-1 / b) * x) * Xi x)) x := by
    intro x
    have he : HasDerivAt (fun x : ℝ => Real.exp ((-1 / b) * x))
        (Real.exp ((-1 / b) * x) * (-1 / b)) x :=
      ((Real.hasDerivAt_exp ((-1 / b) * x)).comp x ((hasDerivAt_id' x).const_mul (-1 / b))).congr_deriv
        (by ring)
    refine (he.mul (hd0 x)).congr_deriv ?_
    rw [hode x]
    field_simp
    ring
  have hcont : Continuous fun x : ℝ => -(1 / b) * (Real.exp ((-1 / b) * x) * Xi x) :=
    continuous_const.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      continuous_Xi)
  have hFTC : ∀ x y : ℝ,
      ∫ t in y..x, -(1 / b) * (Real.exp ((-1 / b) * t) * Xi t) = H x - H y := fun x y =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hHd t)
      (hcont.intervalIntegrable _ _)
  -- zeros at both ends
  obtain ⟨hzp, hzn⟩ := laguerrePolya_preimage_zeros hψ b h
  choose xs hxs hxs0 using fun n : ℕ => hzp n
  choose ys hys hys0 using fun n : ℕ => hzn n
  have hHx : ∀ n, H (xs n) = 0 := fun n => by simp [hH, hψr, hxs0 n]
  have hHy : ∀ n, H (ys n) = 0 := fun n => by simp [hH, hψr, hys0 n]
  have hxt : Tendsto xs atTop atTop :=
    tendsto_atTop_mono (fun n => (hxs n).le) tendsto_natCast_atTop_atTop
  have hyt : Tendsto ys atTop atBot :=
    tendsto_atBot_mono (fun n => (hys n).le)
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  -- integrability and the limit
  have hs : |(-1 / b)| < π / 4 := by
    rw [abs_div, abs_neg, abs_one]; exact hb
  have hint := integrable_exp_mul_Xi hs
  have hlim := intervalIntegral_tendsto_integral hint hyt hxt
  have hzeroInt : ∀ n, ∫ t in ys n..xs n, Real.exp ((-1 / b) * t) * Xi t = 0 := by
    intro n
    have h1 := hFTC (xs n) (ys n)
    rw [hHx, hHy, sub_zero, intervalIntegral.integral_const_mul] at h1
    have hb' : -(1 / b) ≠ 0 := by simp [hb0]
    exact (mul_eq_zero.mp h1).resolve_left hb'
  simp only [hzeroInt] at hlim
  exact (tendsto_nhds_unique hlim tendsto_const_nhds)

/-- `∫ Ξ = 2πΦ(0) > 0`, by Fourier inversion at the origin. -/
theorem integral_Xi_pos : 0 < ∫ t, Xi t := by
  -- `Φ` is continuous and integrable, and its Fourier transform is `w ↦ Ξ(2πw)`
  have hΦc : Continuous riemannPhiKernel := KernelStrip.continuous_riemannPhiKernel
  obtain ⟨C, hC0, hC⟩ := KernelStrip.exists_norm_riemannPhiKernel_le
  have hΦi : Integrable riemannPhiKernel :=
    KernelStrip.integrable_of_norm_le_exp hΦc (C := C) fun u =>
      (hC u).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u]))
        hC0)
  have hF : ∀ w : ℝ, 𝓕 riemannPhiKernel w = (Xi (2 * π * w) : ℂ) := by
    intro w
    rw [fourier_eq_paperFT, show (-(2 * π * w : ℂ)) = ((-(2 * π * w) : ℝ) : ℂ) by push_cast; ring,
      paperFT_riemannPhiKernel_eq_XiC, XiC_ofReal, Xi_neg]
  have hFi : Integrable (𝓕 riemannPhiKernel) := by
    have h0 : |(0 : ℝ)| < π / 4 := by simp [Real.pi_pos]
    have h := integrable_exp_mul_Xi h0
    simp only [zero_mul, Real.exp_zero, one_mul] at h
    have h2 := (h.comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)).ofReal (𝕜 := ℂ)
    refine h2.congr (Eventually.of_forall fun w => ?_)
    simp [hF w]
  have hinv := hΦi.fourierInv_fourier_eq hFi hΦc.continuousAt (v := 0)
  rw [Real.fourierInv_eq] at hinv
  simp only [inner_zero_right, Circle.smul_def] at hinv
  have hval : (∫ w : ℝ, (Xi (2 * π * w) : ℂ)) = riemannPhiKernel 0 := by
    rw [← hinv]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp [hF w]
  have hreal : (∫ w : ℝ, (Xi (2 * π * w) : ℂ)) = ((∫ w : ℝ, Xi (2 * π * w) : ℝ) : ℂ) :=
    integral_complex_ofReal
  rw [hreal, riemannPhiKernel_eq_ofReal] at hval
  have hval' : ∫ w : ℝ, Xi (2 * π * w) = riemannKernelReal 0 := by exact_mod_cast hval
  have hscale : ∫ w : ℝ, Xi (2 * π * w) = (2 * π)⁻¹ * ∫ t, Xi t := by
    rw [Measure.integral_comp_mul_left (fun t => Xi t) (2 * π), abs_of_pos (by positivity),
      smul_eq_mul]
  rw [hscale] at hval'
  have hpos := riemannKernelReal_pos 0
  have h2π : 0 < (2 * π)⁻¹ := by positivity
  nlinarith

/-- **Strong first-order filters.**  There is `a₀ > 0` such that for `0 < |a| < a₀` no
Laguerre–Pólya `ψ` satisfies `(1 − D/a)ψ = Ξ`. -/
theorem exists_pos_not_laguerrePolya_firstOrder_preimage :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, a ≠ 0 → |a| < a₀ →
      ¬ ∃ ψ : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya ψ ∧ ∀ z, XiC z = ψ z - ((1 / a : ℝ) : ℂ) * deriv ψ z := by
  -- continuity of the Laplace integral at `0`
  set M : ℝ → ℝ := fun a => ∫ t, Real.exp (-a * t) * Xi t with hM
  have hr0 : (0 : ℝ) ≤ π / 8 := by positivity
  obtain ⟨K, hK⟩ := exists_abs_Xi_le_exp hr0 (by linarith [Real.pi_pos])
  have hcontM : ContinuousAt M 0 := by
    refine continuousAt_of_dominated (bound := fun t => K * Real.exp (-((π / 16) * |t|)))
      (Eventually.of_forall fun a => ((Real.continuous_exp.comp (continuous_const.mul
        continuous_id)).mul continuous_Xi).aestronglyMeasurable) ?_ ?_
      (Eventually.of_forall fun t => ((Real.continuous_exp.comp
        (continuous_neg.mul continuous_const)).mul continuous_const).continuousAt)
    · have hball : Metric.ball (0 : ℝ) (π / 16) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hball] with a ha
      refine Eventually.of_forall fun t => ?_
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := hK t
      have hK0 : 0 ≤ K := by
        have := hK 0
        simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
        exact (abs_nonneg _).trans this
      calc Real.exp (-a * t) * |Xi t| ≤ Real.exp (-a * t) * (K * Real.exp (-(π / 8 * |t|))) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = K * Real.exp (-a * t - π / 8 * |t|) := by rw [sub_eq_add_neg, Real.exp_add]; ring
        _ ≤ K * Real.exp (-((π / 16) * |t|)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
            have : -a * t ≤ |a| * |t| := by
              rw [← abs_mul]; exact (le_abs_self _).trans (by rw [neg_mul, abs_neg])
            nlinarith [abs_nonneg t]
    · exact (RHTower.integrable_exp_neg_mul_abs' (by positivity : (0 : ℝ) < π / 16)).const_mul K
  have hM0 : 0 < M 0 := by
    simp only [hM, neg_zero, zero_mul, Real.exp_zero, one_mul]
    exact integral_Xi_pos
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (hcontM.eventually (lt_mem_nhds hM0))
  refine ⟨min δ (π / 8), lt_min hδ (by positivity), fun a ha0 ha ⟨ψ, hψ, h⟩ => ?_⟩
  have hMa : 0 < M a := hball (by
    rw [dist_zero_right, Real.norm_eq_abs]; exact lt_of_lt_of_le ha (min_le_left _ _))
  have hb0 : (1 / a : ℝ) ≠ 0 := one_div_ne_zero ha0
  have hb : 1 / |1 / a| < π / 4 := by
    rw [abs_div, abs_one, one_div_one_div]
    have := min_le_right δ (π / 8)
    linarith [Real.pi_pos]
  have hzero := integral_exp_mul_Xi_eq_zero_of_sub_smul_deriv hb0 hb hψ h
  have he : (fun t => Real.exp ((-1 / (1 / a)) * t) * Xi t) = fun t => Real.exp (-a * t) * Xi t := by
    funext t; congr 2; field_simp
  rw [he] at hzero
  exact absurd hzero (ne_of_gt hMa)

/-- **Degree two with a strong factor.**  With `a₀` from
`exists_pos_not_laguerrePolya_firstOrder_preimage`, no Laguerre–Pólya `ψ` satisfies
`(1 − D/a₁)(1 − D/a₂)ψ = Ξ` when `0 < |a₁| < a₀` and `a₂ ≠ 0`. -/
theorem not_laguerrePolya_secondOrder_preimage_of_small {a₀ : ℝ}
    (ha₀ : ∀ a : ℝ, a ≠ 0 → |a| < a₀ →
      ¬ ∃ ψ : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya ψ ∧ ∀ z, XiC z = ψ z - ((1 / a : ℝ) : ℂ) * deriv ψ z)
    {a₁ a₂ : ℝ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hsmall : |a₁| < a₀) :
    ¬ ∃ ψ : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya ψ ∧ ∀ z, ψ z - ((1 / a₁ + 1 / a₂ : ℝ) : ℂ) * deriv ψ z +
      deriv (deriv ψ) z / ((a₁ * a₂ : ℝ) : ℂ) = XiC z := by
  rintro ⟨ψ, hψ, hode⟩
  have hψd : Differentiable ℂ ψ := GaloisForLFunctions.HTGeometry.LaguerrePolya.differentiable hψ
  have hψd' : Differentiable ℂ (deriv ψ) := fun z => ((hψd.analyticAt z).deriv).differentiableAt
  set g : ℂ → ℂ := fun z => ψ z - ((1 / a₂ : ℝ) : ℂ) * deriv ψ z with hg
  have hgLP : GaloisForLFunctions.HTGeometry.LaguerrePolya g := laguerrePolya_sub_smul_deriv hψ (1 / a₂)
  have hgd : ∀ z, deriv g z = deriv ψ z - ((1 / a₂ : ℝ) : ℂ) * deriv (deriv ψ) z := fun z =>
    ((hψd z).hasDerivAt.sub ((hψd' z).hasDerivAt.const_mul ((1 / a₂ : ℝ) : ℂ))).deriv
  refine ha₀ a₁ ha₁ hsmall ⟨g, hgLP, fun z => ?_⟩
  rw [← hode z, hgd z]
  simp only [hg]
  have h1 : (a₁ : ℂ) ≠ 0 := by exact_mod_cast ha₁
  have h2 : (a₂ : ℂ) ≠ 0 := by exact_mod_cast ha₂
  push_cast
  field_simp
  ring

end

end RHTower.Littlewood
