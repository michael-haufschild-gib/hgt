import GaloisForLFunctions.HTGeometry.OneSidedLaplaceAtomRigidity
import GaloisForLFunctions.HTGeometry.StripContourShift
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.DeBruijnNegativeTimeContour

/-!
# A one-sided Gaussian zero-side identity with a real-rooted weight forces RH

Let `F` be holomorphic on the strip `|Im z| < 1/2 + η`, with Gaussian-dominated growth
`‖F z‖ ≤ M e^{A (Re z)²}`, and with only real zeros in that strip. Fix `σ > A` and `κ ∈ ℂ`, and
write `γ_q` for the centered Xi zeros (`Xi(γ) = ξ(1/2 + iγ) = 0`, with multiplicity). Suppose that
for every positive frequency `u`

`∑_q F(γ_q) e^{-σ γ_q²} e^{-iuγ_q} = κ ∫_ℝ F(t) e^{-σ t²} e^{-iut} dt`.

Then every `γ_q` is real: the Riemann hypothesis holds.

This is the zero-side form of the Euler–Lagrange equation of a restricted Weil form, tested
against Gaussian-modulated functions, in the limit of large aperture: `F` is a limit of
real-rooted Fourier transforms of eigenvectors and `κ` is the limiting eigenvalue up to `2π`.
The limit need not be identified with `Xi`.

**Proof.** Shift the line integral down to `Im z = -Y`, `Y = 1/2 + η/2`, and lift the zeros to
`p_ρ = γ_ρ + iY`, which lie in the upper half-plane with bounded imaginary parts and no
accumulation point. After removing the common factor `e^{-uY}`, the identity is a one-sided
Laplace identity between the atoms `m_ρ F(γ_ρ) e^{-σγ_ρ²}` at `p_ρ` and an integrable function on
the line. One-sided Laplace atom rigidity kills every atom, so `F(γ_ρ) = 0`; since the zeros of `F`
in the strip are real, every `γ_ρ` is real.
-/

open Complex MeasureTheory Set Filter Topology Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Gaussian domination: `e^{-a x²} (x² + 1/4) ≤ 1/a + 1` for `a > 0`. -/
theorem exp_neg_mul_sq_mul_add_quarter_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Real.exp (-(a * x ^ 2)) * (x ^ 2 + 1 / 4) ≤ 1 / a + 1 := by
  have hpos : 0 < Real.exp (a * x ^ 2) := Real.exp_pos _
  have hge : a * x ^ 2 + 1 ≤ Real.exp (a * x ^ 2) := Real.add_one_le_exp _
  rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ hpos]
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have h1 : x ^ 2 ≤ (1 / a) * Real.exp (a * x ^ 2) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ ha]
    nlinarith
  have h2 : (1 / 4 : ℝ) ≤ Real.exp (a * x ^ 2) := by nlinarith
  nlinarith

theorem norm_cexp_neg_ofReal_mul_sq (σ : ℝ) (z : ℂ) :
    ‖cexp (-(σ : ℂ) * z ^ 2)‖ = Real.exp (-(σ * (z.re ^ 2 - z.im ^ 2))) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, pow_two,
    mul_im]

theorem norm_cexp_neg_I_mul_ofReal (z : ℂ) (u : ℝ) :
    ‖cexp (-(I * z) * u)‖ = Real.exp (u * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_mul, neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_neg,
    ofReal_re, ofReal_im, mul_zero, sub_zero, mul_im]
  ring

/-- The Gaussian-weighted value of a Gaussian-dominated function on the half-unit strip. -/
theorem norm_mul_cexp_neg_mul_sq_le {F : ℂ → ℂ} {M A σ : ℝ} (hA : 0 ≤ A) (hσ : A < σ) {z : ℂ}
    (hFz : ‖F z‖ ≤ M * Real.exp (A * z.re ^ 2)) (hz : |z.im| ≤ 1 / 2) :
    ‖F z * cexp (-(σ : ℂ) * z ^ 2)‖ ≤
      M * Real.exp (σ / 4) * Real.exp (-((σ - A) * z.re ^ 2)) := by
  have hM : 0 ≤ M := by
    have := le_trans (norm_nonneg _) hFz
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  rw [norm_mul, norm_cexp_neg_ofReal_mul_sq]
  have hy : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have hσpos : 0 ≤ σ := by linarith
  calc ‖F z‖ * Real.exp (-(σ * (z.re ^ 2 - z.im ^ 2)))
      ≤ M * Real.exp (A * z.re ^ 2) * Real.exp (-(σ * (z.re ^ 2 - z.im ^ 2))) := by
        gcongr
    _ = M * Real.exp (σ * z.im ^ 2) * Real.exp (-((σ - A) * z.re ^ 2)) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
    _ ≤ M * Real.exp (σ / 4) * Real.exp (-((σ - A) * z.re ^ 2)) := by
        gcongr
        nlinarith

/-! ## The Gaussian-modulated test on a horizontal line -/

/-- The Gaussian-modulated integrand `F(z) e^{-σz²} e^{-iuz}`. -/
def gaussModulated (F : ℂ → ℂ) (σ u : ℝ) (z : ℂ) : ℂ :=
  F z * cexp (-(σ : ℂ) * z ^ 2) * cexp (-(I * z) * u)

theorem norm_gaussModulated_le {F : ℂ → ℂ} {M A σ : ℝ} {u : ℝ} {z : ℂ}
    (hFz : ‖F z‖ ≤ M * Real.exp (A * z.re ^ 2)) :
    ‖gaussModulated F σ u z‖ ≤
      M * Real.exp (σ * z.im ^ 2 + u * z.im) * Real.exp (-((σ - A) * z.re ^ 2)) := by
  have hM : 0 ≤ M := by
    have := le_trans (norm_nonneg _) hFz
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  rw [gaussModulated, norm_mul, norm_mul, norm_cexp_neg_ofReal_mul_sq, norm_cexp_neg_I_mul_ofReal]
  calc ‖F z‖ * Real.exp (-(σ * (z.re ^ 2 - z.im ^ 2))) * Real.exp (u * z.im)
      ≤ M * Real.exp (A * z.re ^ 2) * Real.exp (-(σ * (z.re ^ 2 - z.im ^ 2))) *
          Real.exp (u * z.im) := by gcongr
    _ = M * Real.exp (σ * z.im ^ 2 + u * z.im) * Real.exp (-((σ - A) * z.re ^ 2)) := by
        rw [mul_assoc, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- On every horizontal line inside the strip the modulated integrand is integrable. -/
theorem integrable_gaussModulated_line {F : ℂ → ℂ} {M A σ W : ℝ} (hσ : A < σ) (u y : ℝ)
    (hy : |y| < W)
    (hF : ∀ z : ℂ, |z.im| < W → DifferentiableAt ℂ F z)
    (hFbound : ∀ z : ℂ, |z.im| < W → ‖F z‖ ≤ M * Real.exp (A * z.re ^ 2)) :
    Integrable (fun x : ℝ => gaussModulated F σ u ((x : ℂ) + (y : ℂ) * I)) := by
  have him : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I).im = y := by intro x; simp
  have hre : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I).re = x := by intro x; simp
  have hcont : Continuous (fun x : ℝ => gaussModulated F σ u ((x : ℂ) + (y : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hFc : ContinuousAt F ((x : ℂ) + (y : ℂ) * I) :=
      (hF _ (by rw [him]; exact hy)).continuousAt
    have hline : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) := by fun_prop
    have hcomp : ContinuousAt (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * I)) x :=
      ContinuousAt.comp (g := F) hFc hline.continuousAt
    have he1 : Continuous fun x : ℝ => cexp (-(σ : ℂ) * ((x : ℂ) + (y : ℂ) * I) ^ 2) := by
      fun_prop
    have he2 : Continuous fun x : ℝ => cexp (-(I * ((x : ℂ) + (y : ℂ) * I)) * u) := by
      fun_prop
    unfold gaussModulated
    exact (hcomp.mul he1.continuousAt).mul he2.continuousAt
  have hdom : Integrable (fun x : ℝ =>
      M * Real.exp (σ * y ^ 2 + u * y) * Real.exp (-((σ - A) * x ^ 2))) := by
    have := (integrable_exp_neg_mul_sq (b := σ - A) (by linarith)).const_mul
      (M * Real.exp (σ * y ^ 2 + u * y))
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [neg_mul]
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have := norm_gaussModulated_le (u := u) (σ := σ)
    (hFbound ((x : ℂ) + (y : ℂ) * I) (by rw [him]; exact hy))
  rw [him, hre] at this
  exact this

/-- Horizontal contour shift of the modulated test from the real line to `Im z = -Y`. -/
theorem integral_gaussModulated_shift {F : ℂ → ℂ} {M A σ W Y : ℝ} (hA : 0 ≤ A) (hσ : A < σ)
    {u : ℝ}
    (hu : 0 < u) (hY : 0 < Y) (hYW : Y < W)
    (hF : ∀ z : ℂ, |z.im| < W → DifferentiableAt ℂ F z)
    (hFbound : ∀ z : ℂ, |z.im| < W → ‖F z‖ ≤ M * Real.exp (A * z.re ^ 2)) :
    (∫ x : ℝ, gaussModulated F σ u (x : ℂ)) =
      ∫ x : ℝ, gaussModulated F σ u ((x : ℂ) + ((-Y : ℝ) : ℂ) * I) := by
  have hM : 0 ≤ M := by
    have := le_trans (norm_nonneg _) (hFbound 0 (by simp; linarith))
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hW : 0 < W := by linarith
  have hzero : (fun x : ℝ => gaussModulated F σ u (x : ℂ)) =
      fun x : ℝ => gaussModulated F σ u ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
    funext x; simp
  rw [hzero]
  have hstrip : ∀ z : ℂ, z.im ∈ uIcc 0 (-Y) → |z.im| < W := by
    intro z hz
    rw [uIcc_of_ge (by linarith)] at hz
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  apply integral_line_shift
  · intro z hz
    unfold gaussModulated
    exact ((hF z (hstrip z hz)).mul (by fun_prop)).mul (by fun_prop)
  · exact integrable_gaussModulated_line hσ u 0 (by simpa using hW) hF hFbound
  · exact integrable_gaussModulated_line hσ u (-Y) (by rw [abs_neg, abs_of_pos hY]; exact hYW)
      hF hFbound
  · -- vertical edges vanish
    set K : ℝ := M * Real.exp (σ * Y ^ 2) with hK
    have hedge : ∀ R : ℝ, ∀ s : ℝ, (s = R ∨ s = -R) →
        ‖∫ y in (0 : ℝ)..(-Y), gaussModulated F σ u ((s : ℂ) + (y : ℂ) * I)‖ ≤
          K * Real.exp (-((σ - A) * R ^ 2)) * |(-Y) - 0| := by
      intro R s hs
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      rw [uIoc_of_ge (by linarith)] at hy
      have hyim : |((s : ℂ) + (y : ℂ) * I).im| < W := by
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
          add_zero, zero_add]
        rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
      have hb := norm_gaussModulated_le (u := u) (σ := σ) (hFbound _ hyim)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add, add_re, mul_re, sub_zero, ofReal_re] at hb
      have hsR : s ^ 2 = R ^ 2 := by rcases hs with rfl | rfl <;> ring
      rw [hsR] at hb
      refine le_trans hb ?_
      rw [hK]
      have hy2 : y ^ 2 ≤ Y ^ 2 := by nlinarith [hy.1, hy.2]
      have huy : u * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.le hy.2
      have hσ0 : 0 ≤ σ := by linarith
      gcongr
      nlinarith
    have hlim : Tendsto (fun R : ℝ => 2 * (K * Real.exp (-((σ - A) * R ^ 2)) * |(-Y) - 0|))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => Real.exp (-((σ - A) * R ^ 2))) atTop (𝓝 0) := by
        apply Real.tendsto_exp_atBot.comp
        apply tendsto_neg_atTop_atBot.comp
        apply Tendsto.const_mul_atTop (by linarith)
        exact tendsto_pow_atTop (by norm_num)
      have := ((h1.const_mul K).mul_const (|(-Y) - 0|)).const_mul 2
      simpa using this
    refine squeeze_zero (fun R => by positivity) (fun R => ?_) hlim
    have h1 := hedge R R (Or.inl rfl)
    have h2 := hedge R (-R) (Or.inr rfl)
    push_cast at h2
    linarith

/-! ## Discreteness of the lifted zeros -/

theorem exists_xiZeroCopy_of_support (ρ : XiDivisorSupport) :
    ∃ q : XiZeroCopy, q.1 = ρ := by
  have hpos := xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
  exact ⟨⟨ρ, ⟨0, hn⟩⟩, rfl⟩

theorem XiC_xiSpectralPointSupport (ρ : XiDivisorSupport) :
    XiC (xiSpectralPointSupport ρ) = 0 := by
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_support ρ
  exact XiC_xiSpectralPoint_eq_zero q

theorem xiSpectralPointSupport_im_mem (ρ : XiDivisorSupport) :
    (-1 / 2 : ℝ) < (xiSpectralPointSupport ρ).im ∧ (xiSpectralPointSupport ρ).im < 1 / 2 := by
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_support ρ
  exact xiSpectralPoint_im_mem_openHalf q

/-- Centered Xi zeros have no accumulation point: around every point a ball contains no
centered zero other than the centre. -/
theorem exists_ball_xiSpectralPointSupport_eq (z : ℂ) :
    ∃ r > 0, ∀ ρ : XiDivisorSupport, xiSpectralPointSupport ρ ∈ ball z r →
      xiSpectralPointSupport ρ = z := by
  have hev : ∀ᶠ w in 𝓝[≠] z, XiC w ≠ 0 :=
    (XiC_analytic z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hlocal => XiC_order_ne_top z (analyticOrderAt_eq_top.mpr hlocal))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨r, hr, hball⟩ := hev
  refine ⟨r, hr, fun ρ hρ => ?_⟩
  by_contra hne
  exact hball _ hρ hne (XiC_xiSpectralPointSupport ρ)

/-! ## The receiver -/

/-- **One-sided Gaussian zero-side identity with a real-rooted weight.** Let `F` be holomorphic on
the strip `|Im z| < 1/2 + η` with `‖F z‖ ≤ M e^{A (Re z)²}` there, and let every zero of `F` in
that strip be real. If, for `σ > A ≥ 0`, some `κ`, and every frequency `u > 0`,
`∑_q F(γ_q) e^{-σγ_q²} e^{-iuγ_q} = κ ∫ F(t) e^{-σt²} e^{-iut} dt` over the centered Xi zeros
with multiplicity, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_gaussianOneSidedZeroIdentity
    {η M A σ : ℝ} (hη : 0 < η) (hA : 0 ≤ A) (hσ : A < σ) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, |z.im| < 1 / 2 + η → DifferentiableAt ℂ F z)
    (hFbound : ∀ z : ℂ, |z.im| < 1 / 2 + η → ‖F z‖ ≤ M * Real.exp (A * z.re ^ 2))
    (hFreal : ∀ z : ℂ, |z.im| < 1 / 2 + η → F z = 0 → z.im = 0) (κ : ℂ)
    (hid : ∀ u : ℝ, 0 < u →
      ∑' q : XiZeroCopy, gaussModulated F σ u (xiSpectralPoint q) =
        κ * ∫ t : ℝ, gaussModulated F σ u (t : ℂ)) :
    RiemannHypothesis := by
  classical
  set W : ℝ := 1 / 2 + η with hWdef
  set Y : ℝ := 1 / 2 + η / 2 with hYdef
  have hY : 0 < Y := by rw [hYdef]; linarith
  have hYW : Y < W := by rw [hYdef, hWdef]; linarith
  have hM : 0 ≤ M := by
    have := le_trans (norm_nonneg _) (hFbound 0 (by simp; linarith))
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hσA : 0 < σ - A := by linarith
  -- atoms and points
  set m : XiDivisorSupport → ℕ :=
    fun ρ => Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) with hm
  set γ : XiDivisorSupport → ℂ := xiSpectralPointSupport with hγ
  set p : XiDivisorSupport → ℂ := fun ρ => γ ρ + (Y : ℂ) * I with hp
  set c : XiDivisorSupport → ℂ :=
    fun ρ => (m ρ : ℂ) * (F (γ ρ) * cexp (-(σ : ℂ) * γ ρ ^ 2)) with hc
  have hγim : ∀ ρ, |(γ ρ).im| < 1 / 2 := by
    intro ρ
    have := xiSpectralPointSupport_im_mem ρ
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have hγW : ∀ ρ, |(γ ρ).im| < W := fun ρ => lt_trans (hγim ρ) (by rw [hWdef]; linarith)
  have hpim : ∀ ρ, (p ρ).im = (γ ρ).im + Y := by intro ρ; simp [hp]
  -- the Gaussian weight is dominated by an inverse square
  set K : ℝ := M * Real.exp (σ / 4) * (1 / (σ - A) + 1) with hK
  have hweight : ∀ z : ℂ, |z.im| < 1 / 2 → z ≠ 0 →
      ‖F z * cexp (-(σ : ℂ) * z ^ 2)‖ ≤ K / ‖z‖ ^ 2 := by
    intro z hz hz0
    have hzW : |z.im| < W := lt_trans hz (by rw [hWdef]; linarith)
    have h1 := norm_mul_cexp_neg_mul_sq_le hA hσ (hFbound z hzW) hz.le
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hpos : 0 < ‖z‖ ^ 2 := by positivity
    have hy2 : z.im ^ 2 ≤ 1 / 4 := by
      have := sq_abs z.im
      nlinarith [abs_nonneg z.im]
    have h2 := exp_neg_mul_sq_mul_add_quarter_le hσA z.re
    have h3 : Real.exp (-((σ - A) * z.re ^ 2)) ≤ (1 / (σ - A) + 1) / ‖z‖ ^ 2 := by
      rw [le_div_iff₀ hpos]
      calc Real.exp (-((σ - A) * z.re ^ 2)) * ‖z‖ ^ 2
          ≤ Real.exp (-((σ - A) * z.re ^ 2)) * (z.re ^ 2 + 1 / 4) := by
            gcongr; rw [hnorm]; linarith
        _ ≤ 1 / (σ - A) + 1 := h2
    calc ‖F z * cexp (-(σ : ℂ) * z ^ 2)‖
        ≤ M * Real.exp (σ / 4) * Real.exp (-((σ - A) * z.re ^ 2)) := h1
      _ ≤ M * Real.exp (σ / 4) * ((1 / (σ - A) + 1) / ‖z‖ ^ 2) := by gcongr
      _ = K / ‖z‖ ^ 2 := by rw [hK]; ring
  have hγne : ∀ ρ, γ ρ ≠ 0 := by
    intro ρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_support ρ
    exact xiSpectralPoint_ne_zero q
  -- summability of the atoms
  have hmcast : ∀ ρ, ((m ρ : ℕ) : ℝ) = ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    intro ρ
    have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
      le_of_lt (xi_divisor_pos_on_support ρ)
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have hcsum : Summable fun ρ => ‖c ρ‖ := by
    refine Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) (fun ρ => ?_)
      (xi_zero_multiplicity_centered_inv_sq_summable.mul_left K)
    rw [hc, norm_mul, Complex.norm_natCast, hmcast]
    have hb := hweight (γ ρ) (hγim ρ) (hγne ρ)
    rw [hγ, norm_xiSpectralPointSupport] at hb
    have hd : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast le_of_lt (xi_divisor_pos_on_support ρ)
    calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          ‖F (xiSpectralPointSupport ρ) * cexp (-(σ : ℂ) * xiSpectralPointSupport ρ ^ 2)‖
        ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (K / ‖(ρ : ℂ) - 1 / 2‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb hd
      _ = K * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2) := by
          ring
  -- the integrable boundary function
  set h : ℝ → ℂ := fun t => κ * (F ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) *
    cexp (-(σ : ℂ) * ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) ^ 2)) with hhdef
  have hhint : Integrable h := by
    have hYabs : |(-Y)| < W := by rw [abs_neg, abs_of_pos hY]; exact hYW
    have := (integrable_gaussModulated_line hσ 0 (-Y) hYabs hF hFbound).const_mul κ
    refine this.congr (ae_of_all _ fun t => ?_)
    simp [hhdef, gaussModulated]
  -- the one-sided Laplace identity for the lifted atoms
  have hlap : ∀ u : ℝ, 0 < u →
      ∑' ρ, c ρ * cexp (-(I * p ρ) * u) = ∫ t : ℝ, h t * cexp (-(I * t) * u) := by
    intro u hu
    have hfac : ∀ z : ℂ, cexp (-(I * (z - (Y : ℂ) * I)) * u) =
        cexp (-(I * z) * u) * cexp (-((Y * u : ℝ) : ℂ)) := by
      intro z
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
    have hexpne : cexp (-((Y * u : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    -- left side over copies
    have hGsum : Summable fun q : XiZeroCopy => gaussModulated F σ u (xiSpectralPoint q) := by
      refine Summable.of_norm_bounded
        (g := fun q : XiZeroCopy => K * Real.exp (u / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
        (xiSpectralPoint_inv_sq_summable.mul_left _) (fun q => ?_)
      have hq := hweight (xiSpectralPoint q) (hγim q.1) (xiSpectralPoint_ne_zero q)
      rw [gaussModulated, norm_mul, norm_cexp_neg_I_mul_ofReal]
      have hexp : Real.exp (u * (xiSpectralPoint q).im) ≤ Real.exp (u / 2) := by
        apply Real.exp_le_exp.mpr
        have hlt : (xiSpectralPoint q).im < 1 / 2 := (abs_lt.mp (hγim q.1)).2
        nlinarith
      calc ‖F (xiSpectralPoint q) * cexp (-(σ : ℂ) * xiSpectralPoint q ^ 2)‖ *
            Real.exp (u * (xiSpectralPoint q).im)
          ≤ K / ‖xiSpectralPoint q‖ ^ 2 * Real.exp (u / 2) := by gcongr
        _ = K * Real.exp (u / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
    have hlhs : ∑' q : XiZeroCopy, gaussModulated F σ u (xiSpectralPoint q) =
        ∑' ρ, (m ρ : ℂ) * gaussModulated F σ u (γ ρ) := by
      rw [hGsum.tsum_sigma' (fun ρ => (hasSum_fintype _).summable)]
      refine tsum_congr fun ρ => ?_
      rw [tsum_fintype]
      simp only [xiSpectralPoint_eq_support, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hγ, hm]
    have hlhs' : ∑' ρ, (m ρ : ℂ) * gaussModulated F σ u (γ ρ) =
        (∑' ρ, c ρ * cexp (-(I * p ρ) * u)) * cexp (-((Y * u : ℝ) : ℂ)) := by
      rw [← tsum_mul_right]
      refine tsum_congr fun ρ => ?_
      have hγp : γ ρ = p ρ - (Y : ℂ) * I := by simp [hp]
      rw [gaussModulated, hc]
      conv_lhs => rw [hγp]
      rw [hfac (p ρ), ← hγp]
      ring
    have hrhs : κ * ∫ t : ℝ, gaussModulated F σ u (t : ℂ) =
        (∫ t : ℝ, h t * cexp (-(I * t) * u)) * cexp (-((Y * u : ℝ) : ℂ)) := by
      rw [integral_gaussModulated_shift hA hσ hu hY hYW hF hFbound, ← integral_mul_const,
        ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      have hshift : ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) = (t : ℂ) - (Y : ℂ) * I := by
        push_cast; ring
      simp only [hhdef, gaussModulated]
      rw [hshift, hfac (t : ℂ)]
      ring
    have := hid u hu
    rw [hlhs, hlhs', hrhs] at this
    exact mul_right_cancel₀ hexpne this
  -- apply atom rigidity
  have hpinj : Function.Injective p := by
    intro ρ τ hρτ
    apply xiSpectralPointSupport_injective
    simpa [hp] using hρτ
  have hppos : ∀ ρ, 0 < (p ρ).im := by
    intro ρ
    rw [hpim]
    linarith [(abs_lt.mp (hγim ρ)).1]
  have hpB : ∀ ρ, (p ρ).im ≤ 1 / 2 + Y := by
    intro ρ
    rw [hpim]
    linarith [(abs_lt.mp (hγim ρ)).2]
  have hpdisc : ∀ z : ℂ, 0 < z.im → ∃ r > 0, ∀ ρ, p ρ ∈ ball z r → p ρ = z := by
    intro z _
    obtain ⟨r, hr, hball⟩ := exists_ball_xiSpectralPointSupport_eq (z - (Y : ℂ) * I)
    refine ⟨r, hr, fun ρ hρ => ?_⟩
    have hmem : γ ρ ∈ ball (z - (Y : ℂ) * I) r := by
      rw [mem_ball, dist_eq_norm] at hρ ⊢
      have : γ ρ - (z - (Y : ℂ) * I) = p ρ - z := by simp [hp]; ring
      rw [this]; exact hρ
    have := hball ρ hmem
    simp only [hp]
    rw [show xiSpectralPointSupport ρ = γ ρ from rfl] at this
    rw [this]; ring
  have hczero := eq_zero_of_oneSidedLaplace_eq hpinj hcsum hppos hpB hpdisc hhint hlap
  -- conclude
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hc0 := hczero q.1
  have hm0 : (m q.1 : ℂ) ≠ 0 := by
    have hpos := xi_divisor_pos_on_support q.1
    have : 0 < m q.1 := by simp only [hm]; omega
    exact_mod_cast this.ne'
  rw [hc, mul_eq_zero] at hc0
  have hFz : F (γ q.1) = 0 := by
    rcases hc0 with h0 | h0
    · exact absurd h0 hm0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact h1
      · exact absurd h1 (Complex.exp_ne_zero _)
  have him := hFreal (γ q.1) (hγW q.1) hFz
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simp only [ofReal_im]
    exact him

/-! ## The converse: under RH, `Xi` itself is such a weight -/

/-- `Xi` is bounded on every horizontal strip of half-width at most `2`. -/
theorem norm_XiC_le_of_abs_im_le {z : ℂ} (hz : |z.im| ≤ 2) :
    ‖XiC z‖ ≤ ∫ x, riemannKernelReal x * Real.exp (2 * |x|) := by
  have he : XiC z = DeBruijn.riemannHeat 0 z := by
    rw [DeBruijn.riemannHeat_zero, XiC, mul_comm]
  rw [he]
  exact (DeBruijn.norm_riemannHeat_zero_le z).trans
    (DeBruijn.integral_riemannKernel_mul_exp_mono hz)

theorem xiSpectralPoint_im_eq_zero_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 0 := by
  have hzero := xi_eq_zero_of_mem_divisor_support q.1
  have hright := rh_iff_xi_ne_zero_right.mp hRH
  have hre : ((q.1 : ℂ)).re = 1 / 2 := by
    rcases lt_trichotomy ((q.1 : ℂ)).re (1 / 2) with hlt | heq | hgt
    · exfalso
      have hrefl : xi (1 - (q.1 : ℂ)) = 0 := by rw [xi_one_sub, hzero]
      exact hright _ (by rw [mem_rightHalf]; simp only [sub_re, one_re]; linarith) hrefl
    · exact heq
    · exact absurd hzero (hright _ (mem_rightHalf.mpr hgt))
  rw [xiSpectralPoint_im_eq, hre]
  ring

/-- **The receiver is exact.** RH holds iff some strip-holomorphic, Gaussian-dominated weight with
only real zeros in the strip satisfies the one-sided Gaussian zero-side identity. Under RH the
weight `Xi` itself works, with `κ = 0`. -/
theorem riemannHypothesis_iff_exists_gaussianOneSidedZeroIdentity :
    RiemannHypothesis ↔
      ∃ (η M A σ : ℝ) (F : ℂ → ℂ) (κ : ℂ), 0 < η ∧ 0 ≤ A ∧ A < σ ∧
        (∀ z : ℂ, |z.im| < 1 / 2 + η → DifferentiableAt ℂ F z) ∧
        (∀ z : ℂ, |z.im| < 1 / 2 + η → ‖F z‖ ≤ M * Real.exp (A * z.re ^ 2)) ∧
        (∀ z : ℂ, |z.im| < 1 / 2 + η → F z = 0 → z.im = 0) ∧
        ∀ u : ℝ, 0 < u →
          ∑' q : XiZeroCopy, gaussModulated F σ u (xiSpectralPoint q) =
            κ * ∫ t : ℝ, gaussModulated F σ u (t : ℂ) := by
  constructor
  · intro hRH
    refine ⟨1, ∫ x, riemannKernelReal x * Real.exp (2 * |x|), 0, 1, XiC, 0, one_pos,
      le_rfl, one_pos, fun z _ => (XiC_analytic z (Set.mem_univ z)).differentiableAt,
      fun z hz => ?_, fun z _ hz => ?_, fun u _ => ?_⟩
    · rw [zero_mul, Real.exp_zero, mul_one]
      exact norm_XiC_le_of_abs_im_le (by linarith)
    · obtain ⟨q, rfl⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
      exact xiSpectralPoint_im_eq_zero_of_rh hRH q
    · simp [gaussModulated, XiC_xiSpectralPoint_eq_zero]
  · rintro ⟨η, M, A, σ, F, κ, hη, hA, hσ, hF, hFbound, hFreal, hid⟩
    exact riemannHypothesis_of_gaussianOneSidedZeroIdentity hη hA hσ hF hFbound hFreal κ hid

end

end RHTower
