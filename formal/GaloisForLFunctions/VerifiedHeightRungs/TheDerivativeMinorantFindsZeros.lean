import GaloisForLFunctions.VerifiedHeightRungs.TheDerivativeMinorant
import GaloisForLFunctions.VerifiedHeightRungs.SeparatedZerosInEveryLongWindow
import GaloisForLFunctions.VerifiedHeightRungs.TheZeroSideOfTheWindowRung

/-!
# The derivative minorant finds zeros

The symbol side of the minorant form `D = σ² W(S_ξ g, S_ξ g) − W(S_ξ g', S_ξ g')`, `t = −2πξ`
(`re_minorantForm_ge`): with `W(S_ξ f) = A_f(ξ) − Π_f(ξ)` and `ĝ'(s) = −is ĝ(s)`,

  `σ² Re A_g − Re A_{g'} = poles + ∫ (σ² − s²) |ĝ(s)|² μ(s + t) ds`.

Freezing `μ` at `t` costs `D_μ |s|`, and `|s|(σ² + s²)|ĝ(s)|² ≤ B²(σ²Y + 1/Y)/(1 + Y²s²)`; by Plancherel the frozen part
is `2π μ(t) (σ² Y E₀ − E₁/Y) ≥ F (log(1 + |t|/4) − 10)`. So

  `Re D ≥ F (L − 10) − π D_μ B² (σ² + Y⁻²) − 64 e^Y Y² N² (1 + |t|)⁻⁴ − σ² |Π_g| − |Π_{g'}|`.

Against the zero side of `re_minorantForm_le_of_gap` this gives the gap theorem `exists_zero_near_of_minorant`: for
`σY ≥ 1`, `2E₁ ≤ (σY)²`, `σ²Y³ ≥ 2949120 B²`, at every height where both prime polynomials are below `L/32` of their
scale, RH within `e^Y` puts a zero within `σ` of `t`. The width is `Y ≍ 1/σ`: no cluster bound enters.

`exists_spread_zeros_minorant` combines it with the windowed Chebyshev bound and the slot argument: every window of
length `10(m + 1)σ ≥ 2e^{2Y}` above the floor holds `4(m + 1)` verified zeros with gaps `σ|i − j|`.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower _root_.RHTower.WeilRegular Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-! ### The archimedean density is Lipschitz -/

theorem exists_mu_lipschitz : ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : ℝ, |mu x - mu y| ≤ D * |x - y| := by
  obtain ⟨C, hC⟩ := gammaFacts.deriv_bound
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    (gammaFacts.smooth.continuous_deriv (by simp)).continuousOn
  set D := max (max C B) 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  have hbound : ∀ τ : ℝ, ‖deriv mu τ‖ ≤ D := by
    intro τ
    rcases le_or_gt |τ| 1 with h | h
    · have hτ : τ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
      exact (hB τ hτ).trans ((le_max_right C B).trans (le_max_left _ _))
    · have hd := hC τ h.le
      rw [Real.norm_eq_abs]
      have hτ0 : 0 < |τ| := by linarith only [h]
      rw [le_div_iff₀ hτ0] at hd
      have hCD : C ≤ D := (le_max_left C B).trans (le_max_left _ _)
      by_contra hlt
      push Not at hlt
      nlinarith only [hd, hlt, hCD, hD0, h]
  refine ⟨D, hD0, fun x y => ?_⟩
  have hdiff : ∀ z ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ mu z := fun z _ =>
    (gammaFacts.smooth.differentiable (by simp)).differentiableAt
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff (fun z _ => hbound z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- A Lipschitz constant `D_μ` of the archimedean density. -/
def muLip : ℝ := Classical.choose exists_mu_lipschitz

theorem muLip_nonneg : 0 ≤ muLip := (Classical.choose_spec exists_mu_lipschitz).1

theorem abs_mu_sub_le (x y : ℝ) : |mu x - mu y| ≤ muLip * |x - y| :=
  (Classical.choose_spec exists_mu_lipschitz).2 x y

/-! ### Sizes of the test -/

theorem integral_norm_const_mul_comp {Y : ℝ} (hY : 0 < Y) (c : ℂ) (h : ℝ → ℂ) :
    ∫ u, ‖c * h (Y⁻¹ * u)‖ = ‖c‖ * (Y * ∫ v, ‖h v‖) := by
  simp_rw [norm_mul]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun v => ‖h v‖) Y⁻¹, inv_inv, abs_of_pos hY,
    smul_eq_mul]

theorem deriv_const_mul_comp (Y : ℝ) (c : ℂ) (h : ℝ → ℂ) :
    deriv (fun u => c * h (Y⁻¹ * u)) = fun u => c * (Y : ℂ)⁻¹ * deriv h (Y⁻¹ * u) := by
  rw [deriv_const_mul_field']
  funext u
  rw [deriv_comp_mul_left, Complex.real_smul]
  push_cast
  ring

theorem integral_norm_sq_minorantTest {Y : ℝ} (hY : 0 < Y) : ∫ u, ‖minorantTest Y u‖ ^ 2 = Y * minorantE₀ := by
  change ∫ u, ‖minorantProfile (Y⁻¹ * u)‖ ^ 2 = _
  rw [Measure.integral_comp_mul_left (fun v => ‖minorantProfile v‖ ^ 2) Y⁻¹, inv_inv, abs_of_pos hY, smul_eq_mul]
  rfl

theorem integral_norm_sq_minorantTestD {Y : ℝ} (hY : 0 < Y) :
    ∫ u, ‖minorantTestD Y u‖ ^ 2 = minorantE₁ / Y := by
  rw [minorantTestD_eq]
  have hn : ∀ u, ‖(Y⁻¹ : ℂ) * minorantProfileD (Y⁻¹ * u)‖ ^ 2 = Y⁻¹ ^ 2 * ‖minorantProfileD (Y⁻¹ * u)‖ ^ 2 :=
    fun u => by
      rw [norm_mul, mul_pow, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hn]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun v => ‖minorantProfileD v‖ ^ 2) Y⁻¹, inv_inv,
    abs_of_pos hY, smul_eq_mul]
  unfold minorantE₁
  field_simp

/-- `N = Σ_{k ≤ 3} ‖φ^{(k)}‖₁`. -/
def minorantN : ℝ :=
  (∫ u, ‖minorantProfile u‖) + (∫ u, ‖minorantProfileD u‖) + (∫ u, ‖deriv minorantProfileD u‖) +
    ∫ u, ‖deriv (deriv minorantProfileD) u‖

/-- The tail constants of `g` and `g'` are at most `16 Y² N²`. -/
theorem minorantTails_le {Y : ℝ} (hY : 1 ≤ Y) :
    (4 * ((∫ u, ‖minorantTest Y u‖) + ∫ u, ‖deriv (deriv (minorantTest Y)) u‖)) ^ 2 ≤
        16 * Y ^ 2 * minorantN ^ 2 ∧
      (4 * ((∫ u, ‖minorantTestD Y u‖) + ∫ u, ‖deriv (deriv (minorantTestD Y)) u‖)) ^ 2 ≤
        16 * Y ^ 2 * minorantN ^ 2 := by
  have hY0 : 0 < Y := by linarith only [hY]
  have hYi : Y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hY
  have hYi0 : 0 < Y⁻¹ := inv_pos.2 hY0
  have hd1 : minorantTestD Y = fun u => (Y⁻¹ : ℂ) * minorantProfileD (Y⁻¹ * u) := minorantTestD_eq Y
  have hd2 : deriv (minorantTestD Y) = fun u => (Y : ℂ)⁻¹ * (Y : ℂ)⁻¹ * deriv minorantProfileD (Y⁻¹ * u) := by
    rw [hd1, deriv_const_mul_comp]
    push_cast
    rfl
  have hd3 : deriv (deriv (minorantTestD Y)) =
      fun u => (Y : ℂ)⁻¹ * (Y : ℂ)⁻¹ * (Y : ℂ)⁻¹ * deriv (deriv minorantProfileD) (Y⁻¹ * u) := by
    rw [hd2, deriv_const_mul_comp]
  have hnY : ‖(Y : ℂ)⁻¹‖ = Y⁻¹ := by rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hYi0]
  have n0 : ∫ u, ‖minorantTest Y u‖ = Y * ∫ v, ‖minorantProfile v‖ := by
    have h := integral_norm_const_mul_comp hY0 1 minorantProfile
    simp only [one_mul, norm_one] at h
    exact h
  have n1 : ∫ u, ‖minorantTestD Y u‖ = ∫ v, ‖minorantProfileD v‖ := by
    rw [hd1, integral_norm_const_mul_comp hY0, hnY]
    field_simp
  have n2 : ∫ u, ‖deriv (deriv (minorantTest Y)) u‖ = Y⁻¹ * ∫ v, ‖deriv minorantProfileD v‖ := by
    change ∫ u, ‖deriv (minorantTestD Y) u‖ = _
    rw [hd2, integral_norm_const_mul_comp hY0, norm_mul, hnY]
    field_simp
  have n3 : ∫ u, ‖deriv (deriv (minorantTestD Y)) u‖ = Y⁻¹ ^ 2 * ∫ v, ‖deriv (deriv minorantProfileD) v‖ := by
    rw [hd3, integral_norm_const_mul_comp hY0, norm_mul, norm_mul, hnY]
    field_simp
  have w0 : 0 ≤ ∫ v, ‖minorantProfile v‖ := integral_nonneg fun _ => norm_nonneg _
  have w1 : 0 ≤ ∫ v, ‖minorantProfileD v‖ := integral_nonneg fun _ => norm_nonneg _
  have w2 : 0 ≤ ∫ v, ‖deriv minorantProfileD v‖ := integral_nonneg fun _ => norm_nonneg _
  have w3 : 0 ≤ ∫ v, ‖deriv (deriv minorantProfileD) v‖ := integral_nonneg fun _ => norm_nonneg _
  have hN : minorantN = (∫ v, ‖minorantProfile v‖) + (∫ v, ‖minorantProfileD v‖) +
      (∫ v, ‖deriv minorantProfileD v‖) + ∫ v, ‖deriv (deriv minorantProfileD) v‖ := rfl
  have hYi2 : Y⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hYi0.le hYi
  have hYN : Y * minorantN = Y * (∫ v, ‖minorantProfile v‖) + Y * (∫ v, ‖minorantProfileD v‖) +
      Y * (∫ v, ‖deriv minorantProfileD v‖) + Y * ∫ v, ‖deriv (deriv minorantProfileD) v‖ := by
    rw [hN]; ring
  have a1 := mul_nonneg hY0.le w1
  have a2 := mul_nonneg hY0.le w2
  have a3 := mul_nonneg hY0.le w3
  constructor
  · rw [n0, n2]
    have h : Y * (∫ v, ‖minorantProfile v‖) + Y⁻¹ * (∫ v, ‖deriv minorantProfileD v‖) ≤ Y * minorantN := by
      have := mul_le_mul_of_nonneg_right (hYi.trans hY) w2
      linarith only [this, hYN, a1, a3]
    have h0 : 0 ≤ Y * (∫ v, ‖minorantProfile v‖) + Y⁻¹ * (∫ v, ‖deriv minorantProfileD v‖) :=
      add_nonneg (mul_nonneg hY0.le w0) (mul_nonneg hYi0.le w2)
    have := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)) 2
    calc _ ≤ (4 * (Y * minorantN)) ^ 2 := this
      _ = _ := by ring
  · rw [n1, n3]
    have h : (∫ v, ‖minorantProfileD v‖) + Y⁻¹ ^ 2 * (∫ v, ‖deriv (deriv minorantProfileD) v‖) ≤ Y * minorantN := by
      have h1 := mul_le_mul_of_nonneg_right hYi2 w3
      have h2 := mul_le_mul_of_nonneg_right hY w1
      have h3 := mul_le_mul_of_nonneg_right hY w3
      have a0 := mul_nonneg hY0.le w0
      linarith only [h1, h2, h3, hYN, a0, a2]
    have h0 : 0 ≤ (∫ v, ‖minorantProfileD v‖) + Y⁻¹ ^ 2 * (∫ v, ‖deriv (deriv minorantProfileD) v‖) :=
      add_nonneg w1 (mul_nonneg (by positivity) w3)
    have := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)) 2
    calc _ ≤ (4 * (Y * minorantN)) ^ 2 := this
      _ = _ := by ring

/-! ### The symbol side -/

theorem two_pi_mul_neg_div (t : ℝ) : 2 * π * (-t / (2 * π)) = -t := by
  field_simp

/-- The real part of `A_f(ξ)`: poles plus the `μ`-weighted mass of `f̂(· + 2πξ)`. -/
theorem re_archPart_eq {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ξ : ℝ) :
    (archPart f ξ).re = (paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (I / 2) +
        paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (-I / 2)).re +
      ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ * (mu τ : ℂ)) =
      fun τ : ℝ => ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ : ℝ) : ℂ) := by
    funext τ
    rw [hval, Complex.ofReal_mul]
  rw [archPart, Complex.add_re, hfun, integral_complex_ofReal, Complex.ofReal_re]

/-- Integrability of `|f̂(τ + 2πξ)|²` and of `|f̂(τ + 2πξ)|² μ(τ)`. -/
theorem integrable_shift_norm_sq {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ξ : ℝ) :
    Integrable (fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2) ∧
      Integrable (fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ) := by
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgc : HasCompactSupport (heightShift ξ f) := hfc.mul_left
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  constructor
  · refine (EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hkd hkc)).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, RCLike.re_to_complex, Complex.ofReal_re]
  · refine (EF.integrable_paperFT_mul_mu hkd hkc gammaFacts).re.congr (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]

/-- `v (1 + v²) ≤ (1 + v)⁴`. -/
theorem mul_one_add_sq_le_pow (v : ℝ) (hv : 0 ≤ v) : v * (1 + v ^ 2) ≤ (1 + v) ^ 4 := by
  nlinarith only [hv, sq_nonneg v, pow_nonneg hv 3, pow_nonneg hv 4]

/-- **The frozen symbol.** `σ² ∫|ĝ(τ − t)|²μ − ∫|ĝ'(τ − t)|²μ ≥ F (L − 10) − π D_μ B² (σ² + Y⁻²)`. -/
theorem minorant_integral_ge {σ Y t : ℝ} (hY : 1 ≤ Y)
    (hF : 0 ≤ σ ^ 2 * Y * minorantE₀ - minorantE₁ / Y) :
    (σ ^ 2 * Y * minorantE₀ - minorantE₁ / Y) * (Real.log (1 + |t| / 4) - 10) -
        π * muLip * minorantB ^ 2 * (σ ^ 2 + 1 / Y ^ 2) ≤
      σ ^ 2 * (∫ τ : ℝ, ‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ) -
        ∫ τ : ℝ, ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ := by
  have hY0 : 0 < Y := by linarith only [hY]
  have hπ := Real.pi_pos
  have hB := minorantB_nonneg
  have hD := muLip_nonneg
  have hgc := hasCompactSupport_of_tsupport_subset_Icc (tsupport_minorantTest hY0)
  have hgc' := hasCompactSupport_of_tsupport_subset_Icc (tsupport_minorantTestD hY0)
  have hshift : ∀ τ : ℝ, τ + 2 * π * (-t / (2 * π)) = τ - t := fun τ => by rw [two_pi_mul_neg_div]; ring
  obtain ⟨hi1, hi2⟩ := integrable_shift_norm_sq (minorantTest_contDiff Y) hgc (-t / (2 * π))
  obtain ⟨hi1', hi2'⟩ := integrable_shift_norm_sq (minorantTestD_contDiff Y) hgc' (-t / (2 * π))
  simp only [hshift] at hi1 hi2 hi1' hi2'
  -- The Cauchy weight.
  set c := muLip * minorantB ^ 2 * (σ ^ 2 * Y + 1 / Y) with hc
  have hci : Integrable fun τ : ℝ => (1 + (Y * (τ - t)) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_left' hY0.ne').comp_sub_right t
  have hcint : ∫ τ : ℝ, (1 + (Y * (τ - t)) ^ 2)⁻¹ = π / Y := by
    rw [integral_sub_right_eq_self (fun τ => (1 + (Y * τ) ^ 2)⁻¹) t,
      Measure.integral_comp_mul_left (fun v => (1 + v ^ 2)⁻¹) Y, integral_univ_inv_one_add_sq,
      abs_of_pos (inv_pos.2 hY0), smul_eq_mul]
    field_simp
  -- Pointwise comparison.
  have hpt : ∀ τ : ℝ, mu t * (σ ^ 2 * ‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 -
      ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2) - c * (1 + (Y * (τ - t)) ^ 2)⁻¹ ≤
      σ ^ 2 * (‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ) -
        ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    intro τ
    set s := τ - t with hs
    set w := ‖paperFT (minorantTest Y) (s : ℂ)‖ with hw
    have hw0 : 0 ≤ w := norm_nonneg _
    have hd : ‖paperFT (minorantTestD Y) (s : ℂ)‖ = |s| * w := by
      rw [paperFT_minorantTestD_eq_mul hY0, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hd]
    -- Decay at the real point `s`.
    have hdec : w ≤ Y * minorantB / (1 + Y * |s|) ^ 2 := by
      have h := norm_paperFT_minorantTest_le hY0 (s : ℂ)
      simp only [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_re] at h
      exact h
    have hdec' : |s| * w ≤ minorantB / (1 + Y * |s|) ^ 2 := by
      have h := norm_paperFT_minorantTestD_le hY0 (s : ℂ)
      simp only [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_re] at h
      rw [← hd]
      exact h
    have hs0 := abs_nonneg s
    set v := Y * |s| with hv
    have hv0 : 0 ≤ v := by positivity
    have hvs : (Y * s) ^ 2 = v ^ 2 := by rw [hv, mul_pow, mul_pow, sq_abs]
    have hden : 0 < 1 + v ^ 2 := by positivity
    have hpow := mul_one_add_sq_le_pow v hv0
    -- `|s| w² ≤ Y B² / (1 + v²)` and `|s| (|s| w)² ≤ B² / (Y (1 + v²))`.
    have hA : |s| * w ^ 2 ≤ Y * minorantB ^ 2 * (1 + v ^ 2)⁻¹ := by
      have h1 : w ^ 2 ≤ (Y * minorantB) ^ 2 / ((1 + v) ^ 2) ^ 2 := by
        have := pow_le_pow_left₀ hw0 hdec 2
        rwa [div_pow] at this
      have h2 : |s| * ((Y * minorantB) ^ 2 / ((1 + v) ^ 2) ^ 2) ≤ Y * minorantB ^ 2 * (1 + v ^ 2)⁻¹ := by
        rw [← pow_mul, show 2 * 2 = 4 by norm_num, mul_div_assoc', div_le_iff₀ (by positivity),
          ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hden]
        have : |s| * (Y * minorantB) ^ 2 * (1 + v ^ 2) = Y * minorantB ^ 2 * (v * (1 + v ^ 2)) := by
          rw [hv]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      calc |s| * w ^ 2 ≤ |s| * ((Y * minorantB) ^ 2 / ((1 + v) ^ 2) ^ 2) := mul_le_mul_of_nonneg_left h1 hs0
        _ ≤ _ := h2
    have hB' : |s| * (|s| * w) ^ 2 ≤ minorantB ^ 2 / Y * (1 + v ^ 2)⁻¹ := by
      have h1 : (|s| * w) ^ 2 ≤ minorantB ^ 2 / ((1 + v) ^ 2) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hdec' 2
        rwa [div_pow] at this
      have h2 : |s| * (minorantB ^ 2 / ((1 + v) ^ 2) ^ 2) ≤ minorantB ^ 2 / Y * (1 + v ^ 2)⁻¹ := by
        rw [← pow_mul, show 2 * 2 = 4 by norm_num, mul_div_assoc', div_le_iff₀ (by positivity)]
        have e : minorantB ^ 2 / Y * (1 + v ^ 2)⁻¹ * (1 + v) ^ 4 =
            minorantB ^ 2 * (1 + v) ^ 4 / (Y * (1 + v ^ 2)) := by
          field_simp
        rw [e, le_div_iff₀ (by positivity)]
        have : |s| * minorantB ^ 2 * (Y * (1 + v ^ 2)) = minorantB ^ 2 * (v * (1 + v ^ 2)) := by
          rw [hv]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      calc |s| * (|s| * w) ^ 2 ≤ |s| * (minorantB ^ 2 / ((1 + v) ^ 2) ^ 2) := mul_le_mul_of_nonneg_left h1 hs0
        _ ≤ _ := h2
    -- The frozen density.
    have hμ := abs_mu_sub_le τ t
    rw [show τ - t = s from rfl] at hμ
    have hsq : (|s| * w) ^ 2 = s ^ 2 * w ^ 2 := by rw [mul_pow, sq_abs]
    rw [hsq]
    have hdiff : |(σ ^ 2 - s ^ 2) * w ^ 2 * (mu τ - mu t)| ≤ muLip * (σ ^ 2 * (|s| * w ^ 2) + |s| * (s ^ 2 * w ^ 2)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg w)]
      have h1 : |σ ^ 2 - s ^ 2| ≤ σ ^ 2 + s ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith only [sq_nonneg σ, sq_nonneg s]
      calc |σ ^ 2 - s ^ 2| * w ^ 2 * |mu τ - mu t| ≤ (σ ^ 2 + s ^ 2) * w ^ 2 * (muLip * |s|) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h1 (sq_nonneg w)) hμ (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hcmp : muLip * (σ ^ 2 * (|s| * w ^ 2) + |s| * (s ^ 2 * w ^ 2)) ≤ c * (1 + (Y * s) ^ 2)⁻¹ := by
      rw [hvs, hc]
      have h3 : |s| * (s ^ 2 * w ^ 2) ≤ minorantB ^ 2 / Y * (1 + v ^ 2)⁻¹ := by rw [← hsq]; exact hB'
      have h4 : σ ^ 2 * (|s| * w ^ 2) ≤ σ ^ 2 * (Y * minorantB ^ 2 * (1 + v ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hA (sq_nonneg σ)
      have h5 := add_le_add h4 h3
      have h6 := mul_le_mul_of_nonneg_left h5 hD
      refine h6.trans (le_of_eq ?_)
      field_simp
    have hneg := neg_abs_le ((σ ^ 2 - s ^ 2) * w ^ 2 * (mu τ - mu t))
    have e1 : σ ^ 2 * (w ^ 2 * mu τ) - s ^ 2 * w ^ 2 * mu τ =
        mu t * (σ ^ 2 * w ^ 2 - s ^ 2 * w ^ 2) + (σ ^ 2 - s ^ 2) * w ^ 2 * (mu τ - mu t) := by ring
    rw [e1]
    linarith only [hneg, hdiff, hcmp]
  -- Integrate.
  have hL1 : Integrable fun τ : ℝ => mu t * (σ ^ 2 * ‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 -
      ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2) - c * (1 + (Y * (τ - t)) ^ 2)⁻¹ :=
    (((hi1.const_mul (σ ^ 2)).sub hi1').const_mul (mu t)).sub (hci.const_mul c)
  have hR1 : Integrable fun τ : ℝ => σ ^ 2 * (‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ) -
      ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ :=
    (hi2.const_mul (σ ^ 2)).sub hi2'
  have hmono := integral_mono hL1 hR1 hpt
  have hI1 : ∫ τ : ℝ, ‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 = 2 * π * (Y * minorantE₀) := by
    rw [integral_sub_right_eq_self (fun s : ℝ => ‖paperFT (minorantTest Y) (s : ℂ)‖ ^ 2) t,
      integral_norm_sq_paperFT_eq (minorantTest_contDiff Y) (tsupport_minorantTest hY0),
      integral_norm_sq_minorantTest hY0]
  have hI2 : ∫ τ : ℝ, ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 = 2 * π * (minorantE₁ / Y) := by
    rw [integral_sub_right_eq_self (fun s : ℝ => ‖paperFT (minorantTestD Y) (s : ℂ)‖ ^ 2) t,
      integral_norm_sq_paperFT_eq (minorantTestD_contDiff Y) (tsupport_minorantTestD hY0),
      integral_norm_sq_minorantTestD hY0]
  have hLint : ∫ τ : ℝ, (mu t * (σ ^ 2 * ‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 -
      ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2) - c * (1 + (Y * (τ - t)) ^ 2)⁻¹) =
      mu t * (σ ^ 2 * (2 * π * (Y * minorantE₀)) - 2 * π * (minorantE₁ / Y)) - c * (π / Y) := by
    rw [integral_sub (((hi1.const_mul (σ ^ 2)).sub hi1').const_mul (mu t)) (hci.const_mul c),
      integral_const_mul, integral_const_mul, integral_sub (hi1.const_mul _) hi1', integral_const_mul, hI1, hI2,
      hcint]
  have hRint : ∫ τ : ℝ, (σ ^ 2 * (‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ) -
      ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ) =
      σ ^ 2 * (∫ τ : ℝ, ‖paperFT (minorantTest Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ) -
        ∫ τ : ℝ, ‖paperFT (minorantTestD Y) ((τ - t : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    rw [integral_sub (hi2.const_mul _) hi2', integral_const_mul]
  rw [hLint, hRint] at hmono
  set F := σ ^ 2 * Y * minorantE₀ - minorantE₁ / Y with hFdef
  have hmu := mu_ge_log t
  have h1 : (Real.log (1 + |t| / 4) - 10) * F ≤ mu t * (2 * π * F) := by
    have h2 : Real.log (1 + |t| / 4) - 10 ≤ 2 * π * mu t := by
      rw [div_le_iff₀ (by positivity)] at hmu
      linarith only [hmu]
    have := mul_le_mul_of_nonneg_right h2 hF
    linarith only [this]
  have h2 : c * (π / Y) = π * muLip * minorantB ^ 2 * (σ ^ 2 + 1 / Y ^ 2) := by
    rw [hc]
    field_simp
  have e : mu t * (σ ^ 2 * (2 * π * (Y * minorantE₀)) - 2 * π * (minorantE₁ / Y)) = mu t * (2 * π * F) := by
    rw [hFdef]
    ring
  rw [e, h2] at hmono
  linarith only [hmono, h1]

/-- **The symbol side of the minorant form.** -/
theorem re_minorantForm_ge {σ Y t : ℝ} (hY : 1 ≤ Y) (hF : 0 ≤ σ ^ 2 * Y * minorantE₀ - minorantE₁ / Y) :
    (σ ^ 2 * Y * minorantE₀ - minorantE₁ / Y) * (Real.log (1 + |t| / 4) - 10) -
        π * muLip * minorantB ^ 2 * (σ ^ 2 + 1 / Y ^ 2) -
        (σ ^ 2 + 1) * (2 * Real.exp Y * (16 * Y ^ 2 * minorantN ^ 2) / (1 + |t|) ^ 4) -
        σ ^ 2 * ‖primePolynomial (minorantTest Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖ -
        ‖primePolynomial (minorantTestD Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖ ≤
      (minorantForm σ Y (-t / (2 * π))).re := by
  have hY0 : 0 < Y := by linarith only [hY]
  have hπ := Real.pi_pos
  set ξ := -t / (2 * π) with hξ
  have hg := minorantTest_contDiff Y (n := 2)
  have hg' := minorantTestD_contDiff Y (n := 2)
  have hgs := tsupport_minorantTest hY0
  have hgs' := tsupport_minorantTestD hY0
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hgc' := hasCompactSupport_of_tsupport_subset_Icc hgs'
  rw [minorantForm, zetaZeroConfig_W_heightShift_eq_sub hg hgs ξ, zetaZeroConfig_W_heightShift_eq_sub hg' hgs' ξ]
  have hσC : ((σ : ℂ) ^ 2) = ((σ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hσC, Complex.sub_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.sub_re,
    re_archPart_eq hg hgc ξ, re_archPart_eq hg' hgc' ξ]
  have hshift : ∀ τ : ℝ, τ + 2 * π * ξ = τ - t := fun τ => by rw [hξ, two_pi_mul_neg_div]; ring
  simp only [hshift]
  have hint := minorant_integral_ge (t := t) hY hF
  -- Poles.
  have habs : 2 * π * |ξ| = |t| := by
    rw [hξ, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    field_simp
  have hp1 := ArithmeticPositivityTheory.abs_re_pole_terms_heightShift_le_decay hY0.le hg hgs ξ
  have hp2 := ArithmeticPositivityTheory.abs_re_pole_terms_heightShift_le_decay hY0.le hg' hgs' ξ
  rw [habs] at hp1 hp2
  obtain ⟨hT1, hT2⟩ := minorantTails_le hY
  have hden : 0 < (1 + |t|) ^ 4 := by positivity
  have hq1 : 2 * Real.exp Y * (4 * ((∫ u, ‖minorantTest Y u‖) + ∫ u, ‖deriv (deriv (minorantTest Y)) u‖)) ^ 2 /
      (1 + |t|) ^ 4 ≤ 2 * Real.exp Y * (16 * Y ^ 2 * minorantN ^ 2) / (1 + |t|) ^ 4 := by
    gcongr
  have hq2 : 2 * Real.exp Y * (4 * ((∫ u, ‖minorantTestD Y u‖) + ∫ u, ‖deriv (deriv (minorantTestD Y)) u‖)) ^ 2 /
      (1 + |t|) ^ 4 ≤ 2 * Real.exp Y * (16 * Y ^ 2 * minorantN ^ 2) / (1 + |t|) ^ 4 := by
    gcongr
  obtain ⟨hp1l, -⟩ := abs_le.1 (hp1.trans hq1)
  obtain ⟨-, hp2u⟩ := abs_le.1 (hp2.trans hq2)
  -- Prime polynomials.
  have hPr1 := Complex.re_le_norm (primePolynomial (minorantTest Y) ⌊Real.exp (2 * Y)⌋₊ ξ)
  have hPr2 := Complex.abs_re_le_norm (primePolynomial (minorantTestD Y) ⌊Real.exp (2 * Y)⌋₊ ξ)
  have hPr2' := (abs_le.1 hPr2).1
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have h1 := mul_le_mul_of_nonneg_left hPr1 hσ2
  have h2 := mul_le_mul_of_nonneg_left hp1l hσ2
  nlinarith only [hint, h1, h2, hp2u, hPr2']

/-! ### The gap theorem -/

/-- **Good heights carry zeros.** -/
theorem exists_zero_near_of_minorant {σ Y t : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 1 ≤ Y) (hσY : 1 ≤ σ * Y)
    (hE₁ : 2 * minorantE₁ ≤ (σ * Y) ^ 2) (hB : 2949120 * minorantB ^ 2 ≤ σ ^ 2 * Y ^ 3)
    (hL : 40 + 32 * π * muLip * minorantB ^ 2 ≤ Real.log (1 + |t| / 4))
    (ht : 1024 * Real.exp Y * Y ^ 3 * minorantN ^ 2 ≤ |t|)
    (hon : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| ≤ Real.exp Y → ρ.re = 1 / 2)
    (hP1 : ‖primePolynomial (minorantTest Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖ ≤
      Y * minorantE₀ * Real.log (1 + |t| / 4) / 32)
    (hP2 : ‖primePolynomial (minorantTestD Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖ ≤
      σ ^ 2 * Y * minorantE₀ * Real.log (1 + |t| / 4) / 32) :
    ∃ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| < σ := by
  by_contra hno
  push Not at hno
  have hY0 : 0 < Y := by linarith only [hY]
  have hπ := Real.pi_pos
  have hE₀ := one_le_minorantE₀
  have hB0 := minorantB_nonneg
  have hD0 := muLip_nonneg
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (1 + |t| / 4) := ⟨_, rfl⟩
  rw [← hLdef] at hL hP1 hP2
  obtain ⟨M, hM⟩ : ∃ M, M = σ ^ 2 * Y * minorantE₀ := ⟨_, rfl⟩
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hM1 : σ ^ 2 * Y ≤ M := by
    rw [hM]
    have := mul_le_mul_of_nonneg_left hE₀ (mul_pos hσ2 hY0).le
    linarith only [this]
  have hMY : 1 ≤ M * Y := by nlinarith only [hM1, hσY, hY0, sq_nonneg (σ * Y)]
  have hM0 : 0 < M := by nlinarith only [hM1, hσ2, hY0]
  have hσM : σ ^ 2 ≤ M := by nlinarith only [hM1, hσ2, hY]
  -- `F ≥ M/2`.
  have hF2 : M / 2 ≤ σ ^ 2 * Y * minorantE₀ - minorantE₁ / Y := by
    have h1 : minorantE₁ / Y ≤ σ ^ 2 * Y / 2 := by
      rw [div_le_iff₀ hY0]
      nlinarith only [hE₁]
    rw [← hM]
    linarith only [h1, hM1]
  have hF0 : 0 ≤ σ ^ 2 * Y * minorantE₀ - minorantE₁ / Y := le_trans (by positivity) hF2
  have hlow := re_minorantForm_ge (t := t) hY hF0
  have hup := re_minorantForm_le_of_gap hσ hσ1 hY hon hno
  rw [← hLdef] at hlow
  -- Bounds of the error terms by `ML/16`.
  have hL40 : 40 ≤ L := by
    have : 0 ≤ 32 * π * muLip * minorantB ^ 2 := mul_nonneg (mul_nonneg (by positivity) hD0) (sq_nonneg _)
    linarith only [hL, this]
  have hmain : M / 2 * (L - 10) ≤ (σ ^ 2 * Y * minorantE₀ - minorantE₁ / Y) * (L - 10) :=
    mul_le_mul_of_nonneg_right hF2 (by linarith only [hL40])
  have herr : π * muLip * minorantB ^ 2 * (σ ^ 2 + 1 / Y ^ 2) ≤ M * L / 16 := by
    have h1 : 1 / Y ^ 2 ≤ σ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hσY]
    have h2 : π * muLip * minorantB ^ 2 * (σ ^ 2 + 1 / Y ^ 2) ≤ 2 * (π * muLip * minorantB ^ 2) * M := by
      have h3 : σ ^ 2 + 1 / Y ^ 2 ≤ 2 * M := by linarith only [h1, hσM]
      have h4 : 0 ≤ π * muLip * minorantB ^ 2 := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left h3 h4]
    have h5 : 32 * (π * muLip * minorantB ^ 2) ≤ L := by linarith only [hL]
    nlinarith only [h2, h5, hM0]
  have hpole : (σ ^ 2 + 1) * (2 * Real.exp Y * (16 * Y ^ 2 * minorantN ^ 2) / (1 + |t|) ^ 4) ≤ M * L / 16 := by
    have ht0 : 0 ≤ |t| := abs_nonneg t
    have h1 : 1 + |t| ≤ (1 + |t|) ^ 4 := by
      calc 1 + |t| = (1 + |t|) ^ 1 := (pow_one _).symm
        _ ≤ (1 + |t|) ^ 4 := pow_le_pow_right₀ (by linarith only [ht0]) (by norm_num)
    have h2 : (σ ^ 2 + 1) * (2 * Real.exp Y * (16 * Y ^ 2 * minorantN ^ 2)) * (16 * Y) ≤ 2 * |t| := by
      have hσ1' : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσ1]
      have : 0 ≤ Real.exp Y * Y ^ 3 * minorantN ^ 2 := by positivity
      nlinarith only [ht, this, hσ1', hσ2]
    have h3 : (σ ^ 2 + 1) * (2 * Real.exp Y * (16 * Y ^ 2 * minorantN ^ 2) / (1 + |t|) ^ 4) ≤ 1 / (8 * Y) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [h2, h1, hY0]
    have h4 : 1 / (8 * Y) ≤ M / 8 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hMY]
    nlinarith only [h3, h4, hL40, hM0]
  have hprime : σ ^ 2 * ‖primePolynomial (minorantTest Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖ +
      ‖primePolynomial (minorantTestD Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖ ≤ M * L / 16 := by
    have h1 := mul_le_mul_of_nonneg_left hP1 hσ2.le
    rw [hM]
    nlinarith only [h1, hP2]
  -- The zero side.
  have hzero : 16 * minorantB ^ 2 / Y ^ 2 * (24 * 240 * Real.log (|t| + 3)) ≤ M * L / 16 := by
    have hlog : Real.log (|t| + 3) ≤ 2 * L := by
      have h1 : Real.log (|t| + 3) ≤ Real.log (4 * (1 + |t| / 4)) :=
        Real.log_le_log (by positivity) (by linarith only)
      rw [Real.log_mul (by norm_num) (by positivity), ← hLdef] at h1
      have h4 : Real.log 4 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.exp_one_gt_d9
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        nlinarith only [this]
      linarith only [h1, h4, hL40]
    have hMY3 : 2949120 * minorantB ^ 2 ≤ M * Y ^ 2 := by
      have : σ ^ 2 * Y ^ 3 ≤ M * Y ^ 2 := by
        have := mul_le_mul_of_nonneg_right hM1 (sq_nonneg Y)
        nlinarith only [this]
      linarith only [hB, this]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hlog0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith only [abs_nonneg t])
    have h1 : 16 * minorantB ^ 2 * (24 * 240 * Real.log (|t| + 3)) ≤ 16 * minorantB ^ 2 * (24 * 240 * (2 * L)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by positivity)
    have h2 : 16 * minorantB ^ 2 * (24 * 240 * (2 * L)) * 16 = 2949120 * minorantB ^ 2 * L := by ring
    have h3 := mul_le_mul_of_nonneg_right hMY3 (by linarith only [hL40] : (0 : ℝ) ≤ L)
    nlinarith only [h1, h2, h3]
  have hfinal : M / 2 * (L - 10) - M * L / 16 - M * L / 16 - M * L / 16 ≤ M * L / 16 := by
    linarith only [hlow, hup, hmain, herr, hpole, hprime, hzero]
  nlinarith only [hfinal, hM0, hL40]

/-! ### Spread zeros in every long window -/

/-- **Spread zeros from the minorant.** A window of length `10(m + 1)σ ≥ 2e^{2Y}` above the floor `t_*`, verified up
to `T − e^Y`, holds `4(m + 1)` zeros with gaps `σ|i − j|`, when the minorant at resolution `σ/4` works at `t_*` and the
two prime polynomials have density `≤ 1/80` of large values. -/
theorem exists_spread_zeros_minorant {σ Y tₛ T c : ℝ} {m : ℕ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 1 ≤ Y)
    (hσY : 1 ≤ σ / 4 * Y) (hE₁ : 2 * minorantE₁ ≤ (σ / 4 * Y) ^ 2)
    (hB : 2949120 * minorantB ^ 2 ≤ (σ / 4) ^ 2 * Y ^ 3)
    (hsL : 40 + 32 * π * muLip * minorantB ^ 2 ≤ Real.log (1 + tₛ / 4))
    (hst : 1024 * Real.exp Y * Y ^ 3 * minorantN ^ 2 ≤ tₛ)
    (hV1 : 640 * π * gapEnergy * primeVariance (minorantTest Y) ⌊Real.exp (2 * Y)⌋₊ ≤
      3 * gapMass ^ 2 * (Y * minorantE₀ * Real.log (1 + tₛ / 4) / 32) ^ 2)
    (hV2 : 640 * π * gapEnergy * primeVariance (minorantTestD Y) ⌊Real.exp (2 * Y)⌋₊ ≤
      3 * gapMass ^ 2 * ((σ / 4) ^ 2 * Y * minorantE₀ * Real.log (1 + tₛ / 4) / 32) ^ 2)
    (hL : 2 * Real.exp (2 * Y) ≤ 10 * ((m : ℝ) + 1) * σ)
    (hfar : ∀ t ∈ Icc c (c + 10 * ((m : ℝ) + 1) * σ), tₛ ≤ |t|)
    (hT : ∀ t ∈ Icc c (c + 10 * ((m : ℝ) + 1) * σ), |t| + Real.exp Y ≤ T) (hRH : RHVerifiedThrough T) :
    ∃ node : ℕ → zetaZeroConfig.carrier,
      (∀ j ∈ range (4 * m + 3 + 1),
        c ≤ ((node j : ℂ)).im ∧ ((node j : ℂ)).im ≤ c + 10 * ((m : ℝ) + 1) * σ) ∧
      ∀ i ∈ range (4 * m + 3 + 1), ∀ j ∈ range (4 * m + 3 + 1),
        σ * |(i : ℝ) - j| ≤ |((node i : ℂ)).im - ((node j : ℂ)).im| := by
  have hπ := Real.pi_pos
  have hm₁ := gapMass_pos
  have hEn := gapEnergy_pos
  have hE₀ := one_le_minorantE₀
  have hY0 : 0 < Y := by linarith only [hY]
  have hM : 2 * (((5 * (m + 1) : ℕ) : ℝ)) * σ = 10 * ((m : ℝ) + 1) * σ := by push_cast; ring
  have hMn : (((5 * (m + 1) : ℕ) : ℝ)) - ((4 * m + 3 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  set N := ⌊Real.exp (2 * Y)⌋₊ with hN
  set Lₛ := Real.log (1 + tₛ / 4) with hLₛ
  have hLₛ0 : 0 < Lₛ := by
    have : 0 ≤ 32 * π * muLip * minorantB ^ 2 := by have := muLip_nonneg; positivity
    linarith only [hsL, this]
  have hs0 : 0 ≤ tₛ := le_trans (by positivity) hst
  obtain ⟨A₁, hA₁⟩ : ∃ A, A = Y * minorantE₀ * Lₛ / 32 := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A, A = (σ / 4) ^ 2 * Y * minorantE₀ * Lₛ / 32 := ⟨_, rfl⟩
  have hA₁0 : 0 < A₁ := by rw [hA₁]; positivity
  have hA₂0 : 0 < A₂ := by rw [hA₂]; positivity
  rw [← hA₁] at hV1
  rw [← hA₂] at hV2
  set G : Set ℝ := {t | ‖primePolynomial (minorantTest Y) N (-t / (2 * π))‖ < A₁} ∩
    {t | ‖primePolynomial (minorantTestD Y) N (-t / (2 * π))‖ < A₂} with hG
  have hLlen : 0 < 10 * ((m : ℝ) + 1) * σ := by positivity
  -- Each family of bad heights has density at most `1/80`.
  have hvol : ∀ (f : ℝ → ℂ) (A : ℝ), ContDiff ℝ 2 f → tsupport f ⊆ Icc (-Y) Y → 0 < A →
      640 * π * gapEnergy * primeVariance f N ≤ 3 * gapMass ^ 2 * A ^ 2 →
      volume (Icc c (c + 10 * ((m : ℝ) + 1) * σ) ∩ {t : ℝ | A ≤ ‖primePolynomial f N (-t / (2 * π))‖}) ≤
        ENNReal.ofReal (10 * ((m : ℝ) + 1) * σ / 80) := by
    intro f A hf hfs hA hV
    refine (volume_bad_heights_le hY0.le hf hfs hL hA c).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hV (by positivity : (0 : ℝ) ≤ 10 * ((m : ℝ) + 1) * σ / 80)
    nlinarith only [this]
  have hbad : volume (Icc c (c + 2 * (((5 * (m + 1) : ℕ) : ℝ)) * σ) \ G) <
      ENNReal.ofReal (σ / 2 * ((((5 * (m + 1) : ℕ) : ℝ)) - ((4 * m + 3 : ℕ) : ℝ))) := by
    rw [hM, hMn]
    have hsub : Icc c (c + 10 * ((m : ℝ) + 1) * σ) \ G ⊆
        (Icc c (c + 10 * ((m : ℝ) + 1) * σ) ∩ {t : ℝ | A₁ ≤ ‖primePolynomial (minorantTest Y) N (-t / (2 * π))‖}) ∪
        (Icc c (c + 10 * ((m : ℝ) + 1) * σ) ∩ {t : ℝ | A₂ ≤ ‖primePolynomial (minorantTestD Y) N (-t / (2 * π))‖}) := by
      rintro t ⟨ht, htG⟩
      simp only [hG, Set.mem_inter_iff, Set.mem_setOf_eq, not_and_or, not_lt] at htG
      rcases htG with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
    have h1 := hvol (minorantTest Y) A₁ (minorantTest_contDiff Y) (tsupport_minorantTest hY0) hA₁0 hV1
    have h2 := hvol (minorantTestD Y) A₂ (minorantTestD_contDiff Y) (tsupport_minorantTestD hY0) hA₂0 hV2
    refine (measure_mono hsub).trans_lt ((measure_union_le _ _).trans_lt ?_)
    refine (add_le_add h1 h2).trans_lt ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith only [hσ, hm0]
  have hzero : ∀ t ∈ Icc c (c + 2 * (((5 * (m + 1) : ℕ) : ℝ)) * σ), t ∈ G →
      ∃ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| < σ / 4 := by
    intro t ht htG
    rw [hM] at ht
    obtain ⟨hG1, hG2⟩ := htG
    simp only [Set.mem_setOf_eq] at hG1 hG2
    have hft := hfar t ht
    have hLt : Lₛ ≤ Real.log (1 + |t| / 4) :=
      Real.log_le_log (by positivity) (by linarith only [hft])
    have hσ4 : 0 < σ / 4 := by positivity
    refine exists_zero_near_of_minorant hσ4 (by linarith only [hσ1, hσ]) hY hσY hE₁ hB (hsL.trans hLt)
      (hst.trans hft) ?_ ?_ ?_
    · intro ρ hρ hρt
      refine re_eq_half_of_mem_carrier hRH hρ ?_
      have h1 : |ρ.im| ≤ |ρ.im - t| + |t| := by
        have := abs_sub_abs_le_abs_sub ρ.im t
        linarith only [this]
      linarith only [h1, hρt, hT t ht]
    · refine hG1.le.trans ?_
      rw [hA₁]
      have := mul_le_mul_of_nonneg_left hLt (by positivity : (0 : ℝ) ≤ Y * minorantE₀)
      linarith only [this]
    · refine hG2.le.trans ?_
      rw [hA₂]
      have := mul_le_mul_of_nonneg_left hLt (by positivity : (0 : ℝ) ≤ (σ / 4) ^ 2 * Y * minorantE₀)
      linarith only [this]
  obtain ⟨node, hnode, hsep⟩ := exists_separated_zeros_of_volume_lt (c := c) hσ hbad hzero
  refine ⟨node, fun j hj => ?_, hsep⟩
  rw [← hM]
  exact hnode j hj

end

end GaloisForLFunctions.VerifiedHeightRungs
