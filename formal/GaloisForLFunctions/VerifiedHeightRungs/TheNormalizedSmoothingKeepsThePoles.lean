import GaloisForLFunctions.RHTower.ZetaWeilFormHeightReduction
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon

/-!
# A normalized smoothing that keeps the pole terms

Let `q = kernelQ b` be the normalized transform of `w_b = (b² − u²)₊^{5/2}`, `g = smoothedTest b f`, so `h_g = h_f q²`.
At the poles `q(±i/2) = r₀` is real and `1 + b²/2560 ≤ r₀ ≤ 1 + b²/4` (`kernelQ_half`). With `κ = r₀²`, the pole terms of
`W(f, g)` are exactly `κ` times those of `W(f, f)`, for every test (no polar constraint), hence

  `W(f, f) − W(f, g)/κ = ∫ |h_f|² (1 − q²/κ) (μ + P_X)` (`re_W_self_ge`).

On the real line `1 − q²/κ ≥ 1 − 1/κ =: ϖ > 0`, of size `b²`. So the difference pays `ϖ ∫|h_f|²` everywhere the symbol is
at least one, and costs at most `D ∫_{|τ| ≤ T₁} |h_f|²` below, `D ≍ b²`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-! ## The weight -/

theorem sinhTestWeight_le {b : ℝ} (hb : 0 < b) (u : ℝ) : sinhTestWeight b u ≤ b ^ 5 := by
  have hb5 : (0 : ℝ) ≤ b ^ 5 := by positivity
  by_cases hu : |u| ≤ b
  · have h0 : 0 ≤ b ^ 2 - u ^ 2 := by
      have := sq_le_sq' (abs_le.1 hu).1 (abs_le.1 hu).2
      linarith only [this]
    have h1 : b ^ 2 - u ^ 2 ≤ b ^ 2 := by nlinarith only [sq_nonneg u]
    have h2 := Real.rpow_le_rpow h0 h1 (by norm_num : (0 : ℝ) ≤ 5 / 2)
    refine h2.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb.le, ← Real.rpow_natCast b 5]
    norm_num
  · rw [sinhTestWeight_eq_zero hb.le (not_le.1 hu)]
    exact hb5

theorem sinhTestWeight_ge {b u : ℝ} (hb : 0 < b) (hu : |u| ≤ b / 2) : 9 / 20 * b ^ 5 ≤ sinhTestWeight b u := by
  have hu2 : u ^ 2 ≤ b ^ 2 / 4 := by
    have := sq_le_sq' (abs_le.1 hu).1 (abs_le.1 hu).2
    nlinarith only [this]
  have hx : 3 * b ^ 2 / 4 ≤ b ^ 2 - u ^ 2 := by linarith only [hu2]
  have hx0 : (0 : ℝ) ≤ 3 * b ^ 2 / 4 := by positivity
  have h1 := Real.rpow_le_rpow hx0 hx (by norm_num : (0 : ℝ) ≤ 5 / 2)
  refine le_trans ?_ h1
  have hsplit : (3 * b ^ 2 / 4 : ℝ) ^ ((5 : ℝ) / 2) = (3 * b ^ 2 / 4) ^ 2 * Real.sqrt (3 * b ^ 2 / 4) := by
    rw [Real.sqrt_eq_rpow, show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num]
    rw [Real.rpow_add' hx0 (by norm_num), Real.rpow_two]
  rw [hsplit]
  have hsq : 4 / 5 * b ≤ Real.sqrt (3 * b ^ 2 / 4) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [sq_nonneg b]
  have hp : (0 : ℝ) ≤ (3 * b ^ 2 / 4) ^ 2 := sq_nonneg _
  calc
    9 / 20 * b ^ 5 = (3 * b ^ 2 / 4) ^ 2 * (4 / 5 * b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hp

theorem kernelMass_le {b : ℝ} (hb : 0 < b) : kernelMass b ≤ 2 * b ^ 6 := by
  have h := integral_le_of_bound_on_Icc (g := sinhTestWeight b) (a := b) (M := b ^ 5) hb.le
    (sinhTestWeight_nonneg b) (fun u _ => sinhTestWeight_le hb u)
    (fun u hu => sinhTestWeight_eq_zero hb.le hu)
  refine h.trans (le_of_eq ?_)
  ring

theorem one_add_sq_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h1 := Real.cosh_two_mul (x / 2)
  have h2 := Real.cosh_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h1
  have h3 : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rw [← sq_abs (x / 2), ← sq_abs (Real.sinh (x / 2)), Real.abs_sinh]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    exact Real.self_le_sinh_iff.2 (abs_nonneg _)
  nlinarith only [h1, h2, h3]

/-! ## The value at the poles -/

theorem integrable_weight_mul {b : ℝ} (hb : 0 ≤ b) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Integrable fun u => sinhTestWeight b u * φ u := by
  refine Continuous.integrable_of_hasCompactSupport ((sinhTestWeight_contDiff b).continuous.mul hφ) ?_
  refine HasCompactSupport.mul_right ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -b) (b := b)) fun u hu => ?_
  exact abs_le.1 (sinhTestWeight_supp hb u hu)

/-- `q(±i/2)` is real, and its excess over one has the size `b²`. -/
theorem kernelQ_half {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ r₀ : ℝ, kernelQ b (I / 2) = (r₀ : ℂ) ∧ kernelQ b (-I / 2) = (r₀ : ℂ) ∧
      1 + b ^ 2 / 2560 ≤ r₀ ∧ r₀ ≤ 1 + b ^ 2 / 4 := by
  obtain ⟨m, hm⟩ : ∃ m, m = kernelMass b := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact kernelMass_pos hb hb1
  have hm6 : m ≤ 2 * b ^ 6 := by rw [hm]; exact kernelMass_le hb
  have hexp1 : Continuous fun u : ℝ => Real.exp (-(u / 2)) := by fun_prop
  have hexp2 : Continuous fun u : ℝ => Real.exp (u / 2) := by fun_prop
  have hcosh : Continuous fun u : ℝ => Real.cosh (u / 2) := by fun_prop
  have i1 := integrable_weight_mul hb.le hexp1
  have i2 := integrable_weight_mul hb.le hexp2
  have ic := integrable_weight_mul hb.le hcosh
  have hswap : ∫ u, sinhTestWeight b u * Real.exp (-(u / 2)) = ∫ u, sinhTestWeight b u * Real.exp (u / 2) := by
    rw [← integral_neg_eq_self (fun u => sinhTestWeight b u * Real.exp (-(u / 2)))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [sinhTestWeight_even, neg_div, neg_neg]
  obtain ⟨c, hc⟩ : ∃ c, c = ∫ u, sinhTestWeight b u * Real.cosh (u / 2) := ⟨_, rfl⟩
  have hcA : ∫ u, sinhTestWeight b u * Real.exp (u / 2) = c := by
    have h : c = ((∫ u, sinhTestWeight b u * Real.exp (u / 2)) +
        ∫ u, sinhTestWeight b u * Real.exp (-(u / 2))) / 2 := by
      have hfun : (fun u => sinhTestWeight b u * Real.cosh (u / 2)) = fun u =>
          (sinhTestWeight b u * Real.exp (u / 2) + sinhTestWeight b u * Real.exp (-(u / 2))) / 2 := by
        funext u
        rw [Real.cosh_eq]
        ring
      rw [hc, hfun, integral_div, integral_add i2 i1]
    rw [hswap] at h
    linarith only [h]
  have hcB : ∫ u, sinhTestWeight b u * Real.exp (-(u / 2)) = c := by rw [hswap, hcA]
  have hval1 : paperFT (fun u => ((sinhTestWeight b u : ℝ) : ℂ)) (I / 2) = (c : ℂ) := by
    rw [paperFT_def, ← hcB, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have e : I * (I / 2) * (u : ℂ) = ((-(u / 2) : ℝ) : ℂ) := by
      have : I * (I / 2) * (u : ℂ) = (I * I) * (u / 2) := by ring
      rw [this, Complex.I_mul_I]
      push_cast
      ring
    simp only
    rw [e, ← Complex.ofReal_exp]
    push_cast
    rfl
  have hval2 : paperFT (fun u => ((sinhTestWeight b u : ℝ) : ℂ)) (-I / 2) = (c : ℂ) := by
    rw [paperFT_def, ← hcA, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have e : I * (-I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
      have : I * (-I / 2) * (u : ℂ) = -(I * I) * (u / 2) := by ring
      rw [this, Complex.I_mul_I]
      push_cast
      ring
    simp only
    rw [e, ← Complex.ofReal_exp]
    push_cast
    rfl
  -- Bounds on `c`.
  have hlow : m + 9 / 10240 * b ^ 8 ≤ c := by
    have hdiff : c - m = ∫ u, sinhTestWeight b u * (Real.cosh (u / 2) - 1) := by
      have hmi : Integrable (sinhTestWeight b) := by
        simpa using integrable_weight_mul hb.le (φ := fun _ => (1 : ℝ)) continuous_const
      rw [hc, hm, kernelMass, ← integral_sub ic hmi]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only
      ring
    have hnn : ∀ u, 0 ≤ sinhTestWeight b u * (Real.cosh (u / 2) - 1) := fun u =>
      mul_nonneg (sinhTestWeight_nonneg b u) (by linarith only [Real.one_le_cosh (u / 2)])
    have hi : Integrable fun u => sinhTestWeight b u * (Real.cosh (u / 2) - 1) :=
      integrable_weight_mul hb.le (φ := fun u => Real.cosh (u / 2) - 1) (hcosh.sub continuous_const)
    have hset : ∫ u in Icc (b / 4) (b / 2), sinhTestWeight b u * (Real.cosh (u / 2) - 1) ≤
        ∫ u, sinhTestWeight b u * (Real.cosh (u / 2) - 1) :=
      setIntegral_le_integral hi (Eventually.of_forall hnn)
    have hconst : ∫ u in Icc (b / 4) (b / 2), (9 / 20 * b ^ 5 * (b ^ 2 / 128) : ℝ) ≤
        ∫ u in Icc (b / 4) (b / 2), sinhTestWeight b u * (Real.cosh (u / 2) - 1) := by
      refine setIntegral_mono_on continuous_const.integrableOn_Icc hi.integrableOn
        measurableSet_Icc fun u hu => ?_
      have hu0 : 0 ≤ u := by linarith only [hu.1, hb]
      have huabs : |u| ≤ b / 2 := by rw [abs_of_nonneg hu0]; exact hu.2
      have h1 := sinhTestWeight_ge hb huabs
      have h2 := one_add_sq_le_cosh (u / 2)
      have h3 : b ^ 2 / 128 ≤ Real.cosh (u / 2) - 1 := by
        have : (b / 4) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu.1 2
        nlinarith only [h2, this]
      exact mul_le_mul h1 h3 (by positivity) (sinhTestWeight_nonneg b u)
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith only [hb])] at hconst
    have hsmul : (b / 2 - b / 4) • (9 / 20 * b ^ 5 * (b ^ 2 / 128) : ℝ) = 9 / 10240 * b ^ 8 := by
      rw [smul_eq_mul]
      ring
    rw [hsmul] at hconst
    linarith only [hdiff, hconst, hset]
  have hup : c ≤ (1 + b ^ 2 / 4) * m := by
    rw [hc, hm, kernelMass, ← integral_const_mul]
    have hmi : Integrable fun u => (1 + b ^ 2 / 4) * sinhTestWeight b u := by
      simpa [mul_comm] using integrable_weight_mul hb.le (φ := fun _ => (1 + b ^ 2 / 4 : ℝ)) continuous_const
    refine integral_mono ic hmi fun u => ?_
    by_cases hw : sinhTestWeight b u = 0
    · simp [hw]
    have hu := sinhTestWeight_supp hb.le u hw
    have h1 : Real.cosh (u / 2) ≤ Real.exp ((u / 2) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    have hsq : u ^ 2 ≤ b ^ 2 := sq_le_sq' (abs_le.1 hu).1 (abs_le.1 hu).2
    have h2 : Real.exp ((u / 2) ^ 2 / 2) ≤ Real.exp (b ^ 2 / 8) := Real.exp_le_exp.2 (by nlinarith only [hsq])
    have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
    have h3 : Real.exp (b ^ 2 / 8) ≤ 1 + b ^ 2 / 4 := by
      have hy0 : 0 ≤ b ^ 2 / 8 := by positivity
      have hy1 : b ^ 2 / 8 < 1 := by linarith only [hb2]
      have := Real.exp_bound_div_one_sub_of_interval hy0 hy1
      refine this.trans ?_
      rw [div_le_iff₀ (by linarith only [hy1])]
      nlinarith only [hb2, sq_nonneg b]
    have hw0 := sinhTestWeight_nonneg b u
    have := mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hw0
    simp only at this ⊢
    linarith only [this]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  refine ⟨c / m, ?_, ?_, ?_, ?_⟩
  · rw [kernelQ, hval1, ← hm]
    push_cast
    rfl
  · rw [kernelQ, hval2, ← hm]
    push_cast
    rfl
  · rw [le_div_iff₀ hm0]
    have h4 : m * (b ^ 2 / 2560) ≤ 9 / 10240 * b ^ 8 := by
      have : m * (b ^ 2 / 2560) ≤ 2 * b ^ 6 * (b ^ 2 / 2560) :=
        mul_le_mul_of_nonneg_right hm6 (by positivity)
      have hb8 : 0 ≤ b ^ 8 := by positivity
      nlinarith only [this, hb8]
    linarith only [hlow, h4]
  · rw [div_le_iff₀ hm0]
    exact hup

/-! ## The explicit formula for a pair of tests -/

/-- The explicit formula for `W(f, h)`, with its pole terms. -/
theorem W_eq_pole_add_integral_bilinear {A : ℝ} {f h : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hfs : tsupport f ⊆ Icc (-A) A) (hhs : tsupport h ⊆ Icc (-A) A) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f h ρ) ∧
      zetaZeroConfig.W f h = paperFT (EF.weilTest f h) (I / 2) + paperFT (EF.weilTest f h) (-I / 2) +
        ∫ τ : ℝ, paperFT (EF.weilTest f h) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ) := by
  have hfs' : tsupport f ⊆ Icc (-(2 * A / 2)) (2 * A / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hhs' : tsupport h ⊆ Icc (-(2 * A / 2)) (2 * A / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hhc := hasCompactSupport_of_tsupport_subset_Icc hhs
  have hkd : ContDiff ℝ 2 (EF.weilTest f h) := EF.weilTest_contDiff hf hh.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f h) := EF.weilTest_hasCompactSupport hfc hhc
  have hks : tsupport (EF.weilTest f h) ⊆ Icc (-(2 * A)) (2 * A) := EF.tsupport_weilTest_subset hfs' hhs'
  have hFk := EF.integrable_fourier_of_contDiff_two hkd hkc
  have hμ := EF.integrable_paperFT_mul_mu hkd hkc gammaFacts
  have hPX := EF.integrable_paperFT_mul_PX (2 * A) hFk
  obtain ⟨hsum, heq⟩ := WeilEF.EF_lit_zetaZeroConfig (EF.weilTest f h) hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hh.continuous hfc hhc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (EF.weilTest f h) (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f h ρ := by
    ext ρ
    simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  refine ⟨hterm ▸ hsum, ?_⟩
  rw [ZeroConfig.W, ← hterm, heq, EF.literatureRHS, sub_eq_add_neg,
    EF.prime_term hkd.continuous hks hFk, EF.gamma_term,
    add_assoc (paperFT (EF.weilTest f h) (I / 2) + paperFT (EF.weilTest f h) (-I / 2)),
    ← integral_add hPX hμ]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  push_cast
  ring

/-- The pointwise form of the symbol estimate. -/
theorem symbol_pointwise {ϖ F V E s m M T₁ τ b : ℝ} (hϖ0 : 0 ≤ ϖ) (hF : ϖ ≤ F) (hF2 : F ≤ ϖ + (b * τ) ^ 2)
    (hE : 0 ≤ E) (hm : 0 ≤ m) (hV : -E ≤ V) (hV1 : T₁ < |τ| → 1 ≤ V) (hM : |τ| ≤ T₁ → m ≤ M)
    (hb : 0 ≤ b) (hT₁ : 0 ≤ T₁) (hs : s = ϖ + (ϖ + (b * T₁) ^ 2) * E) :
    ϖ * m - (Icc (-T₁) T₁).indicator (fun _ => s * M) τ ≤ m * F * V := by
  by_cases hτ : |τ| ≤ T₁
  · have hmem : τ ∈ Icc (-T₁) T₁ := abs_le.1 hτ
    rw [indicator_of_mem hmem]
    have hmM := hM hτ
    have hbτ : (b * τ) ^ 2 ≤ (b * T₁) ^ 2 := by
      rw [← sq_abs (b * τ), abs_mul, abs_of_nonneg hb]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hτ hb) 2
    have hF0 : 0 ≤ F := hϖ0.trans hF
    have hF3 : F ≤ ϖ + (b * T₁) ^ 2 := hF2.trans (by linarith only [hbτ])
    have h1 : -(F * E) ≤ F * V := by
      have := mul_le_mul_of_nonneg_left hV hF0
      linarith only [this]
    have h2 : F * E ≤ (ϖ + (b * T₁) ^ 2) * E := mul_le_mul_of_nonneg_right hF3 hE
    have h3 : m * (-((ϖ + (b * T₁) ^ 2) * E)) ≤ m * (F * V) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) hm
    have hG : 0 ≤ (ϖ + (b * T₁) ^ 2) * E := by positivity
    have h4 : m * ((ϖ + (b * T₁) ^ 2) * E) ≤ M * ((ϖ + (b * T₁) ^ 2) * E) :=
      mul_le_mul_of_nonneg_right hmM hG
    have h5 : ϖ * m ≤ ϖ * M := mul_le_mul_of_nonneg_left hmM hϖ0
    rw [hs]
    nlinarith only [h3, h4, h5]
  · have hmem : τ ∉ Icc (-T₁) T₁ := fun h => hτ (abs_le.2 h)
    rw [indicator_of_notMem hmem, sub_zero]
    have hV2 := hV1 (not_le.1 hτ)
    have hF0 : 0 ≤ F := hϖ0.trans hF
    have h1 : ϖ * 1 ≤ F * V := mul_le_mul hF hV2 (by norm_num) hF0
    have := mul_le_mul_of_nonneg_left h1 hm
    nlinarith only [this]

/-- **The symbol side.** With `κ = r₀²`, `ϖ = 1 − κ⁻¹`, `E = horizonExponent (e^{2(a+2)})` and `T₁ ≥ 4e^{E+2π}`, a bound
`|h_f|² ≤ M` on `|τ| ≤ T₁` gives
`Re W(f, f) ≥ κ⁻¹ Re W(f, g) + 2π ϖ ∫|f|² − D M 2T₁`, `D = ϖ + (ϖ + (bT₁)²) E/2π`. -/
theorem re_W_self_ge {a b T₁ M r₀ : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hr1 : kernelQ b (I / 2) = (r₀ : ℂ)) (hr2 : kernelQ b (-I / 2) = (r₀ : ℂ))
    (hr0 : 1 ≤ r₀)
    (hT₁ : 4 * Real.exp (horizonExponent (Real.exp (2 * (a + 2))) + 2 * π) ≤ T₁)
    (hM : ∀ τ : ℝ, |τ| ≤ T₁ → ‖paperFT f τ‖ ^ 2 ≤ M) :
    (r₀ ^ 2)⁻¹ * (zetaZeroConfig.W f (smoothedTest b f)).re +
        (1 - (r₀ ^ 2)⁻¹) * (2 * π * ∫ u, ‖f u‖ ^ 2) -
        ((1 - (r₀ ^ 2)⁻¹) + ((1 - (r₀ ^ 2)⁻¹) + (b * T₁) ^ 2) *
          (horizonExponent (Real.exp (2 * (a + 2))) / (2 * π))) * M * (2 * T₁) ≤
      (zetaZeroConfig.W f f).re := by
  obtain ⟨A, hAdef⟩ : ∃ A, A = a + 2 := ⟨_, rfl⟩
  rw [← hAdef] at hT₁ ⊢
  obtain ⟨E, hEdef⟩ : ∃ E, E = horizonExponent (Real.exp (2 * A)) := ⟨_, rfl⟩
  rw [← hEdef] at hT₁ ⊢
  have hE0 : 0 < E := by rw [hEdef]; exact horizonExponent_pos _
  have hX0 : (0 : ℝ) ≤ Real.exp (2 * A) := (Real.exp_pos _).le
  have hπ := Real.pi_pos
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = r₀ ^ 2 := ⟨_, rfl⟩
  have hκ1 : 1 ≤ κ := by rw [hκ]; nlinarith only [hr0]
  have hκ0 : 0 < κ := by linarith only [hκ1]
  rw [← hκ]
  have hinv1 : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ1
  have hinv0 : 0 < κ⁻¹ := inv_pos.2 hκ0
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, ϖ = 1 - κ⁻¹ := ⟨_, rfl⟩
  rw [← hϖ]
  have hϖ0 : 0 ≤ ϖ := by rw [hϖ]; linarith only [hinv1]
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hfA : tsupport f ⊆ Icc (-A) A := hfs.trans (Icc_subset_Icc (by linarith only [hAdef]) (by linarith only [hAdef]))
  obtain ⟨g, hgdef⟩ : ∃ g, g = smoothedTest b f := ⟨_, rfl⟩
  rw [← hgdef]
  have hg : ContDiff ℝ 2 g := by rw [hgdef]; exact smoothedTest_contDiff hb.le hf hfc
  have hgc : HasCompactSupport g := by rw [hgdef]; exact hasCompactSupport_smoothedTest hb.le hfc
  have hgA : tsupport g ⊆ Icc (-A) A := by
    rw [hgdef]
    exact (tsupport_smoothedTest_subset hb.le hfs).trans
      (Icc_subset_Icc (by linarith only [hAdef, hb1]) (by linarith only [hAdef, hb1]))
  have h1 := (W_eq_pole_add_integral_bilinear hf hf hfA hfA).2
  have h2 := (W_eq_pole_add_integral_bilinear hf hg hfA hgA).2
  have hfacf := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  have hfacg := EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc
  have hgval (z : ℂ) : paperFT g z = paperFT f z * kernelQ b z ^ 2 := by
    rw [hgdef]
    exact paperFT_smoothedTest hb.le hf.continuous hfc z
  -- The pole terms scale by `κ`.
  have hc1 : (starRingEnd ℂ) (I / 2) = -I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : (starRingEnd ℂ) (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  have hκC : ((κ : ℝ) : ℂ) = (r₀ : ℂ) ^ 2 := by rw [hκ]; push_cast; rfl
  have hp1 : paperFT (EF.weilTest f g) (I / 2) = (κ : ℂ) * paperFT (EF.weilTest f f) (I / 2) := by
    rw [hfacg, hfacf, hc1, hgval, hr2, map_mul, map_pow, Complex.conj_ofReal, hκC]
    ring
  have hp2 : paperFT (EF.weilTest f g) (-I / 2) = (κ : ℂ) * paperFT (EF.weilTest f f) (-I / 2) := by
    rw [hfacg, hfacf, hc2, hgval, hr1, map_mul, map_pow, Complex.conj_ofReal, hκC]
    ring
  have hk1 := EF.weilTest_contDiff hf hf.continuous hfc
  have hk1c := EF.weilTest_hasCompactSupport hfc hfc
  have hk2 := EF.weilTest_contDiff hf hg.continuous hfc
  have hk2c := EF.weilTest_hasCompactSupport hfc hgc
  have i1 := integrable_paperFT_mul_mu_add_PX hk1 hk1c (2 * A)
  have i2 := integrable_paperFT_mul_mu_add_PX hk2 hk2c (2 * A)
  obtain ⟨V, hV⟩ : ∃ V : ℝ → ℝ, V = fun τ => mu τ + PX (Real.exp (2 * A)) τ := ⟨_, rfl⟩
  have hκCne : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0.ne'
  -- The difference is the symbol integral.
  have hdiff : zetaZeroConfig.W f f - (κ⁻¹ : ℝ) * zetaZeroConfig.W f g =
      ∫ τ : ℝ, (paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ) -
        (κ⁻¹ : ℝ) * (paperFT (EF.weilTest f g) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ))) := by
    rw [integral_sub i1 (i2.const_mul _), integral_const_mul, h1, h2, hp1, hp2]
    push_cast
    field_simp
    ring
  have i12 : Integrable (fun τ : ℝ => paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ) -
      (κ⁻¹ : ℝ) * (paperFT (EF.weilTest f g) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ))) :=
    i1.sub (i2.const_mul ((κ⁻¹ : ℝ) : ℂ))
  have iR : Integrable (fun τ : ℝ => (paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ) -
      (κ⁻¹ : ℝ) * (paperFT (EF.weilTest f g) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ))).re) := i12.re
  have hre := integral_re i12
  simp only [RCLike.re_to_complex] at hre
  have hredef : (zetaZeroConfig.W f f).re - κ⁻¹ * (zetaZeroConfig.W f g).re =
      ∫ τ : ℝ, (paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ) -
        (κ⁻¹ : ℝ) * (paperFT (EF.weilTest f g) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ))).re := by
    rw [hre, ← hdiff, Complex.sub_re, Complex.re_ofReal_mul]
  -- The pointwise bound.
  obtain ⟨D, hD⟩ : ∃ D, D = ϖ + (ϖ + (b * T₁) ^ 2) * (E / (2 * π)) := ⟨_, rfl⟩
  rw [← hD]
  have hT₁0 : 0 ≤ T₁ := le_trans (by positivity) hT₁
  have hpt : ∀ τ : ℝ, ϖ * ‖paperFT f τ‖ ^ 2 - (Icc (-T₁) T₁).indicator (fun _ => D * M) τ ≤
      (paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ) -
        (κ⁻¹ : ℝ) * (paperFT (EF.weilTest f g) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ))).re := by
    intro τ
    obtain ⟨r, hr, hr0', hr1'⟩ := kernelQ_real hb hb1 τ
    have hgτ : paperFT g ((starRingEnd ℂ) (τ : ℂ)) = paperFT f τ * (r : ℂ) ^ 2 := by
      rw [Complex.conj_ofReal, hgval, hr]
    have hval : paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ) -
        (κ⁻¹ : ℝ) * (paperFT (EF.weilTest f g) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ)) =
        ((‖paperFT f τ‖ ^ 2 * (1 - r ^ 2 * κ⁻¹) * (mu τ + PX (Real.exp (2 * A)) τ) : ℝ) : ℂ) := by
      rw [hfacf, hfacg, hgτ]
      simp only [Complex.conj_ofReal, map_mul, map_pow]
      have hn : paperFT f τ * (starRingEnd ℂ) (paperFT f τ) = ((‖paperFT f τ‖ : ℝ) : ℂ) ^ 2 :=
        Complex.mul_conj' _
      push_cast
      linear_combination ((mu τ + PX (Real.exp (2 * A)) τ : ℂ) * (1 - (r : ℂ) ^ 2 * (κ : ℂ)⁻¹)) * hn
    rw [hval, Complex.ofReal_re]
    have hsym := mu_add_PX_ge hX0 τ
    rw [← hEdef] at hsym
    have hlog0 : 0 ≤ Real.log (1 + |τ| / 4) := Real.log_nonneg (by linarith only [abs_nonneg τ])
    refine symbol_pointwise (b := b) (T₁ := T₁) (E := E / (2 * π)) (s := D) (M := M) hϖ0 ?_ ?_ (by positivity)
      (sq_nonneg _) ?_ ?_ (hM τ) hb.le hT₁0 hD
    · rw [hϖ]
      have : r ^ 2 * κ⁻¹ ≤ 1 * κ⁻¹ := mul_le_mul_of_nonneg_right (by linarith only [hr0']) hinv0.le
      linarith only [this]
    · have h3 : (1 - r ^ 2) * κ⁻¹ ≤ (b * τ) ^ 2 * 1 :=
        mul_le_mul hr1' hinv1 hinv0.le (sq_nonneg _)
      rw [hϖ]
      linarith only [h3]
    · refine le_trans ?_ hsym
      have : -(E / (2 * π)) = (0 - E) / (2 * π) := by ring
      rw [this]
      exact div_le_div_of_nonneg_right (by linarith only [hlog0]) (by positivity)
    · intro hτ
      refine le_trans ?_ hsym
      rw [le_div_iff₀ (by positivity), one_mul]
      have h4 : Real.exp (E + 2 * π) ≤ 1 + |τ| / 4 := by linarith only [hτ, hT₁]
      have h5 := Real.log_le_log (Real.exp_pos _) h4
      rw [Real.log_exp] at h5
      linarith only [h5]
  -- Integration.
  have hplan := integral_norm_sq_paperFT_eq hf hfs
  have hi2 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 := integrable_normSq_paperFT hf hfs
  have hind : Integrable ((Icc (-T₁) T₁).indicator (fun _ : ℝ => D * M)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hlowI : Integrable (fun τ : ℝ => ϖ * ‖paperFT f τ‖ ^ 2 -
      (Icc (-T₁) T₁).indicator (fun _ => D * M) τ) := (hi2.const_mul ϖ).sub hind
  have hlower := integral_mono hlowI iR hpt
  rw [integral_sub (hi2.const_mul ϖ) hind, integral_const_mul, hplan, integral_indicator measurableSet_Icc,
    setIntegral_const, Real.volume_real_Icc_of_le (by linarith only [hT₁0]), smul_eq_mul, ← hredef] at hlower
  have e : T₁ - -T₁ = 2 * T₁ := by ring
  rw [e] at hlower
  nlinarith only [hlower]

end

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.kernelQ_half
#print axioms GaloisForLFunctions.VerifiedHeightRungs.re_W_self_ge
