import GaloisForLFunctions.ZeroConfigurationGeometry.IsolationIdentifiesTheCluster
import GaloisForLFunctions.ZeroConfigurationGeometry.ShallowConfigurationsAreResolvedLocally
import GaloisForLFunctions.ZeroConfigurationGeometry.WindowsBlindToALattice
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.ZeroConfigurationGeometry.PaleyWienerWindows

/-!
# Configurations of one depth are resolved at the Ingham scale

Tempered mimics at aperture `a > π/(2g)`, whose union is `g`-separated apart from FE partners
and lies at one depth `|Re ρ − ½| = δ`, coincide (`eq_of_mimic_of_oneDepth`). This is the Ingham
threshold, half the any-depth threshold `π/g`.

1. **Modulated lag identity.** For a bump `b` of width `w`, the translated modulated bumps
   `b(u ∓ x/2) e^{iτ(u ∓ x/2)}` are windows of aperture `a` for `|x|/2 + w ≤ a`. Their image of a
   point is `e^{iγx} K_b(γ + τ)` with `K_b(ζ) = b̂(ζ) conj b̂(conj ζ) = ĥ_b(ζ)`, `h_b = b ⋆ b̃`,
   so `Σ_z c(z) e^{iγ_z x} K_b(γ_z + τ) = 0` for all `τ` (`tsum_modLag_eq_zero`).
2. **Averaging over the modulation.** Against `φ` with `φ̂ = ψ` (`invWeight`), Fubini over the
   zero sum gives `Σ_z c(z) e^{iγ_z x} (h_b ψ)^(γ_z) = 0` (`tsum_averaged_lag_eq_zero`).
3. **Folding FE pairs.** With `ψ = χ/(2cosh(δ(· + x)))`, an FE pair `t ∓ iδ` contributes
   `e^{itx} (h_b χ)^(t)` (`pair_term_eq`). The depth enters only through the weight `cosh`, which
   the choice of `ψ` divides out (`tsum_sites_oneDepth_eq_zero`).
4. **Ingham.** The site sum is a summable exponential sum with `g`-separated real frequencies,
   vanishing on `[−V, V]`, `V = 2(a − w) > π/g`. So every coefficient vanishes
   (`coeff_eq_zero_of_tsum_exp_eq_zero`). Since `χ` is arbitrary, `h_b = 0`, against
   `ĥ_b(0) = |b̂(0)|² ≠ 0`.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-! ### Translated modulated bumps -/

/-- The bump `b`, modulated by `e^{iτu}` and translated: `u ↦ b(u + s) e^{iτ(u + s)}`. -/
def modBump (b : ℝ → ℂ) (τ s : ℝ) : ℝ → ℂ := fun u => b (u + s) * cexp (I * τ * (u + s : ℝ))

/-- The pair weight of a bump: `K_b(ζ) = b̂(ζ) conj b̂(conj ζ)`. -/
def bumpWeight (b : ℝ → ℂ) (ζ : ℂ) : ℂ := paperFT b ζ * conj (paperFT b (conj ζ))

theorem paperFT_modBump (b : ℝ → ℂ) (τ s : ℝ) (w : ℂ) :
    paperFT (modBump b τ s) w = cexp (-(I * w * s)) * paperFT b (w + τ) := by
  calc paperFT (modBump b τ s) w
      = paperFT (fun u => (fun v : ℝ => b v * cexp (I * (τ : ℂ) * (v : ℂ))) (u + s)) w := rfl
    _ = cexp (-(I * w * s)) * paperFT (fun v : ℝ => b v * cexp (I * (τ : ℂ) * (v : ℂ))) w :=
        paperFT_shift (fun v : ℝ => b v * cexp (I * (τ : ℂ) * (v : ℂ))) s w
    _ = _ := by
      congr 1
      rw [paperFT_def, paperFT_def]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring

theorem modBump_apertureWindow {b : ℝ → ℂ} {w a : ℝ} (hb : ContDiff ℝ 2 b)
    (hbs : tsupport b ⊆ Icc (-w) w) {τ s : ℝ} (hs : |s| + w ≤ a) :
    ApertureWindow a (modBump b τ s) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ 2 fun u : ℝ => b (u + s) := hb.comp (contDiff_id.add contDiff_const)
    have h2 : ContDiff ℝ 2 fun u : ℝ => cexp (I * τ * ((u + s : ℝ) : ℂ)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (contDiff_id.add contDiff_const))).cexp
    exact h1.mul h2
  · refine (tsupport_mul_subset_left).trans ?_
    have : tsupport (fun u : ℝ => b (u + s)) ⊆ (fun u => u + s) ⁻¹' tsupport b := by
      refine closure_minimal (fun u hu => subset_closure hu) ?_
      exact (isClosed_tsupport b).preimage (continuous_id.add continuous_const)
    refine this.trans fun u hu => ?_
    have h := hbs hu
    simp only [Set.mem_Icc] at h ⊢
    constructor <;> linarith [abs_le.mp (le_refl |s|), neg_abs_le s, le_abs_self s]

/-- **The image of a point under translated modulated bumps** is `e^{iγx} K_b(γ + τ)`. -/
theorem pointImage_modBump (b : ℝ → ℂ) (τ x : ℝ) (z : ℂ) :
    pointImage (modBump b τ (-(x / 2))) (modBump b τ (x / 2)) z =
      cexp (I * gammaOf z * x) * bumpWeight b (gammaOf z + τ) := by
  rw [pointImage, paperFT_modBump, paperFT_modBump, bumpWeight, map_mul, ← Complex.exp_conj]
  have h1 : conj (conj (gammaOf z) + (τ : ℂ)) = gammaOf z + τ := by
    rw [map_add, Complex.conj_conj, Complex.conj_ofReal]
  have h2 : conj (gammaOf z) + (τ : ℂ) = conj (gammaOf z + τ) := by
    rw [map_add, Complex.conj_ofReal]
  rw [h2]
  have h3 : conj (-(I * conj (gammaOf z) * ((x / 2 : ℝ) : ℂ))) = I * gammaOf z * ((x / 2 : ℝ) : ℂ) := by
    rw [map_neg, map_mul, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]; ring
  rw [h3]
  have h4 : cexp (-(I * gammaOf z * ((-(x / 2) : ℝ) : ℂ))) * cexp (I * gammaOf z * ((x / 2 : ℝ) : ℂ)) =
      cexp (I * gammaOf z * x) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← h4]
  ring

/-- **The modulated lag identity.** Mimics at aperture `a` satisfy
`Σ_z c(z) e^{iγ_z x} K_b(γ_z + τ) = 0` for every `τ` and `|x|/2 + w ≤ a`. -/
theorem tsum_modLag_eq_zero {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {a : ℝ} (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {b : ℝ → ℂ} {w : ℝ}
    (hb : ContDiff ℝ 2 b) (hbs : tsupport b ⊆ Icc (-w) w) {x : ℝ} (hx : |x| / 2 + w ≤ a)
    (τ : ℝ) :
    ∑' z, multDiff Z Z' z * (cexp (I * gammaOf z * x) * bumpWeight b (gammaOf z + τ)) = 0 := by
  have hs1 : |(-(x / 2))| + w ≤ a := by rw [abs_neg, abs_div, abs_two]; linarith
  have hs2 : |x / 2| + w ≤ a := by rw [abs_div, abs_two]; linarith
  have hF := modBump_apertureWindow (τ := τ) hb hbs hs1
  have hG := modBump_apertureWindow (τ := τ) hb hbs hs2
  have h := W_sub_W_eq_tsum hZ hZ' hF.1 hF.hasCompactSupport hG.1 hG.hasCompactSupport
  rw [W_eq_of_mimic hZ hZ' hW hF hG, sub_self] at h
  rw [h]
  exact tsum_congr fun z => by rw [pointImage_modBump]

/-! ### Averaging over the modulation -/

theorem bumpWeight_eq_paperFT {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (ζ : ℂ) : bumpWeight b ζ = paperFT (EF.weilTest b b) ζ := by
  rw [EF.paperFT_weilTest hb hb hbc hbc, bumpWeight]

/-- **Fubini for the modulation average.** For integrable `φ`,
`∫ φ(τ) K_b(γ + τ) dτ = (h_b · φ̂)^(γ)`, `h_b = b ⋆ b̃`, `φ̂ = paperFT φ`. -/
theorem integral_mul_bumpWeight {b φ : ℝ → ℂ} (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b)
    (hφ : Integrable φ) (γ : ℂ) :
    ∫ τ : ℝ, φ τ * bumpWeight b (γ + τ) =
      paperFT (fun u => EF.weilTest b b u * paperFT φ u) γ := by
  set h := EF.weilTest b b with hh
  have hhs : ContDiff ℝ 2 h := EF.weilTest_contDiff hb hb.continuous hbc
  have hhc : HasCompactSupport h := by
    rw [hh, EF.weilTest]
    exact hbc.convolution (ContinuousLinearMap.mul ℝ ℂ) (EF.hasCompactSupport_tilde hbc)
  -- the integrand on `ℝ × ℝ`
  set F : ℝ → ℝ → ℂ := fun τ u => φ τ * (h u * cexp (I * γ * u)) * cexp (I * τ * u) with hF
  have hHi : Integrable fun u : ℝ => h u * cexp (I * γ * u) :=
    (hhs.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hhc.mul_right
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    have h1 := hφ.mul_prod hHi
    refine h1.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun p => ?_)
    rw [Complex.norm_exp]
    simp
  have hswap := integral_integral_swap hFi
  -- both sides as iterated integrals
  have hL : ∫ τ : ℝ, φ τ * bumpWeight b (γ + τ) = ∫ τ : ℝ, ∫ u : ℝ, F τ u := by
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    rw [bumpWeight_eq_paperFT hb.continuous hbc, paperFT_def, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF]
    rw [show cexp (I * (γ + τ) * u) = cexp (I * γ * u) * cexp (I * τ * u) by
      rw [← Complex.exp_add]; ring_nf]
    ring
  have hR : paperFT (fun u => h u * paperFT φ u) γ = ∫ u : ℝ, ∫ τ : ℝ, F τ u := by
    rw [paperFT_def]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF]
    rw [paperFT_def, mul_right_comm, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    rw [show I * (u : ℂ) * (τ : ℂ) = I * (τ : ℂ) * (u : ℂ) by ring]
    ring
  rw [hL, hR, hswap]

/-- Peetre's inequality: `(1 + |t + τ|)^{−2} ≤ (1 + |τ|)²/(1 + |t|)²`. -/
theorem inv_one_add_abs_sq_le (t τ : ℝ) :
    ((1 + |t + τ|) ^ 2)⁻¹ ≤ (1 + |τ|) ^ 2 / (1 + |t|) ^ 2 := by
  have h1 : 1 + |t| ≤ (1 + |t + τ|) * (1 + |τ|) := by
    have := abs_sub_abs_le_abs_sub t (-τ)
    rw [sub_neg_eq_add, abs_neg] at this
    nlinarith [abs_nonneg (t + τ), abs_nonneg τ]
  have h2 : (1 + |t|) ^ 2 ≤ ((1 + |t + τ|) * (1 + |τ|)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  rw [mul_pow] at h2
  rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, one_le_div (by positivity)]
  linarith

theorem integrable_inv_one_add_abs_sq :
    Integrable fun τ : ℝ => ((1 + |τ|) ^ 2)⁻¹ := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  refine h.congr (Eventually.of_forall fun τ => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `(1 + |Re γ|)^{−2} ≤ (5/4)(1 + |γ|²)^{−1}` on the strip `|Im γ| ≤ 1/2`. -/
theorem inv_one_add_abs_re_sq_le {γ : ℂ} (hγ : |γ.im| ≤ 1 / 2) :
    ((1 + |γ.re|) ^ 2)⁻¹ ≤ 5 / 4 / (1 + Complex.normSq γ) := by
  have hn : Complex.normSq γ = γ.re ^ 2 + γ.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have him : γ.im ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg γ.im, sq_abs γ.im]
  have h1 : 1 + Complex.normSq γ ≤ 5 / 4 * (1 + |γ.re|) ^ 2 := by
    rw [hn]; nlinarith [abs_nonneg γ.re, sq_abs γ.re]
  have hpos : 0 < 1 + Complex.normSq γ := by linarith [Complex.normSq_nonneg γ]
  rw [inv_le_comm₀ (by positivity) (div_pos (by norm_num) hpos), inv_div,
    div_le_iff₀ (by norm_num)]
  linarith

/-- **The averaged lag identity.** For a decaying weight `φ`, mimics satisfy
`Σ_z c(z) e^{iγ_z x} (h_b φ̂)^(γ_z) = 0` for `|x|/2 + w ≤ a`. -/
theorem tsum_averaged_lag_eq_zero {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a : ℝ} (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    {b : ℝ → ℂ} {w : ℝ} (hw : 0 ≤ w) (hb : ContDiff ℝ 2 b) (hbs : tsupport b ⊆ Icc (-w) w)
    {x : ℝ} (hx : |x| / 2 + w ≤ a) {φ : ℝ → ℂ} {Cφ : ℝ} (hφc : Continuous φ)
    (hφd : ∀ τ, ‖φ τ‖ ≤ Cφ * ((1 + |τ|) ^ 4)⁻¹) :
    ∑' z, multDiff Z Z' z * (cexp (I * gammaOf z * x) *
      paperFT (fun u => EF.weilTest b b u * paperFT φ u) (gammaOf z)) = 0 := by
  classical
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport b) hbs
  set h := EF.weilTest b b with hh
  have hhs : ContDiff ℝ 2 h := EF.weilTest_contDiff hb hb.continuous hbc
  have hhsupp : ∀ u, h u ≠ 0 → |u| ≤ 2 * w := by
    have hbs' : tsupport b ⊆ Icc (-(2 * w / 2)) (2 * w / 2) := by
      rw [show 2 * w / 2 = w by ring]; exact hbs
    exact RHTower.weilTest_abs_le hbs' hbs'
  have hhc : HasCompactSupport h := hasCompactSupport_of_support_subset_abs hhsupp
  have hφi : Integrable φ := by
    have hint : Integrable fun τ : ℝ => Cφ * ((1 + |τ|) ^ 4)⁻¹ := by
      refine (integrable_inv_one_add_abs_sq.mono' ?_ ?_).const_mul Cφ
      · exact (Continuous.inv₀ (by fun_prop) fun τ => by positivity :
          Continuous fun τ : ℝ => ((1 + |τ|) ^ 4)⁻¹).aestronglyMeasurable
      · refine Eventually.of_forall fun τ => ?_
        rw [Real.norm_of_nonneg (by positivity)]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith [abs_nonneg τ])
          (by norm_num))
    exact hint.mono' hφc.aestronglyMeasurable (Eventually.of_forall hφd)
  have hCφ : 0 ≤ Cφ := by
    have := (norm_nonneg _).trans (hφd 0)
    rwa [abs_zero, add_zero, one_pow, inv_one, mul_one] at this
  -- the decay of the pair weight on the strip
  obtain ⟨Cb, hCb⟩ : ∃ Cb, Cb = Real.exp w *
      (4 * ((∫ u, ‖h u‖) + ∫ u, ‖deriv (deriv h) u‖)) := ⟨_, rfl⟩
  have hN1 : 0 ≤ ∫ u, ‖h u‖ := integral_nonneg fun u => norm_nonneg _
  have hN2 : 0 ≤ ∫ u, ‖deriv (deriv h) u‖ := integral_nonneg fun u => norm_nonneg _
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hK : ∀ ζ : ℂ, |ζ.im| ≤ 1 / 2 → ‖bumpWeight b ζ‖ ≤ Cb * ((1 + |ζ.re|) ^ 2)⁻¹ := by
    intro ζ hζ
    rw [bumpWeight_eq_paperFT hb.continuous hbc]
    refine (RHTower.norm_paperFT_le_decay hhs hhsupp ζ).trans ?_
    rw [hCb, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
      (by positivity)) (by positivity)
    nlinarith [abs_nonneg ζ.im]
  -- the zeros lie in the strip
  have hstrip : ∀ z, z ∈ Z.carrier ∪ Z'.carrier → |(gammaOf z).im| ≤ 1 / 2 := by
    intro z hz
    rw [show (gammaOf z).im = 1 / 2 - z.re by simp [gammaOf], abs_le]
    rcases hz with h' | h'
    · obtain ⟨h1, h2⟩ := Z.strip _ h'; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := Z'.strip _ h'; constructor <;> linarith
  -- the summands as integrals
  set G : ℂ → ℝ → ℂ := fun z τ =>
    multDiff Z Z' z * (cexp (I * gammaOf z * x) * (φ τ * bumpWeight b (gammaOf z + τ))) with hG
  have hsummand : ∀ z, multDiff Z Z' z * (cexp (I * gammaOf z * x) *
      paperFT (fun u => h u * paperFT φ u) (gammaOf z)) = ∫ τ, G z τ := by
    intro z
    rw [← integral_mul_bumpWeight hb hbc hφi, ← integral_const_mul, ← integral_const_mul]
  -- the countable carrier
  set S : Set ℂ := Z.carrier ∪ Z'.carrier with hS
  haveI : Countable S := ((carrier_countable Z).union (carrier_countable Z')).to_subtype
  have hGS : ∀ τ z, z ∉ S → G z τ = 0 := fun τ z hz => by
    have : multDiff Z Z' z = 0 := by
      by_contra hc; exact hz (mem_carrier_of_multDiff_ne_zero hc)
    simp only [hG, this, zero_mul]
  -- domination
  have hdom : ∀ z : S, ∀ τ, ‖G z τ‖ ≤ ‖multDiff Z Z' z‖ * Real.exp (|x| / 2) * Cφ * Cb *
      (((1 + |τ|) ^ 2)⁻¹ * ((1 + |(gammaOf z).re|) ^ 2)⁻¹) := by
    intro z τ
    have hzs := hstrip z z.2
    have hexp : ‖cexp (I * gammaOf z * x)‖ ≤ Real.exp (|x| / 2) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have : (I * gammaOf z * x).re = -((gammaOf z).im * x) := by simp [Complex.mul_re]
      rw [this]
      have := abs_mul (gammaOf z).im x
      nlinarith [neg_abs_le ((gammaOf z).im * x), abs_nonneg x, abs_nonneg (gammaOf z).im]
    have hKz : ‖bumpWeight b (gammaOf z + τ)‖ ≤ Cb * ((1 + |(gammaOf z).re + τ|) ^ 2)⁻¹ := by
      refine (hK _ ?_).trans (le_of_eq ?_)
      · simpa using hzs
      · simp
    have hP := inv_one_add_abs_sq_le (gammaOf z).re τ
    have h4 : ((1 + |τ|) ^ 4)⁻¹ * (1 + |τ|) ^ 2 = ((1 + |τ|) ^ 2)⁻¹ := by
      field_simp
    simp only [hG, norm_mul]
    calc ‖multDiff Z Z' z‖ * (‖cexp (I * gammaOf z * x)‖ * (‖φ τ‖ *
          ‖bumpWeight b (gammaOf z + τ)‖))
        ≤ ‖multDiff Z Z' z‖ * (Real.exp (|x| / 2) * (Cφ * ((1 + |τ|) ^ 4)⁻¹ *
            (Cb * ((1 + |τ|) ^ 2 / (1 + |(gammaOf z).re|) ^ 2)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hexp (mul_le_mul (hφd τ)
            (hKz.trans (mul_le_mul_of_nonneg_left hP hCb0)) (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)) (norm_nonneg _)
      _ = _ := by
          rw [div_eq_mul_inv, ← h4]; ring
  have hint : ∀ z : S, Integrable (G z) := by
    intro z
    refine Integrable.mono' ((integrable_inv_one_add_abs_sq.const_mul
      (‖multDiff Z Z' z‖ * Real.exp (|x| / 2) * Cφ * Cb)).mul_const
      ((1 + |(gammaOf z).re|) ^ 2)⁻¹) ?_ (Eventually.of_forall fun τ => ?_)
    · have hcont : Continuous fun τ : ℝ => bumpWeight b (gammaOf z + τ) := by
        have hd := RHTower.EvenSector.differentiable_paperFT_of_compact hhs.continuous hhc
        simp_rw [bumpWeight_eq_paperFT hb.continuous hbc]
        exact hd.continuous.comp (continuous_const.add Complex.continuous_ofReal)
      exact (continuous_const.mul (continuous_const.mul (hφc.mul hcont))).aestronglyMeasurable
    · refine (hdom z τ).trans (le_of_eq ?_); ring
  have hsum : Summable fun z : S => ∫ τ, ‖G z τ‖ := by
    have hbound : ∀ z : S, ∫ τ, ‖G z τ‖ ≤ (‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z))) *
        (Real.exp (|x| / 2) * Cφ * Cb * (∫ τ : ℝ, ((1 + |τ|) ^ 2)⁻¹) * (5 / 4)) := by
      intro z
      have hzs := hstrip z z.2
      have hre := inv_one_add_abs_re_sq_le hzs
      have hI0 : 0 ≤ ∫ τ : ℝ, ((1 + |τ|) ^ 2)⁻¹ := integral_nonneg fun τ => by positivity
      calc ∫ τ, ‖G z τ‖ ≤ ∫ τ, ‖multDiff Z Z' z‖ * Real.exp (|x| / 2) * Cφ * Cb *
            (((1 + |τ|) ^ 2)⁻¹ * ((1 + |(gammaOf z).re|) ^ 2)⁻¹) :=
          integral_mono (hint z).norm ((integrable_inv_one_add_abs_sq.mul_const _).const_mul _)
            fun τ => hdom z τ
        _ = ‖multDiff Z Z' z‖ * Real.exp (|x| / 2) * Cφ * Cb *
            ((∫ τ : ℝ, ((1 + |τ|) ^ 2)⁻¹) * ((1 + |(gammaOf z).re|) ^ 2)⁻¹) := by
          rw [integral_const_mul, integral_mul_const]
        _ ≤ ‖multDiff Z Z' z‖ * Real.exp (|x| / 2) * Cφ * Cb *
            ((∫ τ : ℝ, ((1 + |τ|) ^ 2)⁻¹) * (5 / 4 / (1 + Complex.normSq (gammaOf z)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hre hI0) (by positivity)
        _ = _ := by ring
    refine Summable.of_nonneg_of_le (fun z => integral_nonneg fun τ => norm_nonneg _) hbound ?_
    exact ((summable_multDiff_div Z Z' hZ hZ').subtype S).mul_right _
  -- the interchange
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hsubS : ∀ F : ℂ → ℂ, (∀ z, z ∉ S → F z = 0) → ∑' z : S, F z = ∑' z, F z := by
    intro F hF
    rw [tsum_subtype S F]
    exact tsum_congr fun z => by
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hF z hz]
  have hzero : ∀ τ, ∑' z : S, G z τ = 0 := by
    intro τ
    rw [hsubS (fun z => G z τ) (fun z hz => hGS τ z hz)]
    have e : ∀ z, G z τ = φ τ * (multDiff Z Z' z * (cexp (I * gammaOf z * x) *
        bumpWeight b (gammaOf z + τ))) := fun z => by simp only [hG]; ring
    rw [tsum_congr e, tsum_mul_left, tsum_modLag_eq_zero hZ hZ' hW hb hbs hx τ, mul_zero]
  rw [tsum_congr hsummand, ← hsubS (fun z => ∫ τ, G z τ) (fun z hz => by
    simp only [hGS _ z hz, integral_zero]), hswap]
  simp only [hzero, integral_zero]

/-! ### The inverse weight -/

/-- The inverse transform `φ(τ) = (2π)⁻¹ ψ̂(−τ)`, with `φ̂ = ψ` (`paperFT_invWeight`). -/
def invWeight (ψ : ℝ → ℂ) (τ : ℝ) : ℂ := (1 / (2 * π) : ℂ) * paperFT ψ (-(τ : ℂ))

theorem norm_paperFT_real_le {ψ : ℝ → ℂ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hψs : tsupport ψ ⊆ Icc (-r₀) r₀) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖paperFT ψ τ‖ ≤ C * ((1 + |τ|) ^ m)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_pow_mul_norm_paperFT_le_exp hψ hr₀ hψs m
  refine ⟨C, hC0, fun τ => ?_⟩
  have h := hC τ
  rw [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one, Complex.norm_real,
    Real.norm_eq_abs] at h
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

theorem paperFT_invWeight {ψ : ℝ → ℂ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hψs : tsupport ψ ⊆ Icc (-r₀) r₀) (u : ℝ) : paperFT (invWeight ψ) u = ψ u := by
  have hψc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) hψs
  obtain ⟨C, hC0, hC⟩ := norm_paperFT_real_le hψ hr₀ hψs 2
  have hFi : Integrable fun r : ℝ => paperFT ψ r := by
    refine (integrable_inv_one_add_abs_sq.const_mul C).mono' ?_ (Eventually.of_forall hC)
    exact ((_root_.RHTower.EvenSector.differentiable_paperFT_of_compact hψ.continuous
      hψc).continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
  have hF' : Integrable (FourierTransform.fourier ψ) := by
    have h := hFi.comp_mul_left' (R := -(2 * π)) (neg_ne_zero.mpr (by positivity))
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [EF.paperFT_ofReal_eq_fourier]
    field_simp
  have hinv := EF.paper_inversion hψ.continuous (hψ.continuous.integrable_of_hasCompactSupport hψc)
    hF' u
  rw [hinv, paperFT_def]
  simp only [invWeight]
  rw [← integral_neg_eq_self, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [Complex.ofReal_neg, neg_neg]
  ring_nf

theorem invWeight_props {ψ : ℝ → ℂ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hψs : tsupport ψ ⊆ Icc (-r₀) r₀) :
    Continuous (invWeight ψ) ∧ ∃ Cφ : ℝ, ∀ τ, ‖invWeight ψ τ‖ ≤ Cφ * ((1 + |τ|) ^ 4)⁻¹ := by
  have hψc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) hψs
  refine ⟨continuous_const.mul ((_root_.RHTower.EvenSector.differentiable_paperFT_of_compact
    hψ.continuous hψc).continuous.comp Complex.continuous_ofReal.neg), ?_⟩
  obtain ⟨C, hC0, hC⟩ := norm_paperFT_real_le hψ hr₀ hψs 4
  refine ⟨1 / (2 * π) * C, fun τ => ?_⟩
  rw [invWeight, norm_mul, ← Complex.ofReal_neg]
  have h1 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [h1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((hC (-τ)).trans (le_of_eq ?_)) (by positivity)
  rw [abs_neg]

/-! ### The depth weight -/

/-- The depth weight `χ(u)/(2 cosh(δ(u + x)))`. -/
def depthWeight (χ : ℝ → ℂ) (δ x : ℝ) (u : ℝ) : ℂ :=
  χ u * (((2 * Real.cosh (δ * (u + x)))⁻¹ : ℝ) : ℂ)

theorem depthWeight_props {χ : ℝ → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {R : ℝ}
    (hχs : tsupport χ ⊆ Icc (-R) R) (δ x : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (depthWeight χ δ x) ∧ tsupport (depthWeight χ δ x) ⊆ Icc (-R) R := by
  refine ⟨?_, ?_⟩
  · have hc : ContDiff ℝ (⊤ : ℕ∞) fun u : ℝ => (2 * Real.cosh (δ * (u + x)))⁻¹ :=
      (contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul
        (contDiff_id.add contDiff_const)))).inv fun u =>
        (by positivity : (0 : ℝ) < 2 * Real.cosh (δ * (u + x))).ne'
    exact hχ.mul (Complex.ofRealCLM.contDiff.comp hc)
  · refine (closure_minimal (fun u hu => subset_closure ?_) (isClosed_tsupport χ)).trans hχs
    intro h0
    apply hu
    simp [depthWeight, h0]

/-- On the line (`δ = 0`) the depth weight halves the transform. -/
theorem paperFT_depthWeight_zero (h χ : ℝ → ℂ) (x : ℝ) (ζ : ℂ) :
    paperFT (fun u => h u * depthWeight χ 0 x u) ζ = paperFT (fun u => h u * χ u) ζ / 2 := by
  rw [paperFT_def, paperFT_def, div_eq_mul_inv, ← integral_mul_const_C]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [depthWeight, zero_mul, Real.cosh_zero, mul_one]
  push_cast
  ring

theorem depthWeight_mul_cosh (h χ : ℝ → ℂ) (δ x : ℝ) :
    (fun u => h u * depthWeight χ δ x u * ((2 * Real.cosh (δ * (u + x)) : ℝ) : ℂ)) =
      fun u => h u * χ u := by
  funext u
  have hc : 2 * Real.cosh (δ * (u + x)) ≠ 0 := by positivity
  simp only [depthWeight]
  rw [mul_assoc, mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc, Complex.ofReal_one, mul_one]

/-! ### An FE pair of one depth -/

/-- **The pair term of an FE pair of depth `δ`.**
`e^{iγx} κ̂(γ) + e^{iγ̄x} κ̂(γ̄) = e^{itx} (κ · 2cosh(δ(· + x)))^(t)` for `γ = t − iδ`. -/
theorem pair_term_eq {κ : ℝ → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) (t δ x : ℝ) :
    cexp (I * ((t : ℂ) - I * δ) * x) * paperFT κ ((t : ℂ) - I * δ) +
        cexp (I * ((t : ℂ) + I * δ) * x) * paperFT κ ((t : ℂ) + I * δ) =
      cexp (I * t * x) *
        paperFT (fun u => κ u * ((2 * Real.cosh (δ * (u + x)) : ℝ) : ℂ)) t := by
  have hint : ∀ c : ℂ, Integrable fun u : ℝ => κ u * cexp (c * u) := fun c =>
    (hκ.mul (by fun_prop)).integrable_of_hasCompactSupport hκc.mul_right
  rw [paperFT_def, paperFT_def, paperFT_def, ← integral_const_mul, ← integral_const_mul,
    ← integral_const_mul, ← integral_add]
  · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    have e1 : ∀ y : ℝ, cexp (I * ((t : ℂ) - I * δ) * y) = cexp (I * t * y) * cexp (δ * y) :=
      fun y => by
        rw [← Complex.exp_add]; congr 1; linear_combination (-(δ : ℂ) * y) * Complex.I_sq
    have e2 : ∀ y : ℝ, cexp (I * ((t : ℂ) + I * δ) * y) = cexp (I * t * y) * (cexp (δ * y))⁻¹ :=
      fun y => by
        rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1
        linear_combination ((δ : ℂ) * y) * Complex.I_sq
    have hc : (((2 * Real.cosh (δ * (u + x)) : ℝ)) : ℂ) =
        cexp (δ * x) * cexp (δ * u) + (cexp (δ * x))⁻¹ * (cexp (δ * u))⁻¹ := by
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cosh, Complex.two_cosh,
        ← Complex.exp_add, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
      congr 1 <;> congr 1 <;> push_cast <;> ring
    rw [e1 x, e1 u, e2 x, e2 u, hc]
    ring
  · exact (hint _).const_mul _
  · exact (hint _).const_mul _

/-! ### Folding the averaged identity over FE pairs -/

theorem abs_gammaOf_im_le {Z Z' : ZeroConfig} {z : ℂ} (hz : z ∈ Z.carrier ∪ Z'.carrier) :
    |(gammaOf z).im| ≤ 1 / 2 := by
  rw [show (gammaOf z).im = 1 / 2 - z.re by simp [gammaOf], abs_le]
  rcases hz with h' | h'
  · obtain ⟨h1, h2⟩ := Z.strip _ h'; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := Z'.strip _ h'; constructor <;> linarith

theorem norm_cexp_I_mul_le {γ : ℂ} (hγ : |γ.im| ≤ 1 / 2) (x : ℝ) :
    ‖cexp (I * γ * x)‖ ≤ Real.exp (|x| / 2) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : (I * γ * x).re = -(γ.im * x) := by simp [Complex.mul_re]
  rw [this]
  have := abs_mul γ.im x
  nlinarith [neg_abs_le (γ.im * x), abs_nonneg x, abs_nonneg γ.im]

/-- Transforms of `C²` tests of bounded support decay like `(1 + |Re ζ|)^{−2}` on the strip. -/
theorem norm_paperFT_strip_le {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) {A : ℝ}
    (hsupp : ∀ u, c u ≠ 0 → |u| ≤ A) :
    ∃ C, 0 ≤ C ∧ ∀ ζ : ℂ, |ζ.im| ≤ 1 / 2 → ‖paperFT c ζ‖ ≤ C * ((1 + |ζ.re|) ^ 2)⁻¹ := by
  have hN1 : 0 ≤ ∫ u, ‖c u‖ := integral_nonneg fun u => norm_nonneg _
  have hN2 : 0 ≤ ∫ u, ‖deriv (deriv c) u‖ := integral_nonneg fun u => norm_nonneg _
  refine ⟨Real.exp (|A| / 2) * (4 * ((∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖)), by positivity,
    fun ζ hζ => ?_⟩
  refine (RHTower.norm_paperFT_le_decay hc hsupp ζ).trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
    (by positivity)) (by positivity)
  calc |ζ.im| * A ≤ |ζ.im| * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) (abs_nonneg _)
    _ ≤ 1 / 2 * |A| := mul_le_mul_of_nonneg_right hζ (abs_nonneg _)
    _ = |A| / 2 := by ring

theorem summable_multDiff_mul {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ z ∈ Z.carrier ∪ Z'.carrier, ‖F z‖ ≤ C * ((1 + |(gammaOf z).re|) ^ 2)⁻¹) :
    Summable fun z => multDiff Z Z' z * F z := by
  refine Summable.of_norm_bounded ((summable_multDiff_div Z Z' hZ hZ').mul_right (C * (5 / 4)))
    fun z => ?_
  by_cases hc : multDiff Z Z' z = 0
  · rw [hc, zero_mul, norm_zero, zero_div, zero_mul]
  · have hz := mem_carrier_of_multDiff_ne_zero hc
    have hre := inv_one_add_abs_re_sq_le (abs_gammaOf_im_le hz)
    rw [norm_mul]
    calc ‖multDiff Z Z' z‖ * ‖F z‖ ≤
        ‖multDiff Z Z' z‖ * (C * (5 / 4 / (1 + Complex.normSq (gammaOf z)))) :=
          mul_le_mul_of_nonneg_left ((hF z hz).trans (mul_le_mul_of_nonneg_left hre hC))
            (norm_nonneg _)
      _ = _ := by ring

/-- The site mass: `c(z)/2` on the critical line, `c(z)` off it. -/
def siteMass (Z Z' : ZeroConfig) (z : ℂ) : ℂ :=
  if z.re = 1 / 2 then multDiff Z Z' z / 2 else multDiff Z Z' z

theorem norm_siteMass_le (Z Z' : ZeroConfig) (z : ℂ) :
    ‖siteMass Z Z' z‖ ≤ ‖multDiff Z Z' z‖ := by
  unfold siteMass
  split_ifs
  · rw [norm_div, Complex.norm_two]; linarith [norm_nonneg (multDiff Z Z' z)]
  · exact le_rfl

theorem siteMass_ne_zero {Z Z' : ZeroConfig} {z : ℂ} (h : multDiff Z Z' z ≠ 0) :
    siteMass Z Z' z ≠ 0 := by
  unfold siteMass
  split_ifs
  · exact div_ne_zero h two_ne_zero
  · exact h

/-- **The site sum of one depth vanishes.** If every point of the union has depth `δ`, mimicry at
aperture `a` gives `Σ_k e^{i t_k x} m_k (h_b χ)^(t_k) = 0` over the sites `k` (`Re k ≥ ½`), with
`m_k` the site mass, for `|x|/2 + w ≤ a`: average the modulated lag identity against `φ` with
`φ̂ = χ/(2cosh(δ(· + x)))` and fold each FE pair (`pair_term_eq`). -/
theorem tsum_sites_oneDepth_eq_zero {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a δ : ℝ} (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (hdepth : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.re - 1 / 2| = δ)
    {b : ℝ → ℂ} {w : ℝ} (hw : 0 ≤ w) (hb : ContDiff ℝ 2 b) (hbs : tsupport b ⊆ Icc (-w) w)
    {χ : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : tsupport χ ⊆ Icc (-R) R) {x : ℝ} (hx : |x| / 2 + w ≤ a) :
    ∑' k : pairSites Z Z', cexp (I * (k : ℂ).im * x) *
      (siteMass Z Z' k * paperFT (fun u => EF.weilTest b b u * χ u) ((k : ℂ).im)) = 0 := by
  classical
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport b) hbs
  obtain ⟨hψd, hψs⟩ := depthWeight_props hχ hχs δ x
  obtain ⟨hφc, Cφ, hφd⟩ := invWeight_props hψd hR hψs
  have hlag := tsum_averaged_lag_eq_zero hZ hZ' hW hw hb hbs hx hφc hφd
  have hfun : (fun u : ℝ => EF.weilTest b b u * paperFT (invWeight (depthWeight χ δ x)) u) =
      fun u => EF.weilTest b b u * depthWeight χ δ x u :=
    funext fun u => by rw [paperFT_invWeight hψd hR hψs]
  rw [hfun] at hlag
  set h := EF.weilTest b b with hh
  have hhs : ContDiff ℝ 2 h := EF.weilTest_contDiff hb hb.continuous hbc
  have hhsupp : ∀ u, h u ≠ 0 → |u| ≤ 2 * w := by
    have hbs' : tsupport b ⊆ Icc (-(2 * w / 2)) (2 * w / 2) := by
      rw [show 2 * w / 2 = w by ring]; exact hbs
    exact RHTower.weilTest_abs_le hbs' hbs'
  have hκd : ContDiff ℝ 2 (fun u => h u * depthWeight χ δ x u) :=
    hhs.mul (hψd.of_le (by norm_cast))
  have hκsupp : ∀ u, h u * depthWeight χ δ x u ≠ 0 → |u| ≤ 2 * w := fun u hu =>
    hhsupp u (fun h0 => hu (by rw [h0, zero_mul]))
  have hκc : HasCompactSupport (fun u => h u * depthWeight χ δ x u) :=
    hasCompactSupport_of_support_subset_abs hκsupp
  set F : ℂ → ℂ := fun z => multDiff Z Z' z *
    (cexp (I * gammaOf z * x) * paperFT (fun u => h u * depthWeight χ δ x u) (gammaOf z)) with hF
  -- summability and the FE split
  obtain ⟨Cκ, hCκ0, hCκ⟩ := norm_paperFT_strip_le hκd hκsupp
  have hfs : Summable F := by
    refine summable_multDiff_mul hZ hZ' (mul_nonneg (Real.exp_pos _).le hCκ0)
      (C := Real.exp (|x| / 2) * Cκ) fun z hz => ?_
    have hzs := abs_gammaOf_im_le hz
    rw [norm_mul, mul_assoc (Real.exp (|x| / 2))]
    exact mul_le_mul (norm_cexp_I_mul_le hzs x) (hCκ _ hzs) (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨hRs, hsplit⟩ := tsum_split_reflect hfs
  set G : ℂ → ℂ := fun z => {z : ℂ | z.re = 1 / 2}.indicator F z +
    {z : ℂ | 1 / 2 < z.re}.indicator (fun z => F z + F (reflect z)) z with hG
  have hsum0 : ∑' z, G z = 0 := by
    rw [hG]
    simp only
    rw [Summable.tsum_add (hfs.indicator _) hRs, ← hsplit]
    exact hlag
  -- the folded term at a site
  have hsite : ∀ k : pairSites Z Z', cexp (I * (k : ℂ).im * x) *
      (siteMass Z Z' k * paperFT (fun u => h u * χ u) ((k : ℂ).im)) = G k := by
    intro k
    have hdk := hdepth k k.2.1
    by_cases hon : (k : ℂ).re = 1 / 2
    · have hδ0 : δ = 0 := by rw [← hdk, hon, sub_self, abs_zero]
      have hγ : gammaOf k = (((k : ℂ).im : ℝ) : ℂ) := by
        rw [gammaOf_eq, show depth (k : ℂ) = 0 by rw [depth, hon, sub_self],
          Complex.ofReal_zero, mul_zero, sub_zero]
      rw [hG]
      simp only
      rw [Set.indicator_of_mem (show (k : ℂ) ∈ {z : ℂ | z.re = 1 / 2} from hon),
        Set.indicator_of_notMem (show (k : ℂ) ∉ {z : ℂ | 1 / 2 < z.re} from fun h' => by
          simp only [Set.mem_setOf_eq] at h'; linarith), add_zero]
      simp only [hF, hγ, siteMass, hon, if_true]
      rw [hδ0, paperFT_depthWeight_zero]
      ring
    · have hk' : 1 / 2 < (k : ℂ).re := lt_of_le_of_ne k.2.2 (Ne.symm hon)
      have hδ : (k : ℂ).re - 1 / 2 = δ := by rw [← hdk, abs_of_pos (by linarith)]
      have hγ : gammaOf k = (((k : ℂ).im : ℝ) : ℂ) - I * δ := by rw [gammaOf_eq, depth, hδ]
      have hγr : gammaOf (reflect k) = (((k : ℂ).im : ℝ) : ℂ) + I * δ := by
        rw [gammaOf_reflect_eq_conj, hγ, map_sub, map_mul, Complex.conj_ofReal,
          Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [hG]
      simp only
      rw [Set.indicator_of_notMem (show (k : ℂ) ∉ {z : ℂ | z.re = 1 / 2} from hon),
        Set.indicator_of_mem (show (k : ℂ) ∈ {z : ℂ | 1 / 2 < z.re} from hk'), zero_add]
      simp only [hF, hγ, hγr, multDiff_reflect, siteMass, hon, if_false]
      rw [← mul_add, pair_term_eq (κ := fun u => h u * depthWeight χ δ x u)
        (hhs.continuous.mul hψd.continuous) hκc, depthWeight_mul_cosh]
      ring
  -- `G` vanishes off the sites
  have hGoff : ∀ z, z ∉ pairSites Z Z' → G z = 0 := by
    intro z hz
    have hF0 : ∀ y, y ∉ Z.carrier ∪ Z'.carrier → F y = 0 := fun y hy => by
      have : multDiff Z Z' y = 0 := by
        by_contra hc
        exact hy (mem_carrier_of_multDiff_ne_zero hc)
      simp only [hF, this, zero_mul]
    rw [hG]
    simp only
    by_cases hre : 1 / 2 ≤ z.re
    · have hzU : z ∉ Z.carrier ∪ Z'.carrier := fun h' => hz ⟨h', hre⟩
      have hrU : reflect z ∉ Z.carrier ∪ Z'.carrier := by
        rw [Set.mem_union, reflect_mem_iff, reflect_mem_iff]; exact hzU
      by_cases he : z.re = 1 / 2
      · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | z.re = 1 / 2} from he), hF0 z hzU,
          Set.indicator_of_notMem (show z ∉ {z : ℂ | 1 / 2 < z.re} from fun h' => by
            simp only [Set.mem_setOf_eq] at h'; linarith), add_zero]
      · rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | z.re = 1 / 2} from he),
          Set.indicator_of_mem (show z ∈ {z : ℂ | 1 / 2 < z.re} from
            lt_of_le_of_ne hre (Ne.symm he)), hF0 z hzU, hF0 _ hrU]
        ring
    · have hre' := not_le.mp hre
      rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | z.re = 1 / 2} from fun h' => by
          simp only [Set.mem_setOf_eq] at h'; linarith),
        Set.indicator_of_notMem (show z ∉ {z : ℂ | 1 / 2 < z.re} from fun h' => by
          simp only [Set.mem_setOf_eq] at h'; linarith), add_zero]
  rw [tsum_congr hsite, tsum_subtype (pairSites Z Z') G]
  have hind : (pairSites Z Z').indicator G = G := by
    funext z
    by_cases hz : z ∈ pairSites Z Z'
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hGoff z hz]
  rw [hind]
  exact hsum0

/-! ### Ingham at the sites -/

/-- **Ingham for a summable sum of real frequencies.** If `Σ_k p_k e^{iγ_k v}` vanishes on
`[−V, V]`, with `g`-separated `γ` and `g > π/V`, every coefficient vanishes. -/
theorem coeff_eq_zero_of_tsum_exp_eq_zero {κ : Type*} (γ : κ → ℝ) (p : κ → ℂ) {g V : ℝ}
    (hg : 0 < g) (hV : 0 < V) (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) (hgap : π / V < g)
    (hsum : Summable fun k => ‖p k‖)
    (hzero : ∀ v ∈ Icc (-V) V, ∑' k, cexp (I * γ k * v) * p k = 0) (k₀ : κ) : p k₀ = 0 := by
  have h := inghamConst_mul_normSq_le γ (fun _ => 0) p (fun _ => 0) hg hV le_rfl
    (fun _ => by simp) hsep hgap (by simpa using hsum) (fun v hv => by simpa using hzero v hv) k₀
  simp only [remConst_zero, mul_zero, zero_mul, add_zero] at h
  have hθ := inghamConst_pos hV hgap
  have h2 : ‖p k₀‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖p k₀‖]
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h2 (sq_nonneg _)))

theorem summable_site_oneDepth (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {κ : ℝ → ℂ} (hκ : ContDiff ℝ 2 κ) {A : ℝ}
    (hsupp : ∀ u, κ u ≠ 0 → |u| ≤ A) :
    Summable fun k : pairSites Z Z' => ‖siteMass Z Z' k * paperFT κ ((k : ℂ).im)‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_paperFT_strip_le hκ hsupp
  have hbound : ∀ k : pairSites Z Z', ‖siteMass Z Z' k * paperFT κ ((k : ℂ).im)‖ ≤
      ‖multDiff Z Z' k‖ / (1 + Complex.normSq (gammaOf k)) * (C * (5 / 4)) := by
    intro k
    have hre := inv_one_add_abs_re_sq_le (abs_gammaOf_im_le k.2.1)
    have hγre : (gammaOf (k : ℂ)).re = (k : ℂ).im := by rw [gammaOf_eq]; simp
    rw [hγre] at hre
    have hF := hC (((k : ℂ).im : ℝ) : ℂ) (by rw [Complex.ofReal_im, abs_zero]; norm_num)
    rw [Complex.ofReal_re] at hF
    rw [norm_mul]
    calc ‖siteMass Z Z' k‖ * ‖paperFT κ ((k : ℂ).im)‖ ≤
        ‖multDiff Z Z' k‖ * (C * (5 / 4 / (1 + Complex.normSq (gammaOf k)))) :=
          mul_le_mul (norm_siteMass_le Z Z' k) (hF.trans (mul_le_mul_of_nonneg_left hre hC0))
            (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound
    (((summable_multDiff_div Z Z' hZ hZ').subtype (pairSites Z Z')).mul_right _)

theorem exists_tsupport_subset_Icc {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ R, 0 ≤ R ∧ tsupport f ⊆ Icc (-R) R := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, hR.trans ?_⟩
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add]
  exact Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _)

/-! ### Configurations of one depth -/

/-- **Configurations of one depth are resolved at the Ingham scale.** Let `Z, Z'` be tempered,
with union `g`-separated apart from FE partners and lying at one depth `δ` (`|Re ρ − ½| = δ`).
If `Z, Z'` are mimics at an aperture `a > π/(2g)`, they coincide with multiplicity.

For a site `k₀` with `c(k₀) ≠ 0`, the folded identity (`tsum_sites_oneDepth_eq_zero`) and Ingham
give `(h_b χ)^(t₀) = 0` for every smooth compactly supported `χ`. Modulating `χ` to the site turns
this into `∫ ζ h_b = 0` for all smooth `ζ`, so `h_b = 0`, against `ĥ_b(0) = |b̂(0)|² ≠ 0`. -/
theorem eq_of_mimic_of_oneDepth {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {g a δ : ℝ} (hg : 0 < g) (hga : π / (2 * g) < a)
    (hdepth : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.re - 1 / 2| = δ)
    (hsep : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ →
      ρ' ≠ reflect ρ → g ≤ |ρ.im - ρ'.im|)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  classical
  refine eq_of_multDiff_eq_zero fun ρ₀ => ?_
  by_contra hc
  obtain ⟨t₀, ht₀re, hct₀⟩ := exists_site_of_multDiff_ne_zero hc
  -- the bump width and the lag range
  have hπg : 0 < π / (2 * g) := by positivity
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = (a - π / (2 * g)) / 2 := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hwdef]; linarith
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = 2 * a - 2 * w := ⟨_, rfl⟩
  have hV : 0 < V := by rw [hVdef, hwdef]; linarith
  have hgap : π / V < g := by
    have hga' : π < a * (2 * g) := (div_lt_iff₀ (by positivity)).mp hga
    have hgV : g * V = g * a + π / 2 := by rw [hVdef, hwdef]; field_simp; ring
    rw [div_lt_iff₀ hV]
    nlinarith
  -- the bump
  set b := _root_.RHTower.modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbsupp := modScaledBump_support hw0 0
  have hbs : tsupport b ⊆ Icc (-w) w :=
    closure_minimal (fun u hu => abs_le.mp (hbsupp u hu)) isClosed_Icc
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport b) hbs
  set h := EF.weilTest b b with hh
  have hhs : ContDiff ℝ 2 h := EF.weilTest_contDiff hb hb.continuous hbc
  have hhsupp : ∀ u, h u ≠ 0 → |u| ≤ 2 * w := by
    have hbs' : tsupport b ⊆ Icc (-(2 * w / 2)) (2 * w / 2) := by
      rw [show 2 * w / 2 = w by ring]; exact hbs
    exact RHTower.weilTest_abs_le hbs' hbs'
  -- every smooth test integrates `h` to zero
  have hvanish : ∀ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      ∫ u, ζ u • h u = 0 := by
    intro ζ hζ hζc
    obtain ⟨R, hR, hRs⟩ := exists_tsupport_subset_Icc hζc
    set χ : ℝ → ℂ := fun u => (ζ u : ℂ) * cexp (-(I * t₀.im * u)) with hχ
    have hχd : ContDiff ℝ (⊤ : ℕ∞) χ :=
      (Complex.ofRealCLM.contDiff.comp hζ).mul
        (Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg))
    have hχs : tsupport χ ⊆ Icc (-R) R := by
      refine (closure_minimal (fun u hu => subset_closure ?_) (isClosed_tsupport ζ)).trans hRs
      intro h0
      apply hu
      simp [hχ, h0]
    have hzero : ∀ v ∈ Icc (-V) V, ∑' k : pairSites Z Z', cexp (I * (k : ℂ).im * v) *
        (siteMass Z Z' k * paperFT (fun u => h u * χ u) ((k : ℂ).im)) = 0 := by
      intro v hv
      have hva : |v| / 2 + w ≤ a := by
        have := abs_le.mpr hv
        rw [hVdef] at this
        linarith
      exact tsum_sites_oneDepth_eq_zero hZ hZ' hW hdepth hw0.le hb hbs hR hχd hχs hva
    have hκd : ContDiff ℝ 2 (fun u => h u * χ u) := hhs.mul (hχd.of_le (by norm_cast))
    have hκsupp : ∀ u, h u * χ u ≠ 0 → |u| ≤ 2 * w := fun u hu =>
      hhsupp u (fun h0 => hu (by rw [h0, zero_mul]))
    have hp := coeff_eq_zero_of_tsum_exp_eq_zero (fun k : pairSites Z Z' => (k : ℂ).im)
      (fun k => siteMass Z Z' k * paperFT (fun u => h u * χ u) ((k : ℂ).im)) hg hV
      (sites_sep hsep) hgap (summable_site_oneDepth Z Z' hZ hZ' hκd hκsupp) hzero
      ⟨t₀, mem_carrier_of_multDiff_ne_zero hct₀, ht₀re⟩
    have hF0 : paperFT (fun u => h u * χ u) (t₀.im : ℂ) = 0 :=
      (mul_eq_zero.mp hp).resolve_left (siteMass_ne_zero hct₀)
    rw [paperFT_def] at hF0
    rw [← hF0]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have e : cexp (-(I * t₀.im * u)) * cexp (I * t₀.im * u) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    simp only [hχ, Complex.real_smul]
    linear_combination (-((ζ u : ℂ) * h u)) * e
  -- so `h = 0`, against `ĥ(0) = |b̂(0)|² ≠ 0`
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hhs.continuous.locallyIntegrable hvanish
  have hzero : h = 0 := (Continuous.ae_eq_iff_eq volume hhs.continuous continuous_const).mp hae
  have hb0 : paperFT b 0 ≠ 0 := by
    have h1 := _root_.RHTower.norm_paperFT_scaledBump_I_mul_ge hw0 0
    have hint := _root_.RHTower.weilBump.integral_pos (μ := volume)
    have hpos : 0 < 4 * w * (Real.exp (-(w * |(0 : ℝ)|)) * ∫ u, _root_.RHTower.weilBump u) :=
      mul_pos (mul_pos (by norm_num) hw0) (mul_pos (Real.exp_pos _) hint)
    have hbe : paperFT b 0 = paperFT (_root_.RHTower.scaledBump w) (((0 : ℝ) : ℂ) * I) := by
      rw [Complex.ofReal_zero, zero_mul]
      congr 1
      funext u
      simp [hbdef, _root_.RHTower.modScaledBump]
    rw [hbe]
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  have hK0 : bumpWeight b 0 = 0 := by
    rw [bumpWeight_eq_paperFT hb.continuous hbc, ← hh, hzero]
    simp [paperFT_def]
  have hK : bumpWeight b 0 = paperFT b 0 * conj (paperFT b 0) := by simp [bumpWeight]
  rw [hK, Complex.mul_conj, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at hK0
  exact hb0 hK0

end GaloisForLFunctions.ZeroConfigurationGeometry
