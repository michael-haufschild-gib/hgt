import GaloisForLFunctions.SquareRootThreshold.HeightWindowAverageRepresentation
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# Small-aperture positivity and height-window positivity for the zeros of `ζ`

**Small-aperture lower bound** (`zetaZeroConfig_re_W_ge_of_small_support`). Let `f` be a `C²` test
supported in `[-a, a]` with `2a < log 2`, and let `R ≥ 0`. Then
`Re W_ζ(f, f) ≥ (ℓ − 10 − 2aRℓ/π − 2S(a)) ‖f‖²`, where `ℓ = log(1 + R/4)` and
`S(a) = sinh a − a`.

* The explicit formula has no prime terms at this aperture.
* The pole terms `h_k(i/2) + h_k(−i/2)` are the pair term of an off-line pair at depth `½` and
  height `0`. The rank-two estimate of `IsolatedOffLinePairVisibilityLaw` bounds their cost by
  `2S(a)‖f‖²`.
* The archimedean density satisfies `μ(τ) ≥ (log(1 + |τ|/4) − 10)/2π`.
* By Cauchy–Schwarz, `|h_f(τ)|² ≤ 2a‖f‖²`. So at most `4aR‖f‖²` of the total spectral mass
  `2π‖f‖²` lies below height `R`.

**Small-aperture positivity** (`zetaZeroConfig_re_W_nonneg_of_small_aperture`). With
`R = π/(4a)`, the bound is `(ℓ/2 − 10 − 2S(a))‖f‖²`, which is positive for `a ≤ e^{−50}`. This is a
Yoshida-type theorem with a crude constant.

**Height-window positivity for `ζ`** (`re_windowedW_zetaZeroConfig_nonneg`,
`re_integral_heightShift_zetaZeroConfig_nonneg`). Let `η` be a window supported in
`[−e^{−50}, e^{−50}]`. For every test `f` of arbitrary aperture, `∫ |h_η(−2πξ)|² W_ζ(S_ξ f, S_ξ f) dξ`
has nonnegative real part. The off-line lattice pair of spacing `π e^{50}` has the same property
at every depth (`integral_heightShift_offLineLattice_eq`). This unconditional positivity therefore
carries no information on the real parts of the zeros.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Three estimates at small aperture -/

/-- **Cauchy–Schwarz on the real line.** A test supported in `[-a, a]` has
`|h_f(τ)|² ≤ 2a ‖f‖²`. -/
theorem norm_paperFT_sq_le {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc (-a) a) (τ : ℝ) :
    ‖paperFT f τ‖ ^ 2 ≤ 2 * a * ∫ t, ‖f t‖ ^ 2 := by
  set g : ℝ → ℝ := (Icc (-a) a).indicator fun _ => (1 : ℝ) with hg
  have hnorm : ‖paperFT f τ‖ ≤ ∫ u, ‖f u‖ * g u := by
    rw [paperFT_def]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun u => ?_)))
    simp only [norm_mul]
    have he : ‖cexp (I * (τ : ℂ) * (u : ℂ))‖ = 1 := by
      rw [norm_cexp_I_mul]
      simp
    rw [he, mul_one, hg]
    by_cases hu : u ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hu, mul_one]
    · rw [Set.indicator_of_notMem hu, eq_zero_of_not_mem_Icc hfs hu]
      simp
  have hfsq : Integrable (fun u => ‖f u‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro
      (isCompact_Icc (a := -a) (b := a))
      fun u (hu : u ∉ Icc (-a) a) => by simp [eq_zero_of_not_mem_Icc hfs hu])
  have hgsq : (fun u => g u ^ 2) = g := by
    funext u
    by_cases hu : u ∈ Icc (-a) a
    · rw [hg, Set.indicator_of_mem hu, one_pow]
    · rw [hg, Set.indicator_of_notMem hu]
      ring
  have hgi : Integrable g :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hgsq_int : Integrable (fun u => g u ^ 2) := by rw [hgsq]; exact hgi
  have hgm : AEStronglyMeasurable g := hgi.aestronglyMeasurable
  have hcs := HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    (hf.norm.aestronglyMeasurable) hgm hfsq hgsq_int
  have hgval : ∫ u, g u ^ 2 = 2 * a := by
    rw [hgsq, hg, integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  have hprod_nonneg : 0 ≤ ∫ u, ‖f u‖ * g u :=
    integral_nonneg fun u => mul_nonneg (norm_nonneg _)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) u)
  calc ‖paperFT f τ‖ ^ 2 ≤ (∫ u, ‖f u‖ * g u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ u, ‖f u‖ ^ 2) * ∫ u, g u ^ 2 := hcs
    _ = 2 * a * ∫ t, ‖f t‖ ^ 2 := by rw [hgval]; ring

/-- **The pole terms are a pair term.** For a test supported in `[-a, a]`, the pole terms
`h_k(i/2) + h_k(−i/2)` of `k = f ⋆ f̃` have real part at least `−2S(a)‖f‖²`, where
`S(a) = pairEnergy (1/2) a`. -/
theorem neg_le_re_pole_terms {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    -(2 * pairEnergy (1 / 2) a * ∫ t, ‖f t‖ ^ 2) ≤
      (paperFT (EF.weilTest f f) (I / 2) + paperFT (EF.weilTest f f) (-I / 2)).re := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have h1 := norm_sub_sq_le_pairEnergy (by norm_num : (0 : ℝ) < 1 / 2) ha 0 hf hfs
  have hA : ((0 : ℝ) : ℂ) - I * ((1 / 2 : ℝ) : ℂ) = -I / 2 := by push_cast; ring
  have hB : ((0 : ℝ) : ℂ) + I * ((1 / 2 : ℝ) : ℂ) = I / 2 := by push_cast; ring
  rw [hA, hB] at h1
  have h2 := neg_half_normSq_sub_le_re_pair (paperFT f (-I / 2)) (paperFT f (I / 2))
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [EF.paperFT_weilTest hf hf hfc hfc, EF.paperFT_weilTest hf hf hfc hfc, hc1, hc2]
  rw [add_comm (paperFT f (-I / 2) * conj (paperFT f (I / 2)))] at h2
  linarith

/-- At aperture below `(log 2)/2` the prime terms of the explicit formula vanish. -/
theorem tsum_vonMangoldt_eq_zero_of_small_support {a : ℝ} (ha2 : 2 * a < Real.log 2)
    {k : ℝ → ℂ} (hks : tsupport k ⊆ Icc (-(2 * a)) (2 * a)) :
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)) = 0 := by
  have h : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)) = 0 := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hlog : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have h1 : Real.log n ∉ Icc (-(2 * a)) (2 * a) := fun h => by linarith [h.2]
      have h2 : -Real.log n ∉ Icc (-(2 * a)) (2 * a) := fun h => by linarith [h.1]
      rw [eq_zero_of_not_mem_Icc hks h1, eq_zero_of_not_mem_Icc hks h2, add_zero, mul_zero]
  exact (tsum_congr h).trans tsum_zero

/-- **The archimedean term at small aperture.** For a test supported in `[-a, a]` and `R ≥ 0`,
`∫ |h_f|² μ ≥ (ℓ − 10 − 2aRℓ/π) ‖f‖²` with `ℓ = log(1 + R/4)`. -/
theorem integral_norm_sq_paperFT_mul_mu_ge {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    (Real.log (1 + R / 4) - 10 - 2 * a * R * Real.log (1 + R / 4) / π) * ∫ t, ‖f t‖ ^ 2 ≤
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * mu τ := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hval : ∀ τ : ℝ, paperFT (EF.weilTest f f) τ = ((‖paperFT f τ‖ ^ 2 : ℝ) : ℂ) :=
    paperFT_weilTest_self_ofReal hf.continuous hfc
  have hint_mu : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * mu τ := by
    refine (EF.integrable_paperFT_mul_mu hkd hkc gammaFacts).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have hint_sq : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 := by
    refine (EF.integrable_paperFT_ofReal
      (EF.integrable_fourier_of_contDiff_two hkd hkc)).re.congr (Eventually.of_forall fun τ => ?_)
    simp only [hval, RCLike.re_to_complex, Complex.ofReal_re]
  set N := ∫ t, ‖f t‖ ^ 2 with hN
  set ℓ := Real.log (1 + R / 4) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  set C := 2 * a * N with hC
  set c₁ := (ℓ - 10) / (2 * π) with hc₁
  set c₂ := ℓ / (2 * π) with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  set ind : ℝ → ℝ := (Icc (-R) R).indicator fun _ => (1 : ℝ) with hind
  have hint_ind : Integrable ind :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hptw : ∀ τ : ℝ, c₁ * ‖paperFT f τ‖ ^ 2 - c₂ * C * ind τ ≤ ‖paperFT f τ‖ ^ 2 * mu τ := by
    intro τ
    have hmu := mu_ge_log τ
    have hfb : ‖paperFT f τ‖ ^ 2 ≤ C := norm_paperFT_sq_le ha hf.continuous hfs τ
    have hX : 0 ≤ ‖paperFT f τ‖ ^ 2 := sq_nonneg _
    have hπ : 0 < 2 * π := by positivity
    by_cases hτ : τ ∈ Icc (-R) R
    · rw [hind, Set.indicator_of_mem hτ, mul_one]
      have hlog0 : 0 ≤ Real.log (1 + |τ| / 4) :=
        Real.log_nonneg (by linarith [abs_nonneg τ])
      have hμ : c₁ - c₂ ≤ mu τ := by
        refine le_trans ?_ hmu
        rw [hc₁, hc₂, ← sub_div]
        exact div_le_div_of_nonneg_right (by linarith) hπ.le
      have e1 : ‖paperFT f τ‖ ^ 2 * (c₁ - c₂) ≤ ‖paperFT f τ‖ ^ 2 * mu τ :=
        mul_le_mul_of_nonneg_left hμ hX
      have e2 : c₂ * ‖paperFT f τ‖ ^ 2 ≤ c₂ * C := mul_le_mul_of_nonneg_left hfb hc₂0
      linarith
    · rw [hind, Set.indicator_of_notMem hτ, mul_zero, sub_zero]
      have hRτ : R ≤ |τ| := by
        by_contra h
        exact hτ (abs_le.mp (le_of_lt (not_le.mp h)))
      have hlog : ℓ ≤ Real.log (1 + |τ| / 4) :=
        Real.log_le_log (by linarith) (by linarith)
      have hμ : c₁ ≤ mu τ := by
        refine le_trans ?_ hmu
        rw [hc₁]
        exact div_le_div_of_nonneg_right (by linarith) hπ.le
      have e1 : ‖paperFT f τ‖ ^ 2 * c₁ ≤ ‖paperFT f τ‖ ^ 2 * mu τ :=
        mul_le_mul_of_nonneg_left hμ hX
      linarith
  have hlow : Integrable fun τ : ℝ => c₁ * ‖paperFT f τ‖ ^ 2 - c₂ * C * ind τ :=
    (hint_sq.const_mul c₁).sub (hint_ind.const_mul (c₂ * C))
  have hmono := integral_mono hlow hint_mu hptw
  have hind_val : ∫ τ, ind τ = 2 * R := by
    rw [hind, integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  rw [integral_sub (hint_sq.const_mul c₁) (hint_ind.const_mul (c₂ * C)), integral_const_mul,
    integral_const_mul, hind_val, integral_norm_sq_paperFT_eq hf hfs] at hmono
  refine le_trans (le_of_eq ?_) hmono
  rw [hc₁, hc₂, hC]
  field_simp
  ring

/-! ### Small-aperture positivity of `ζ` -/

/-- **Small-aperture lower bound for `ζ`.** For a `C²` test supported in `[-a, a]` with
`2a < log 2` and every `R ≥ 0`,
`Re W_ζ(f, f) ≥ (ℓ − 10 − 2aRℓ/π − 2S(a)) ‖f‖²`, with `ℓ = log(1 + R/4)`. -/
theorem zetaZeroConfig_re_W_ge_of_small_support {a R : ℝ} (ha : 0 ≤ a)
    (ha2 : 2 * a < Real.log 2) (hR : 0 ≤ R) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    (Real.log (1 + R / 4) - 10 - 2 * a * R * Real.log (1 + R / 4) / π -
        2 * pairEnergy (1 / 2) a) * ∫ t, ‖f t‖ ^ 2 ≤ (zetaZeroConfig.W f f).re := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hfs' : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hks : tsupport (EF.weilTest f f) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset hfs' hfs'
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig (EF.weilTest f f) hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (EF.weilTest f f) (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ := by
    ext ρ
    simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  have hW : zetaZeroConfig.W f f = paperFT (EF.weilTest f f) (I / 2) +
      paperFT (EF.weilTest f f) (-I / 2) + ∫ τ : ℝ, paperFT (EF.weilTest f f) τ * (mu τ : ℂ) := by
    rw [ZeroConfig.W, ← hterm, heq, EF.literatureRHS,
      tsum_vonMangoldt_eq_zero_of_small_support ha2 hks, sub_zero, EF.gamma_term]
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest f f) τ * (mu τ : ℂ)).re =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * mu τ := by
    have h : (fun τ : ℝ => paperFT (EF.weilTest f f) τ * (mu τ : ℂ)) =
        fun τ : ℝ => ((‖paperFT f τ‖ ^ 2 * mu τ : ℝ) : ℂ) := by
      funext τ
      rw [paperFT_weilTest_self_ofReal hf.continuous hfc τ, Complex.ofReal_mul]
    rw [h, integral_complex_ofReal, Complex.ofReal_re]
  have hpole := neg_le_re_pole_terms ha hf.continuous hfs
  have harch := integral_norm_sq_paperFT_mul_mu_ge ha hR hf hfs
  rw [hW, Complex.add_re, hμre]
  linarith

theorem pairEnergy_half_le_two {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : pairEnergy (1 / 2) a ≤ 2 := by
  unfold pairEnergy
  rw [show 2 * (1 / 2 : ℝ) * a = a by ring, show 2 * (1 / 2 : ℝ) = 1 by ring, div_one,
    Real.sinh_eq]
  have h1 : Real.exp a ≤ Real.exp 1 := Real.exp_le_exp.mpr ha1
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (-a)
  norm_num at h2
  linarith

/-- **Small-aperture positivity of `ζ`.** Every `C²` test supported in `[−e^{−50}, e^{−50}]`
satisfies `Re W_ζ(f, f) ≥ 0`. -/
theorem zetaZeroConfig_re_W_nonneg_of_small_aperture {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-Real.exp (-50)) (Real.exp (-50))) :
    0 ≤ (zetaZeroConfig.W f f).re := by
  set a := Real.exp (-50) with ha_def
  have ha0 : 0 < a := Real.exp_pos _
  have hae : a * Real.exp 50 = 1 := by
    rw [ha_def, ← Real.exp_add]
    norm_num
  have h50 := Real.add_one_le_exp 50
  have ha1 : a ≤ 1 / 51 := by nlinarith
  have ha2 : 2 * a < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this
    linarith
  set R := π / (4 * a) with hR_def
  have hR : 0 ≤ R := by positivity
  have hfrac : 2 * a * R / π = 1 / 2 := by
    rw [hR_def]
    field_simp
    ring
  have hℓ : 40 ≤ Real.log (1 + R / 4) := by
    have h10 := Real.add_one_le_exp 10
    have hsplit : Real.exp 50 = Real.exp 40 * Real.exp 10 := by
      rw [← Real.exp_add]
      norm_num
    have hR4 : R / 4 = π * Real.exp 50 / 16 := by
      rw [hR_def]
      field_simp
      nlinarith [hae]
    have hle : Real.exp 40 ≤ 1 + R / 4 := by
      rw [hR4, hsplit]
      have h40 := Real.exp_pos 40
      nlinarith [Real.pi_gt_three]
    calc (40 : ℝ) = Real.log (Real.exp 40) := (Real.log_exp 40).symm
      _ ≤ Real.log (1 + R / 4) := Real.log_le_log (Real.exp_pos 40) hle
  have hS := pairEnergy_half_le_two ha0.le (by linarith)
  have hbound := zetaZeroConfig_re_W_ge_of_small_support ha0.le ha2 hR hf hfs
  have hcoef : 0 ≤ Real.log (1 + R / 4) - 10 - 2 * a * R * Real.log (1 + R / 4) / π -
      2 * pairEnergy (1 / 2) a := by
    have : 2 * a * R * Real.log (1 + R / 4) / π = 2 * a * R / π * Real.log (1 + R / 4) := by
      ring
    rw [this, hfrac]
    linarith
  exact le_trans (mul_nonneg hcoef (integral_nonneg fun _ => sq_nonneg _)) hbound

/-! ### Height-window positivity for `ζ` -/

theorem temperedConfig_zetaZeroConfig : TemperedConfig zetaZeroConfig :=
  summable_zetaZeroConfig

/-- **Windowed positivity for `ζ`.** For every window supported in `[−e^{−50}, e^{−50}]` and every
test of arbitrary aperture, the windowed Weil form of the zeros of `ζ` has nonnegative real
part. -/
theorem re_windowedW_zetaZeroConfig_nonneg {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-Real.exp (-50)) (Real.exp (-50))) :
    0 ≤ (windowedW zetaZeroConfig f η).re :=
  re_windowedW_nonneg_of_aperture_nonneg _ temperedConfig_zetaZeroConfig
    (fun _ hg hgs => zetaZeroConfig_re_W_nonneg_of_small_aperture hg hgs) hf hfc hη hηs

/-- **Height-window positivity for `ζ`.** For every window `η` supported in
`[−e^{−50}, e^{−50}]` and every test `f` of arbitrary aperture,
`∫ |h_η(−2πξ)|² W_ζ(S_ξ f, S_ξ f) dξ` has nonnegative real part. -/
theorem re_integral_heightShift_zetaZeroConfig_nonneg {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-Real.exp (-50)) (Real.exp (-50))) :
    0 ≤ (∫ ξ : ℝ, ((‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 : ℝ) : ℂ) *
      zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re :=
  re_integral_heightShift_nonneg_of_aperture_nonneg _ temperedConfig_zetaZeroConfig
    (fun _ hg hgs => zetaZeroConfig_re_W_nonneg_of_small_aperture hg hgs) hf hfc hη hηs

end GaloisForLFunctions.SquareRootThreshold
