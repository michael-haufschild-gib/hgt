import GaloisForLFunctions.SquareRootThreshold.ZetaHidingRequiresLoudTwins
import GaloisForLFunctions.RHTower.ZetaPoleBoundExplicit
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeAssembly
import GaloisForLFunctions.RHTower.EvenLandauPairTest

/-!
# The unconditional lag envelope of `ζ`

The window functional of the difference test at lag `v` is `P_v = φ(0) − φ(v)`,
`φ(v) = 2 Re S(v) = Σ_z D(z) e^{zv}`. RH is `P_v ≥ 0` for all large `v`; every quasi-RH half-plane
`Re ρ ≤ ½ + σ` is `P_v ≥ −C e^{σv}` (`OneParameterLagFamilyMeasuresTheAbscissa`). This module proves
the strongest bound the corpus zero-free regions give, with an explicit lag.

**Zero-free region ⟹ lag envelope** (`abs_two_re_lagStructure_le_of_zeroFree`). For a `C²` bump the
coefficients satisfy `|D(z)| ≲ m (1 + |Im z|)^{−4}`, so `S₂ = Σ_z |D(z)| (1 + |Im z|)²` is finite
for every tempered configuration (`summable_norm_evenCoeff_mul_sq`). If every exponent of height
`|Im z| ≤ G` has `Re z ≤ ½ − η`, then
`|φ(v)| ≤ e^{v/2} (W e^{−ηv} + S₂/(1 + G)²)`, `W = Σ_z |D(z)|`:
the height cut `G` trades the zero-free width `η` against the bump decay. This is the exact form of
the tradeoff between the zero-free region and the lag envelope.

**For `ζ`** (`zeta_lag_envelope`). The corpus gives `Re ρ ≤ 1 − 1/(100 log γ)` above
`γ₀ = e^{29K/63} < e^{23}` (`RHTower.xiZeroCopy_zero_free_explicit`) and
`Re ρ ≤ 1 − η₀`, `η₀ = c₀/(2·25⁹)`, `c₀ = zeroFreeConst`, at every height up to `e^{23}`
(`RHTower.Sieve.riemannZeta_ne_zero_of_re_gt` with `N = ⌈e^{24}⌉`). With `G = e^{√v/10}`:
for every width `w ∈ (0, ½ log 2)` and every lag `v ≥ V₀ = max(230², 1/(100 η₀²))`,

`P_v ≥ −|φ(0)| − (W + S₂) e^{v/2 − √v/10}`.

So `P_v/√X → 0` unconditionally (`X = e^v`), at the rate `e^{−√(log X)/10}` of the de la Vallée
Poussin region; RH needs `P_v ≥ 0`, a quasi-RH half-plane needs `P_v ≥ −C X^σ`. The gap between this
envelope and `O(1)` is the whole problem. The envelope is attained only by zeros hugging the
zero-free boundary at height `≈ e^{√v/10}`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The second moment of the coefficients -/

/-- The bump constant `B_b = 4(∫|b| + ∫|b''|)` of the decay bound for `h_b`. -/
def bumpDecayConstant (b : ℝ → ℂ) : ℝ := 4 * ((∫ u, ‖b u‖) + ∫ u, ‖deriv (deriv b) u‖)

theorem bumpDecayConstant_nonneg (b : ℝ → ℂ) : 0 ≤ bumpDecayConstant b :=
  mul_nonneg (by norm_num) (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => norm_nonneg _))

/-- **Product decay.** `|F(z)| ≤ m_{½+z} e^{w} B_b² (1 + |Im z|)^{−4}`. -/
theorem norm_lagCoeff_le_decay (Z : ZeroConfig) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (z : ℂ) :
    ‖lagCoeff Z b z‖ ≤ Z.carrier.indicator (fun ρ => (Z.mult ρ : ℝ)) (1 / 2 + z) *
      (Real.exp w * bumpDecayConstant b ^ 2) / (1 + |z.im|) ^ 4 := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  by_cases hz : (1 / 2 + z) ∈ Z.carrier
  · rw [lagCoeff, Set.indicator_of_mem hz, Set.indicator_of_mem hz, norm_mul,
      EF.paperFT_weilTest hb.continuous hb.continuous hbc hbc, norm_mul, Complex.norm_conj]
    have hstrip := Z.strip _ hz
    have him : |(gammaOf (1 / 2 + z)).im| ≤ 1 / 2 := by
      rw [im_gammaOf, abs_le]; simp at hstrip ⊢; constructor <;> linarith [hstrip.1, hstrip.2]
    have hre : (gammaOf (1 / 2 + z)).re = z.im := by rw [re_gammaOf]; simp
    have h1 := norm_paperFT_le_decay hb hbs (gammaOf (1 / 2 + z))
    have h2 := norm_paperFT_le_decay hb hbs (conj (gammaOf (1 / 2 + z)))
    rw [Complex.conj_im, abs_neg, Complex.conj_re] at h2
    rw [hre] at h1 h2
    have he : Real.exp (|(gammaOf (1 / 2 + z)).im| * w) ≤ Real.exp (w / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (gammaOf (1 / 2 + z)).im])
    have hB := bumpDecayConstant_nonneg b
    rw [← bumpDecayConstant] at h1 h2
    have hd : 0 < (1 + |z.im|) ^ 2 := by positivity
    have h1' : ‖paperFT b (gammaOf (1 / 2 + z))‖ ≤ Real.exp (w / 2) * bumpDecayConstant b /
        (1 + |z.im|) ^ 2 := h1.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right he hB) hd.le)
    have h2' : ‖paperFT b (conj (gammaOf (1 / 2 + z)))‖ ≤ Real.exp (w / 2) * bumpDecayConstant b /
        (1 + |z.im|) ^ 2 := h2.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right he hB) hd.le)
    have hprod := mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
    have hm : ‖(Z.mult (1 / 2 + z) : ℂ)‖ = (Z.mult (1 / 2 + z) : ℝ) := by
      rw [Complex.norm_natCast]
    rw [hm]
    calc (Z.mult (1 / 2 + z) : ℝ) * (‖paperFT b (gammaOf (1 / 2 + z))‖ *
          ‖paperFT b (conj (gammaOf (1 / 2 + z)))‖)
        ≤ (Z.mult (1 / 2 + z) : ℝ) * (Real.exp (w / 2) * bumpDecayConstant b / (1 + |z.im|) ^ 2 *
          (Real.exp (w / 2) * bumpDecayConstant b / (1 + |z.im|) ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
      _ = _ := by
          rw [show Real.exp w = Real.exp (w / 2) * Real.exp (w / 2) by
            rw [← Real.exp_add]; ring_nf]
          field_simp
  · rw [lagCoeff, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero, zero_mul,
      zero_div]

/-- `Σ_z m_{½+z} (1 + |Im z|)^{−2} < ∞` for a tempered configuration. -/
theorem summable_indicator_mult_div_sq (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    Summable fun z : ℂ => Z.carrier.indicator (fun ρ => (Z.mult ρ : ℝ)) (1 / 2 + z) /
      (1 + |z.im|) ^ 2 := by
  -- on the carrier, `(1 + |γ|)^{−2} ≤ (5/4)/(1 + |γ_ρ|²)`
  have hsub : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im|) ^ 2 := by
    refine (hZ.mul_left (5 / 4)).of_nonneg_of_le (fun ρ => by positivity) fun ρ => ?_
    have hstrip := Z.strip ρ.1 ρ.2
    have hns : Complex.normSq (gammaOf ρ) = (ρ : ℂ).im ^ 2 + (1 / 2 - (ρ : ℂ).re) ^ 2 := by
      rw [Complex.normSq_apply, re_gammaOf, im_gammaOf]; ring
    have hb : (1 / 2 - (ρ : ℂ).re) ^ 2 ≤ 1 / 4 := by
      nlinarith [hstrip.1, hstrip.2]
    have hm := (Nat.cast_nonneg (Z.mult ρ) : (0 : ℝ) ≤ _)
    rw [hns, div_le_iff₀ (by positivity)]
    have hsq : 1 + (ρ : ℂ).im ^ 2 ≤ (1 + |(ρ : ℂ).im|) ^ 2 := by
      nlinarith [abs_nonneg (ρ : ℂ).im, sq_abs (ρ : ℂ).im]
    rw [show 5 / 4 * ((Z.mult ρ : ℝ) / (1 + ((ρ : ℂ).im ^ 2 + (1 / 2 - (ρ : ℂ).re) ^ 2))) *
      (1 + |(ρ : ℂ).im|) ^ 2 = (Z.mult ρ : ℝ) * (5 / 4 * (1 + |(ρ : ℂ).im|) ^ 2 /
        (1 + ((ρ : ℂ).im ^ 2 + (1 / 2 - (ρ : ℂ).re) ^ 2))) by ring]
    refine le_mul_of_one_le_right hm ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hind : Summable (Z.carrier.indicator fun ρ : ℂ => (Z.mult ρ : ℝ) / (1 + |ρ.im|) ^ 2) :=
    summable_subtype_iff_indicator.mp hsub
  have hcomp := (Equiv.summable_iff (Equiv.addLeft (1 / 2 : ℂ))).mpr hind
  refine hcomp.congr fun z => ?_
  simp only [Function.comp, Equiv.coe_addLeft]
  by_cases h : (1 / 2 + z) ∈ Z.carrier
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_div]

/-- **The second moment of the coefficients.** `S₂ = Σ_z |D(z)| (1 + |Im z|)² < ∞`. -/
theorem summable_norm_evenCoeff_mul_sq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    Summable fun z : ℂ => ‖evenCoeff Z b z‖ * (1 + |z.im|) ^ 2 := by
  have hC0 : 0 ≤ Real.exp w * bumpDecayConstant b ^ 2 := by positivity
  have hgs := summable_indicator_mult_div_sq Z hZ
  have hgc := hgs.comp_injective (starRingEnd ℂ).injective
  have hF : ∀ z : ℂ, ‖lagCoeff Z b z‖ * (1 + |z.im|) ^ 2 ≤ Real.exp w * bumpDecayConstant b ^ 2 *
      (Z.carrier.indicator (fun ρ => (Z.mult ρ : ℝ)) (1 / 2 + z) / (1 + |z.im|) ^ 2) := fun z => by
    have h := norm_lagCoeff_le_decay Z hb hw hbs z
    generalize Z.carrier.indicator (fun ρ => (Z.mult ρ : ℝ)) (1 / 2 + z) = m at h ⊢
    generalize Real.exp w * bumpDecayConstant b ^ 2 = C at h ⊢
    have hy0 : 0 < 1 + |z.im| := by positivity
    generalize 1 + |z.im| = y at h hy0 ⊢
    calc ‖lagCoeff Z b z‖ * y ^ 2 ≤ m * C / y ^ 4 * y ^ 2 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = C * (m / y ^ 2) := by field_simp
  refine ((hgs.mul_left (Real.exp w * bumpDecayConstant b ^ 2)).add
    (hgc.mul_left (Real.exp w * bumpDecayConstant b ^ 2))).of_nonneg_of_le
    (fun z => mul_nonneg (norm_nonneg _) (by positivity)) fun z => ?_
  have h1 := hF z
  have h2 := hF (conj z)
  have hci : |(conj z).im| = |z.im| := by rw [Complex.conj_im, abs_neg]
  rw [hci] at h2
  have hD : ‖evenCoeff Z b z‖ ≤ ‖lagCoeff Z b z‖ + ‖lagCoeff Z b (conj z)‖ := by
    rw [evenCoeff]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_conj]
  calc ‖evenCoeff Z b z‖ * (1 + |z.im|) ^ 2 ≤ (‖lagCoeff Z b z‖ + ‖lagCoeff Z b (conj z)‖) *
        (1 + |z.im|) ^ 2 := mul_le_mul_of_nonneg_right hD (by positivity)
    _ ≤ _ := by
        rw [add_mul]
        refine (add_le_add h1 h2).trans (le_of_eq ?_)
        simp only [Function.comp_apply, hci]

/-! ### Zero-free region ⟹ lag envelope -/

/-- **Zero-free region ⟹ lag envelope.** If every exponent of height `|Im z| ≤ G` has
`Re z ≤ ½ − η`, then `|2 Re S(v)| ≤ e^{v/2}(W e^{−ηv} + S₂/(1 + G)²)` for `v ≥ 0`. -/
theorem abs_two_re_lagStructure_le_of_zeroFree (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    {v η G : ℝ} (hv : 0 ≤ v) (hG : 0 ≤ G)
    (hfree : ∀ z, evenCoeff Z b z ≠ 0 → |z.im| ≤ G → z.re ≤ 1 / 2 - η) :
    |2 * (lagStructure Z b v).re| ≤ Real.exp (v / 2) *
      ((∑' z : ℂ, ‖evenCoeff Z b z‖) * Real.exp (-η * v) +
        (∑' z : ℂ, ‖evenCoeff Z b z‖ * (1 + |z.im|) ^ 2) / (1 + G) ^ 2) := by
  obtain ⟨hs, he⟩ := two_re_lagStructure_eq Z hZ hb hbs v
  have hsD := summable_norm_evenCoeff Z hZ hb hbs
  have hs2 := summable_norm_evenCoeff_mul_sq Z hZ hb hw hbs
  have hG2 : 0 < (1 + G) ^ 2 := by positivity
  have hterm : ∀ z : ℂ, ‖evenCoeff Z b z * cexp (z * v)‖ ≤ Real.exp (v / 2) *
      (‖evenCoeff Z b z‖ * Real.exp (-η * v) +
        ‖evenCoeff Z b z‖ * (1 + |z.im|) ^ 2 / (1 + G) ^ 2) := fun z => by
    by_cases hz : evenCoeff Z b z = 0
    · simp [hz]
    rw [norm_mul, Complex.norm_exp, show (z * (v : ℂ)).re = z.re * v by simp]
    have hD := norm_nonneg (evenCoeff Z b z)
    have hre := (abs_le.mp (abs_re_le_of_evenCoeff_ne_zero hz)).2
    by_cases hIm : |z.im| ≤ G
    · have h1 : Real.exp (z.re * v) ≤ Real.exp (v / 2) * Real.exp (-η * v) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [hfree z hz hIm])
      have h2 : 0 ≤ ‖evenCoeff Z b z‖ * (1 + |z.im|) ^ 2 / (1 + G) ^ 2 := by positivity
      have h4 : 0 ≤ Real.exp (v / 2) * (‖evenCoeff Z b z‖ * (1 + |z.im|) ^ 2 / (1 + G) ^ 2) := by
        positivity
      calc ‖evenCoeff Z b z‖ * Real.exp (z.re * v) ≤
            ‖evenCoeff Z b z‖ * (Real.exp (v / 2) * Real.exp (-η * v)) :=
            mul_le_mul_of_nonneg_left h1 hD
        _ = Real.exp (v / 2) * (‖evenCoeff Z b z‖ * Real.exp (-η * v)) := by ring
        _ ≤ _ := by rw [mul_add]; linarith
    · push Not at hIm
      have h1 : Real.exp (z.re * v) ≤ Real.exp (v / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h2 : 1 ≤ (1 + |z.im|) ^ 2 / (1 + G) ^ 2 := by
        rw [le_div_iff₀ hG2, one_mul]
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h3 : 0 ≤ Real.exp (v / 2) * (‖evenCoeff Z b z‖ * Real.exp (-η * v)) := by positivity
      calc ‖evenCoeff Z b z‖ * Real.exp (z.re * v) ≤ ‖evenCoeff Z b z‖ * Real.exp (v / 2) :=
            mul_le_mul_of_nonneg_left h1 hD
        _ ≤ ‖evenCoeff Z b z‖ * ((1 + |z.im|) ^ 2 / (1 + G) ^ 2) * Real.exp (v / 2) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hD h2) (Real.exp_pos _).le
        _ = Real.exp (v / 2) * (‖evenCoeff Z b z‖ * (1 + |z.im|) ^ 2 / (1 + G) ^ 2) := by ring
        _ ≤ _ := by rw [mul_add]; linarith
  have hR : Summable fun z : ℂ => Real.exp (v / 2) *
      (‖evenCoeff Z b z‖ * Real.exp (-η * v) +
        ‖evenCoeff Z b z‖ * (1 + |z.im|) ^ 2 / (1 + G) ^ 2) :=
    ((hsD.mul_right _).add (hs2.div_const _)).mul_left _
  have habs : |2 * (lagStructure Z b v).re| = ‖∑' z : ℂ, evenCoeff Z b z * cexp (z * v)‖ := by
    rw [← he, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ((hs.norm.tsum_le_tsum hterm hR).trans
    (le_of_eq ?_))
  rw [tsum_mul_left, Summable.tsum_add (hsD.mul_right _) (hs2.div_const _), tsum_mul_right,
    tsum_div_const]

/-! ### The zero-free profile of `ζ` -/

/-- The explicit width `η₀ = c₀/(2·25⁹)` of the zero-free region below height `e^{23}`. -/
def lowZeroFreeWidth : ℝ := Sieve.zeroFreeConst / (2 * 25 ^ 9)

theorem lowZeroFreeWidth_pos : 0 < lowZeroFreeWidth := by
  unfold lowZeroFreeWidth; have := Sieve.zeroFreeConst_pos; positivity

/-- `K = dlvpSharpConstant 1 = 14 + 10π + 6 log 2 < 49.7`, so `e^{29K/63} ≤ e^{23}`. -/
theorem exp_dlvpSharpConstant_le : Real.exp (29 * dlvpSharpConstant 1 / 63) ≤ Real.exp 23 := by
  refine Real.exp_le_exp.mpr ?_
  unfold dlvpSharpConstant landauSharpConstant digammaVerticalLogConstant
  have hpi := Real.pi_lt_d2
  have hl := Real.log_two_lt_d9
  norm_num at hl
  linarith

/-- **Below `e^{23}`.** Every nontrivial zero with `|γ| ≤ e^{23}` has `Re ρ ≤ 1 − η₀`. -/
theorem re_le_of_mem_zetaCarrier_low {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    (him : |ρ.im| ≤ Real.exp 23) : ρ.re ≤ 1 - lowZeroFreeWidth := by
  by_contra hgt
  push Not at hgt
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
  have h4 : 4 ≤ |ρ.im| := by
    by_contra h; push Not at h
    exact riemannZeta_ne_zero_of_abs_im_lt_four hstrip.1 hstrip.2 h hρ.1
  set N₀ : ℕ := ⌈Real.exp 24⌉₊ with hN₀
  have hN₀ge : Real.exp 24 ≤ N₀ := Nat.le_ceil _
  have hN₀le : (N₀ : ℝ) ≤ Real.exp 25 := by
    have := Nat.ceil_lt_add_one (Real.exp_pos 24).le
    have h1 : Real.exp 24 + 1 ≤ Real.exp 25 := by
      have : Real.exp 25 = Real.exp 24 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]
      nlinarith [Real.add_one_le_exp 1, Real.add_one_le_exp 24]
    linarith
  have hN₀pos : (0 : ℝ) < N₀ := lt_of_lt_of_le (Real.exp_pos _) hN₀ge
  have hlog24 : 24 ≤ Real.log N₀ := by
    rw [Real.le_log_iff_exp_le hN₀pos]; exact hN₀ge
  have hlog25 : Real.log N₀ ≤ 25 := by
    rw [Real.log_le_iff_le_exp hN₀pos]; exact hN₀le
  have hN₀2 : 2 ≤ N₀ := by
    have : (2 : ℝ) ≤ N₀ := le_trans (by linarith [Real.add_one_le_exp 24]) hN₀ge
    exact_mod_cast this
  have hbig : 3 + 2 * |ρ.im| ≤ (N₀ : ℝ) := by
    refine le_trans ?_ hN₀ge
    have : Real.exp 24 = Real.exp 23 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    have he1 := Real.exp_one_gt_d9
    have h24 : (24 : ℝ) ≤ Real.exp 23 := by linarith [Real.add_one_le_exp 23]
    have hmul : Real.exp 23 * 2.7182818283 ≤ Real.exp 23 * Real.exp 1 :=
      mul_le_mul_of_nonneg_left he1.le (Real.exp_pos _).le
    linarith
  have hc : Sieve.zeroFreeConst / (2 * Real.log N₀ ^ 9) ≥ lowZeroFreeWidth := by
    unfold lowZeroFreeWidth
    have hc0 := Sieve.zeroFreeConst_pos
    apply div_le_div_of_nonneg_left hc0.le (by positivity)
    have : Real.log N₀ ^ 9 ≤ 25 ^ 9 := pow_le_pow_left₀ (by linarith) hlog25 9
    linarith
  have hne := Sieve.riemannZeta_ne_zero_of_re_gt (β := ρ.re) (γ := ρ.im) (N := N₀) (by linarith)
    hN₀2 (by linarith) hbig hstrip.2.le (by linarith)
  rw [Complex.re_add_im] at hne
  exact hne hρ.1

/-- **Above `e^{23}`.** Every nontrivial zero with `|γ| ≥ e^{23}` has `Re ρ ≤ 1 − 1/(100 log|γ|)`. -/
theorem re_le_of_mem_zetaCarrier_high {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    (him : Real.exp 23 ≤ |ρ.im|) : ρ.re ≤ 1 - 1 / 100 / Real.log |ρ.im| := by
  have h0 := exp_dlvpSharpConstant_le
  rcases le_or_gt 0 ρ.im with hpos | hneg
  · rw [abs_of_nonneg hpos] at him ⊢
    have := xiZeroCopy_zero_free_explicit (q := carrierCopy ⟨ρ, hρ⟩) (by
      rw [carrierCopy_val]; exact h0.trans him)
    rwa [carrierCopy_val] at this
  · rw [abs_of_neg hneg] at him ⊢
    have hc := conj_mem_zetaZeroConfig hρ
    have := xiZeroCopy_zero_free_explicit (q := carrierCopy ⟨conj ρ, hc⟩) (by
      rw [carrierCopy_val, Complex.conj_im]; exact h0.trans him)
    rwa [carrierCopy_val, Complex.conj_re, Complex.conj_im] at this

/-- **The zero-free profile of the exponents.** For `G ≥ e^{23}`, every exponent of the lag function
of `ζ` with `|Im z| ≤ G` has `Re z ≤ ½ − min(η₀, 1/(100 log G))`. -/
theorem re_le_of_evenCoeff_zeta {b : ℝ → ℂ} {G : ℝ} (hG : Real.exp 23 ≤ G) {z : ℂ}
    (hz : evenCoeff zetaZeroConfig b z ≠ 0) (him : |z.im| ≤ G) :
    z.re ≤ 1 / 2 - min lowZeroFreeWidth (1 / (100 * Real.log G)) := by
  have hG0 : 0 < G := lt_of_lt_of_le (Real.exp_pos _) hG
  have hlogG : 23 ≤ Real.log G := by rw [Real.le_log_iff_exp_le hG0]; exact hG
  -- the carrier point with real part `½ + Re z` and ordinate `± Im z`
  have key : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 + z.re → |ρ.im| = |z.im| →
      z.re ≤ 1 / 2 - min lowZeroFreeWidth (1 / (100 * Real.log G)) := fun ρ hρ hre him' => by
    rcases le_or_gt |ρ.im| (Real.exp 23) with hlow | hhigh
    · have := re_le_of_mem_zetaCarrier_low hρ hlow
      have := min_le_left lowZeroFreeWidth (1 / (100 * Real.log G))
      linarith
    · have h1 := re_le_of_mem_zetaCarrier_high hρ hhigh.le
      have hlog0 : 0 < Real.log |ρ.im| := Real.log_pos (lt_of_le_of_lt
        (by linarith [Real.add_one_le_exp 23]) hhigh)
      have hlogle : Real.log |ρ.im| ≤ Real.log G := Real.log_le_log
        (lt_trans (Real.exp_pos _) hhigh) ((le_of_eq him').trans him)
      have h2 : 1 / (100 * Real.log G) ≤ 1 / 100 / Real.log |ρ.im| := by
        rw [div_div]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      have := min_le_right lowZeroFreeWidth (1 / (100 * Real.log G))
      linarith
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · exact key _ h (by simp) (by simp)
  · exact key _ h (by simp) (by simp)

/-! ### The envelope -/

/-- **The unconditional lag envelope of `ζ`.** For every width `w ∈ (0, ½ log 2)` and every lag
`v ≥ max(230², 1/(100 η₀²))`, the window functional of the difference test satisfies
`P_v ≥ −|M| − (W + S₂) e^{v/2 − √v/10}`, with `M = 2 Re S(0)`, `W = Σ_z |D(z)|`,
`S₂ = Σ_z |D(z)| (1 + |Im z|)²`. -/
theorem zeta_lag_envelope {w v : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (hv1 : 230 ^ 2 ≤ v)
    (hv2 : 1 / (100 * lowZeroFreeWidth ^ 2) ≤ v) :
    -|2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| -
        ((∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖) +
          ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * (1 + |z.im|) ^ 2) *
          Real.exp (v / 2 - Real.sqrt v / 10) ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ w := modScaledBump_support hw 0
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv1
  have hP : (lagPrimeWindowRHS v w (EF.weilTest (twoBump b v (-1)) (twoBump b v (-1)))).re =
      2 * (lagStructure zetaZeroConfig b 0).re - 2 * (lagStructure zetaZeroConfig b v).re := by
    rw [hbdef, ← literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv0,
      ← zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
        (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
        (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
          (modScaledBump_support hw 0)) v (-1)),
      re_W_lag_eq zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs v]
  rw [hP]
  -- the height cut `G = e^{√v/10}`
  set q : ℝ := Real.sqrt v with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg v
  have hq230 : 230 ≤ q := by rw [hq]; exact Real.le_sqrt_of_sq_le (by linarith)
  have hqsq : q ^ 2 = v := by rw [hq]; exact Real.sq_sqrt hv0
  set G : ℝ := Real.exp (q / 10) with hG
  have hG23 : Real.exp 23 ≤ G := Real.exp_le_exp.mpr (by linarith)
  have hlogG : Real.log G = q / 10 := by rw [hG, Real.log_exp]
  set η : ℝ := min lowZeroFreeWidth (1 / (100 * Real.log G)) with hη
  have hfree : ∀ z, evenCoeff zetaZeroConfig b z ≠ 0 → |z.im| ≤ G → z.re ≤ 1 / 2 - η :=
    fun z hz him => re_le_of_evenCoeff_zeta hG23 hz him
  have henv := abs_two_re_lagStructure_le_of_zeroFree zetaZeroConfig temperedConfig_zetaZeroConfig
    hb hw.le hbs hv0 (Real.exp_pos _).le hfree
  -- `ηv ≥ √v/10` and `(1 + G)^{−2} ≤ e^{−√v/10}`
  have hηv : q / 10 ≤ η * v := by
    rw [hη]
    rcases le_total lowZeroFreeWidth (1 / (100 * Real.log G)) with h | h
    · rw [min_eq_left h]
      have hη0 := lowZeroFreeWidth_pos
      have : 1 ≤ 100 * lowZeroFreeWidth ^ 2 * v := by
        rw [div_le_iff₀ (by positivity)] at hv2; linarith
      have hsq : (1 / 10 : ℝ) ≤ lowZeroFreeWidth * q := by
        by_contra hlt
        push Not at hlt
        have hnn : 0 ≤ lowZeroFreeWidth * q := mul_nonneg hη0.le hq0
        have h1 : (lowZeroFreeWidth * q) ^ 2 < (1 / 10) ^ 2 :=
          pow_lt_pow_left₀ hlt hnn (by norm_num)
        have h2 : (lowZeroFreeWidth * q) ^ 2 = lowZeroFreeWidth ^ 2 * v := by rw [← hqsq]; ring
        nlinarith
      have := mul_le_mul_of_nonneg_right hsq hq0
      have h3 : lowZeroFreeWidth * v = lowZeroFreeWidth * q * q := by rw [← hqsq]; ring
      linarith
    · rw [min_eq_right h, hlogG]
      have hq1 : 0 < q := by linarith
      rw [← hqsq]; field_simp; ring_nf; nlinarith
  have hE1 : Real.exp (-η * v) ≤ Real.exp (-(q / 10)) := Real.exp_le_exp.mpr (by linarith)
  have hE2 : 1 / (1 + G) ^ 2 ≤ Real.exp (-(q / 10)) := by
    have hG0 : 0 < G := Real.exp_pos _
    have hx0 : 0 ≤ Real.exp (-(q / 10)) := (Real.exp_pos _).le
    have hx1 : Real.exp (-(q / 10)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc 1 / (1 + G) ^ 2 ≤ 1 / G ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hG0.le (by linarith) 2)
      _ = Real.exp (-(q / 10)) ^ 2 := by rw [hG, Real.exp_neg, inv_pow, one_div]
      _ ≤ Real.exp (-(q / 10)) := pow_le_of_le_one hx0 hx1 (by norm_num)
  set W : ℝ := ∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖ with hW
  set S₂ : ℝ := ∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖ * (1 + |z.im|) ^ 2 with hS₂
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hS0 : 0 ≤ S₂ := tsum_nonneg fun z => by positivity
  have hphi : |2 * (lagStructure zetaZeroConfig b v).re| ≤ (W + S₂) * Real.exp (v / 2 - q / 10) := by
    refine henv.trans ?_
    have h1 : W * Real.exp (-η * v) ≤ W * Real.exp (-(q / 10)) :=
      mul_le_mul_of_nonneg_left hE1 hW0
    have h2 : S₂ / (1 + G) ^ 2 ≤ S₂ * Real.exp (-(q / 10)) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hE2 hS0
    calc Real.exp (v / 2) * (W * Real.exp (-η * v) + S₂ / (1 + G) ^ 2)
        ≤ Real.exp (v / 2) * (W * Real.exp (-(q / 10)) + S₂ * Real.exp (-(q / 10))) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.exp_pos _).le
      _ = (W + S₂) * Real.exp (v / 2 - q / 10) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
  have hM := neg_abs_le (2 * (lagStructure zetaZeroConfig b 0).re)
  have hphi' := (abs_le.mp hphi).2
  linarith

end GaloisForLFunctions.SquareRootThreshold
