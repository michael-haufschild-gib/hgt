import GaloisForLFunctions.HTGeometry.WienerHopfIndexTheorem
import GaloisForLFunctions.HTGeometry.RealGroupCStarFaithful

/-!
# `C*(ℝ) ≅ C₀(ℝ̂)` on the circle, and the circle multiplier representation

The Cayley symbol `c(w) = (-1 - 2πiw)/(1 - 2πiw)` maps the frequency line homeomorphically onto the
circle minus `1`, with inverse `cayleyInv z = -Im z / (π |z - 1|²)` (`cayleySymbol_cayleyInv`,
`cayleyInv_cayleySymbol`), and `c(w) → 1` as `w → ∞`.

* `le_norm_lpBoundedMulCLM`, `le_norm_fourierMulCLM`: a multiplier dominates its symbol at every
  point of continuity (test on the indicator of a short interval).  Hence the circle multiplier
  representation `U ↦ C_{U ∘ c}` is isometric (`norm_circleMultiplier`).
* `circleOfC0`: a continuous symbol vanishing at infinity descends to the circle, with value `0` at
  `1` (near `1`, `1 ≤ 2π |z - 1| |cayleyInv z|`).  By Riemann–Lebesgue the convolution operator of
  `G ∈ C_c(ℝ)` is the circle multiplier of `𝓕G ∘ c⁻¹` (`op_conv_eq_circleMultiplier`).
* `circleMultiplier_sub_mem_range`: for every `U ∈ C(S¹)`, `C_U - U(1) ∈ C*(ℝ)`.  The symbols with
  this property form a closed `*`-subalgebra containing the coordinate (`C_z = 1 - 2V` with `V`
  convolution by an `L¹` kernel, approximated in `L¹` by `C_c`), hence all of `C(S¹)` by
  Stone–Weierstrass.
* `realGroupCStarEquiv : RealGroupCStar ≃⋆ₐ[ℂ] circleVanishing`: the full group C⋆-algebra of `ℝ` is
  the algebra of continuous functions on the circle vanishing at `1` (full = reduced for `ℝ` plus the
  two inclusions above).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology FourierTransform
open scoped CompactlySupported ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open BandKernel

/-! ## Lower bounds for multipliers -/

/-- **A multiplication operator dominates its symbol at points of continuity.** -/
theorem le_norm_lpBoundedMulCLM {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) {w₀ : ℝ} (hcont : ContinuousAt φ w₀) :
    ‖φ w₀‖ ≤ ‖lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC‖ := by
  set M := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC
  refine le_of_forall_sub_le fun ε hε => ?_
  by_cases hle : ‖φ w₀‖ - ε ≤ 0
  · exact hle.trans (norm_nonneg _)
  push Not at hle
  obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  set s := Ioo (w₀ - δ) (w₀ + δ)
  have hμs : volume s ≠ ∞ := measure_Ioo_lt_top.ne
  set g := indicatorConstLp 2 measurableSet_Ioo hμs (1 : ℂ)
  have hvol : volume.real s = 2 * δ := by
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hg : 0 < ‖g‖ := by
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul, hvol]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hpt : ‖(((‖φ w₀‖ - ε : ℝ) : ℂ)) • g‖ ≤ ‖M g‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [Lp.coeFn_smul (((‖φ w₀‖ - ε : ℝ) : ℂ)) g, lpBoundedMulCLM_coeFn hφ hC0 hC g,
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioo) (hμs := hμs) (c := (1 : ℂ))]
      with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, norm_mul, norm_mul]
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, norm_one, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hle]
      have hd : dist x w₀ < δ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have := hδφ hd
      rw [dist_eq_norm] at this
      linarith [norm_sub_norm_le (φ w₀) (φ x), norm_sub_rev (φ x) (φ w₀)]
    · rw [indicator_of_notMem hx, norm_zero, mul_zero, mul_zero]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hle] at hpt
  have h2 := hpt.trans (M.le_opNorm g)
  exact le_of_mul_le_mul_right h2 hg

/-- **A Fourier multiplier dominates its symbol at points of continuity.** -/
theorem le_norm_fourierMulCLM {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) {w₀ : ℝ} (hcont : ContinuousAt φ w₀) :
    ‖φ w₀‖ ≤ ‖fourierMulCLM hφ hC0 hC‖ := by
  refine (le_norm_lpBoundedMulCLM hφ hC0 hC hcont).trans ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
  have h := (fourierMulCLM hφ hC0 hC).le_opNorm (fourierL2inv ℝ g)
  rw [fourierMulCLM_apply, fourierL2_fourierL2inv, norm_fourierL2inv_apply,
    norm_fourierL2inv_apply] at h
  exact h

/-! ## The inverse Cayley map -/

/-- The point `1` of the circle, the image of `w = ±∞`. -/
def circleOne : UnitCircle := ⟨1, by simp⟩

/-- The inverse Cayley map `z ↦ -Im z / (π |z - 1|²)` (for `|z| = 1`, `z ≠ 1`). -/
def cayleyInv (z : ℂ) : ℝ := -z.im / (Real.pi * Complex.normSq (z - 1))

theorem one_sub_two_pi_mul_I_ne_zero (w : ℝ) : (1 - 2 * Real.pi * w * Complex.I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem cayleySymbol_sub_one (w : ℝ) :
    cayleySymbol w - 1 = -2 / (1 - 2 * Real.pi * w * Complex.I) := by
  rw [cayleySymbol_eq, div_sub_one (one_sub_two_pi_mul_I_ne_zero w)]
  congr 1
  ring

theorem cayleySymbol_ne_one (w : ℝ) : cayleySymbol w ≠ 1 := by
  intro h
  have h' := cayleySymbol_sub_one w
  rw [h, sub_self] at h'
  exact (div_ne_zero (by norm_num) (one_sub_two_pi_mul_I_ne_zero w)) h'.symm

theorem cayleySymbol_injective : Function.Injective cayleySymbol := by
  intro w₁ w₂ h
  have h1 := cayleySymbol_sub_one w₁
  rw [h, cayleySymbol_sub_one, div_eq_div_iff (one_sub_two_pi_mul_I_ne_zero w₂)
    (one_sub_two_pi_mul_I_ne_zero w₁)] at h1
  have h2 := congrArg Complex.im h1
  simp at h2
  linarith

theorem re_sq_add_im_sq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z.re * z.re + z.im * z.im = 1 := by
  have h := Complex.normSq_eq_norm_sq z
  rw [hz, one_pow, Complex.normSq_apply] at h
  exact h

theorem re_lt_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) : z.re < 1 := by
  have hn := re_sq_add_im_sq_of_norm_eq_one hz
  have hle : z.re ≤ 1 := by nlinarith [mul_self_nonneg z.im, mul_self_nonneg (z.re - 1)]
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    apply h1
    have him : z.im = 0 := by nlinarith [mul_self_nonneg z.im]
    exact Complex.ext (by simpa using h) (by simpa using him)

theorem normSq_sub_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.normSq (z - 1) = 2 - 2 * z.re := by
  have hn := re_sq_add_im_sq_of_norm_eq_one hz
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

/-- **The inverse Cayley map inverts the Cayley symbol** on the circle minus `1`. -/
theorem cayleySymbol_cayleyInv {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) :
    cayleySymbol (cayleyInv z) = z := by
  have hn := re_sq_add_im_sq_of_norm_eq_one hz
  have hx := re_lt_one_of_norm_eq_one hz h1
  have ha : (0 : ℝ) < 1 - z.re := by linarith
  have ht : 2 * Real.pi * cayleyInv z = -z.im / (1 - z.re) := by
    rw [cayleyInv, normSq_sub_one_of_norm_eq_one hz]
    field_simp
  rw [cayleySymbol_eq, div_eq_iff (one_sub_two_pi_mul_I_ne_zero _)]
  have hc : (2 * (Real.pi : ℂ) * (cayleyInv z : ℂ)) = ((-z.im / (1 - z.re) : ℝ) : ℂ) := by
    rw [← ht]
    push_cast
    ring
  rw [show (-1 - 2 * (Real.pi : ℂ) * (cayleyInv z : ℂ) * Complex.I) =
      -1 - (2 * (Real.pi : ℂ) * (cayleyInv z : ℂ)) * Complex.I by ring,
    show (1 - 2 * (Real.pi : ℂ) * (cayleyInv z : ℂ) * Complex.I) =
      1 - (2 * (Real.pi : ℂ) * (cayleyInv z : ℂ)) * Complex.I by ring, hc]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.mul_im, Complex.sub_im,
      Complex.one_im]
    field_simp
    nlinarith
  · simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.mul_im, Complex.sub_im,
      Complex.one_im, Complex.neg_im]
    field_simp
    ring

theorem cayleyInv_cayleySymbol (w : ℝ) : cayleyInv (cayleySymbol w) = w :=
  cayleySymbol_injective (cayleySymbol_cayleyInv (norm_cayleySymbol w) (cayleySymbol_ne_one w))

/-- Near `1` the inverse Cayley map is large: `1 ≤ 2π |z - 1| |cayleyInv z|`. -/
theorem one_le_mul_abs_cayleyInv {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) (hd : ‖z - 1‖ ≤ 1) :
    1 ≤ 2 * Real.pi * ‖z - 1‖ * |cayleyInv z| := by
  have hn := re_sq_add_im_sq_of_norm_eq_one hz
  have hx := re_lt_one_of_norm_eq_one hz h1
  have hns := normSq_sub_one_of_norm_eq_one hz
  have hd2 : ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by rw [← Complex.normSq_eq_norm_sq, hns]
  have hx2 : 1 / 2 ≤ z.re := by nlinarith [norm_nonneg (z - 1)]
  have hpos : 0 < ‖z - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact h1
  have hsq : (2 * Real.pi * ‖z - 1‖ * |cayleyInv z|) ^ 2 = 4 * z.im ^ 2 / (2 - 2 * z.re) := by
    rw [mul_pow, mul_pow, mul_pow, sq_abs, cayleyInv, hns, div_pow, hd2]
    have : (2 - 2 * z.re) ≠ 0 := by linarith
    field_simp
    ring
  have hge : 1 ≤ (2 * Real.pi * ‖z - 1‖ * |cayleyInv z|) ^ 2 := by
    rw [hsq, le_div_iff₀ (by linarith)]
    nlinarith
  have h0 : 0 ≤ 2 * Real.pi * ‖z - 1‖ * |cayleyInv z| := by positivity
  nlinarith

theorem continuousAt_cayleyInv {z : ℂ} (h1 : z ≠ 1) : ContinuousAt cayleyInv z := by
  have hne : Complex.normSq (z - 1) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero, sub_eq_zero]
    exact h1
  unfold cayleyInv
  refine ContinuousAt.div (Complex.continuous_im.neg.continuousAt) ?_ ?_
  · exact (continuous_const.mul (Complex.continuous_normSq.comp
      (continuous_id.sub continuous_const))).continuousAt
  · exact mul_ne_zero Real.pi_ne_zero hne

/-- **Descent of `C₀(ℝ)` symbols to the circle**: `φ ∘ c⁻¹` extended by `0` at `1`. -/
def circleOfC0 (φ : ℝ → ℂ) (hφ : Continuous φ) (h0 : Tendsto φ (cocompact ℝ) (𝓝 0)) :
    C(UnitCircle, ℂ) where
  toFun z := if (z : ℂ) = 1 then 0 else φ (cayleyInv z)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro z₀
    by_cases hz₀ : (z₀ : ℂ) = 1
    · rw [Metric.continuousAt_iff]
      intro ε hε
      rw [cocompact_eq_atBot_atTop] at h0
      have hbot := (Metric.tendsto_nhds.mp (h0.mono_left le_sup_left)) ε hε
      have htop := (Metric.tendsto_nhds.mp (h0.mono_left le_sup_right)) ε hε
      obtain ⟨A, hA⟩ := Filter.eventually_atBot.mp hbot
      obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp htop
      set R := max (|A|) (|B|) + 1
      have hR : 0 < R := by positivity
      refine ⟨min 1 (1 / (2 * Real.pi * R)), by positivity, fun z hz => ?_⟩
      rw [if_pos hz₀]
      by_cases hz1 : (z : ℂ) = 1
      · rw [if_pos hz1, dist_self]
        exact hε
      · rw [if_neg hz1, dist_zero_right]
        rw [Subtype.dist_eq, hz₀, dist_eq_norm] at hz
        have hd1 : ‖(z : ℂ) - 1‖ ≤ 1 := (lt_of_lt_of_le hz (min_le_left _ _)).le
        have hdR : ‖(z : ℂ) - 1‖ < 1 / (2 * Real.pi * R) := lt_of_lt_of_le hz (min_le_right _ _)
        have hbig := one_le_mul_abs_cayleyInv (norm_coe_unitCircle z) hz1 hd1
        have hR' : R < |cayleyInv z| := by
          by_contra hle
          push Not at hle
          have : 2 * Real.pi * ‖(z : ℂ) - 1‖ * |cayleyInv z| <
              2 * Real.pi * (1 / (2 * Real.pi * R)) * R := by
            have hp : 0 < 2 * Real.pi := by positivity
            calc 2 * Real.pi * ‖(z : ℂ) - 1‖ * |cayleyInv z|
                ≤ 2 * Real.pi * ‖(z : ℂ) - 1‖ * R := by gcongr
              _ < 2 * Real.pi * (1 / (2 * Real.pi * R)) * R := by gcongr
          rw [show 2 * Real.pi * (1 / (2 * Real.pi * R)) * R = 1 by field_simp] at this
          linarith
        rcases le_or_gt 0 (cayleyInv z) with hpos | hneg
        · rw [abs_of_nonneg hpos] at hR'
          have := hB (cayleyInv z) (by linarith [le_abs_self B, le_max_right (|A|) (|B|)])
          rwa [dist_zero_right] at this
        · rw [abs_of_neg hneg] at hR'
          have := hA (cayleyInv z) (by linarith [neg_abs_le A, le_max_left (|A|) (|B|)])
          rwa [dist_zero_right] at this
    · have hev : (fun z : UnitCircle => if (z : ℂ) = 1 then 0 else φ (cayleyInv z)) =ᶠ[𝓝 z₀]
          fun z => φ (cayleyInv z) := by
        have hopen : IsOpen {z : UnitCircle | (z : ℂ) ≠ 1} :=
          isOpen_ne_fun continuous_subtype_val continuous_const
        filter_upwards [hopen.mem_nhds hz₀] with z hz
        rw [if_neg hz]
      refine ContinuousAt.congr ?_ hev.symm
      exact hφ.continuousAt.comp ((continuousAt_cayleyInv hz₀).comp continuous_subtype_val.continuousAt)

theorem circleOfC0_cayleyCirclePoint (φ : ℝ → ℂ) (hφ : Continuous φ)
    (h0 : Tendsto φ (cocompact ℝ) (𝓝 0)) (w : ℝ) :
    circleOfC0 φ hφ h0 (cayleyCirclePoint w) = φ w := by
  change (if cayleySymbol w = 1 then 0 else φ (cayleyInv (cayleySymbol w))) = φ w
  rw [if_neg (cayleySymbol_ne_one w), cayleyInv_cayleySymbol]

theorem circleOfC0_one (φ : ℝ → ℂ) (hφ : Continuous φ) (h0 : Tendsto φ (cocompact ℝ) (𝓝 0)) :
    circleOfC0 φ hφ h0 circleOne = 0 := by
  change (if (1 : ℂ) = 1 then 0 else φ (cayleyInv 1)) = 0
  rw [if_pos rfl]

theorem tendsto_cayleySymbol_atTop : Tendsto cayleySymbol atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun w : ℝ => (Real.pi)⁻¹ * w⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (Real.pi)⁻¹
  refine squeeze_zero' (Eventually.of_forall fun w => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with w hw
  rw [cayleySymbol_sub_one, norm_div, norm_neg]
  have hden : 2 * Real.pi * w ≤ ‖(1 - 2 * Real.pi * w * Complex.I : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re]
    simp
    rw [abs_of_pos hw, abs_of_pos Real.pi_pos]
  have hpos : 0 < 2 * Real.pi * w := by positivity
  calc ‖(2 : ℂ)‖ / ‖(1 - 2 * Real.pi * w * Complex.I : ℂ)‖ ≤ 2 / (2 * Real.pi * w) := by
        rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
        exact div_le_div_of_nonneg_left (by norm_num) hpos hden
    _ = (Real.pi)⁻¹ * w⁻¹ := by field_simp

/-! ## The circle multiplier representation is isometric -/

/-- **`‖C_U‖ = ‖U‖_∞`**: the multiplier dominates its symbol at every Cayley point, and the Cayley
points accumulate at `1`. -/
theorem norm_circleMultiplier (U : C(UnitCircle, ℂ)) : ‖circleMultiplier U‖ = ‖U‖ := by
  refine le_antisymm (norm_circleMultiplier_le U) ?_
  have hpt : ∀ w : ℝ, ‖U (cayleyCirclePoint w)‖ ≤ ‖circleMultiplier U‖ := fun w =>
    le_norm_fourierMulCLM (measurable_circleSymbol U) (norm_nonneg U) (norm_circleSymbol_le U)
      (U.continuous.comp continuous_cayleyCirclePoint).continuousAt
  refine (ContinuousMap.norm_le U (norm_nonneg _)).mpr fun z => ?_
  by_cases hz : (z : ℂ) = 1
  · have hc : Tendsto cayleyCirclePoint atTop (𝓝 z) := by
      rw [tendsto_subtype_rng, hz]
      exact tendsto_cayleySymbol_atTop
    exact le_of_tendsto ((U.continuous.tendsto z).comp hc).norm (Eventually.of_forall hpt)
  · have hzc : z = cayleyCirclePoint (cayleyInv z) :=
      Subtype.ext (cayleySymbol_cayleyInv (norm_coe_unitCircle z) hz).symm
    rw [hzc]
    exact hpt _

theorem circleMultiplier_injective : Function.Injective circleMultiplier := by
  intro U V h
  have := norm_circleMultiplier (U - V)
  rw [show circleMultiplier (U - V) = circleMultiplier U - circleMultiplier V from
    map_sub circleMultiplierHom U V, h, sub_self, norm_zero] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this.symm)

theorem isometry_circleMultiplier : Isometry circleMultiplier :=
  AddMonoidHomClass.isometry_of_norm circleMultiplierHom norm_circleMultiplier

/-! ## Convolution operators are circle multipliers -/

/-- The circle symbol `𝓕G ∘ c⁻¹` of a convolution kernel (Riemann–Lebesgue: it vanishes at `1`). -/
def convCircle (G : C_c(ℝ, ℂ)) : C(UnitCircle, ℂ) :=
  circleOfC0 (𝓕 (G : ℝ → ℂ)) (continuous_fourier_of_integrable' (BandKernel.integrable_cc G))
    (Real.zero_at_infty_fourier _)

theorem convCircle_one (G : C_c(ℝ, ℂ)) : convCircle G circleOne = 0 := circleOfC0_one _ _ _

theorem op_conv_eq_circleMultiplier (G : C_c(ℝ, ℂ)) :
    (BandKernel.conv G).op = circleMultiplier (convCircle G) := by
  rw [BandKernel.op_conv]
  exact fourierMulCLM_congr_ae _ _ _ _ _ _
    (Eventually.of_forall fun w => (circleOfC0_cayleyCirclePoint _ _ _ w).symm)

/-! ## `C*(ℝ) ≅ C₀(ℝ̂)` on the circle -/

/-- The circle symbols vanishing at `1 = c(±∞)`: `C₀(ℝ̂)` transported to the circle. -/
def circleVanishing : NonUnitalStarSubalgebra ℂ C(UnitCircle, ℂ) where
  carrier := {V | V circleOne = 0}
  add_mem' {V W} hV hW := by
    change V circleOne + W circleOne = 0
    rw [show V circleOne = 0 from hV, show W circleOne = 0 from hW, add_zero]
  zero_mem' := rfl
  mul_mem' {V W} hV _ := by
    change V circleOne * W circleOne = 0
    rw [show V circleOne = 0 from hV, zero_mul]
  smul_mem' c V hV := by
    change c * V circleOne = 0
    rw [show V circleOne = 0 from hV, mul_zero]
  star_mem' {V} hV := by
    change star (V circleOne) = 0
    rw [show V circleOne = 0 from hV, star_zero]

theorem mem_circleVanishing {V : C(UnitCircle, ℂ)} : V ∈ circleVanishing ↔ V circleOne = 0 :=
  Iff.rfl

theorem isClosed_circleVanishing : IsClosed (circleVanishing : Set C(UnitCircle, ℂ)) :=
  isClosed_eq (continuous_eval_const circleOne) continuous_const

theorem isClosed_range_convRegular : IsClosed (Set.range convRegular) :=
  (AddMonoidHomClass.isometry_of_norm convRegular norm_convRegular).isClosedEmbedding.isClosed_range

/-- **Every element of `C*(ℝ)` is a circle multiplier with symbol vanishing at `1`.** -/
theorem exists_circle_of_convRegular (z : RealGroupCStar) :
    ∃ V ∈ circleVanishing, circleMultiplier V = convRegular z := by
  have hT : IsClosed (circleMultiplier '' (circleVanishing : Set C(UnitCircle, ℂ))) :=
    isometry_circleMultiplier.isClosedEmbedding.isClosedMap _ isClosed_circleVanishing
  have hP : IsClosed {z : RealGroupCStar |
      convRegular z ∈ circleMultiplier '' (circleVanishing : Set C(UnitCircle, ℂ))} :=
    hT.preimage continuous_convRegular
  refine (toEnvelope_dense convKernels convL1Norm).induction_on z hP fun K => ?_
  obtain ⟨_, ⟨G, rfl⟩⟩ := K
  exact ⟨convCircle G, convCircle_one G, (op_conv_eq_circleMultiplier G).symm⟩

/-- The Volterra operator `V = conv(k)` lies in `C*(ℝ)` (`L¹`-approximation of `k` by `C_c`). -/
theorem cayleyVolterra_mem_range_convRegular : cayleyVolterra ∈ Set.range convRegular := by
  rw [← isClosed_range_convRegular.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hgcs, hgint, hgc, hgi⟩ :=
    integrable_cayleyKernel.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  set G : C_c(ℝ, ℂ) := ⟨⟨g, hgc⟩, hgcs⟩
  refine ⟨convRegular (toEnvelope convKernels convL1Norm (convElem G)), ⟨_, rfl⟩, ?_⟩
  rw [convRegular_toEnvelope, dist_eq_norm]
  have hm : Measurable fun t => cayleyKernel t - g t := measurable_cayleyKernel.sub hgc.measurable
  have hi : Integrable fun t => cayleyKernel t - g t := integrable_cayleyKernel.sub hgi
  have hdiff : cayleyVolterra - (convElem G : BandKernel).op =
      (convolutionKernel (fun t => cayleyKernel t - g t) hm hi).op := by
    rw [cayleyVolterra, show (convElem G : BandKernel).op =
      (convolutionKernel g hgc.measurable hgi).op from SchurKernel.op_congr fun _ _ => rfl,
      ← SchurKernel.sub_op]
    exact SchurKernel.op_congr fun _ _ => rfl
  rw [hdiff]
  refine lt_of_le_of_lt (SchurKernel.norm_op_le _) ?_
  have hb : ((convolutionKernel (fun t => cayleyKernel t - g t) hm hi).bound : ℝ) =
      ∫ t, ‖cayleyKernel t - g t‖ := by
    change ((∫⁻ x, ‖cayleyKernel x - g x‖ₑ).toNNReal : ℝ) = _
    rw [ENNReal.coe_toNNReal_eq_toReal, integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  rw [hb]
  linarith

/-- **Every circle multiplier is a scalar plus an element of `C*(ℝ)`**: `C_U - U(1) ∈ C*(ℝ)`
(Stone–Weierstrass on the closed `*`-subalgebra of such symbols, which contains the coordinate
since `C_z = 1 - 2V`). -/
theorem circleMultiplier_sub_mem_range (U : C(UnitCircle, ℂ)) :
    circleMultiplier U - U circleOne • (1 : L2Real →L[ℂ] L2Real) ∈ Set.range convRegular := by
  set R := NonUnitalStarAlgHom.range convRegular
  have hR : ∀ T, T ∈ R ↔ T ∈ Set.range convRegular := fun T => Iff.rfl
  let B : StarSubalgebra ℂ C(UnitCircle, ℂ) :=
    { carrier := {U | circleMultiplier U - U circleOne • (1 : L2Real →L[ℂ] L2Real) ∈ R}
      mul_mem' := by
        intro U V hU hV
        change circleMultiplier (U * V) - (U circleOne * V circleOne) • (1 : L2Real →L[ℂ] L2Real)
          ∈ R
        have h : circleMultiplier (U * V) - (U circleOne * V circleOne) •
            (1 : L2Real →L[ℂ] L2Real) =
            (circleMultiplier U - U circleOne • 1) * (circleMultiplier V - V circleOne • 1) +
              U circleOne • (circleMultiplier V - V circleOne • 1) +
              V circleOne • (circleMultiplier U - U circleOne • 1) := by
          rw [circleMultiplier_mul]
          simp only [mul_sub, sub_mul, smul_sub, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
            smul_smul]
          rw [mul_comm (V circleOne) (U circleOne)]
          abel
        rw [h]
        exact R.add_mem (R.add_mem (R.mul_mem hU hV) (R.smul_mem _ hV)) (R.smul_mem _ hU)
      add_mem' := by
        intro U V hU hV
        change circleMultiplier (U + V) - (U circleOne + V circleOne) •
          (1 : L2Real →L[ℂ] L2Real) ∈ R
        rw [circleMultiplier_add, add_smul]
        have h : circleMultiplier U + circleMultiplier V - (U circleOne • (1 : L2Real →L[ℂ] L2Real)
            + V circleOne • 1) = (circleMultiplier U - U circleOne • 1) +
              (circleMultiplier V - V circleOne • 1) := by abel
        rw [h]
        exact R.add_mem hU hV
      algebraMap_mem' c := by
        change circleMultiplier (algebraMap ℂ C(UnitCircle, ℂ) c) -
          (algebraMap ℂ C(UnitCircle, ℂ) c) circleOne • (1 : L2Real →L[ℂ] L2Real) ∈ R
        rw [Algebra.algebraMap_eq_smul_one, circleMultiplier_smul, circleMultiplier_one]
        simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one,
          sub_self]
        exact R.zero_mem
      star_mem' := by
        intro U hU
        change circleMultiplier (star U) - (star (U circleOne)) • (1 : L2Real →L[ℂ] L2Real) ∈ R
        have h : circleMultiplier (star U) - (star (U circleOne)) • (1 : L2Real →L[ℂ] L2Real) =
            star (circleMultiplier U - U circleOne • 1) := by
          rw [circleMultiplier_star, star_sub, star_smul, star_one]
        rw [h]
        exact star_mem hU }
  have hBc : IsClosed (B : Set C(UnitCircle, ℂ)) := by
    have he : Continuous fun U : C(UnitCircle, ℂ) => U circleOne := continuous_eval_const circleOne
    have hc : Continuous fun U : C(UnitCircle, ℂ) =>
        circleMultiplier U - U circleOne • (1 : L2Real →L[ℂ] L2Real) :=
      continuous_circleMultiplier.sub (he.smul continuous_const)
    exact isClosed_range_convRegular.preimage hc
  have hcoord : circleCoord ∈ B := by
    change circleMultiplier circleCoord - circleCoord circleOne • (1 : L2Real →L[ℂ] L2Real) ∈ R
    have h1 : circleCoord circleOne = 1 := rfl
    rw [circleMultiplier_circleCoord, h1, one_smul, cayleyUnitary,
      show (1 : L2Real →L[ℂ] L2Real) - (2 : ℂ) • cayleyVolterra - 1 = (-2 : ℂ) • cayleyVolterra by
        rw [neg_smul]; abel]
    exact R.smul_mem _ cayleyVolterra_mem_range_convRegular
  have hle : StarAlgebra.elemental ℂ circleCoord ≤ B :=
    StarAlgebra.elemental.le_of_mem hBc hcoord
  have htop := ContinuousMap.elemental_id_eq_top (𝕜 := ℂ) UnitCircle
  have hU : U ∈ StarAlgebra.elemental ℂ circleCoord := by
    rw [circleCoord, htop]
    trivial
  exact hle hU

theorem exists_convRegular_of_mem_circleVanishing {V : C(UnitCircle, ℂ)} (hV : V ∈ circleVanishing) :
    ∃ z : RealGroupCStar, convRegular z = circleMultiplier V := by
  obtain ⟨z, hz⟩ := circleMultiplier_sub_mem_range V
  refine ⟨z, ?_⟩
  rw [hz, show V circleOne = 0 from hV, zero_smul, sub_zero]

/-- The circle symbol of an element of `C*(ℝ)`. -/
def groupCStarSymbol (z : RealGroupCStar) : C(UnitCircle, ℂ) :=
  Classical.choose (exists_circle_of_convRegular z)

theorem groupCStarSymbol_mem (z : RealGroupCStar) : groupCStarSymbol z ∈ circleVanishing :=
  (Classical.choose_spec (exists_circle_of_convRegular z)).1

theorem circleMultiplier_groupCStarSymbol (z : RealGroupCStar) :
    circleMultiplier (groupCStarSymbol z) = convRegular z :=
  (Classical.choose_spec (exists_circle_of_convRegular z)).2

theorem groupCStarSymbol_eq {z : RealGroupCStar} {V : C(UnitCircle, ℂ)}
    (h : circleMultiplier V = convRegular z) : groupCStarSymbol z = V :=
  circleMultiplier_injective (by rw [circleMultiplier_groupCStarSymbol, h])

/-- The circle symbol as a `*`-homomorphism `C*(ℝ) → C₀`. -/
def groupCStarSymbolHom : RealGroupCStar →⋆ₙₐ[ℂ] circleVanishing where
  toFun z := ⟨groupCStarSymbol z, groupCStarSymbol_mem z⟩
  map_smul' c z := Subtype.ext (groupCStarSymbol_eq (by
    change circleMultiplier (c • groupCStarSymbol z) = _
    rw [circleMultiplier_smul, circleMultiplier_groupCStarSymbol, map_smul]))
  map_zero' := Subtype.ext (groupCStarSymbol_eq (by
    change circleMultiplier 0 = _
    rw [map_zero]
    exact map_zero circleMultiplierHom))
  map_add' z w := Subtype.ext (groupCStarSymbol_eq (by
    change circleMultiplier (groupCStarSymbol z + groupCStarSymbol w) = _
    rw [circleMultiplier_add, circleMultiplier_groupCStarSymbol, circleMultiplier_groupCStarSymbol,
      map_add]))
  map_mul' z w := Subtype.ext (groupCStarSymbol_eq (by
    change circleMultiplier (groupCStarSymbol z * groupCStarSymbol w) = _
    rw [circleMultiplier_mul, circleMultiplier_groupCStarSymbol, circleMultiplier_groupCStarSymbol,
      map_mul]))
  map_star' z := Subtype.ext (groupCStarSymbol_eq (by
    change circleMultiplier (star (groupCStarSymbol z)) = _
    rw [circleMultiplier_star, circleMultiplier_groupCStarSymbol, map_star]))

theorem groupCStarSymbolHom_bijective : Function.Bijective groupCStarSymbolHom := by
  refine ⟨fun z w h => convRegular_injective ?_, fun V => ?_⟩
  · have h' : groupCStarSymbol z = groupCStarSymbol w := congrArg Subtype.val h
    rw [← circleMultiplier_groupCStarSymbol, ← circleMultiplier_groupCStarSymbol, h']
  · obtain ⟨z, hz⟩ := exists_convRegular_of_mem_circleVanishing V.2
    exact ⟨z, Subtype.ext (groupCStarSymbol_eq hz.symm)⟩

/-- **`C*(ℝ) ≅ C₀(ℝ̂)`**: the full group C⋆-algebra of `ℝ` is the algebra of continuous functions on
the circle (the one-point compactification of the frequency line through the Cayley map) vanishing
at `1 = c(±∞)`; the element `G ∈ C_c(ℝ)` has symbol `𝓕G ∘ c⁻¹`. -/
def realGroupCStarEquiv : RealGroupCStar ≃⋆ₐ[ℂ] circleVanishing :=
  StarAlgEquiv.ofBijective groupCStarSymbolHom groupCStarSymbolHom_bijective

theorem circleMultiplier_realGroupCStarEquiv (z : RealGroupCStar) :
    circleMultiplier (realGroupCStarEquiv z : C(UnitCircle, ℂ)) = convRegular z :=
  circleMultiplier_groupCStarSymbol z

theorem realGroupCStarEquiv_toEnvelope (G : C_c(ℝ, ℂ)) :
    (realGroupCStarEquiv (toEnvelope convKernels convL1Norm (convElem G)) : C(UnitCircle, ℂ)) =
      convCircle G :=
  groupCStarSymbol_eq (op_conv_eq_circleMultiplier G).symm

end GaloisForLFunctions.HTGeometry
