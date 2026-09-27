import GaloisForLFunctions.RHTower.TiltedRiemannKernel

/-!
# Krein pinning up to the Landau height

A positive measure `ν` dominated by the level-`L` Hodge form of `ζ` (`∫ |f̂|² dν ≤ |W(f,f)|` on
the Hodge class, in particular every positive Krein completion) is pinned to the zero ordinates
up to the height `(1 - η) · 2π e^{2L}`, for every `η > 0`:

**Theorem** (`zeta_krein_completion_pinned_below_landau_height`).  For `0 < η ≤ 1/2` there is
`L₀` such that for `L ≥ L₀`, every dominated `ν` satisfies
`ν([τ₀ - δ/2, τ₀ + δ/2]) ≤ exp(-(π/2) η^{3/2} e^{2L})` whenever `5 ≤ τ₀ ≤ (1-η) 2π e^{2L}`,
every zero ordinate is at distance `≥ δ` from `τ₀` (`0 < δ ≤ 1`), and
`12 C log(τ₀+1)/δ ≤ (π/2) η^{3/2} e^{2L}`.

`2π e^{2L}` is the height at which the zero density `(1/2π) log(τ/2π)` reaches the Nyquist rate
`L/π` of tests supported in `[-L, L]`.  The test is the tilted radical test
`(Φ_θ 1_{[-U,U]}) ⋆ (κ_{w,τ₀}'' - κ_{w,τ₀}/4)` with `θ = π/4 - √η/2`, `w = η/8`, `U = L - w`: its
transform is `e^{zθ} Ξ(z)` up to the tail, so on the window it is of size `e^{-(π/4-θ)τ₀}` (sharp
quarter-line Gamma bound), while its Weil energy is the square of a tail of size
`e^{-π sin(2(π/4-θ)) e^{2U}}`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal
open Bottcher Zeta23

namespace RHTower

noncomputable section

/-! ## The bump at radius `w` -/

/-- The bump rescaled to radius `w`: `κ_w(u) = κ(u/(4w))`, supported in `(-w, w)`. -/
def scaledBump (w u : ℝ) : ℂ := weilBumpC (u / (4 * w))

theorem contDiff_scaledBump (w : ℝ) : ContDiff ℝ 4 (scaledBump w) := by
  unfold scaledBump
  exact contDiff_weilBumpC.comp (contDiff_id.div_const _)

theorem scaledBump_eq_zero {w u : ℝ} (hw : 0 < w) (hu : w ≤ |u|) : scaledBump w u = 0 := by
  apply weilBumpC_eq_zero
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * w), le_div_iff₀ (by positivity)]
  linarith

theorem paperFT_scaledBump {w : ℝ} (hw : 0 < w) (z : ℂ) :
    paperFT (scaledBump w) z = ((4 * w : ℝ) : ℂ) * paperFT weilBumpC (((4 * w : ℝ) : ℂ) * z) := by
  have h4 : (4 * w : ℝ) ≠ 0 := by positivity
  have h : ∫ x : ℝ, scaledBump w (4 * w * x) * cexp (I * z * ((4 * w * x : ℝ) : ℂ)) =
      |(4 * w)⁻¹| • ∫ y : ℝ, scaledBump w y * cexp (I * z * y) :=
    Measure.integral_comp_mul_left (fun u : ℝ => scaledBump w u * cexp (I * z * u)) (4 * w)
  have e : (fun x : ℝ => scaledBump w (4 * w * x) * cexp (I * z * ((4 * w * x : ℝ) : ℂ))) =
      fun x : ℝ => weilBumpC x * cexp (I * (((4 * w : ℝ) : ℂ) * z) * x) := by
    funext x
    rw [scaledBump, mul_div_cancel_left₀ x h4]
    congr 2; push_cast; ring
  rw [e] at h
  unfold paperFT
  rw [h, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 4 * w), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ h4, Complex.ofReal_one, one_mul]

/-- In the strip `|Im z| ≤ 1/2`, for `4w ≤ 1`: `|κ̂_w(z)| ≤ C_κ / ((4w)³ (1 + |Re z|)⁴)`. -/
theorem norm_paperFT_scaledBump_le {w : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (scaledBump w) z‖ ≤ bumpDecayConst / ((4 * w) ^ 3 * (1 + |z.re|) ^ 4) := by
  rw [paperFT_scaledBump hw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 4 * w)]
  have hz' : |((((4 * w : ℝ) : ℂ)) * z).im| ≤ 1 / 2 := by
    rw [show ((((4 * w : ℝ) : ℂ)) * z).im = 4 * w * z.im by simp]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * w)]
    nlinarith [abs_nonneg z.im]
  have h := norm_paperFT_weilBumpC_le hz'
  rw [show ((((4 * w : ℝ) : ℂ)) * z).re = 4 * w * z.re by simp] at h
  have hC := bumpDecayConst_nonneg
  have hre : 4 * w * (1 + |z.re|) ≤ 1 + |4 * w * z.re| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * w)]; nlinarith [abs_nonneg z.re]
  have hpow : (4 * w) ^ 4 * (1 + |z.re|) ^ 4 ≤ (1 + |4 * w * z.re|) ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hre 4
  calc 4 * w * ‖paperFT weilBumpC (((4 * w : ℝ) : ℂ) * z)‖
      ≤ 4 * w * (bumpDecayConst / (1 + |4 * w * z.re|) ^ 4) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 4 * w * (bumpDecayConst / ((4 * w) ^ 4 * (1 + |z.re|) ^ 4)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC (by positivity) hpow)
          (by positivity)
    _ = bumpDecayConst / ((4 * w) ^ 3 * (1 + |z.re|) ^ 4) := by
        field_simp

/-- For real `|s| ≤ 1/2` and `4w ≤ 1`: `|κ̂_w(s)| ≥ 4w cos(1/8) ∫ κ`. -/
theorem norm_paperFT_scaledBump_real_ge {w : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) {s : ℝ}
    (hs : |s| ≤ 1 / 2) :
    4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)) ≤ ‖paperFT (scaledBump w) (s : ℂ)‖ := by
  rw [paperFT_scaledBump hw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 4 * w)]
  have hs' : |4 * w * s| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * w)]; nlinarith [abs_nonneg s]
  have h := norm_paperFT_weilBumpC_real_ge hs'
  rw [show (((4 * w : ℝ) : ℂ) * (s : ℂ)) = ((4 * w * s : ℝ) : ℂ) by push_cast; ring]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ## The modulated polar-free bump at radius `w` -/

/-- `κ_{w,ω}(u) = e^{-iωu} κ_w(u)`. -/
def modScaledBump (w ω u : ℝ) : ℂ := cexp (-(I * ω * u)) * scaledBump w u

theorem contDiff_modScaledBump (w ω : ℝ) : ContDiff ℝ 4 (modScaledBump w ω) := by
  unfold modScaledBump
  refine ContDiff.mul ?_ (contDiff_scaledBump w)
  have : ContDiff ℝ 4 (fun u : ℝ => -(I * (ω : ℂ) * (u : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
  exact Complex.contDiff_exp.comp this

theorem modScaledBump_eq_zero {w ω u : ℝ} (hw : 0 < w) (hu : w ≤ |u|) :
    modScaledBump w ω u = 0 := by
  simp [modScaledBump, scaledBump_eq_zero hw hu]

theorem hasCompactSupport_modScaledBump {w : ℝ} (hw : 0 < w) (ω : ℝ) :
    HasCompactSupport (modScaledBump w ω) :=
  hasCompactSupport_of_support_subset_abs (Λ := w) fun u hu => by
    by_contra h; push Not at h; exact hu (modScaledBump_eq_zero hw h.le)

/-- `κ₂ = κ_{w,ω}'' - κ_{w,ω}/4`: transform `-(z² + 1/4) κ̂_w(z - ω)`, vanishing at `±i/2`. -/
def scaledBumpPolarFree (w ω u : ℝ) : ℂ :=
  deriv (deriv (modScaledBump w ω)) u - modScaledBump w ω u / 4

theorem contDiff_deriv_deriv_modScaledBump (w ω : ℝ) :
    ContDiff ℝ 2 (deriv (deriv (modScaledBump w ω))) := by
  have h3 : ContDiff ℝ 3 (deriv (modScaledBump w ω)) := (contDiff_modScaledBump w ω).deriv'
  exact h3.deriv'

theorem contDiff_scaledBumpPolarFree (w ω : ℝ) : ContDiff ℝ 2 (scaledBumpPolarFree w ω) :=
  (contDiff_deriv_deriv_modScaledBump w ω).sub
    (((contDiff_modScaledBump w ω).of_le (by norm_num)).div_const 4)

theorem tsupport_modScaledBump_subset {w : ℝ} (hw : 0 < w) (ω : ℝ) :
    tsupport (modScaledBump w ω) ⊆ Metric.closedBall 0 w := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro v hv
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h; push Not at h; exact hv (modScaledBump_eq_zero hw h.le)

theorem scaledBumpPolarFree_eq_zero {w ω u : ℝ} (hw : 0 < w) (hu : w < |u|) :
    scaledBumpPolarFree w ω u = 0 := by
  have hnot : u ∉ tsupport (modScaledBump w ω) := fun h => by
    have := tsupport_modScaledBump_subset hw ω h
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this; linarith
  have hd1 : tsupport (deriv (modScaledBump w ω)) ⊆ tsupport (modScaledBump w ω) :=
    closure_minimal (support_deriv_subset) (isClosed_tsupport _)
  have hd2 : deriv (deriv (modScaledBump w ω)) u = 0 := by
    apply Function.notMem_support.mp
    exact fun h => hnot (hd1 (support_deriv_subset h))
  simp [scaledBumpPolarFree, hd2, modScaledBump_eq_zero hw hu.le]

theorem hasCompactSupport_scaledBumpPolarFree {w : ℝ} (hw : 0 < w) (ω : ℝ) :
    HasCompactSupport (scaledBumpPolarFree w ω) :=
  hasCompactSupport_of_support_subset_abs (Λ := 2 * w) fun u hu => by
    by_contra h; push Not at h; exact hu (scaledBumpPolarFree_eq_zero hw (by linarith))

theorem paperFT_modScaledBump (w ω : ℝ) (z : ℂ) :
    paperFT (modScaledBump w ω) z = paperFT (scaledBump w) (z - ω) :=
  paperFT_modulate (scaledBump w) ω z

theorem paperFT_scaledBumpPolarFree {w : ℝ} (hw : 0 < w) (ω : ℝ) (z : ℂ) :
    paperFT (scaledBumpPolarFree w ω) z = -(z ^ 2 + 1 / 4) * paperFT (scaledBump w) (z - ω) := by
  have hc2 : ContDiff ℝ 2 (modScaledBump w ω) := (contDiff_modScaledBump w ω).of_le (by norm_num)
  have hdd := paperFT_deriv_deriv hc2 (hasCompactSupport_modScaledBump hw ω) z
  have hi1 : Integrable
      (fun u : ℝ => deriv (deriv (modScaledBump w ω)) u * Complex.exp (I * z * u)) :=
    ((contDiff_deriv_deriv_modScaledBump w ω).continuous.mul
      (by fun_prop)).integrable_of_hasCompactSupport
      ((hasCompactSupport_modScaledBump hw ω).deriv.deriv.mul_right)
  have hi2 : Integrable (fun u : ℝ => modScaledBump w ω u / 4 * Complex.exp (I * z * u)) := by
    refine ((hc2.continuous.div_const 4).mul (by fun_prop)).integrable_of_hasCompactSupport ?_
    refine hasCompactSupport_of_support_subset_abs (Λ := w) fun u hu => ?_
    by_contra h; push Not at h; exact hu (by simp [modScaledBump_eq_zero hw h.le])
  have hdd' : paperFT (deriv (deriv (modScaledBump w ω))) z =
      -(z ^ 2) * paperFT (modScaledBump w ω) z := by
    rw [hdd]
  unfold paperFT at hdd' ⊢
  simp only [scaledBumpPolarFree, sub_mul]
  rw [integral_sub hi1 hi2, hdd']
  have : ∫ u : ℝ, modScaledBump w ω u / 4 * Complex.exp (I * z * u) =
      (∫ u : ℝ, modScaledBump w ω u * Complex.exp (I * z * u)) / 4 := by
    rw [← integral_div]; congr 1; funext u; ring
  rw [this]
  have hm := paperFT_modScaledBump w ω z
  unfold paperFT at hm
  rw [hm]; ring

/-- `B_w = C_κ / (4w)³`. -/
def scaledBumpConst (w : ℝ) : ℝ := bumpDecayConst / (4 * w) ^ 3

theorem scaledBumpConst_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ scaledBumpConst w := by
  unfold scaledBumpConst
  have := bumpDecayConst_nonneg
  positivity

/-- At a point of the strip with real part `γ`: `|κ̂₂(x)| ≤ B_w (1+|ω|)² / (1+|γ-ω|)²`. -/
theorem norm_paperFT_scaledBumpPolarFree_le {w : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) (ω : ℝ)
    {x : ℂ} (hx : |x.im| ≤ 1 / 2) :
    ‖paperFT (scaledBumpPolarFree w ω) x‖ ≤
      scaledBumpConst w * (1 + |ω|) ^ 2 / (1 + |x.re - ω|) ^ 2 := by
  rw [paperFT_scaledBumpPolarFree hw, norm_mul, norm_neg]
  have hw' : |(x - ω).im| ≤ 1 / 2 := by simpa using hx
  have hk0 := norm_paperFT_scaledBump_le hw hw4 hw'
  have hre : (x - (ω : ℂ)).re = x.re - ω := by simp
  rw [hre] at hk0
  have hk : ‖paperFT (scaledBump w) (x - ω)‖ ≤ scaledBumpConst w / (1 + |x.re - ω|) ^ 4 := by
    refine hk0.trans (le_of_eq ?_); unfold scaledBumpConst; field_simp
  have hC := scaledBumpConst_nonneg hw
  have hq : ‖x ^ 2 + 1 / 4‖ ≤ (1 + |x.re|) ^ 2 := by
    have h1 : ‖x ^ 2 + 1 / 4‖ ≤ ‖x‖ ^ 2 + 1 / 4 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow]; norm_num
    have h2 : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have h3 : x.im ^ 2 ≤ 1 / 4 := by
      have := abs_le.mp hx; nlinarith
    have h4 : x.re ^ 2 = |x.re| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg x.re]
  have hmul := one_add_abs_le_mul x.re ω
  have hd : 0 < (1 + |x.re - ω|) := by positivity
  have hsq : (1 + |x.re|) ^ 2 ≤ (1 + |ω|) ^ 2 * (1 + |x.re - ω|) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hmul 2
  calc ‖x ^ 2 + 1 / 4‖ * ‖paperFT (scaledBump w) (x - ω)‖
      ≤ ((1 + |ω|) ^ 2 * (1 + |x.re - ω|) ^ 2) * (scaledBumpConst w / (1 + |x.re - ω|) ^ 4) :=
        mul_le_mul (hq.trans hsq) hk (norm_nonneg _) (by positivity)
    _ = scaledBumpConst w * (1 + |ω|) ^ 2 / (1 + |x.re - ω|) ^ 2 := by
        field_simp

/-! ## The tilted radical test -/

/-- `T = Φ_{θ,≤U} ⋆ κ₂`: `C²`, supported in `[-(U+w), U+w]`, polar-free, with transform
`Φ̂_{θ,≤U}(z) · (-(z² + 1/4)) κ̂_w(z - ω)`. -/
def landauRadicalTest (U θ w ω : ℝ) : ℝ → ℂ :=
  convolution (tiltedCore U θ) (scaledBumpPolarFree w ω) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem integrable_scaledBumpPolarFree_mul_exp {w : ℝ} (hw : 0 < w) (ω : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => scaledBumpPolarFree w ω x * Complex.exp (I * z * x)) :=
  ((contDiff_scaledBumpPolarFree w ω).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
    (hasCompactSupport_scaledBumpPolarFree hw ω).mul_right

theorem paperFT_landauRadicalTest {U θ w : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (hw : 0 < w)
    (ω : ℝ) (z : ℂ) :
    paperFT (landauRadicalTest U θ w ω) z =
      paperFT (tiltedCore U θ) z * paperFT (scaledBumpPolarFree w ω) z :=
  paperFT_convolution (integrable_tiltedCore_mul_cexp hθ0 hθ z)
    (integrable_scaledBumpPolarFree_mul_exp hw ω z)

theorem contDiff_landauRadicalTest {U θ w : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (hw : 0 < w)
    (ω : ℝ) : ContDiff ℝ 2 (landauRadicalTest U θ w ω) :=
  (hasCompactSupport_scaledBumpPolarFree hw ω).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) (n := 2) (integrable_tiltedCore hθ0 hθ).locallyIntegrable
    (contDiff_scaledBumpPolarFree w ω)

theorem landauRadicalTest_eq_zero {U θ w x : ℝ} (hw : 0 < w) (ω : ℝ) (hx : U + w < |x|) :
    landauRadicalTest U θ w ω x = 0 := by
  unfold landauRadicalTest
  rw [convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (tiltedCore U θ t)
      (scaledBumpPolarFree w ω (x - t)) = 0 := by
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    by_cases ht : U < |t|
    · have : tiltedCore U θ t = 0 := by
        unfold tiltedCore
        refine indicator_of_notMem (fun hm => ?_) _
        have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
      rw [this, zero_mul]
    · push Not at ht
      have hxt : w < |x - t| := by
        have := abs_sub_abs_le_abs_sub x t; linarith
      rw [scaledBumpPolarFree_eq_zero hw hxt, mul_zero]
  simp [this]

theorem tsupport_landauRadicalTest {U θ w L : ℝ} (hw : 0 < w) (ω : ℝ) (hL : U + w ≤ L) :
    tsupport (landauRadicalTest U θ w ω) ⊆ Icc (-L) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ U + w < |x| := fun h => hx (landauRadicalTest_eq_zero hw ω h)
  push Not at h
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

theorem paperFT_landauRadicalTest_half_I {U θ w : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2)
    (hw : 0 < w) (ω : ℝ) : paperFT (landauRadicalTest U θ w ω) (I / 2) = 0 := by
  rw [paperFT_landauRadicalTest hθ0 hθ hw, paperFT_scaledBumpPolarFree hw]
  have : (I / 2) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

theorem paperFT_landauRadicalTest_neg_half_I {U θ w : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2)
    (hw : 0 < w) (ω : ℝ) : paperFT (landauRadicalTest U θ w ω) (-(I / 2)) = 0 := by
  rw [paperFT_landauRadicalTest hθ0 hθ hw, paperFT_scaledBumpPolarFree hw]
  have : (-(I / 2)) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

/-! ## The Weil energy of the tilted radical test -/

/-- **Weil energy of the tilted radical test.**  Both evaluation points of every zero see only the
tail of `Φ_θ`, so `‖W(T,T)‖ ≤ ε² B_w² (1+|ω|)⁴ · 24 A₀ log(|ω|+3)`,
`ε = ∫ |Φ_{θ,>U}| e^{|u|/2}`. -/
theorem norm_W_landauRadicalTest_le {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {U θ w : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (hw : 0 < w) (hw4 : 4 * w ≤ 1) (ω : ℝ) :
    ‖zetaZeroConfig.W (landauRadicalTest U θ w ω) (landauRadicalTest U θ w ω)‖ ≤
      (∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|)) ^ 2 * scaledBumpConst w ^ 2 *
        (1 + |ω|) ^ 4 * (24 * A₀ * Real.log (|ω| + 3)) := by
  set ε := ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|) with hε
  have hε0 : 0 ≤ ε := integral_nonneg fun _ => by positivity
  have hC := scaledBumpConst_nonneg hw
  obtain ⟨hsumm, hsumle⟩ := window_tsum_le zetaZeroConfig hA₀ hloc ω
  set K := ε ^ 2 * scaledBumpConst w ^ 2 * (1 + |ω|) ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (landauRadicalTest U θ w ω) (landauRadicalTest U θ w ω) ρ‖ ≤
        K * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3) := by
    intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    obtain ⟨hc1, hc2⟩ := paperFT_tiltedCore_at_zero (U := U) hθ0 hθ hmem
    have hre1 : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
    have hre2 : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
      rw [Complex.conj_re, WeilEF.gammaOf_re]
    have hv : ∀ x : ℂ, |x.im| ≤ 1 / 2 → x.re = (ρ : ℂ).im →
        paperFT (tiltedCore U θ) x = -paperFT (tiltedTail U θ) x →
        ‖paperFT (landauRadicalTest U θ w ω) x‖ ≤
          ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / (1 + |(ρ : ℂ).im - ω|) ^ 2) := by
      intro x hx hxre hcore
      rw [paperFT_landauRadicalTest hθ0 hθ hw, hcore, norm_mul, norm_neg]
      have h1 := norm_paperFT_tiltedTail_le (U := U) hθ0 hθ hx
      have h2 := norm_paperFT_scaledBumpPolarFree_le hw hw4 ω hx
      rw [hxre] at h2
      exact mul_le_mul h1 h2 (norm_nonneg _) hε0
    have hv1 := hv _ hIm hre1 hc1
    have hv2 := hv _ hIm' hre2 hc2
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    set D := 1 + |(ρ : ℂ).im - ω| with hD
    have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg ((ρ : ℂ).im - ω)]
    have hq : ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) *
        (ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2)) ≤ K * (1 / D ^ 3) := by
      rw [hK]
      have hD4 : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
      have e : ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) *
          (ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2)) =
          ε ^ 2 * scaledBumpConst w ^ 2 * (1 + |ω|) ^ 4 * (1 / D ^ 4) := by
        field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hK0
      exact one_div_le_one_div_of_le (by positivity) hD4
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (landauRadicalTest U θ w ω) (gammaOf ρ)‖ *
          ‖paperFT (landauRadicalTest U θ w ω) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2)) *
            (ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2)) := by gcongr
      _ = (zetaZeroConfig.mult ρ : ℝ) * (ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) *
            (ε * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2))) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (K * (1 / D ^ 3)) := mul_le_mul_of_nonneg_left hq hm
      _ = K * ((zetaZeroConfig.mult ρ : ℝ) / D ^ 3) := by ring
  have hsum' : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (landauRadicalTest U θ w ω) (landauRadicalTest U θ w ω) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsumm.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsumm.mul_left _)).trans ?_
  rw [tsum_mul_left]
  calc K * ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3
      ≤ K * (24 * A₀ * Real.log (|ω| + 3)) := mul_le_mul_of_nonneg_left hsumle hK0
    _ = _ := by rw [hK]

/-! ## The tilted radical test on the real line -/

/-- For real `τ` with `|τ - ω| ≤ 1/2`:
`|T̂(τ)| ≥ (e^{τθ}|Ξ(τ)| - ε)(τ² + 1/4) · 4w cos(1/8) ∫κ`. -/
theorem norm_paperFT_landauRadicalTest_real_ge {U θ w : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2)
    (hw : 0 < w) (hw4 : 4 * w ≤ 1) (ω : ℝ) {τ : ℝ} (hτ : |τ - ω| ≤ 1 / 2) :
    (Real.exp (τ * θ) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ -
        ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|)) *
      ((τ ^ 2 + 1 / 4) * (4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)))) ≤
      ‖paperFT (landauRadicalTest U θ w ω) (τ : ℂ)‖ := by
  set ε := ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|)
  have hz : |(τ : ℂ).im| ≤ 1 / 2 := by simp
  rw [paperFT_landauRadicalTest hθ0 hθ hw, norm_mul, paperFT_tiltedCore_eq hθ0 hθ hz,
    paperFT_scaledBumpPolarFree hw, norm_mul, norm_neg]
  have htail : ‖paperFT (tiltedTail U θ) (τ : ℂ)‖ ≤ ε := norm_paperFT_tiltedTail_le hθ0 hθ hz
  have hexp : ‖cexp ((τ : ℂ) * θ) * riemannPhiTransform (1 / 2 + I * τ)‖ =
      Real.exp (τ * θ) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ := by
    rw [norm_mul, show ((τ : ℂ) * (θ : ℂ)) = ((τ * θ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal]
  have hcore : Real.exp (τ * θ) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ - ε ≤
      ‖cexp ((τ : ℂ) * θ) * riemannPhiTransform (1 / 2 + I * τ) -
        paperFT (tiltedTail U θ) (τ : ℂ)‖ := by
    have := norm_sub_norm_le (cexp ((τ : ℂ) * θ) * riemannPhiTransform (1 / 2 + I * τ))
      (paperFT (tiltedTail U θ) (τ : ℂ))
    rw [hexp] at this
    linarith
  have hq : ‖(τ : ℂ) ^ 2 + 1 / 4‖ = τ ^ 2 + 1 / 4 := by
    rw [show (τ : ℂ) ^ 2 + 1 / 4 = ((τ ^ 2 + 1 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hk := norm_paperFT_scaledBump_real_ge hw hw4 (s := τ - ω) hτ
  rw [show ((τ : ℂ) - (ω : ℂ)) = ((τ - ω : ℝ) : ℂ) by push_cast; ring, hq]
  have hI0 : 0 ≤ ∫ u, weilBump u := integral_nonneg fun u => weilBump.nonneg
  have hc0 : 0 ≤ Real.cos (1 / 8) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  rcases le_or_gt (Real.exp (τ * θ) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ - ε) 0 with hneg | hpos
  · have : (Real.exp (τ * θ) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ - ε) *
        ((τ ^ 2 + 1 / 4) * (4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
    exact this.trans (by positivity)
  · exact mul_le_mul hcore (mul_le_mul_of_nonneg_left hk (by positivity)) (by positivity)
      (norm_nonneg _)

/-! ## The sharp quarter-line Gamma bound -/

/-- The arithmetic closing the quarter-line bound: `π e^{-πs/2} ≤ A² e (1 + s/2)` forces
`A ≥ e^{-πs/4}/(1+s)`. -/
theorem quarter_gamma_lower_of_ratio {A s y : ℝ} (hs : 4 ≤ s) (hy : y = s / 2) (hA0 : 0 < A)
    (hA2 : π * Real.exp (-(π * s / 2)) ≤ A ^ 2 * (Real.exp 1 * (1 + y))) :
    Real.exp (-(π * s / 4)) / (1 + s) ≤ A := by
  subst hy
  set q := Real.exp (-(π * s / 4)) / (1 + s) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hexpsq : Real.exp (-(π * s / 4)) ^ 2 = Real.exp (-(π * s / 2)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hq2 : q ^ 2 = Real.exp (-(π * s / 2)) / (1 + s) ^ 2 := by
    rw [hq, div_pow, hexpsq]
  have h3 : Real.exp 1 * (1 + s / 2) ≤ π * (1 + s) ^ 2 := by
    have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have hs1 : 1 + s / 2 ≤ 1 + s := by linarith
    have hs2 : 1 + s ≤ (1 + s) ^ 2 := by nlinarith
    have h4 : Real.exp 1 * (1 + s / 2) ≤ 3 * (1 + s / 2) :=
      mul_le_mul_of_nonneg_right he.le (by linarith)
    have h5 : 3 * (1 + s) ^ 2 ≤ π * (1 + s) ^ 2 :=
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity)
    linarith
  have hqsq : q ^ 2 * (Real.exp 1 * (1 + s / 2)) ≤ π * Real.exp (-(π * s / 2)) := by
    rw [hq2]
    have hs0 : (0 : ℝ) < (1 + s) ^ 2 := by positivity
    calc Real.exp (-(π * s / 2)) / (1 + s) ^ 2 * (Real.exp 1 * (1 + s / 2))
        ≤ Real.exp (-(π * s / 2)) / (1 + s) ^ 2 * (π * (1 + s) ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = π * Real.exp (-(π * s / 2)) := by field_simp
  have hpos : 0 < Real.exp 1 * (1 + s / 2) := by
    have : (0 : ℝ) < 1 + s / 2 := by linarith
    positivity
  have hfinal : q ^ 2 ≤ A ^ 2 := le_of_mul_le_mul_right (hqsq.trans hA2) hpos
  exact (pow_le_pow_iff_left₀ hq0 hA0.le two_ne_zero).mp hfinal

/-- **Sharp quarter-line Gamma bound.**  For `s ≥ 4`: `|Γ(1/4 + is/2)| ≥ e^{-πs/4}/(1+s)`.
Duplication gives `|Γ(1/4+iy)Γ(3/4+iy)| = √(2π)|Γ(1/2+2iy)| ≥ √2 π e^{-2π|y|/2 ·...}`, and the
digamma bound on the segment `[1/4, 3/4] + iy` gives `|Γ(3/4+iy)| ≤ e(1+y)|Γ(1/4+iy)|`. -/
theorem norm_Gamma_quarter_line_sharp {s : ℝ} (hs : 4 ≤ s) :
    Real.exp (-(π * s / 4)) / (1 + s) ≤
      ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I)‖ := by
  set y : ℝ := s / 2 with hy
  have hy2 : 2 ≤ y := by rw [hy]; linarith
  have hy0 : 0 < y := by linarith
  set A : ℝ := ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ with hAdef
  set B : ℝ := ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (s : ℂ) * I)‖ with hBdef
  set D : ℝ := ‖Complex.Gamma (((3 / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ with hDdef
  -- duplication
  have hdup := Complex.Gamma_mul_Gamma_add_half (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)
  have hdupNorm := congrArg norm hdup
  simp only [norm_mul] at hdupNorm
  have hpow : ‖(2 : ℂ) ^ (1 - 2 * (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I))‖ = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    simp; norm_num
  rw [hpow] at hdupNorm
  have hzplus : (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I) + 1 / 2 = ((3 / 4 : ℝ) : ℂ) + (y : ℂ) * I := by
    push_cast; ring
  have h2z : 2 * (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I) = ((1 / 2 : ℝ) : ℂ) + (s : ℂ) * I := by
    rw [hy]; push_cast; ring
  rw [hzplus, h2z] at hdupNorm
  have hdupAD : A * D = B * (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt π := by
    simpa only [hAdef, hBdef, hDdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hdupNorm
  have hB : Real.sqrt π * Real.exp (-(π * |s| / 2)) ≤ B := by
    rw [hBdef]
    convert (GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_bounds s).1 using 1
    norm_num
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s)] at hB
  -- the digamma ratio bound
  have hne : ∀ x : ℝ, Complex.Gamma ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro x
    apply Complex.Gamma_ne_zero
    intro m h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hA0 : 0 < A := norm_pos_iff.mpr (hne _)
  have hD0 : 0 < D := norm_pos_iff.mpr (hne _)
  have hcont : IntervalIntegrable (fun x : ℝ => (Complex.digamma ((x : ℂ) + (y : ℂ) * I)).re)
      volume (1 / 4) (3 / 4) := by
    apply ContinuousOn.intervalIntegrable
    have hφ : ContinuousOn (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (uIcc (1 / 4) (3 / 4)) := by
      fun_prop
    have hmaps : MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (uIcc (1 / 4) (3 / 4))
        {z : ℂ | 0 < z.im} := by
      intro x _
      simp only [mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
      exact hy0
    exact Complex.continuous_re.comp_continuousOn (digamma_continuousOn_uhp.comp hφ hmaps)
  set Q : ℝ := 1 / 2 * Real.log (1 + y ^ 2) + (1 / y ^ 2 + π / (2 * y)) with hQ
  have hupper : ∫ x in (1 / 4 : ℝ)..(3 / 4), (Complex.digamma ((x : ℂ) + (y : ℂ) * I)).re ≤
      ∫ _x in (1 / 4 : ℝ)..(3 / 4), Q := by
    apply intervalIntegral.integral_mono_on (by norm_num) hcont intervalIntegrable_const
    intro x hx
    have hb := re_digamma_vertical_bound_uncond (σ := x) (t := y) (by linarith [hx.1]) hy0
    have hlog : Real.log (x ^ 2 + y ^ 2) ≤ Real.log (1 + y ^ 2) :=
      Real.log_le_log (by nlinarith [hx.1]) (by nlinarith [hx.1, hx.2])
    have := (abs_le.mp hb).2
    rw [hQ]
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul, ftc_log_norm_Gamma hy0] at hupper
  have hQle : (3 / 4 - 1 / 4 : ℝ) * Q ≤ 1 / 4 * Real.log (1 + y ^ 2) + 1 := by
    have h1 : 1 / y ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : π / (2 * y) ≤ π / 4 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
    rw [hQ]
    nlinarith [Real.pi_lt_four]
  have hratio : Real.log D - Real.log A ≤ 1 / 4 * Real.log (1 + y ^ 2) + 1 := by
    rw [hDdef, hAdef]; linarith
  have hroot : Real.exp (1 / 4 * Real.log (1 + y ^ 2)) ≤ 1 + y := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < 1 + y)]
    apply Real.exp_le_exp.mpr
    have h4 : Real.log (1 + y ^ 2) ≤ Real.log ((1 + y) ^ 4) :=
      Real.log_le_log (by positivity) (by nlinarith [sq_nonneg y])
    rw [Real.log_pow] at h4
    push_cast at h4
    linarith
  have hDle : D ≤ A * (Real.exp 1 * (1 + y)) := by
    have hexp := Real.exp_le_exp.mpr hratio
    rw [Real.exp_sub, Real.exp_log hD0, Real.exp_log hA0, Real.exp_add] at hexp
    rw [div_le_iff₀ hA0] at hexp
    calc D ≤ Real.exp (1 / 4 * Real.log (1 + y ^ 2)) * Real.exp 1 * A := hexp
      _ ≤ (1 + y) * Real.exp 1 * A := by gcongr
      _ = A * (Real.exp 1 * (1 + y)) := by ring
  -- combine
  have h2half : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hsq : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hAD : π * Real.exp (-(π * s / 2)) ≤ A * D := by
    rw [hdupAD]
    calc π * Real.exp (-(π * s / 2)) = (Real.sqrt π * Real.sqrt π) * Real.exp (-(π * s / 2)) := by
          rw [hsq]
      _ = Real.sqrt π * Real.exp (-(π * s / 2)) * 1 * Real.sqrt π := by ring
      _ ≤ B * (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt π := by gcongr
  have hA2 : π * Real.exp (-(π * s / 2)) ≤ A ^ 2 * (Real.exp 1 * (1 + y)) := by
    calc π * Real.exp (-(π * s / 2)) ≤ A * D := hAD
      _ ≤ A * (A * (Real.exp 1 * (1 + y))) := mul_le_mul_of_nonneg_left hDle hA0.le
      _ = A ^ 2 * (Real.exp 1 * (1 + y)) := by ring
  exact quarter_gamma_lower_of_ratio hs hy hA0 hA2

/-! ## The tilted `Ξ` on the critical line away from the zeros -/

/-- `c_L = π^{-1/4}/6`. -/
def tiltedXiLineConst : ℝ := Real.pi ^ (-(1 / 4 : ℝ)) / 6

theorem tiltedXiLineConst_pos : 0 < tiltedXiLineConst := by
  unfold tiltedXiLineConst
  have := Real.rpow_pos_of_pos Real.pi_pos (-(1 / 4 : ℝ))
  positivity

/-- **Lower bound for the tilted `Ξ` on the critical line.**  If every zero ordinate is at
distance `≥ δ` from `τ ≥ 4`, then
`e^{τθ} |Ξ(τ)| ≥ c_L (τ²/(1+τ)) e^{(θ - π/4)τ} exp(-(3/2) C log τ / δ)`. -/
theorem tilted_xi_line_ge {θ τ δ : ℝ} (hτ : 4 ≤ τ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfar : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - τ|) :
    tiltedXiLineConst * (τ ^ 2 / (1 + τ)) * Real.exp ((θ - π / 4) * τ) *
        Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ)) ≤
      Real.exp (τ * θ) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ := by
  set s : ℂ := 1 / 2 + I * τ with hs
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsre0 : 0 < s.re := by rw [hsre]; norm_num
  rw [riemannPhiTransform_eq_xi, xi_eq_xiUnit_mul_zeta hs0 hs1 hsre0, norm_mul]
  -- the zeta factor
  have hζ : (1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ)) ≤
      ‖riemannZeta s‖ := by
    have hfar' : ∀ x ∈ Icc (1 / 2 : ℝ) 2, ∀ ρ ∈ zetaZeroConfig.carrier,
        δ ≤ ‖((x : ℂ) + τ * I) - ρ‖ := by
      intro x _ ρ hρ
      refine (hfar ρ hρ).trans ?_
      have : |ρ.im - τ| = |(((x : ℂ) + τ * I) - ρ).im| := by
        simp; rw [abs_sub_comm]
      rw [this]; exact Complex.abs_im_le_norm _
    have h := log_norm_zeta_ge_horizontal (σ := 1 / 2) (by norm_num) (by norm_num) hτ hδ hδ1 hfar'
    have hsEq : ((1 / 2 : ℝ) : ℂ) + τ * I = s := by rw [hs]; push_cast; ring
    rw [hsEq] at h
    have hpos : 0 < ‖riemannZeta s‖ := by
      rcases eq_or_ne (riemannZeta s) 0 with h0 | h0
      · exfalso
        have hmem : s ∈ zetaZeroConfig.carrier := ⟨h0, hsre0, by rw [hsre]; norm_num⟩
        have := hfar s hmem
        simp [hs] at this; linarith
      · exact norm_pos_iff.mpr h0
    have := Real.exp_le_exp.mpr h
    rw [Real.exp_log hpos, Real.exp_sub, Real.exp_log (by norm_num)] at this
    have e : Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ)) =
        (Real.exp (logDerivZetaConstant * Real.log τ / δ * (2 - 1 / 2)))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    calc (1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ))
        = (1 / 3) / Real.exp (logDerivZetaConstant * Real.log τ / δ * (2 - 1 / 2)) := by
          rw [e, div_eq_mul_inv (1 / 3 : ℝ)]
      _ ≤ ‖riemannZeta s‖ := this
  -- the archimedean factor, with the sharp Gamma bound
  have hU : 3 * tiltedXiLineConst * (τ ^ 2 / (1 + τ)) * Real.exp (-(π * τ / 4)) ≤
      ‖xiUnit s‖ := by
    unfold xiUnit
    have hss : s * (s - 1) = -((τ ^ 2 + 1 / 4 : ℝ) : ℂ) := by
      rw [hs]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [hss, norm_mul, norm_div, Complex.Gammaℝ_def, norm_mul]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-(1 / 4 : ℝ)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      congr 1; simp [hs]; norm_num
    rw [hpi]
    have hΓ := norm_Gamma_quarter_line_sharp hτ
    have hs2 : s / 2 = ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [hs2]
    have hpq : 0 < Real.pi ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos Real.pi_pos _
    unfold tiltedXiLineConst
    calc 3 * (Real.pi ^ (-(1 / 4 : ℝ)) / 6) * (τ ^ 2 / (1 + τ)) * Real.exp (-(π * τ / 4))
        = (τ ^ 2 / 2) * (Real.pi ^ (-(1 / 4 : ℝ)) * (Real.exp (-(π * τ / 4)) / (1 + τ))) := by
          ring
      _ ≤ ((τ ^ 2 + 1 / 4) / 2) * (Real.pi ^ (-(1 / 4 : ℝ)) *
            ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) := by
          apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hΓ hpq.le) (by positivity)
            (by positivity)
      _ = _ := by ring
  have hz0 : 0 ≤ (1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ)) := by
    positivity
  have hprod := mul_le_mul hU hζ hz0 (norm_nonneg _)
  have hθexp : Real.exp (τ * θ) * Real.exp (-(π * τ / 4)) = Real.exp ((θ - π / 4) * τ) := by
    rw [← Real.exp_add]; congr 1; ring
  calc tiltedXiLineConst * (τ ^ 2 / (1 + τ)) * Real.exp ((θ - π / 4) * τ) *
        Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ))
      = Real.exp (τ * θ) * ((3 * tiltedXiLineConst * (τ ^ 2 / (1 + τ)) *
          Real.exp (-(π * τ / 4))) *
          ((1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ)))) := by
        rw [← hθexp]; ring
    _ ≤ Real.exp (τ * θ) * (‖xiUnit s‖ * ‖riemannZeta s‖) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le

end

end RHTower
