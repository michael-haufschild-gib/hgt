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
With `y = s/2`, duplication gives `|Γ(1/4+iy)Γ(3/4+iy)| = √(2π)|Γ(1/2+is)| ≥ π e^{-πs/2}`, and the
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

/-! ## The window floor and the Christoffel bound -/

/-- The lower envelope of `e^{τ(π/4-ε)}|Ξ(τ)|` on `[τ₀ - δ/2, τ₀ + δ/2]`. -/
def tiltedWindowFloor (ε τ₀ δ : ℝ) : ℝ :=
  tiltedXiLineConst * ((τ₀ - 1 / 2) ^ 2 / (τ₀ + 3 / 2)) * Real.exp (-(ε * (τ₀ + 1 / 2))) *
    Real.exp (-(3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ))

theorem tiltedWindowFloor_pos {ε τ₀ δ : ℝ} (hτ₀ : 5 ≤ τ₀) : 0 < tiltedWindowFloor ε τ₀ δ := by
  unfold tiltedWindowFloor
  have := tiltedXiLineConst_pos
  have : 0 < τ₀ - 1 / 2 := by linarith
  have : 0 < τ₀ + 3 / 2 := by linarith
  positivity

theorem tilted_xi_window_ge {ε τ₀ δ τ : ℝ} (hε : 0 ≤ ε) (hτ₀ : 5 ≤ τ₀) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - τ₀|)
    (hτ : τ ∈ Icc (τ₀ - δ / 2) (τ₀ + δ / 2)) :
    tiltedWindowFloor ε τ₀ δ ≤
      Real.exp (τ * (π / 4 - ε)) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ := by
  have hτ4 : 4 ≤ τ := by linarith [hτ.1]
  have hfar : ∀ ρ ∈ zetaZeroConfig.carrier, δ / 2 ≤ |ρ.im - τ| := by
    intro ρ hρ
    have h1 := hsep ρ hρ
    have h2 : |τ - τ₀| ≤ δ / 2 := abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have := abs_sub_abs_le_abs_sub (ρ.im - τ₀) (τ - τ₀)
    have e : ρ.im - τ₀ - (τ - τ₀) = ρ.im - τ := by ring
    rw [e] at this
    linarith [abs_sub_comm (ρ.im - τ₀) (τ - τ₀)]
  have h := tilted_xi_line_ge (θ := π / 4 - ε) hτ4 (by linarith : (0 : ℝ) < δ / 2)
    (by linarith) hfar
  refine le_trans ?_ h
  have hC := logDerivZetaConstant_nonneg
  have hc := tiltedXiLineConst_pos
  unfold tiltedWindowFloor
  have hfrac : (τ₀ - 1 / 2) ^ 2 / (τ₀ + 3 / 2) ≤ τ ^ 2 / (1 + τ) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hsq : (τ₀ - 1 / 2) ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [hτ.1]) 2
    have h1 : 1 + τ ≤ τ₀ + 3 / 2 := by linarith [hτ.2]
    exact mul_le_mul hsq h1 (by linarith) (by positivity)
  have he1 : Real.exp (-(ε * (τ₀ + 1 / 2))) ≤ Real.exp ((π / 4 - ε - π / 4) * τ) := by
    apply Real.exp_le_exp.mpr
    have : τ ≤ τ₀ + 1 / 2 := by linarith [hτ.2]
    nlinarith
  have hlog : Real.log τ ≤ Real.log (τ₀ + 1) :=
    Real.log_le_log (by linarith) (by linarith [hτ.2])
  have he2 : Real.exp (-(3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ)) ≤
      Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / (δ / 2))) := by
    apply Real.exp_le_exp.mpr
    rw [show 3 / 2 * logDerivZetaConstant * Real.log τ / (δ / 2) =
      3 * logDerivZetaConstant * Real.log τ / δ by field_simp]
    have : 3 * logDerivZetaConstant * Real.log τ / δ ≤
        3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ := by
      apply div_le_div_of_nonneg_right _ hδ.le
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  have h0 : 0 ≤ tiltedXiLineConst * ((τ₀ - 1 / 2) ^ 2 / (τ₀ + 3 / 2)) := by
    have : 0 < τ₀ + 3 / 2 := by linarith
    positivity
  calc tiltedXiLineConst * ((τ₀ - 1 / 2) ^ 2 / (τ₀ + 3 / 2)) * Real.exp (-(ε * (τ₀ + 1 / 2))) *
        Real.exp (-(3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ))
      ≤ tiltedXiLineConst * (τ ^ 2 / (1 + τ)) * Real.exp ((π / 4 - ε - π / 4) * τ) *
          Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / (δ / 2))) := by
        gcongr

/-- **Christoffel bound (raw form).**  If `ν` is dominated by the level-`L` Hodge form, the tilted
test fits in `[-L, L]`, and twice the tail is below the window floor, then
`ν([τ₀ - δ/2, τ₀ + δ/2]) ≤ ‖W(T,T)‖ / ℓ²`, `ℓ = (m/2)(τ₀ - 1/2)² · 4w cos(1/8) ∫κ`. -/
theorem measure_window_le_of_dominated_tilted {L U w ε : ℝ} {ν : Measure ℝ}
    (hν : DominatedByHodgeForm L ν) (hε : 0 ≤ ε) (hθ0 : 0 ≤ π / 4 - ε)
    (hθ : 2 * (π / 4 - ε) < π / 2) (hw : 0 < w) (hw4 : 4 * w ≤ 1) (hUL : U + w ≤ L)
    {τ₀ δ : ℝ} (hτ₀ : 5 ≤ τ₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - τ₀|)
    (hbig : 2 * (∫ u : ℝ, ‖tiltedTail U (π / 4 - ε) u‖ * Real.exp (1 / 2 * |u|)) ≤
      tiltedWindowFloor ε τ₀ δ) :
    ν (Icc (τ₀ - δ / 2) (τ₀ + δ / 2)) ≤
      ENNReal.ofReal (‖zetaZeroConfig.W (landauRadicalTest U (π / 4 - ε) w τ₀)
          (landauRadicalTest U (π / 4 - ε) w τ₀)‖ /
        ((tiltedWindowFloor ε τ₀ δ / 2) * (τ₀ - 1 / 2) ^ 2 *
          (4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)))) ^ 2) := by
  set θ := π / 4 - ε with hθdef
  set εt := ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|) with hεt
  set m := tiltedWindowFloor ε τ₀ δ with hm
  set I₀ := Icc (τ₀ - δ / 2) (τ₀ + δ / 2) with hI₀
  set c := 4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)) with hc
  have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hcos : 0 < Real.cos (1 / 8) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hm0 : 0 < m := tiltedWindowFloor_pos hτ₀
  set ℓ := (m / 2) * (τ₀ - 1 / 2) ^ 2 * c with hℓ
  have hτ₀' : 0 < τ₀ - 1 / 2 := by linarith
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  have hpt : ∀ τ ∈ I₀, ℓ ≤ ‖paperFT (landauRadicalTest U θ w τ₀) (τ : ℂ)‖ := by
    intro τ hτ
    have hτω : |τ - τ₀| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hlow := norm_paperFT_landauRadicalTest_real_ge (U := U) hθ0 hθ hw hw4 τ₀ hτω
    have hXi := tilted_xi_window_ge hε hτ₀ hδ hδ1 hsep hτ
    rw [← hεt] at hlow
    have hsq : (τ₀ - 1 / 2) ^ 2 ≤ τ ^ 2 + 1 / 4 := by
      have : (τ₀ - 1 / 2) ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [hτ.1]) 2
      linarith
    have hdiff : m / 2 ≤ Real.exp (τ * θ) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ - εt := by
      rw [hθdef]; linarith
    calc ℓ = (m / 2) * ((τ₀ - 1 / 2) ^ 2 * c) := by rw [hℓ]; ring
      _ ≤ (Real.exp (τ * θ) * ‖riemannPhiTransform (1 / 2 + I * τ)‖ - εt) *
            ((τ ^ 2 + 1 / 4) * c) := by
          apply mul_le_mul hdiff (mul_le_mul_of_nonneg_right hsq hc0.le) (by positivity)
            (by linarith)
      _ ≤ ‖paperFT (landauRadicalTest U θ w τ₀) (τ : ℂ)‖ := hlow
  have hdom := hν (landauRadicalTest U θ w τ₀) (contDiff_landauRadicalTest hθ0 hθ hw τ₀)
    (tsupport_landauRadicalTest hw τ₀ hUL) (paperFT_landauRadicalTest_half_I hθ0 hθ hw τ₀)
    (paperFT_landauRadicalTest_neg_half_I hθ0 hθ hw τ₀)
  have hind : ∫⁻ τ, I₀.indicator (fun _ => ENNReal.ofReal (ℓ ^ 2)) τ ∂ν ≤
      ∫⁻ τ, ENNReal.ofReal (‖paperFT (landauRadicalTest U θ w τ₀) τ‖ ^ 2) ∂ν := by
    refine lintegral_mono fun τ => ?_
    by_cases hτ : τ ∈ I₀
    · rw [indicator_of_mem hτ]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hℓ0.le (hpt τ hτ) 2)
    · rw [indicator_of_notMem hτ]; exact bot_le
  rw [lintegral_indicator_const measurableSet_Icc] at hind
  have hkey : ENNReal.ofReal (ℓ ^ 2) * ν I₀ ≤
      ENNReal.ofReal ‖zetaZeroConfig.W (landauRadicalTest U θ w τ₀)
        (landauRadicalTest U θ w τ₀)‖ :=
    hind.trans hdom
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  rw [ENNReal.ofReal_div_of_pos hℓ2]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hℓ2).ne')
    (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm]; exact hkey

/-! ## The exponent balance at the Landau height -/

/-- With `ε = √η/2` and `w = η/8`:
`2ε(1 - η/2) e^{2L} ≤ cos(2(π/4 - ε)) e^{2(L - w)}`. -/
theorem landau_rate_ge {η L : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    2 * (Real.sqrt η / 2) * (1 - η / 2) * Real.exp (2 * L) ≤
      Real.cos (2 * (π / 4 - Real.sqrt η / 2)) * Real.exp (2 * (L - η / 8)) := by
  set ε := Real.sqrt η / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεsq : ε ^ 2 = η / 4 := by rw [hε, div_pow, Real.sq_sqrt hη.le]; ring
  have hcos : Real.cos (2 * (π / 4 - ε)) = Real.sin (2 * ε) := by
    rw [show 2 * (π / 4 - ε) = π / 2 - 2 * ε by ring, Real.cos_pi_div_two_sub]
  have hsin : 2 * ε * (1 - ε ^ 2) ≤ Real.sin (2 * ε) := by
    have h := Real.sin_gt_sub_cube (x := 2 * ε) (by positivity)
    have h3 : 0 < ε ^ 3 := pow_pos hε0 3
    nlinarith
  have hexp : Real.exp (2 * L) * (1 - η / 4) ≤ Real.exp (2 * (L - η / 8)) := by
    have := Real.add_one_le_exp (-(η / 4))
    rw [show 2 * (L - η / 8) = 2 * L + (-(η / 4)) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  rw [hcos]
  have hs0 : 0 ≤ 2 * ε * (1 - ε ^ 2) := by
    have : ε ^ 2 ≤ 1 := by rw [hεsq]; linarith
    have : 0 ≤ 1 - ε ^ 2 := by linarith
    positivity
  have hE := Real.exp_pos (2 * L)
  have hq : 1 - η / 2 ≤ (1 - η / 4) * (1 - η / 4) := by nlinarith
  calc 2 * ε * (1 - η / 2) * Real.exp (2 * L)
      = (2 * ε * Real.exp (2 * L)) * (1 - η / 2) := by ring
    _ ≤ (2 * ε * Real.exp (2 * L)) * ((1 - η / 4) * (1 - η / 4)) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 2 * ε * (1 - ε ^ 2) * (Real.exp (2 * L) * (1 - η / 4)) := by rw [hεsq]; ring
    _ ≤ Real.sin (2 * ε) * Real.exp (2 * (L - η / 8)) :=
        mul_le_mul hsin hexp (by nlinarith) (hs0.trans hsin)

/-- **The gain below the Landau height.**  For `τ₀ ≤ (1-η) 2π e^{2L}`, the tail rate
`R = π cos(2θ) e^{2(L-w)}` exceeds the tilt cost `ε(τ₀ + 1/2)` by `(π/2) η^{3/2} e^{2L} - ε/2`. -/
theorem landau_gain {η L τ₀ : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hτ : τ₀ ≤ (1 - η) * (2 * π * Real.exp (2 * L))) :
    π / 2 * (η * Real.sqrt η) * Real.exp (2 * L) - Real.sqrt η / 2 / 2 ≤
      π * Real.cos (2 * (π / 4 - Real.sqrt η / 2)) * Real.exp (2 * (L - η / 8)) -
        Real.sqrt η / 2 * (τ₀ + 1 / 2) := by
  have hr := landau_rate_ge (L := L) hη hη2
  have hs0 : 0 ≤ Real.sqrt η := Real.sqrt_nonneg _
  have hpi := Real.pi_pos
  have h1 : π * (2 * (Real.sqrt η / 2) * (1 - η / 2) * Real.exp (2 * L)) ≤
      π * (Real.cos (2 * (π / 4 - Real.sqrt η / 2)) * Real.exp (2 * (L - η / 8))) :=
    mul_le_mul_of_nonneg_left hr hpi.le
  have h2 : Real.sqrt η / 2 * τ₀ ≤ Real.sqrt η / 2 * ((1 - η) * (2 * π * Real.exp (2 * L))) :=
    mul_le_mul_of_nonneg_left hτ (by positivity)
  nlinarith

/-- The level threshold: `B + 16L ≤ κ e^{2L}` for all large `L`. -/
theorem exists_level_linear_le_exp {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 < κ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → B + 16 * L ≤ κ * Real.exp (2 * L) := by
  refine ⟨max 1 ((B + 16) / (2 * κ)), le_max_left _ _, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : (B + 16) / (2 * κ) ≤ L := le_trans (le_max_right _ _) hL
  have hexp : 2 * L ^ 2 ≤ Real.exp (2 * L) := by
    have := Real.sum_le_exp_of_nonneg (x := 2 * L) (by linarith) 3
    simp [Finset.sum_range_succ, Nat.factorial] at this
    nlinarith
  have hk : B + 16 ≤ 2 * κ * L := by
    rw [div_le_iff₀ (by positivity)] at hL2; linarith
  have h1 : B + 16 * L ≤ (B + 16) * L := by nlinarith
  have h2 : (B + 16) * L ≤ 2 * κ * L * L := mul_le_mul_of_nonneg_right hk (by linarith)
  have h3 : 2 * κ * L * L ≤ κ * Real.exp (2 * L) := by
    have := mul_le_mul_of_nonneg_left hexp hκ.le
    nlinarith
  linarith

/-- Twice the tail is below the window floor. -/
theorem landau_two_tail_le_floor {M cL L G R εt ε τ₀ δ B : ℝ} (hM : 0 ≤ M)
    (hcL : cL = tiltedXiLineConst) (hτ₀ : 5 ≤ τ₀) (hε1 : ε ≤ 1) (hL : 0 ≤ L)
    (hεt : εt ≤ 2 * M * Real.exp (6 * L) * Real.exp (-R))
    (hgain : G / 2 - ε / 2 ≤ R - ε * (τ₀ + 1 / 2))
    (hZ : 3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ ≤ G / 8)
    (hB : Real.log (4 * M / cL + 1) + 1 ≤ B) (hBL : B + 16 * L ≤ G / 4) :
    2 * εt ≤ tiltedWindowFloor ε τ₀ δ := by
  have hcL0 : 0 < cL := by rw [hcL]; exact tiltedXiLineConst_pos
  have hlog0 : 0 ≤ Real.log (4 * M / cL + 1) :=
    Real.log_nonneg (by have : 0 ≤ 4 * M / cL := by positivity
                        linarith)
  set X := Real.exp (-(ε * (τ₀ + 1 / 2))) with hX
  have hX0 : 0 < X := Real.exp_pos _
  set Z := Real.exp (-(3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ)) with hZdef
  have hZlow : Real.exp (-(G / 8)) ≤ Z := Real.exp_le_exp.mpr (by linarith)
  have hQ : 1 ≤ (τ₀ - 1 / 2) ^ 2 / (τ₀ + 3 / 2) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hR : Real.exp (-R) ≤ Real.exp (1 / 2 - G / 2) * X := by
    rw [hX, ← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  have hexpB : 4 * M / cL + 1 ≤ Real.exp B := by
    calc 4 * M / cL + 1 = Real.exp (Real.log (4 * M / cL + 1)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr (by linarith)
  have hkey : 4 * M * Real.exp (6 * L + 1 / 2 - G / 2) ≤ cL * Real.exp (-(G / 8)) := by
    have h1 : 4 * M ≤ cL * Real.exp B := by
      have := mul_le_mul_of_nonneg_left hexpB hcL0.le
      rw [mul_add, mul_div_cancel₀ _ hcL0.ne', mul_one] at this
      linarith
    calc 4 * M * Real.exp (6 * L + 1 / 2 - G / 2)
        ≤ cL * Real.exp B * Real.exp (6 * L + 1 / 2 - G / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = cL * Real.exp (B + 6 * L + 1 / 2 - G / 2) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ cL * Real.exp (-(G / 8)) := by
          apply mul_le_mul_of_nonneg_left _ hcL0.le
          apply Real.exp_le_exp.mpr
          linarith
  unfold tiltedWindowFloor
  rw [← hcL, ← hX, ← hZdef]
  calc 2 * εt ≤ 2 * (2 * M * Real.exp (6 * L) * (Real.exp (1 / 2 - G / 2) * X)) := by
        have := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 2 * M * Real.exp (6 * L))
        linarith
    _ = 4 * M * Real.exp (6 * L + 1 / 2 - G / 2) * X := by
        rw [show 6 * L + 1 / 2 - G / 2 = 6 * L + (1 / 2 - G / 2) by ring, Real.exp_add]; ring
    _ ≤ cL * Real.exp (-(G / 8)) * X := mul_le_mul_of_nonneg_right hkey hX0.le
    _ ≤ cL * ((τ₀ - 1 / 2) ^ 2 / (τ₀ + 3 / 2)) * X * Z := by
        have hcX : 0 ≤ cL * X := by positivity
        calc cL * Real.exp (-(G / 8)) * X = (cL * X) * Real.exp (-(G / 8)) := by ring
          _ ≤ (cL * X) * (((τ₀ - 1 / 2) ^ 2 / (τ₀ + 3 / 2)) * Z) := by
              apply mul_le_mul_of_nonneg_left _ hcX
              have : Real.exp (-(G / 8)) ≤ 1 * Z := by linarith
              exact this.trans (mul_le_mul_of_nonneg_right hQ (Real.exp_pos _).le)
          _ = _ := by ring

/-- The numeric form of the Christoffel ratio below the Landau height. -/
theorem landau_ratio_le {M Bw A₀ cL w c₀ L E G R εt ε τ₀ δ Wv B : ℝ} (hM : 0 ≤ M)
    (hA₀ : 1 ≤ A₀) (hcL : cL = tiltedXiLineConst) (hw : 0 < w) (hc₀ : 0 < c₀)
    (hτ₀ : 5 ≤ τ₀) (hε1 : ε ≤ 1) (hE : E = Real.exp (2 * L))
    (hτE : τ₀ + 3 / 2 ≤ 8 * E)
    (hεt0 : 0 ≤ εt) (hεt : εt ≤ 2 * M * Real.exp (6 * L) * Real.exp (-R))
    (hgain : G / 2 - ε / 2 ≤ R - ε * (τ₀ + 1 / 2))
    (hZ : 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ ≤ G / 4)
    (hW : Wv ≤ εt ^ 2 * Bw ^ 2 * (1 + τ₀) ^ 4 * (24 * A₀ * Real.log (τ₀ + 3)))
    (hB : Real.log (64 * (96 * (M ^ 2 * Bw ^ 2 * A₀) / (cL ^ 2 * w ^ 2 * c₀ ^ 2)) + 1) + 1 ≤ B)
    (hBL : B + 16 * L ≤ G / 4) :
    Wv / ((tiltedWindowFloor ε τ₀ δ / 2) * (τ₀ - 1 / 2) ^ 2 * (4 * w * c₀)) ^ 2 ≤
      Real.exp (-(G / 2)) := by
  have hcL0 : 0 < cL := by rw [hcL]; exact tiltedXiLineConst_pos
  set K₃ := 96 * (M ^ 2 * Bw ^ 2 * A₀) / (cL ^ 2 * w ^ 2 * c₀ ^ 2) with hK₃
  have hK₃0 : 0 ≤ K₃ := by
    rw [hK₃]
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (by linarith))
  set X := Real.exp (-(ε * (τ₀ + 1 / 2))) with hX
  have hX0 : 0 < X := Real.exp_pos _
  set Z := Real.exp (-(3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ)) with hZdef
  have hZ0 : 0 < Z := Real.exp_pos _
  have hZ2 : Real.exp (-(G / 4)) ≤ Z ^ 2 := by
    rw [hZdef, sq, ← Real.exp_add]; apply Real.exp_le_exp.mpr
    have e : 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ =
        2 * (3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ) := by ring
    rw [e] at hZ; linarith
  set x := τ₀ - 1 / 2 with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  set y := τ₀ + 3 / 2 with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hm : tiltedWindowFloor ε τ₀ δ = cL * (x ^ 2 / y) * X * Z := by
    unfold tiltedWindowFloor; rw [hcL]
  set T := 2 * M * Real.exp (6 * L) * (Real.exp (1 / 2 - G / 2) * X) with hT
  have hR : Real.exp (-R) ≤ Real.exp (1 / 2 - G / 2) * X := by
    rw [hX, ← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  have hεtT : εt ≤ T := by
    rw [hT]
    exact hεt.trans (mul_le_mul_of_nonneg_left hR (by positivity))
  have hpoly := pinning_poly_le hτ₀
  have hlog0 : 0 ≤ Real.log (τ₀ + 3) := Real.log_nonneg (by linarith)
  have hWv : Wv ≤ T ^ 2 * Bw ^ 2 * (24 * A₀) * (4 * x ^ 8) := by
    have hA0' : 0 ≤ 24 * A₀ := by linarith
    calc Wv ≤ εt ^ 2 * Bw ^ 2 * (1 + τ₀) ^ 4 * (24 * A₀ * Real.log (τ₀ + 3)) := hW
      _ = εt ^ 2 * (Bw ^ 2 * (24 * A₀)) * ((1 + τ₀) ^ 4 * Real.log (τ₀ + 3)) := by ring
      _ ≤ T ^ 2 * (Bw ^ 2 * (24 * A₀)) * (4 * (τ₀ - 1 / 2) ^ 8) := by
          gcongr
      _ = T ^ 2 * Bw ^ 2 * (24 * A₀) * (4 * x ^ 8) := by rw [hx]; ring
  have hden : ((cL * (x ^ 2 / y) * X * Z) / 2 * x ^ 2 * (4 * w * c₀)) ^ 2 =
      4 * cL ^ 2 * w ^ 2 * c₀ ^ 2 * X ^ 2 * Z ^ 2 * x ^ 8 / y ^ 2 := by
    field_simp; ring
  rw [hm, hden]
  have hden0 : 0 < 4 * cL ^ 2 * w ^ 2 * c₀ ^ 2 * X ^ 2 * Z ^ 2 * x ^ 8 / y ^ 2 := by positivity
  rw [div_le_iff₀ hden0]
  have hyE : y ^ 2 ≤ 64 * Real.exp (4 * L) := by
    have h8 : y ≤ 8 * Real.exp (2 * L) := by rw [hy, ← hE]; exact hτE
    have h2 : Real.exp (4 * L) = Real.exp (2 * L) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [h2]
    calc y ^ 2 ≤ (8 * Real.exp (2 * L)) ^ 2 := pow_le_pow_left₀ hy0.le h8 2
      _ = 64 * Real.exp (2 * L) ^ 2 := by ring
  have hexpB : 64 * K₃ + 1 ≤ Real.exp (B - 1) := by
    calc 64 * K₃ + 1 = Real.exp (Real.log (64 * K₃ + 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (B - 1) := Real.exp_le_exp.mpr (by linarith)
  -- the target: T² Bw² 24A₀ 4x⁸ ≤ e^{-G/2} · 4cL²w²c₀²X²Z²x⁸/y²
  have hT2 : T ^ 2 = 4 * M ^ 2 * Real.exp (12 * L) * Real.exp (1 - G) * X ^ 2 := by
    rw [hT]
    have e1 : Real.exp (6 * L) ^ 2 = Real.exp (12 * L) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have e2 : Real.exp (1 / 2 - G / 2) ^ 2 = Real.exp (1 - G) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [show (2 * M * Real.exp (6 * L) * (Real.exp (1 / 2 - G / 2) * X)) ^ 2 =
      4 * M ^ 2 * Real.exp (6 * L) ^ 2 * Real.exp (1 / 2 - G / 2) ^ 2 * X ^ 2 by ring, e1, e2]
  have hbig : 64 * K₃ * Real.exp (16 * L + 1 - 3 / 4 * G) ≤ Real.exp (-(G / 2)) := by
    calc 64 * K₃ * Real.exp (16 * L + 1 - 3 / 4 * G)
        ≤ Real.exp (B - 1) * Real.exp (16 * L + 1 - 3 / 4 * G) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = Real.exp (B + 16 * L - 3 / 4 * G) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(G / 2)) := Real.exp_le_exp.mpr (by linarith)
  have hWv' : T ^ 2 * Bw ^ 2 * (24 * A₀) * (4 * x ^ 8) =
      K₃ * (4 * cL ^ 2 * w ^ 2 * c₀ ^ 2 * X ^ 2 * x ^ 8) * (Real.exp (12 * L) * Real.exp (1 - G)) := by
    rw [hT2, hK₃]; field_simp; ring
  have hstep : K₃ * (4 * cL ^ 2 * w ^ 2 * c₀ ^ 2 * X ^ 2 * x ^ 8) *
      (Real.exp (12 * L) * Real.exp (1 - G)) ≤
      Real.exp (-(G / 2)) * (4 * cL ^ 2 * w ^ 2 * c₀ ^ 2 * X ^ 2 * Z ^ 2 * x ^ 8 / y ^ 2) := by
    set P := 4 * cL ^ 2 * w ^ 2 * c₀ ^ 2 * X ^ 2 * x ^ 8 with hP
    have hP0 : 0 < P := by rw [hP]; positivity
    have hr : 4 * cL ^ 2 * w ^ 2 * c₀ ^ 2 * X ^ 2 * Z ^ 2 * x ^ 8 / y ^ 2 = P * (Z ^ 2 / y ^ 2) := by
      rw [hP]; field_simp
    rw [hr]
    have hZy : Real.exp (-(G / 4)) / (64 * Real.exp (4 * L)) ≤ Z ^ 2 / y ^ 2 :=
      div_le_div₀ (by positivity) hZ2 (by positivity) hyE
    have hmain : K₃ * (Real.exp (12 * L) * Real.exp (1 - G)) ≤
        Real.exp (-(G / 2)) * (Real.exp (-(G / 4)) / (64 * Real.exp (4 * L))) := by
      have e : Real.exp (-(G / 2)) * (Real.exp (-(G / 4)) / (64 * Real.exp (4 * L))) =
          Real.exp (-(G / 2)) * Real.exp (-(G / 4)) / (64 * Real.exp (4 * L)) := by ring
      rw [e, le_div_iff₀ (by positivity)]
      have e3 : Real.exp (16 * L + 1 - 3 / 4 * G) * Real.exp (-(G / 4)) =
          Real.exp (12 * L) * Real.exp (1 - G) * Real.exp (4 * L) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
      have e2 : K₃ * (Real.exp (12 * L) * Real.exp (1 - G)) * (64 * Real.exp (4 * L)) =
          64 * K₃ * Real.exp (16 * L + 1 - 3 / 4 * G) * Real.exp (-(G / 4)) := by
        rw [mul_assoc (64 * K₃), e3]; ring
      rw [e2]
      exact mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
    calc K₃ * P * (Real.exp (12 * L) * Real.exp (1 - G))
        = P * (K₃ * (Real.exp (12 * L) * Real.exp (1 - G))) := by ring
      _ ≤ P * (Real.exp (-(G / 2)) * (Real.exp (-(G / 4)) / (64 * Real.exp (4 * L)))) :=
          mul_le_mul_of_nonneg_left hmain hP0.le
      _ ≤ P * (Real.exp (-(G / 2)) * (Z ^ 2 / y ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZy (Real.exp_pos _).le) hP0.le
      _ = Real.exp (-(G / 2)) * (P * (Z ^ 2 / y ^ 2)) := by ring
  calc Wv ≤ T ^ 2 * Bw ^ 2 * (24 * A₀) * (4 * x ^ 8) := hWv
    _ = _ := hWv'
    _ ≤ _ := hstep

/-! ## The pinning law at the Landau height -/

/-- **Krein pinning up to the Landau height.**  For every `0 < η ≤ 1/2` there is `L₀` such that for
all `L ≥ L₀`, every positive measure `ν` dominated by the level-`L` Hodge form of `ζ` has
`ν([τ₀ - δ/2, τ₀ + δ/2]) ≤ exp(-(π/2) η^{3/2} e^{2L})` whenever `5 ≤ τ₀ ≤ (1-η) 2π e^{2L}`,
every zero ordinate is at distance `≥ δ` from `τ₀`, `0 < δ ≤ 1`, and
`12 C log(τ₀+1)/δ ≤ (π/2) η^{3/2} e^{2L}`. -/
theorem zeta_krein_completion_pinned_below_landau_height :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ ν : Measure ℝ,
      DominatedByHodgeForm L ν → ∀ τ₀ δ : ℝ, 5 ≤ τ₀ →
        τ₀ ≤ (1 - η) * (2 * π * Real.exp (2 * L)) → 0 < δ → δ ≤ 1 →
        (∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - τ₀|) →
        12 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ ≤
          π / 2 * (η * Real.sqrt η) * Real.exp (2 * L) →
        ν (Icc (τ₀ - δ / 2) (τ₀ + δ / 2)) ≤
          ENNReal.ofReal (Real.exp (-(π / 2 * (η * Real.sqrt η) * Real.exp (2 * L)))) := by
  intro η hη hη2
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = Real.sqrt η / 2 := ⟨_, rfl⟩
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hs1 : Real.sqrt η ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by rw [hεdef]; linarith
  have hθ0 : 0 ≤ π / 4 - ε := by rw [hεdef]; linarith [Real.pi_gt_three]
  have hθ : 2 * (π / 4 - ε) < π / 2 := by linarith
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = η / 8 := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hwdef]; positivity
  have hw4 : 4 * w ≤ 1 := by rw [hwdef]; linarith
  have hM : 0 ≤ tiltedPhiTailConst := tiltedPhiTailConst_nonneg
  have hBw : 0 ≤ scaledBumpConst w := scaledBumpConst_nonneg hw
  have hcL0 : 0 < tiltedXiLineConst := tiltedXiLineConst_pos
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = Real.cos (1 / 8) * (∫ u, weilBump u) := ⟨_, rfl⟩
  have hc₀ : 0 < c₀ := by
    have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
    have hcos : 0 < Real.cos (1 / 8) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    rw [hc₀def]; positivity
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : ℝ, B₁ = Real.log (4 * tiltedPhiTailConst / tiltedXiLineConst + 1) :=
    ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B₂ : ℝ, B₂ = Real.log (64 * (96 * (tiltedPhiTailConst ^ 2 *
      scaledBumpConst w ^ 2 * A₀) / (tiltedXiLineConst ^ 2 * w ^ 2 * c₀ ^ 2)) + 1) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max B₁ B₂ + 1 := ⟨_, rfl⟩
  have hB₁0 : 0 ≤ B₁ := by
    rw [hB₁]
    apply Real.log_nonneg
    have : 0 ≤ 4 * tiltedPhiTailConst / tiltedXiLineConst := by positivity
    linarith
  have hmaxl := le_max_left B₁ B₂
  have hmaxr := le_max_right B₁ B₂
  have hB0 : 0 ≤ B := by rw [hBdef]; linarith
  have hκ : 0 < π / 4 * (η * Real.sqrt η) := by have := Real.pi_pos; positivity
  obtain ⟨L₀, hL₀1, hL₀⟩ := exists_level_linear_le_exp hB0 hκ
  refine ⟨L₀, fun L hL ν hν τ₀ δ hτ₀ hτ hδ hδ1 hsep hH => ?_⟩
  have hL1 : 1 ≤ L := le_trans hL₀1 hL
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (2 * L) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hEdef]; exact Real.one_le_exp (by linarith)
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = π * (η * Real.sqrt η) * E := ⟨_, rfl⟩
  have hBL : B + 16 * L ≤ G / 4 := by
    have h := hL₀ L hL
    rw [← hEdef] at h
    rw [hGdef]; linarith
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = L - w := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = π * Real.cos (2 * (π / 4 - ε)) * Real.exp (2 * U) :=
    ⟨_, rfl⟩
  have hgain0 := landau_gain (L := L) hη hη2 hτ
  rw [← hεdef, ← hwdef, ← hEdef, ← hUdef, ← hRdef] at hgain0
  have hgain : G / 2 - ε / 2 ≤ R - ε * (τ₀ + 1 / 2) := by
    rw [hGdef]; linarith
  have hG68 : 68 ≤ G := by linarith
  have hR3 : 3 ≤ R := by
    have : 0 ≤ ε * (τ₀ + 1 / 2) := by
      have : 0 ≤ τ₀ + 1 / 2 := by linarith
      positivity
    linarith
  have hεt := integral_norm_tiltedTail_mul_exp_le (U := U) hθ0 hθ (by rw [← hRdef]; exact hR3)
  rw [← hRdef] at hεt
  have hU6 : Real.exp (6 * U) ≤ Real.exp (6 * L) :=
    Real.exp_le_exp.mpr (by rw [hUdef]; linarith)
  have hεt' : (∫ u : ℝ, ‖tiltedTail U (π / 4 - ε) u‖ * Real.exp (1 / 2 * |u|)) ≤
      2 * tiltedPhiTailConst * Real.exp (6 * L) * Real.exp (-R) := by
    refine hεt.trans ?_
    have := Real.exp_pos (-R)
    gcongr
  have hεt0 : 0 ≤ ∫ u : ℝ, ‖tiltedTail U (π / 4 - ε) u‖ * Real.exp (1 / 2 * |u|) :=
    integral_nonneg fun _ => by positivity
  have hH' : 4 * (3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ) ≤ G / 2 := by
    have e : 12 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ =
        4 * (3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ) := by ring
    rw [e, ← hEdef] at hH
    rw [hGdef]; linarith
  have hZ8 : 3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ ≤ G / 8 := by linarith
  have hZ4 : 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ ≤ G / 4 := by
    have e : 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ =
        2 * (3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ) := by ring
    rw [e]; linarith
  have hbig := landau_two_tail_le_floor hM rfl hτ₀ hε1 (by linarith) hεt' hgain hZ8
    (by rw [← hB₁]; linarith) hBL
  have hUL : U + w ≤ L := by rw [hUdef]; linarith
  have hraw := measure_window_le_of_dominated_tilted hν hε0.le hθ0 hθ hw hw4 hUL hτ₀ hδ hδ1 hsep
    hbig
  refine le_trans hraw (ENNReal.ofReal_le_ofReal ?_)
  have hW := norm_W_landauRadicalTest_le hA₀ hloc (U := U) hθ0 hθ hw hw4 τ₀
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ₀)] at hW
  have hτE : τ₀ + 3 / 2 ≤ 8 * E := by
    have hπ : π < 3.15 := Real.pi_lt_d2
    have h1 : τ₀ ≤ 2 * π * E := by
      rw [hEdef]
      have : 0 ≤ η * (2 * π * Real.exp (2 * L)) := by have := Real.pi_pos; positivity
      linarith
    have h2 : π * E ≤ 3.15 * E := mul_le_mul_of_nonneg_right hπ.le (by linarith)
    linarith
  have hratio := landau_ratio_le hM hA₀ rfl hw hc₀ hτ₀ hε1 hEdef hτE
    hεt0 hεt' hgain hZ4 hW (by rw [← hB₂]; linarith) hBL
  have eG : π / 2 * (η * Real.sqrt η) * Real.exp (2 * L) = G / 2 := by
    rw [hGdef, hEdef]; ring
  rw [eG, ← hc₀def]
  exact hratio

end

end RHTower
