import GaloisForLFunctions.RHTower.RiemannKernelWeilRadical
import GaloisForLFunctions.RHTower.IsolatedDeepZeroHodgeIndex
import Zeta23.Statement.SeamClosed

/-!
# The Weil margin is super-exponentially small, unconditionally

Riemann's kernel `Φ` lies in the radical of the Weil form of `ζ`: its transform vanishes at every
nontrivial zero (`RiemannKernelWeilRadical`). Truncate `Φ` to `[-(L-1/4), L-1/4]` and smooth it
with `κ₂ = κ'' - κ/4`, where `κ` is a fixed bump. The transform of `κ₂` vanishes at `±i/2`, so
the resulting test `f_L` lies in the Hodge class: `C²`, supported in `[-L, L]`, with
`f̂_L(±i/2) = 0`.

At every zero, both Weil evaluation points see only the tail of `Φ` beyond `L - 1/4`, which has
size `exp(-π e^{2L - 1/2})`. The other factor decays like `(1 + |γ|)^{-2}` because `f_L` is `C²`.
Summing over the zeros with the unconditional local count gives

`‖W(f_L, f_L)‖ ≤ C e^{12L} e^{-π e^{2L-1/2}} ‖f_L‖₂²`   (`zeta_weil_margin_superexponential`).

Hence the ground energy of the Weil form at level `L`, and of its polar-constrained (Hodge)
restriction, is at most `C e^{12L - π e^{2L-1/2}}`. This holds with or without the Riemann
hypothesis.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Bottcher Zeta23

namespace RHTower

noncomputable section

local notation "Mθ" => jacobiThetaTailConstant
local notation "Φ" => riemannPhiKernel

/-! ## Analytic facts about Riemann's kernel -/

theorem continuous_riemannPhiKernel : Continuous Φ :=
  continuous_modSource thetaThree_differentiableOn

theorem riemannPhiKernel_neg (x : ℝ) : Φ (-x) = Φ x :=
  modSource_neg thetaThree_differentiableOn thetaThree_axis x

theorem norm_riemannPhiKernel_le {x : ℝ} (hx : 3 ≤ Real.exp (2 * x)) :
    ‖Φ x‖ ≤ 4 * Mθ * Real.exp π * Real.exp (x / 2) *
      (3 * Real.exp (2 * x) + 2 * Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x)) :=
  norm_modSource_le_of_cuspDecay (c := 1) thetaThree_differentiableOn thetaThree_cuspDecay hx

theorem exists_norm_riemannPhiKernel_le_exp {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖Φ x‖ ≤ C * Real.exp (-(B * |x|)) :=
  exists_norm_modSource_le_exp (c := 1) thetaThree_differentiableOn thetaThree_axis
    thetaThree_cuspDecay hB

/-- One-sided far tail bound in a form adapted to integration: for `e^{2U} ≥ 3`, `u ≥ U`,
`0 ≤ b ≤ 3/2`, `‖Φ(u)‖ e^{bu} ≤ 20 Mθ e^π e^{6U} e^{-πe^{2U}} e^{-(6π-6)(u-U)}`. -/
theorem norm_riemannPhiKernel_mul_exp_le {U u b : ℝ} (hU : 3 ≤ Real.exp (2 * U)) (hu : U ≤ u)
    (hb : b ≤ 3 / 2) :
    ‖Φ u‖ * Real.exp (b * u) ≤ 20 * Mθ * Real.exp π * Real.exp (6 * U) *
      Real.exp (-π * Real.exp (2 * U)) * Real.exp (-(6 * π - 6) * (u - U)) := by
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  have hU0 : 0 ≤ U := by
    by_contra h; push Not at h
    have : Real.exp (2 * U) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hu3 : 3 ≤ Real.exp (2 * u) := hU.trans (Real.exp_le_exp.mpr (by linarith))
  have h1 := norm_riemannPhiKernel_le hu3
  set y := Real.exp (2 * u) with hy
  have hy1 : 1 ≤ y := by linarith
  have hpoly : 3 * y + 2 * y ^ 2 ≤ 5 * y ^ 2 := by nlinarith
  -- y² = e^{4u}
  have hy2 : y ^ 2 = Real.exp (4 * u) := by rw [hy, ← Real.exp_nat_mul]; push_cast; ring_nf
  -- e^{2u} ≥ e^{2U} + 6(u - U)
  have hgrow : Real.exp (2 * U) + 6 * (u - U) ≤ y := by
    have h := Real.add_one_le_exp (2 * (u - U))
    have hmul : Real.exp (2 * U) * (2 * (u - U) + 1) ≤ Real.exp (2 * U) * Real.exp (2 * (u - U)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    rw [← Real.exp_add, show 2 * U + 2 * (u - U) = 2 * u by ring] at hmul
    nlinarith
  have hE : Real.exp (-π * y) ≤ Real.exp (-π * Real.exp (2 * U)) * Real.exp (-(6 * π) * (u - U)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
  have hexp : Real.exp (u / 2) * Real.exp (4 * u) * Real.exp (b * u) ≤
      Real.exp (6 * U) * Real.exp (6 * (u - U)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr; nlinarith
  calc ‖Φ u‖ * Real.exp (b * u)
      ≤ (4 * Mθ * Real.exp π * Real.exp (u / 2) * (3 * y + 2 * y ^ 2) * Real.exp (-π * y)) *
          Real.exp (b * u) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ (4 * Mθ * Real.exp π * Real.exp (u / 2) * (5 * y ^ 2) * Real.exp (-π * y)) *
          Real.exp (b * u) := by
        gcongr
    _ = 20 * Mθ * Real.exp π * (Real.exp (u / 2) * Real.exp (4 * u) * Real.exp (b * u)) *
          Real.exp (-π * y) := by rw [hy2]; ring
    _ ≤ 20 * Mθ * Real.exp π * (Real.exp (6 * U) * Real.exp (6 * (u - U))) *
          (Real.exp (-π * Real.exp (2 * U)) * Real.exp (-(6 * π) * (u - U))) := by
        gcongr
    _ = 20 * Mθ * Real.exp π * Real.exp (6 * U) * Real.exp (-π * Real.exp (2 * U)) *
          (Real.exp (6 * (u - U)) * Real.exp (-(6 * π) * (u - U))) := by ring
    _ = 20 * Mθ * Real.exp π * Real.exp (6 * U) * Real.exp (-π * Real.exp (2 * U)) *
          Real.exp (-(6 * π - 6) * (u - U)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- The part of Riemann's kernel beyond `|u| > L - 1/4`. -/
def riemannPhiTail (L : ℝ) : ℝ → ℂ := {u : ℝ | L - 1 / 4 < |u|}.indicator Φ

/-- The part of Riemann's kernel on `[-(L - 1/4), L - 1/4]`. -/
def riemannPhiCore (L : ℝ) : ℝ → ℂ := (Icc (-(L - 1 / 4)) (L - 1 / 4)).indicator Φ

theorem riemannPhiCore_add_tail (L u : ℝ) : riemannPhiCore L u + riemannPhiTail L u = Φ u := by
  unfold riemannPhiCore riemannPhiTail
  by_cases h : L - 1 / 4 < |u|
  · have h' : u ∉ Icc (-(L - 1 / 4)) (L - 1 / 4) := by
      intro hm; have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
    rw [indicator_of_notMem h', indicator_of_mem (show u ∈ {u : ℝ | L - 1 / 4 < |u|} from h)]
    simp
  · push Not at h
    have h' : u ∈ Icc (-(L - 1 / 4)) (L - 1 / 4) := ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
    rw [indicator_of_mem h', indicator_of_notMem (show u ∉ {u : ℝ | L - 1 / 4 < |u|} from
      fun hm => by simp only [mem_setOf_eq] at hm; linarith)]
    simp

theorem measurableSet_tailSet (L : ℝ) : MeasurableSet {u : ℝ | L - 1 / 4 < |u|} :=
  measurableSet_lt measurable_const measurable_abs

theorem norm_riemannPhiKernel_abs (u : ℝ) : ‖Φ |u|‖ = ‖Φ u‖ := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, riemannPhiKernel_neg]

/-- **Tail integral.**  For `L ≥ 1` and `0 ≤ b ≤ 3/2`,
`∫ ‖Φ_{>L-1/4}(u)‖ e^{b|u|} du ≤ (40 Mθ e^π/(6π-6)) e^{6(L-1/4)} e^{-π e^{2(L-1/4)}}`. -/
theorem integral_norm_riemannPhiTail_mul_exp_le {L b : ℝ} (hL : 1 ≤ L) (hb : b ≤ 3 / 2) :
    ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (b * |u|) ≤
      40 * Mθ * Real.exp π / (6 * π - 6) * Real.exp (6 * (L - 1 / 4)) *
        Real.exp (-π * Real.exp (2 * (L - 1 / 4))) := by
  set U := L - 1 / 4 with hUdef
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  have hU0 : 0 < U := by linarith
  have hU3 : 3 ≤ Real.exp (2 * U) := by
    have : (3 : ℝ) ≤ Real.exp (3 / 2) := by
      have := Real.add_one_le_exp (3 / 2); nlinarith [Real.add_one_le_exp (1 / 2),
        Real.exp_pos (1/2), Real.exp_add (1/2 : ℝ) 1, Real.exp_one_gt_d9]
    exact this.trans (Real.exp_le_exp.mpr (by linarith))
  have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
  set K : ℝ := 20 * Mθ * Real.exp π * Real.exp (6 * U) * Real.exp (-π * Real.exp (2 * U)) with hK
  have hK0 : 0 ≤ K := by positivity
  clear_value K
  set G : ℝ → ℝ := fun v => {v : ℝ | U < v}.indicator (fun v => ‖Φ v‖ * Real.exp (b * v)) v
    with hG
  have hpt : ∀ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (b * |u|) = G |u| := by
    intro u
    simp only [riemannPhiTail, hG]
    by_cases h : U < |u|
    · rw [indicator_of_mem (show u ∈ {u : ℝ | L - 1 / 4 < |u|} from h),
        indicator_of_mem (show |u| ∈ {v : ℝ | U < v} from h), norm_riemannPhiKernel_abs]
    · rw [indicator_of_notMem (show u ∉ {u : ℝ | L - 1 / 4 < |u|} from h),
        indicator_of_notMem (show |u| ∉ {v : ℝ | U < v} from h)]
      simp
  simp_rw [hpt]
  rw [integral_comp_abs]
  -- majorant on (0, ∞)
  set H : ℝ → ℝ := {v : ℝ | U < v}.indicator (fun v => K * Real.exp (-(6 * π - 6) * (v - U)))
    with hH
  have hGH : ∀ v ∈ Ioi (0 : ℝ), G v ≤ H v := by
    intro v _
    simp only [hG, hH]
    by_cases h : U < v
    · rw [indicator_of_mem (show v ∈ {v : ℝ | U < v} from h),
        indicator_of_mem (show v ∈ {v : ℝ | U < v} from h)]
      rw [hK]; exact norm_riemannPhiKernel_mul_exp_le hU3 h.le hb
    · rw [indicator_of_notMem (show v ∉ {v : ℝ | U < v} from h),
        indicator_of_notMem (show v ∉ {v : ℝ | U < v} from h)]
  have hmeasU : MeasurableSet {v : ℝ | U < v} := measurableSet_lt measurable_const measurable_id
  have hexpInt : IntegrableOn (fun v => K * Real.exp (-(6 * π - 6) * (v - U))) (Ioi U) := by
    have h : IntegrableOn (fun v => K * Real.exp ((6 * π - 6) * U) * Real.exp (-(6 * π - 6) * v))
        (Ioi U) := (integrableOn_exp_mul_Ioi (a := -(6 * π - 6)) (by linarith) U).const_mul _
    refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp only
    rw [show -(6 * π - 6) * (v - U) = (6 * π - 6) * U + -(6 * π - 6) * v by ring, Real.exp_add]
    ring
  have hHint : IntegrableOn H (Ioi (0 : ℝ)) := by
    have : IntegrableOn H univ := by
      rw [integrableOn_univ, hH]
      refine (integrable_indicator_iff hmeasU).mpr ?_
      simpa [Set.Ioi] using hexpInt
    exact this.mono_set (subset_univ _)
  have hGint : IntegrableOn G (Ioi (0 : ℝ)) := by
    refine Integrable.mono' hHint ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => ?_)
    · refine (AEStronglyMeasurable.indicator ?_ hmeasU)
      exact ((continuous_riemannPhiKernel.norm).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · have h0 : 0 ≤ G v := by
        simp only [hG]; exact indicator_nonneg (fun v _ => by positivity) v
      rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact hGH v hv
  have hmono := setIntegral_mono_on hGint hHint measurableSet_Ioi hGH
  have hHval : ∫ v in Ioi (0 : ℝ), H v = K / (6 * π - 6) := by
    rw [hH, setIntegral_indicator hmeasU]
    have hset : Ioi (0 : ℝ) ∩ {v : ℝ | U < v} = Ioi U := by
      ext v; simp only [mem_inter_iff, mem_Ioi, mem_setOf_eq]; constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by linarith, h⟩
    rw [hset]
    have hcalc : ∀ v : ℝ, K * Real.exp (-(6 * π - 6) * (v - U)) =
        (K * Real.exp ((6 * π - 6) * U)) * Real.exp (-(6 * π - 6) * v) := by
      intro v
      rw [show -(6 * π - 6) * (v - U) = (6 * π - 6) * U + -(6 * π - 6) * v by ring, Real.exp_add]
      ring
    simp_rw [hcalc]
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) U]
    have hone : Real.exp ((6 * π - 6) * U) * Real.exp (-(6 * π - 6) * U) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have hne : (-(6 * π - 6)) ≠ 0 := by linarith
    rw [show K * Real.exp ((6 * π - 6) * U) * (-Real.exp (-(6 * π - 6) * U) / -(6 * π - 6)) =
        K * (Real.exp ((6 * π - 6) * U) * Real.exp (-(6 * π - 6) * U)) / (6 * π - 6) by
      field_simp, hone, mul_one]
  calc 2 * ∫ v in Ioi (0 : ℝ), G v ≤ 2 * (K / (6 * π - 6)) := by linarith
    _ = 40 * Mθ * Real.exp π / (6 * π - 6) * Real.exp (6 * U) *
          Real.exp (-π * Real.exp (2 * U)) := by rw [hK]; field_simp; ring

/-! ## The convolution theorem for the Zeta23 transform -/

theorem paperFT_convolution {f g : ℝ → ℂ} {z : ℂ}
    (hf : Integrable (fun x : ℝ => f x * Complex.exp (I * z * x)))
    (hg : Integrable (fun x : ℝ => g x * Complex.exp (I * z * x))) :
    paperFT (convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume) z =
      paperFT f z * paperFT g z := by
  set F : ℝ → ℂ := fun x => f x * Complex.exp (I * z * x) with hF
  set G : ℝ → ℂ := fun x => g x * Complex.exp (I * z * x) with hG
  have hconv : ∀ x : ℝ, convolution F G (ContinuousLinearMap.mul ℝ ℂ) volume x =
      convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume x * Complex.exp (I * z * x) := by
    intro x
    rw [convolution_def, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', hF, hG]
    rw [← integral_mul_const]
    congr 1; funext t
    have e : Complex.exp (I * z * t) * Complex.exp (I * z * ((x - t : ℝ) : ℂ)) =
        Complex.exp (I * z * x) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination (f t * g (x - t)) * e
  unfold paperFT
  have h1 : (fun x : ℝ => convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume x *
      Complex.exp (I * z * x)) = convolution F G (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext x; rw [hconv]
  rw [h1, integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hf hg]
  simp [hF, hG]

/-! ## The smoothing bump and its polar-free second difference -/

/-- A fixed smooth bump: equal to `1` on `[-1/8, 1/8]`, supported in `(-1/4, 1/4)`. -/
def weilBump : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The bump as a complex-valued function. -/
def weilBumpC (u : ℝ) : ℂ := ((weilBump u : ℝ) : ℂ)

theorem contDiff_weilBumpC : ContDiff ℝ 4 weilBumpC :=
  Complex.ofRealCLM.contDiff.comp (weilBump.contDiff (n := 4))

theorem weilBumpC_eq_zero {u : ℝ} (hu : 1 / 4 ≤ |u|) : weilBumpC u = 0 := by
  have h : u ∉ Function.support (weilBump : ℝ → ℝ) := by
    rw [weilBump.support_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hu
  simp only [weilBumpC, Function.notMem_support.mp h, Complex.ofReal_zero]

theorem hasCompactSupport_weilBumpC : HasCompactSupport weilBumpC :=
  hasCompactSupport_of_support_subset_abs (Λ := 1 / 4) fun u hu => by
    by_contra h; push Not at h; exact hu (weilBumpC_eq_zero h.le)

/-- `κ₂ = κ'' - κ/4`: its transform `-(z² + 1/4)κ̂(z)` vanishes at the poles `z = ±i/2`. -/
def weilBumpPolarFree (u : ℝ) : ℂ := deriv (deriv weilBumpC) u - weilBumpC u / 4

theorem contDiff_deriv_deriv_weilBumpC : ContDiff ℝ 2 (deriv (deriv weilBumpC)) := by
  have h3 : ContDiff ℝ 3 (deriv weilBumpC) := contDiff_weilBumpC.deriv'
  exact h3.deriv'

theorem contDiff_weilBumpPolarFree : ContDiff ℝ 2 weilBumpPolarFree :=
  contDiff_deriv_deriv_weilBumpC.sub ((contDiff_weilBumpC.of_le (by norm_num)).div_const 4)

theorem weilBumpPolarFree_eq_zero {u : ℝ} (hu : 1 / 4 < |u|) : weilBumpPolarFree u = 0 := by
  have hts : tsupport weilBumpC ⊆ Metric.closedBall 0 (1 / 4) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro v hv
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra h; push Not at h; exact hv (weilBumpC_eq_zero h.le)
  have hnot : u ∉ tsupport weilBumpC := fun h => by
    have := hts h
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this; linarith
  have hd1 : tsupport (deriv weilBumpC) ⊆ tsupport weilBumpC :=
    closure_minimal (support_deriv_subset) (isClosed_tsupport _)
  have hd2 : deriv (deriv weilBumpC) u = 0 := by
    apply Function.notMem_support.mp
    exact fun h => hnot (hd1 (support_deriv_subset h))
  simp [weilBumpPolarFree, hd2, weilBumpC_eq_zero hu.le]

theorem hasCompactSupport_weilBumpPolarFree : HasCompactSupport weilBumpPolarFree :=
  hasCompactSupport_of_support_subset_abs (Λ := 1 / 2) fun u hu => by
    by_contra h; push Not at h; exact hu (weilBumpPolarFree_eq_zero (by linarith))

theorem paperFT_weilBumpPolarFree (z : ℂ) :
    paperFT weilBumpPolarFree z = -(z ^ 2 + 1 / 4) * paperFT weilBumpC z := by
  have hc2 : ContDiff ℝ 2 weilBumpC := contDiff_weilBumpC.of_le (by norm_num)
  have hdd := paperFT_deriv_deriv hc2 hasCompactSupport_weilBumpC z
  have hi1 : Integrable (fun u : ℝ => deriv (deriv weilBumpC) u * Complex.exp (I * z * u)) :=
    (contDiff_deriv_deriv_weilBumpC.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_weilBumpC.deriv.deriv.mul_right)
  have hi2 : Integrable (fun u : ℝ => weilBumpC u / 4 * Complex.exp (I * z * u)) := by
    refine ((hc2.continuous.div_const 4).mul (by fun_prop)).integrable_of_hasCompactSupport ?_
    refine hasCompactSupport_of_support_subset_abs (Λ := 1 / 4) fun u hu => ?_
    by_contra h; push Not at h; exact hu (by simp [weilBumpC_eq_zero h.le])
  unfold paperFT at hdd ⊢
  simp only [weilBumpPolarFree, sub_mul]
  rw [integral_sub hi1 hi2, hdd]
  have : ∫ u : ℝ, weilBumpC u / 4 * Complex.exp (I * z * u) =
      (∫ u : ℝ, weilBumpC u * Complex.exp (I * z * u)) / 4 := by
    rw [← integral_div]; congr 1; funext u; ring
  rw [this]; ring

theorem paperFT_weilBumpPolarFree_half_I : paperFT weilBumpPolarFree (I / 2) = 0 := by
  rw [paperFT_weilBumpPolarFree]; ring_nf; rw [Complex.I_sq]; ring

theorem paperFT_weilBumpPolarFree_neg_half_I : paperFT weilBumpPolarFree (-(I / 2)) = 0 := by
  rw [paperFT_weilBumpPolarFree]; ring_nf; rw [Complex.I_sq]; ring

/-! ## The truncated radical test -/

/-- The Hodge-class test `f_L = Φ_{≤L-1/4} ⋆ κ₂`: a truncation of Riemann's kernel smoothed by the
polar-free bump. It is `C²`, supported in `[-L, L]`, and its transform vanishes at `±i/2`. -/
def weilRadicalTest (L : ℝ) : ℝ → ℂ :=
  convolution (riemannPhiCore L) weilBumpPolarFree (ContinuousLinearMap.mul ℝ ℂ) volume

theorem integrable_riemannPhiKernel_mul_exp (z : ℂ) :
    Integrable (fun x : ℝ => Φ x * Complex.exp (I * z * x)) := by
  obtain ⟨C, -, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := |z.im| + 1) (by positivity)
  have h := integrable_exp_line_mul continuous_riemannPhiKernel (-z) (C := C)
    (by simpa [abs_neg] using hC)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only; ring_nf

theorem integrable_norm_riemannPhiKernel_mul_exp {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun x : ℝ => ‖Φ x‖ * Real.exp (b * |x|)) := by
  obtain ⟨C, -, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := b + 1) (by positivity)
  refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 1) one_pos).const_mul C)
    (continuous_riemannPhiKernel.norm.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖Φ x‖ * Real.exp (b * |x|) ≤ C * Real.exp (-((b + 1) * |x|)) * Real.exp (b * |x|) :=
        mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le
    _ = C * Real.exp (-1 * |x|) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem integrable_riemannPhiKernel : Integrable Φ := by
  have h := integrable_norm_riemannPhiKernel_mul_exp (b := 0) le_rfl
  refine Integrable.mono' h continuous_riemannPhiKernel.aestronglyMeasurable
    (Eventually.of_forall fun x => by simp)

theorem integrable_riemannPhiCore_mul_exp (L : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => riemannPhiCore L x * Complex.exp (I * z * x)) := by
  have h : (fun x : ℝ => riemannPhiCore L x * Complex.exp (I * z * x)) =
      (Icc (-(L - 1 / 4)) (L - 1 / 4)).indicator (fun x => Φ x * Complex.exp (I * z * x)) := by
    funext x; simp only [riemannPhiCore, indicator]; split_ifs <;> simp
  rw [h]
  exact (integrable_riemannPhiKernel_mul_exp z).indicator measurableSet_Icc

theorem integrable_riemannPhiTail_mul_exp (L : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => riemannPhiTail L x * Complex.exp (I * z * x)) := by
  have h : (fun x : ℝ => riemannPhiTail L x * Complex.exp (I * z * x)) =
      {u : ℝ | L - 1 / 4 < |u|}.indicator (fun x => Φ x * Complex.exp (I * z * x)) := by
    funext x; simp only [riemannPhiTail, indicator]; split_ifs <;> simp
  rw [h]
  exact (integrable_riemannPhiKernel_mul_exp z).indicator (measurableSet_tailSet L)

theorem integrable_riemannPhiCore (L : ℝ) : Integrable (riemannPhiCore L) :=
  integrable_riemannPhiKernel.indicator measurableSet_Icc

theorem integrable_weilBumpPolarFree_mul_exp (z : ℂ) :
    Integrable (fun x : ℝ => weilBumpPolarFree x * Complex.exp (I * z * x)) :=
  (contDiff_weilBumpPolarFree.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
    hasCompactSupport_weilBumpPolarFree.mul_right

theorem paperFT_weilRadicalTest (L : ℝ) (z : ℂ) :
    paperFT (weilRadicalTest L) z = paperFT (riemannPhiCore L) z * paperFT weilBumpPolarFree z :=
  paperFT_convolution (integrable_riemannPhiCore_mul_exp L z)
    (integrable_weilBumpPolarFree_mul_exp z)

theorem contDiff_weilRadicalTest (L : ℝ) : ContDiff ℝ 2 (weilRadicalTest L) :=
  hasCompactSupport_weilBumpPolarFree.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (n := 2) (integrable_riemannPhiCore L).locallyIntegrable contDiff_weilBumpPolarFree

theorem convolution_riemannPhiCore_eq_zero {L x : ℝ} {h : ℝ → ℂ}
    (hh : ∀ u : ℝ, 1 / 4 < |u| → h u = 0) (hx : L < |x|) :
    convolution (riemannPhiCore L) h (ContinuousLinearMap.mul ℝ ℂ) volume x = 0 := by
  rw [convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (riemannPhiCore L t) (h (x - t)) = 0 := by
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    by_cases ht : L - 1 / 4 < |t|
    · have : riemannPhiCore L t = 0 := by
        unfold riemannPhiCore
        refine indicator_of_notMem (fun hm => ?_) _
        have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
      rw [this, zero_mul]
    · push Not at ht
      have hxt : 1 / 4 < |x - t| := by
        have := abs_sub_abs_le_abs_sub x t; linarith
      rw [hh _ hxt, mul_zero]
  simp [this]

theorem weilRadicalTest_eq_zero {L x : ℝ} (hx : L < |x|) : weilRadicalTest L x = 0 :=
  convolution_riemannPhiCore_eq_zero (fun _ hu => weilBumpPolarFree_eq_zero hu) hx

theorem tsupport_weilRadicalTest (L : ℝ) : tsupport (weilRadicalTest L) ⊆ Icc (-L) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ L < |x| := fun h => hx (weilRadicalTest_eq_zero h)
  push Not at h
  exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

theorem paperFT_weilRadicalTest_half_I (L : ℝ) : paperFT (weilRadicalTest L) (I / 2) = 0 := by
  rw [paperFT_weilRadicalTest, paperFT_weilBumpPolarFree_half_I, mul_zero]

theorem paperFT_weilRadicalTest_neg_half_I (L : ℝ) :
    paperFT (weilRadicalTest L) (-(I / 2)) = 0 := by
  rw [paperFT_weilRadicalTest, paperFT_weilBumpPolarFree_neg_half_I, mul_zero]

theorem paperFT_riemannPhiCore_eq (L : ℝ) (z : ℂ) :
    paperFT (riemannPhiCore L) z = riemannPhiTransform (1 / 2 + I * z) -
      paperFT (riemannPhiTail L) z := by
  rw [← paperFT_riemannPhiKernel]
  unfold paperFT
  rw [eq_sub_iff_add_eq, ← integral_add (integrable_riemannPhiCore_mul_exp L z)
    (integrable_riemannPhiTail_mul_exp L z)]
  congr 1; funext x
  rw [← add_mul, riemannPhiCore_add_tail]

/-- At a nontrivial zero both Weil evaluation points see only the tail. -/
theorem paperFT_riemannPhiCore_at_zero {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (L : ℝ) :
    paperFT (riemannPhiCore L) (gammaOf ρ) = -paperFT (riemannPhiTail L) (gammaOf ρ) ∧
      paperFT (riemannPhiCore L) ((starRingEnd ℂ) (gammaOf ρ)) =
        -paperFT (riemannPhiTail L) ((starRingEnd ℂ) (gammaOf ρ)) := by
  have hz : ∀ σ ∈ zetaZeroConfig.carrier, riemannPhiTransform σ = 0 := by
    intro σ hσ
    rw [zetaZeroConfig_carrier] at hσ
    exact riemannPhiTransform_eq_zero_of_nontrivial hσ.1 hσ.2.1 hσ.2.2
  have h1 : 1 / 2 + I * gammaOf ρ = ρ := by
    unfold gammaOf; field_simp; ring
  have h2 : 1 / 2 + I * (starRingEnd ℂ) (gammaOf ρ) = Zeta23.reflect ρ := by
    unfold gammaOf Zeta23.reflect
    apply Complex.ext
    · simp; ring
    · simp
  refine ⟨?_, ?_⟩
  · rw [paperFT_riemannPhiCore_eq, h1, hz ρ hρ, zero_sub]
  · rw [paperFT_riemannPhiCore_eq, h2, hz _ (zetaZeroConfig.reflect_mem ρ hρ), zero_sub]

theorem norm_cexp_I_mul_le_exp {z : ℂ} {b : ℝ} (hz : |z.im| ≤ b) (u : ℝ) :
    ‖Complex.exp (I * z * u)‖ ≤ Real.exp (b * |u|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [Complex.mul_re]
  rw [this]
  calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ b * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)

theorem norm_paperFT_riemannPhiTail_le {L b : ℝ} (hb : 0 ≤ b) {z : ℂ} (hz : |z.im| ≤ b) :
    ‖paperFT (riemannPhiTail L) z‖ ≤ ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (b * |u|) := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) ?_ (Eventually.of_forall fun u => ?_))
  · refine Integrable.mono' (integrable_norm_riemannPhiKernel_mul_exp hb)
      ((show AEStronglyMeasurable (riemannPhiTail L) volume from
        continuous_riemannPhiKernel.aestronglyMeasurable.indicator (measurableSet_tailSet L)).norm.mul
        (by fun_prop : Continuous fun u : ℝ => Real.exp (b * |u|)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      simp only [riemannPhiTail, indicator]; split_ifs <;> simp
  · simp only
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

theorem norm_paperFT_weilBumpPolarFree_le {z : ℂ} (hz : |z.im| ≤ 3 / 2) :
    ‖paperFT weilBumpPolarFree z‖ ≤ Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ := by
  have h := norm_paperFT_le (Λ := 1 / 2)
    (contDiff_weilBumpPolarFree.continuous.integrable_of_hasCompactSupport
      hasCompactSupport_weilBumpPolarFree)
    (fun u hu => by by_contra h; push Not at h; exact hu (weilBumpPolarFree_eq_zero (by linarith)))
    z
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
    (integral_nonneg fun _ => norm_nonneg _))
  nlinarith [abs_nonneg z.im]

/-! ## Size of the test and of its second derivative -/

theorem norm_convolution_riemannPhiCore_le {L : ℝ} {h : ℝ → ℂ} {B : ℝ} (hB : ∀ u, ‖h u‖ ≤ B)
    (x : ℝ) :
    ‖convolution (riemannPhiCore L) h (ContinuousLinearMap.mul ℝ ℂ) volume x‖ ≤
      B * ∫ u : ℝ, ‖Φ u‖ := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine (norm_integral_le_integral_norm _).trans ?_
  have hmaj : ∀ t : ℝ, ‖riemannPhiCore L t * h (x - t)‖ ≤ B * ‖Φ t‖ := by
    intro t
    rw [norm_mul]
    have hc : ‖riemannPhiCore L t‖ ≤ ‖Φ t‖ := by
      unfold riemannPhiCore indicator; split_ifs <;> simp
    calc ‖riemannPhiCore L t‖ * ‖h (x - t)‖ ≤ ‖Φ t‖ * B :=
          mul_le_mul hc (hB _) (norm_nonneg _) (norm_nonneg _)
      _ = B * ‖Φ t‖ := by ring
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (integrable_riemannPhiKernel.norm.const_mul B) (Eventually.of_forall hmaj)

theorem weilBumpPolarFree_tsupport_subset :
    tsupport weilBumpPolarFree ⊆ Metric.closedBall 0 (1 / 4) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro v hv
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h; push Not at h; exact hv (weilBumpPolarFree_eq_zero h)

theorem deriv_deriv_weilBumpPolarFree_eq_zero {u : ℝ} (hu : 1 / 4 < |u|) :
    deriv (deriv weilBumpPolarFree) u = 0 := by
  have hnot : u ∉ tsupport weilBumpPolarFree := fun h => by
    have := weilBumpPolarFree_tsupport_subset h
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this; linarith
  have hd1 : tsupport (deriv weilBumpPolarFree) ⊆ tsupport weilBumpPolarFree :=
    closure_minimal support_deriv_subset (isClosed_tsupport _)
  apply Function.notMem_support.mp
  exact fun h => hnot (hd1 (support_deriv_subset h))

theorem deriv_deriv_weilRadicalTest (L : ℝ) :
    deriv (deriv (weilRadicalTest L)) =
      convolution (riemannPhiCore L) (deriv (deriv weilBumpPolarFree))
        (ContinuousLinearMap.mul ℝ ℂ) volume := by
  have hloc := (integrable_riemannPhiCore L).locallyIntegrable
  have h1 : deriv (weilRadicalTest L) = convolution (riemannPhiCore L) (deriv weilBumpPolarFree)
      (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext x
    exact (hasCompactSupport_weilBumpPolarFree.hasDerivAt_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ) hloc (contDiff_weilBumpPolarFree.of_le (by norm_num)) x).deriv
  rw [h1]
  funext x
  exact (hasCompactSupport_weilBumpPolarFree.deriv.hasDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) hloc contDiff_weilBumpPolarFree.deriv' x).deriv

theorem integral_norm_le_of_abs_support {g : ℝ → ℂ} {L B : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ x, L < |x| → g x = 0) (hB : ∀ x, ‖g x‖ ≤ B) :
    ∫ x : ℝ, ‖g x‖ ≤ 2 * L * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hmaj : ∀ x, ‖g x‖ ≤ (Icc (-L) L).indicator (fun _ => B) x := by
    intro x
    by_cases hx : x ∈ Icc (-L) L
    · rw [indicator_of_mem hx]; exact hB x
    · rw [indicator_of_notMem hx]
      have : L < |x| := by
        by_contra h; push Not at h; exact hx ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
      simp [hsupp x this]
  have hint : Integrable ((Icc (-L) L).indicator (fun _ : ℝ => B)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))
  calc ∫ x : ℝ, ‖g x‖ ≤ ∫ x : ℝ, (Icc (-L) L).indicator (fun _ => B) x :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
          (Eventually.of_forall hmaj)
    _ = 2 * L * B := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith)]; ring

/-- `4(‖f_L‖₁ + ‖f_L''‖₁) ≤ L K₀` for the truncated radical test. -/
theorem exists_weilRadicalTest_norms_le :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ L : ℝ, 0 ≤ L →
      4 * ((∫ u : ℝ, ‖weilRadicalTest L u‖) + ∫ u : ℝ, ‖deriv (deriv (weilRadicalTest L)) u‖)
        ≤ L * K₀ := by
  obtain ⟨B₀, hB₀⟩ := contDiff_weilBumpPolarFree.continuous.bounded_above_of_compact_support
    hasCompactSupport_weilBumpPolarFree
  have hd1 : ContDiff ℝ 1 (deriv weilBumpPolarFree) := contDiff_weilBumpPolarFree.deriv'
  have hd0 : ContDiff ℝ 0 (deriv (deriv weilBumpPolarFree)) := hd1.deriv'
  obtain ⟨B₂, hB₂⟩ := hd0.continuous.bounded_above_of_compact_support
    hasCompactSupport_weilBumpPolarFree.deriv.deriv
  set P : ℝ := ∫ u : ℝ, ‖Φ u‖ with hP
  have hP0 : 0 ≤ P := integral_nonneg fun _ => norm_nonneg _
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0)
  refine ⟨8 * (B₀ + B₂) * P, by positivity, fun L hL => ?_⟩
  have h0 := integral_norm_le_of_abs_support (g := weilRadicalTest L) hL
    (fun x hx => weilRadicalTest_eq_zero hx) (norm_convolution_riemannPhiCore_le hB₀)
  have h2 := integral_norm_le_of_abs_support (g := deriv (deriv (weilRadicalTest L))) hL
    (fun x hx => by
      rw [deriv_deriv_weilRadicalTest]
      exact convolution_riemannPhiCore_eq_zero (fun _ hu => deriv_deriv_weilBumpPolarFree_eq_zero hu) hx)
    (fun x => by rw [deriv_deriv_weilRadicalTest]; exact norm_convolution_riemannPhiCore_le hB₂ x)
  nlinarith

/-! ## The Weil energy of the truncated radical test -/

theorem one_div_one_add_abs_im_sq_le {ρ : ℂ} (hρ : 0 ≤ ρ.re ∧ ρ.re ≤ 1) :
    1 / (1 + |ρ.im|) ^ 2 ≤ (5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))) := by
  have hn : Complex.normSq (gammaOf ρ) ≤ ρ.im ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    nlinarith [hρ.1, hρ.2]
  have h1 : 0 < 1 + Complex.normSq (gammaOf ρ) := by
    have := Complex.normSq_nonneg (gammaOf ρ); linarith
  have h2 : 0 < (1 + |ρ.im|) ^ 2 := by positivity
  rw [one_div_le h2 (by positivity)]
  rw [show (1 : ℝ) / (5 / 4 * (1 / (1 + Complex.normSq (gammaOf ρ)))) =
    (4 / 5) * (1 + Complex.normSq (gammaOf ρ)) by field_simp]
  have : ρ.im ^ 2 = |ρ.im| ^ 2 := (sq_abs _).symm
  nlinarith [abs_nonneg ρ.im]

/-- **Weil energy of the truncated radical test.**  Every Weil summand is a product of a tail
value (small) and a decaying value (from `C²`); summing over the zeros with the unconditional
local count gives
`‖W(f_L,f_L)‖ ≤ (5/4) S_Z · e^{3/4}‖κ₂‖₁ · ε_L · e^{L/2} L K₀`, where
`ε_L = ∫ ‖Φ_{>L-1/4}(u)‖ e^{|u|/2} du`. -/
theorem norm_W_weilRadicalTest_le {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK : ∀ L : ℝ, 0 ≤ L →
      4 * ((∫ u : ℝ, ‖weilRadicalTest L u‖) + ∫ u : ℝ, ‖deriv (deriv (weilRadicalTest L)) u‖)
        ≤ L * K₀)
    {L : ℝ} (hL : 0 ≤ L) :
    ‖zetaZeroConfig.W (weilRadicalTest L) (weilRadicalTest L)‖ ≤
      (5 / 4) * (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) *
      ((Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) *
        (∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|))) *
      (Real.exp (L / 2) * (L * K₀)) := by
  set A : ℝ := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  set ε : ℝ := ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|) with hε
  set D : ℝ := Real.exp (L / 2) * (L * K₀) with hD
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  have hε0 : 0 ≤ ε := integral_nonneg fun _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    have := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using this
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (weilRadicalTest L) (weilRadicalTest L) ρ‖ ≤
        (5 / 4) * (A * ε * D) *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hmem := ρ.2
    have hstrip := zetaZeroConfig.strip ρ hmem
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    obtain ⟨hc1, -⟩ := paperFT_riemannPhiCore_at_zero hmem L
    have hv1 : ‖paperFT (weilRadicalTest L) (gammaOf ρ)‖ ≤ ε * A := by
      rw [paperFT_weilRadicalTest, hc1, norm_mul, norm_neg]
      exact mul_le_mul (norm_paperFT_riemannPhiTail_le (by norm_num) hIm)
        (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hε0
    have hv2 : ‖paperFT (weilRadicalTest L) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        D * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by
      have h := norm_paperFT_le_decay (contDiff_weilRadicalTest L)
        (fun u hu => by
          by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h))
        ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))
      have hre : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
        rw [Complex.conj_re, WeilEF.gammaOf_re]
      rw [hre] at h
      refine h.trans ?_
      have he : Real.exp (|((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| * L) ≤ Real.exp (L / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hden : 0 < (1 + |(ρ : ℂ).im|) ^ 2 := by positivity
      rw [hD, div_eq_mul_one_div, mul_assoc]
      rw [show Real.exp (L / 2) * (L * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) =
        Real.exp (L / 2) * (L * K₀ * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) by ring]
      exact mul_le_mul he (mul_le_mul_of_nonneg_right (hK L hL) (by positivity))
        (by positivity) (Real.exp_pos _).le
    have hq := one_div_one_add_abs_im_sq_le hstrip
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (weilRadicalTest L) (gammaOf ρ)‖ *
          ‖paperFT (weilRadicalTest L) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (ε * A) * (D * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) := by
          gcongr
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (ε * A) *
            (D * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))))) := by
          gcongr
      _ = (5 / 4) * (A * ε * D) *
            ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by ring
  have hsum' : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (weilRadicalTest L) (weilRadicalTest L) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsum.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left]; ring

/-! ## A lower bound for the size of the test -/

/-- Cauchy–Schwarz on `[-L, L]`: `(∫‖f‖)² ≤ 2L ∫‖f‖²` for continuous `f` vanishing off `[-L, L]`. -/
theorem sq_integral_norm_le_of_abs_support {f : ℝ → ℂ} (hf : Continuous f) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ x, L < |x| → f x = 0) :
    (∫ x : ℝ, ‖f x‖) ^ 2 ≤ 2 * L * ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs (Λ := L)
    fun u hu => by by_contra h; push Not at h; exact hu (hsupp u h)
  have hi1 : Integrable (fun x => ‖f x‖) := (hf.integrable_of_hasCompactSupport hcs).norm
  have hcs2 : HasCompactSupport (fun x => ‖f x‖ ^ 2) :=
    hasCompactSupport_of_support_subset_abs (Λ := L)
      fun u hu => by by_contra h; push Not at h; exact hu (by simp [hsupp u h])
  have hi2 : Integrable (fun x => ‖f x‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport hcs2
  have hIcc : ∀ g : ℝ → ℝ, (∀ x, L < |x| → g x = 0) → ∫ x : ℝ, g x = ∫ x in Icc (-L) L, g x := by
    intro g hg
    rw [← integral_indicator measurableSet_Icc]
    congr 1; funext x
    by_cases hx : x ∈ Icc (-L) L
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      exact hg x (by by_contra h; push Not at h; exact hx ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩)
  rw [hIcc _ (fun x hx => by simp [hsupp x hx]), hIcc _ (fun x hx => by simp [hsupp x hx])]
  set P : ℝ := ∫ x in Icc (-L) L, ‖f x‖ with hP
  set Q : ℝ := ∫ x in Icc (-L) L, ‖f x‖ ^ 2 with hQ
  set m : ℝ := P / (2 * L) with hm
  have h0 : 0 ≤ ∫ x in Icc (-L) L, (‖f x‖ - m) ^ 2 := setIntegral_nonneg measurableSet_Icc
    fun _ _ => sq_nonneg _
  have hexp : ∫ x in Icc (-L) L, (‖f x‖ - m) ^ 2 = Q - 2 * m * P + m ^ 2 * (2 * L) := by
    have e : ∀ x : ℝ, (‖f x‖ - m) ^ 2 = ‖f x‖ ^ 2 - 2 * m * ‖f x‖ + m ^ 2 := fun x => by ring
    simp_rw [e]
    rw [integral_add, integral_sub, integral_const_mul, setIntegral_const]
    · simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith)]; ring
    · exact hi2.integrableOn
    · exact (hi1.const_mul _).integrableOn
    · exact (hi2.integrableOn.sub (hi1.const_mul _).integrableOn)
    · exact integrableOn_const (by simp) (by simp)
  rw [hexp] at h0
  have hL2 : 0 < 2 * L := by linarith
  have hmP : m * (2 * L) = P := by rw [hm]; field_simp
  nlinarith [sq_nonneg P, sq_nonneg m]

theorem paperFT_weilBumpC_three_halves :
    paperFT weilBumpC (-(3 / 2 * I)) =
      ((∫ u : ℝ, weilBump u * Real.exp (3 / 2 * u) : ℝ) : ℂ) := by
  unfold paperFT weilBumpC
  rw [← integral_complex_ofReal]
  congr 1; funext u
  push_cast
  congr 1; congr 1; ring_nf; rw [Complex.I_sq]; ring

theorem integral_weilBump_mul_exp_ge :
    Real.exp (-(3 / 16)) / 4 ≤ ∫ u : ℝ, weilBump u * Real.exp (3 / 2 * u) := by
  have hint : Integrable (fun u : ℝ => weilBump u * Real.exp (3 / 2 * u)) :=
    ((weilBump.contDiff (n := 0)).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      weilBump.hasCompactSupport.mul_right
  have hnn : 0 ≤ᵐ[volume] (fun u : ℝ => weilBump u * Real.exp (3 / 2 * u)) :=
    Eventually.of_forall fun u => mul_nonneg weilBump.nonneg (Real.exp_pos _).le
  refine le_trans ?_ (setIntegral_le_integral (s := Icc (-(1 / 8)) (1 / 8)) hint hnn)
  have hlow : ∀ u ∈ Icc (-(1 / 8) : ℝ) (1 / 8), Real.exp (-(3 / 16)) ≤
      weilBump u * Real.exp (3 / 2 * u) := by
    intro u hu
    have h1 : weilBump u = 1 := weilBump.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      change |u| ≤ 1 / 8
      exact abs_le.mpr ⟨hu.1, hu.2⟩)
    rw [h1, one_mul]; exact Real.exp_le_exp.mpr (by linarith [hu.1])
  calc Real.exp (-(3 / 16)) / 4 = ∫ u in Icc (-(1 / 8) : ℝ) (1 / 8), Real.exp (-(3 / 16)) := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by norm_num)]; ring
    _ ≤ ∫ u in Icc (-(1 / 8) : ℝ) (1 / 8), weilBump u * Real.exp (3 / 2 * u) :=
        setIntegral_mono_on (integrableOn_const (by simp) (by simp)) hint.integrableOn
          measurableSet_Icc hlow

theorem norm_paperFT_weilBumpPolarFree_three_halves_ge :
    Real.exp (-(3 / 16)) / 2 ≤ ‖paperFT weilBumpPolarFree (-(3 / 2 * I))‖ := by
  rw [paperFT_weilBumpPolarFree, paperFT_weilBumpC_three_halves]
  have hz : -((-(3 / 2 * I)) ^ 2 + 1 / 4) = (2 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  have h := integral_weilBump_mul_exp_ge
  have hpos : 0 ≤ ∫ u : ℝ, weilBump u * Real.exp (3 / 2 * u) :=
    le_trans (by positivity) h
  rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos,
    Complex.norm_ofNat]
  linarith

/-! ## The super-exponential margin law -/

theorem riemannPhiTail_bound_le (E₀ C₆ : ℝ) (hE₀ : E₀ = 40 * Mθ * Real.exp π / (6 * π - 6))
    (hC₆ : ∀ x : ℝ, 0 ≤ x → Real.exp (6 * x) * (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) *
      Real.exp (-π * Real.exp (2 * x)) ≤ C₆ * Real.exp (-x))
    {L b : ℝ} (hL : 1 ≤ L) (hb : b ≤ 3 / 2) :
    ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (b * |u|) ≤ E₀ * C₆ * Real.exp (-(L - 1 / 4)) := by
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
  have hE0 : 0 ≤ E₀ := by rw [hE₀]; positivity
  have h1 := integral_norm_riemannPhiTail_mul_exp_le (b := b) hL hb
  rw [← hE₀] at h1
  refine h1.trans ?_
  have h2 := hC₆ (L - 1 / 4) (by linarith)
  have hpoly : 1 ≤ 1 + Real.exp (2 * (L - 1 / 4)) + Real.exp (2 * (L - 1 / 4)) ^ 2 := by
    have := Real.exp_pos (2 * (L - 1 / 4)); nlinarith [sq_nonneg (Real.exp (2 * (L - 1 / 4)))]
  have h3 : Real.exp (6 * (L - 1 / 4)) * Real.exp (-π * Real.exp (2 * (L - 1 / 4))) ≤
      C₆ * Real.exp (-(L - 1 / 4)) := by
    refine le_trans ?_ h2
    have hp : 0 ≤ Real.exp (6 * (L - 1 / 4)) * Real.exp (-π * Real.exp (2 * (L - 1 / 4))) :=
      by positivity
    nlinarith
  calc E₀ * Real.exp (6 * (L - 1 / 4)) * Real.exp (-π * Real.exp (2 * (L - 1 / 4)))
      = E₀ * (Real.exp (6 * (L - 1 / 4)) * Real.exp (-π * Real.exp (2 * (L - 1 / 4)))) := by ring
    _ ≤ E₀ * (C₆ * Real.exp (-(L - 1 / 4))) := mul_le_mul_of_nonneg_left h3 hE0
    _ = E₀ * C₆ * Real.exp (-(L - 1 / 4)) := by ring

/-- The mass of the test at the evaluation point `z₀ = -(3/2)i`, where `Φ̂(z₀) = ξ(2)`. -/
theorem weilRadicalTest_mass_ge {L : ℝ}
    (hsmall : ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (3 / 2 * |u|) ≤
      ‖riemannPhiTransform 2‖ / 2) :
    ‖riemannPhiTransform 2‖ / 2 * (Real.exp (-(3 / 16)) / 2) ≤
      Real.exp (3 / 2 * L) * ∫ u : ℝ, ‖weilRadicalTest L u‖ := by
  have hz₀ : (1 / 2 : ℂ) + I * (-(3 / 2 * I)) = 2 := by ring_nf; rw [Complex.I_sq]; ring
  have hcore : ‖riemannPhiTransform 2‖ / 2 ≤ ‖paperFT (riemannPhiCore L) (-(3 / 2 * I))‖ := by
    rw [paperFT_riemannPhiCore_eq, hz₀]
    have ht := norm_paperFT_riemannPhiTail_le (L := L) (b := 3 / 2) (by norm_num)
      (z := -(3 / 2 * I)) (by simp; norm_num)
    have h1 := norm_sub_norm_le (riemannPhiTransform 2) (paperFT (riemannPhiTail L) (-(3 / 2 * I)))
    linarith
  have hκ := norm_paperFT_weilBumpPolarFree_three_halves_ge
  have hval : ‖riemannPhiTransform 2‖ / 2 * (Real.exp (-(3 / 16)) / 2) ≤
      ‖paperFT (weilRadicalTest L) (-(3 / 2 * I))‖ := by
    rw [paperFT_weilRadicalTest, norm_mul]
    exact mul_le_mul hcore hκ (by positivity) (norm_nonneg _)
  have hup := norm_paperFT_le (Λ := L)
    ((contDiff_weilRadicalTest L).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (Λ := L) fun u hu => by
        by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h)))
    (fun u hu => by by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h))
    (-(3 / 2 * I))
  have him : |(-(3 / 2 * I)).im| = 3 / 2 := by simp; norm_num
  rw [him] at hup
  linarith

/-- Arithmetic of the margin: combine the energy bound, the tail bound and the mass bound. -/
theorem weilMargin_arith {W N1 N2 L S A ε K₀ E₀ X c₁ : ℝ} (hL : 1 ≤ L) (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hK₀ : 0 ≤ K₀) (hE₀ : 0 ≤ E₀) (hX : 0 ≤ X) (hc₁ : 0 < c₁)
    (hW : W ≤ 5 / 4 * S * (A * ε) * (Real.exp (L / 2) * (L * K₀)))
    (hε : ε ≤ E₀ * Real.exp (6 * L) * X)
    (hmass : c₁ ≤ Real.exp (3 / 2 * L) * N1) (hcs : N1 ^ 2 ≤ 2 * L * N2) :
    0 < N2 ∧ W ≤ (5 / 2 * S * A * K₀ * E₀ / c₁ ^ 2 + 1) * Real.exp (12 * L) * X * N2 := by
  have hLpos : 0 < L := by linarith
  have hE := Real.exp_pos (3 / 2 * L)
  have h3L : Real.exp (3 * L) = Real.exp (3 / 2 * L) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hc2 : c₁ ^ 2 ≤ 2 * L * Real.exp (3 * L) * N2 := by
    have hsq : c₁ ^ 2 ≤ (Real.exp (3 / 2 * L) * N1) ^ 2 := pow_le_pow_left₀ hc₁.le hmass 2
    rw [h3L]; nlinarith [sq_nonneg N1]
  have hN2 : 0 < N2 := by
    by_contra h; push Not at h
    have : 2 * L * Real.exp (3 * L) * N2 ≤ 0 := by
      have : 0 ≤ 2 * L * Real.exp (3 * L) := by positivity
      nlinarith
    nlinarith [sq_pos_of_pos hc₁]
  refine ⟨hN2, ?_⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 5 / 2 * S * A * K₀ * E₀ := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hε0 : 0 ≤ ε ∨ ε < 0 := le_or_gt 0 ε
  have hLe : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hL2 : L ^ 2 ≤ Real.exp (2 * L) := by
    rw [show Real.exp (2 * L) = Real.exp L ^ 2 by rw [← Real.exp_nat_mul]; push_cast; ring]
    exact pow_le_pow_left₀ hLpos.le hLe 2
  -- W ≤ (5/4) S A K₀ E₀ L e^{13L/2} X
  have hW' : W ≤ 5 / 4 * S * A * K₀ * E₀ * L * Real.exp (L / 2 + 6 * L) * X := by
    rcases hε0 with h0 | h0
    · refine hW.trans ?_
      have hAε : A * ε ≤ A * (E₀ * Real.exp (6 * L) * X) := mul_le_mul_of_nonneg_left hε hA
      rw [Real.exp_add]
      have : 0 ≤ 5 / 4 * S * (Real.exp (L / 2) * (L * K₀)) := by positivity
      nlinarith
    · have : 5 / 4 * S * (A * ε) * (Real.exp (L / 2) * (L * K₀)) ≤ 0 := by
        have : A * ε ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA h0.le
        have h2 : 0 ≤ 5 / 4 * S * (Real.exp (L / 2) * (L * K₀)) := by positivity
        nlinarith
      have : 0 ≤ 5 / 4 * S * A * K₀ * E₀ * L * Real.exp (L / 2 + 6 * L) * X := by positivity
      linarith
  -- 1 ≤ 2 L e^{3L} N2 / c₁²
  have hratio : 1 ≤ 2 * L * Real.exp (3 * L) * N2 / c₁ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hfinal : 5 / 4 * S * A * K₀ * E₀ * L * Real.exp (L / 2 + 6 * L) * X ≤
      (5 / 2 * S * A * K₀ * E₀ / c₁ ^ 2 + 1) * Real.exp (12 * L) * X * N2 := by
    have hmid : 5 / 4 * S * A * K₀ * E₀ * L * Real.exp (L / 2 + 6 * L) * X ≤
        5 / 4 * S * A * K₀ * E₀ * L * Real.exp (L / 2 + 6 * L) * X *
          (2 * L * Real.exp (3 * L) * N2 / c₁ ^ 2) := by
      have : 0 ≤ 5 / 4 * S * A * K₀ * E₀ * L * Real.exp (L / 2 + 6 * L) * X := by positivity
      nlinarith
    refine hmid.trans ?_
    have hexps : L * L * Real.exp (L / 2 + 6 * L) * Real.exp (3 * L) ≤ Real.exp (12 * L) := by
      have : L * L * (Real.exp (L / 2 + 6 * L) * Real.exp (3 * L)) ≤
          Real.exp (2 * L) * (Real.exp (L / 2 + 6 * L) * Real.exp (3 * L)) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      rw [← Real.exp_add, ← Real.exp_add] at this
      calc L * L * Real.exp (L / 2 + 6 * L) * Real.exp (3 * L)
          = L * L * (Real.exp (L / 2 + 6 * L) * Real.exp (3 * L)) := by ring
        _ ≤ _ := by rw [← Real.exp_add]; exact this
        _ ≤ Real.exp (12 * L) := Real.exp_le_exp.mpr (by linarith)
    have hc₁2 : 0 < c₁ ^ 2 := by positivity
    have hXN : 0 ≤ X * N2 := mul_nonneg hX hN2.le
    calc 5 / 4 * S * A * K₀ * E₀ * L * Real.exp (L / 2 + 6 * L) * X *
          (2 * L * Real.exp (3 * L) * N2 / c₁ ^ 2)
        = (5 / 2 * S * A * K₀ * E₀ / c₁ ^ 2) *
            (L * L * Real.exp (L / 2 + 6 * L) * Real.exp (3 * L)) * (X * N2) := by
          field_simp; ring
      _ ≤ (5 / 2 * S * A * K₀ * E₀ / c₁ ^ 2) * Real.exp (12 * L) * (X * N2) := by
          gcongr
      _ ≤ (5 / 2 * S * A * K₀ * E₀ / c₁ ^ 2 + 1) * Real.exp (12 * L) * (X * N2) := by
          gcongr; linarith
      _ = _ := by ring
  exact hW'.trans hfinal

/-- **No-slack margin law for the Weil and Hodge forms of `ζ` (unconditional).**
For all large `L` there is a `C²` test supported in `[-L, L]` whose transform vanishes at `±i/2`
(so it lies in the Hodge class) and whose Weil energy is super-exponentially small:
`‖W(f,f)‖ ≤ C e^{12L} e^{-π e^{2L - 1/2}} ‖f‖₂²`.  Consequently the level-`L` ground energy of
the Weil form, and of its polar-constrained Hodge restriction, is at most
`C e^{12L - π e^{2L-1/2}}`, whether or not the Riemann hypothesis holds.  The test is a
truncation of Riemann's kernel, which lies in the radical of the Weil form. -/
theorem zeta_weil_margin_superexponential :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ f : ℝ → ℂ,
      ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ 0 < ∫ x : ℝ, ‖f x‖ ^ 2 ∧
      ‖zetaZeroConfig.W f f‖ ≤
        C * Real.exp (12 * L) * Real.exp (-π * Real.exp (2 * L - 1 / 2)) *
          ∫ x : ℝ, ‖f x‖ ^ 2 := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = 40 * Mθ * Real.exp π / (6 * π - 6) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E₀ := by rw [hE₀]; positivity
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]; exact tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]; exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ₂ : ℝ, γ₂ = ‖riemannPhiTransform 2‖ := ⟨_, rfl⟩
  have hγ₂0 : 0 < γ₂ := by rw [hγ₂]; exact norm_pos_iff.mpr riemannPhiTransform_two_ne_zero
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = γ₂ / 2 * (Real.exp (-(3 / 16)) / 2) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  have hX0 : 0 ≤ 2 * E₀ * C₆ / γ₂ := by positivity
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = 1 + Real.log (2 * E₀ * C₆ / γ₂ + 1) := ⟨_, rfl⟩
  have hlog0 : 0 ≤ Real.log (2 * E₀ * C₆ / γ₂ + 1) := Real.log_nonneg (by linarith)
  refine ⟨5 / 2 * S * A * K₀ * E₀ / c₁ ^ 2 + 1, L₀, by positivity, by rw [hL₀]; linarith,
    fun L hL => ?_⟩
  have hL1 : 1 ≤ L := by rw [hL₀] at hL; linarith
  have hLpos : 0 < L := by linarith
  refine ⟨weilRadicalTest L, contDiff_weilRadicalTest L, tsupport_weilRadicalTest L,
    paperFT_weilRadicalTest_half_I L, paperFT_weilRadicalTest_neg_half_I L, ?_⟩
  -- smallness of the tail at the evaluation point
  have hexpL : 2 * E₀ * C₆ / γ₂ + 1 ≤ Real.exp (L - 1 / 4) := by
    have hle : Real.log (2 * E₀ * C₆ / γ₂ + 1) ≤ L - 1 / 4 := by rw [hL₀] at hL; linarith
    calc 2 * E₀ * C₆ / γ₂ + 1 = Real.exp (Real.log (2 * E₀ * C₆ / γ₂ + 1)) :=
          (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (L - 1 / 4) := Real.exp_le_exp.mpr hle
  have htail_small : E₀ * C₆ * Real.exp (-(L - 1 / 4)) ≤ γ₂ / 2 := by
    have he := Real.exp_pos (L - 1 / 4)
    have hinv : Real.exp (-(L - 1 / 4)) * Real.exp (L - 1 / 4) = 1 := by
      rw [← Real.exp_add]; simp
    have h2 : 2 * E₀ * C₆ ≤ γ₂ * Real.exp (L - 1 / 4) := by
      have := mul_le_mul_of_nonneg_left hexpL hγ₂0.le
      rw [mul_add, mul_div_cancel₀ _ hγ₂0.ne'] at this
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(L - 1 / 4))).le]
  have hsmall := (riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hL1 (b := 3 / 2) le_rfl).trans
    htail_small
  rw [hγ₂] at hsmall
  have hmass := weilRadicalTest_mass_ge hsmall
  rw [← hγ₂, ← hc₁] at hmass
  have hcs := sq_integral_norm_le_of_abs_support (f := weilRadicalTest L) (contDiff_weilRadicalTest L).continuous
    hLpos (fun x hx => weilRadicalTest_eq_zero hx)
  have hW := norm_W_weilRadicalTest_le hK₀ hK (L := L) hLpos.le
  rw [← hS, ← hA] at hW
  have hε : ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|) ≤
      E₀ * Real.exp (6 * L) * Real.exp (-π * Real.exp (2 * L - 1 / 2)) := by
    have h1 := integral_norm_riemannPhiTail_mul_exp_le (b := 1 / 2) hL1 (by norm_num)
    rw [← hE₀] at h1
    refine h1.trans ?_
    rw [show 2 * (L - 1 / 4) = 2 * L - 1 / 2 by ring]
    have : Real.exp (6 * (L - 1 / 4)) ≤ Real.exp (6 * L) := Real.exp_le_exp.mpr (by linarith)
    gcongr
  have := weilMargin_arith hL1 hS0 hA0 hK₀ hE0 (Real.exp_pos _).le hc₁0 hW hε hmass hcs
  exact this

end

end RHTower
