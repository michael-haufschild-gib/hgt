import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion
import GaloisForLFunctions.RHTower.CCMMetaplecticGammaMomentSeries


/-!
# The modulated radical test

Modulating the polar-free smoothing bump moves the radical test to any frequency `ω` while keeping it
in the radical and in the Hodge class.  With `κ_ω(u) = e^{-iωu}κ(u)` and
`κ₂,ω = κ_ω'' - κ_ω/4`, the test `f_{L,ω} = Φ_{≤L-1/4} ⋆ κ₂,ω` is `C²`, supported in `[-L, L]`, has
`f̂(±i/2) = 0`, and has transform `Φ̂_core(z)·(-(z² + 1/4))·κ̂(z - ω)`.

* `norm_W_modRadicalTest_le`: at every zero both evaluation points see only the tail of `Φ`, so
  `‖W(f_{L,ω}, f_{L,ω})‖ ≤ ε_L² C_κ² (1+|ω|)⁴ · 24 A₀ log(|ω|+3)`, with
  `ε_L = ∫|Φ_{>L-1/4}| e^{|u|/2} = O(e^{6L} e^{-π e^{2L-1/2}})`.
* `norm_paperFT_modRadicalTest_real_ge`: on the real line within `1/2` of `ω`,
  `|f̂_{L,ω}(τ)| ≥ (|Ξ(τ)| - ε_L)(τ² + 1/4) cos(1/8) ∫κ`.
* `norm_riemannPhiTransform_line_ge`: `|Ξ(τ)| ≥ c_Ξ τ² e^{-πτ/2} exp(-(3/2) C log τ/δ)` when every
  zero ordinate is at distance `≥ δ` from `τ ≥ 4`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Bottcher Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## The modulated polar-free bump -/

/-- The bump modulated to frequency `ω`: `κ_ω(u) = e^{-iωu} κ(u)`. -/
def modBump (ω : ℝ) (u : ℝ) : ℂ := cexp (-(I * ω * u)) * weilBumpC u

theorem contDiff_modBump (ω : ℝ) : ContDiff ℝ 4 (modBump ω) := by
  unfold modBump
  refine ContDiff.mul ?_ contDiff_weilBumpC
  have : ContDiff ℝ 4 (fun u : ℝ => -(I * (ω : ℂ) * (u : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
  exact Complex.contDiff_exp.comp this

theorem modBump_eq_zero {ω u : ℝ} (hu : 1 / 4 ≤ |u|) : modBump ω u = 0 := by
  simp [modBump, weilBumpC_eq_zero hu]

theorem hasCompactSupport_modBump (ω : ℝ) : HasCompactSupport (modBump ω) :=
  hasCompactSupport_of_support_subset_abs (Λ := 1 / 4) fun u hu => by
    by_contra h; push Not at h; exact hu (modBump_eq_zero h.le)

/-- `κ₂,ω = κ_ω'' - κ_ω/4`: transform `-(z² + 1/4) κ̂(z - ω)`, vanishing at `z = ±i/2`. -/
def modBumpPolarFree (ω : ℝ) (u : ℝ) : ℂ := deriv (deriv (modBump ω)) u - modBump ω u / 4

theorem contDiff_deriv_deriv_modBump (ω : ℝ) : ContDiff ℝ 2 (deriv (deriv (modBump ω))) := by
  have h3 : ContDiff ℝ 3 (deriv (modBump ω)) := (contDiff_modBump ω).deriv'
  exact h3.deriv'

theorem contDiff_modBumpPolarFree (ω : ℝ) : ContDiff ℝ 2 (modBumpPolarFree ω) :=
  (contDiff_deriv_deriv_modBump ω).sub (((contDiff_modBump ω).of_le (by norm_num)).div_const 4)

theorem tsupport_modBump_subset (ω : ℝ) : tsupport (modBump ω) ⊆ Metric.closedBall 0 (1 / 4) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro v hv
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h; push Not at h; exact hv (modBump_eq_zero h.le)

theorem modBumpPolarFree_eq_zero {ω u : ℝ} (hu : 1 / 4 < |u|) : modBumpPolarFree ω u = 0 := by
  have hnot : u ∉ tsupport (modBump ω) := fun h => by
    have := tsupport_modBump_subset ω h
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this; linarith
  have hd1 : tsupport (deriv (modBump ω)) ⊆ tsupport (modBump ω) :=
    closure_minimal (support_deriv_subset) (isClosed_tsupport _)
  have hd2 : deriv (deriv (modBump ω)) u = 0 := by
    apply Function.notMem_support.mp
    exact fun h => hnot (hd1 (support_deriv_subset h))
  simp [modBumpPolarFree, hd2, modBump_eq_zero hu.le]

theorem hasCompactSupport_modBumpPolarFree (ω : ℝ) : HasCompactSupport (modBumpPolarFree ω) :=
  hasCompactSupport_of_support_subset_abs (Λ := 1 / 2) fun u hu => by
    by_contra h; push Not at h; exact hu (modBumpPolarFree_eq_zero (by linarith))

theorem paperFT_modBump (ω : ℝ) (z : ℂ) : paperFT (modBump ω) z = paperFT weilBumpC (z - ω) :=
  paperFT_modulate weilBumpC ω z

theorem paperFT_modBumpPolarFree (ω : ℝ) (z : ℂ) :
    paperFT (modBumpPolarFree ω) z = -(z ^ 2 + 1 / 4) * paperFT weilBumpC (z - ω) := by
  have hc2 : ContDiff ℝ 2 (modBump ω) := (contDiff_modBump ω).of_le (by norm_num)
  have hdd := paperFT_deriv_deriv hc2 (hasCompactSupport_modBump ω) z
  have hi1 : Integrable (fun u : ℝ => deriv (deriv (modBump ω)) u * Complex.exp (I * z * u)) :=
    ((contDiff_deriv_deriv_modBump ω).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hasCompactSupport_modBump ω).deriv.deriv.mul_right)
  have hi2 : Integrable (fun u : ℝ => modBump ω u / 4 * Complex.exp (I * z * u)) := by
    refine ((hc2.continuous.div_const 4).mul (by fun_prop)).integrable_of_hasCompactSupport ?_
    refine hasCompactSupport_of_support_subset_abs (Λ := 1 / 4) fun u hu => ?_
    by_contra h; push Not at h; exact hu (by simp [modBump_eq_zero h.le])
  have hdd' : paperFT (deriv (deriv (modBump ω))) z = -(z ^ 2) * paperFT (modBump ω) z := by
    rw [hdd]
  unfold paperFT at hdd' ⊢
  simp only [modBumpPolarFree, sub_mul]
  rw [integral_sub hi1 hi2, hdd']
  have : ∫ u : ℝ, modBump ω u / 4 * Complex.exp (I * z * u) =
      (∫ u : ℝ, modBump ω u * Complex.exp (I * z * u)) / 4 := by
    rw [← integral_div]; congr 1; funext u; ring
  rw [this]
  have hm := paperFT_modBump ω z
  unfold paperFT at hm
  rw [hm]; ring

theorem paperFT_modBumpPolarFree_half_I (ω : ℝ) : paperFT (modBumpPolarFree ω) (I / 2) = 0 := by
  rw [paperFT_modBumpPolarFree]; ring_nf; rw [Complex.I_sq]; ring

theorem paperFT_modBumpPolarFree_neg_half_I (ω : ℝ) :
    paperFT (modBumpPolarFree ω) (-(I / 2)) = 0 := by
  rw [paperFT_modBumpPolarFree]; ring_nf; rw [Complex.I_sq]; ring


/-! ## The modulated radical test -/

/-- `f_{L,ω} = Φ_{≤L-1/4} ⋆ κ₂,ω`: `C²`, supported in `[-L, L]`, polar-free, with transform
`Φ̂_core(z) · (-(z² + 1/4)) κ̂(z - ω)`. -/
def modRadicalTest (L ω : ℝ) : ℝ → ℂ :=
  convolution (riemannPhiCore L) (modBumpPolarFree ω) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem integrable_modBumpPolarFree_mul_exp (ω : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => modBumpPolarFree ω x * Complex.exp (I * z * x)) :=
  ((contDiff_modBumpPolarFree ω).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
    (hasCompactSupport_modBumpPolarFree ω).mul_right

theorem paperFT_modRadicalTest (L ω : ℝ) (z : ℂ) :
    paperFT (modRadicalTest L ω) z =
      paperFT (riemannPhiCore L) z * paperFT (modBumpPolarFree ω) z :=
  paperFT_convolution (integrable_riemannPhiCore_mul_exp L z)
    (integrable_modBumpPolarFree_mul_exp ω z)

theorem contDiff_modRadicalTest (L ω : ℝ) : ContDiff ℝ 2 (modRadicalTest L ω) :=
  (hasCompactSupport_modBumpPolarFree ω).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (n := 2) (integrable_riemannPhiCore L).locallyIntegrable (contDiff_modBumpPolarFree ω)

theorem modRadicalTest_eq_zero {L ω x : ℝ} (hx : L < |x|) : modRadicalTest L ω x = 0 :=
  convolution_riemannPhiCore_eq_zero (fun _ hu => modBumpPolarFree_eq_zero hu) hx

theorem tsupport_modRadicalTest (L ω : ℝ) : tsupport (modRadicalTest L ω) ⊆ Icc (-L) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ L < |x| := fun h => hx (modRadicalTest_eq_zero h)
  push Not at h
  exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

theorem paperFT_modRadicalTest_half_I (L ω : ℝ) : paperFT (modRadicalTest L ω) (I / 2) = 0 := by
  rw [paperFT_modRadicalTest, paperFT_modBumpPolarFree_half_I, mul_zero]

theorem paperFT_modRadicalTest_neg_half_I (L ω : ℝ) :
    paperFT (modRadicalTest L ω) (-(I / 2)) = 0 := by
  rw [paperFT_modRadicalTest, paperFT_modBumpPolarFree_neg_half_I, mul_zero]

/-! ## Fourth-order decay of the bump transform -/

/-- The bump constant `C_κ = 8 e^{1/8} (N₀ + 2 N₂ + N₄)`, `N_j` the `L¹` norms of the derivatives. -/
def bumpDecayConst : ℝ :=
  8 * Real.exp (1 / 8) * ((∫ u, ‖weilBumpC u‖) + 2 * (∫ u, ‖deriv (deriv weilBumpC) u‖) +
    ∫ u, ‖deriv (deriv (deriv (deriv weilBumpC))) u‖)

theorem bumpDecayConst_nonneg : 0 ≤ bumpDecayConst := by
  unfold bumpDecayConst
  have h1 : 0 ≤ ∫ u, ‖weilBumpC u‖ := integral_nonneg fun _ => norm_nonneg _
  have h2 : 0 ≤ ∫ u, ‖deriv (deriv weilBumpC) u‖ := integral_nonneg fun _ => norm_nonneg _
  have h3 : 0 ≤ ∫ u, ‖deriv (deriv (deriv (deriv weilBumpC))) u‖ :=
    integral_nonneg fun _ => norm_nonneg _
  positivity

/-- In the strip `|Im w| ≤ 1/2`: `|κ̂(w)| ≤ C_κ / (1 + |Re w|)^4`. -/
theorem norm_paperFT_weilBumpC_le {w : ℂ} (hw : |w.im| ≤ 1 / 2) :
    ‖paperFT weilBumpC w‖ ≤ bumpDecayConst / (1 + |w.re|) ^ 4 := by
  have hsupp : ∀ u, weilBumpC u ≠ 0 → |u| ≤ 1 / 4 := fun u hu => by
    by_contra h; push Not at h; exact hu (weilBumpC_eq_zero h.le)
  have hc2 : ContDiff ℝ 2 weilBumpC := contDiff_weilBumpC.of_le (by norm_num)
  have hdd2 : ContDiff ℝ 2 (deriv (deriv weilBumpC)) := by
    have h3 : ContDiff ℝ 3 (deriv weilBumpC) := contDiff_weilBumpC.deriv'
    exact h3.deriv'
  have hts : tsupport weilBumpC ⊆ Metric.closedBall 0 (1 / 4) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro v hv
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra h'; push Not at h'; exact hv (weilBumpC_eq_zero h'.le)
  have hsupp2 : ∀ u, deriv (deriv weilBumpC) u ≠ 0 → |u| ≤ 1 / 4 := by
    intro u hu
    by_contra h; push Not at h
    have hnot : u ∉ tsupport weilBumpC := fun ht => by
      have := hts ht
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this; linarith
    have hd1 : tsupport (deriv weilBumpC) ⊆ tsupport weilBumpC :=
      closure_minimal (support_deriv_subset) (isClosed_tsupport _)
    exact hu (Function.notMem_support.mp fun h' => hnot (hd1 (support_deriv_subset h')))
  have hE : Real.exp (|w.im| * (1 / 4)) ≤ Real.exp (1 / 8) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.im])
  have hA := norm_paperFT_le_decay hc2 hsupp w
  have hB := norm_paperFT_le_decay hdd2 hsupp2 w
  have hdd := paperFT_deriv_deriv hc2 hasCompactSupport_weilBumpC w
  rw [hdd, norm_mul, norm_neg, norm_pow] at hB
  set N₀ := ∫ u, ‖weilBumpC u‖
  set N₂ := ∫ u, ‖deriv (deriv weilBumpC) u‖
  set N₄ := ∫ u, ‖deriv (deriv (deriv (deriv weilBumpC))) u‖
  have hN₀ : 0 ≤ N₀ := integral_nonneg fun _ => norm_nonneg _
  have hN₂ : 0 ≤ N₂ := integral_nonneg fun _ => norm_nonneg _
  have hN₄ : 0 ≤ N₄ := integral_nonneg fun _ => norm_nonneg _
  set F := ‖paperFT weilBumpC w‖
  have hF0 : 0 ≤ F := norm_nonneg _
  set r := |w.re|
  have hr0 : 0 ≤ r := abs_nonneg _
  have hre : r ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hden : 0 < (1 + r) ^ 2 := by positivity
  have hA' : F * (1 + r) ^ 2 ≤ Real.exp (1 / 8) * (4 * (N₀ + N₂)) := by
    have := (le_div_iff₀ hden).mp hA
    calc F * (1 + r) ^ 2 ≤ Real.exp (|w.im| * (1 / 4)) * (4 * (N₀ + N₂)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_right hE (by positivity)
  have hB' : ‖w‖ ^ 2 * F * (1 + r) ^ 2 ≤ Real.exp (1 / 8) * (4 * (N₂ + N₄)) := by
    have := (le_div_iff₀ hden).mp hB
    calc ‖w‖ ^ 2 * F * (1 + r) ^ 2 ≤ Real.exp (|w.im| * (1 / 4)) * (4 * (N₂ + N₄)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_right hE (by positivity)
  have hsum : (1 + ‖w‖ ^ 2) * F * (1 + r) ^ 2 ≤
      Real.exp (1 / 8) * (4 * (N₀ + 2 * N₂ + N₄)) := by nlinarith
  have hsq : (1 + r) ^ 2 ≤ 2 * (1 + ‖w‖ ^ 2) := by
    nlinarith [sq_nonneg (r - 1), mul_le_mul hre hre hr0 (norm_nonneg w)]
  rw [le_div_iff₀ (by positivity)]
  have hstep : F * (1 + r) ^ 4 ≤ 2 * ((1 + ‖w‖ ^ 2) * F * (1 + r) ^ 2) := by
    have e : F * (1 + r) ^ 4 = F * (1 + r) ^ 2 * (1 + r) ^ 2 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsq (mul_nonneg hF0 hden.le)
    nlinarith
  calc F * (1 + r) ^ 4 ≤ 2 * ((1 + ‖w‖ ^ 2) * F * (1 + r) ^ 2) := hstep
    _ ≤ 2 * (Real.exp (1 / 8) * (4 * (N₀ + 2 * N₂ + N₄))) := by linarith
    _ = bumpDecayConst := by unfold bumpDecayConst; ring


/-! ## Weil energy of the modulated radical test -/

theorem one_add_abs_le_mul (γ ω : ℝ) : 1 + |γ| ≤ (1 + |ω|) * (1 + |γ - ω|) := by
  have h := abs_sub_abs_le_abs_sub γ ω
  nlinarith [abs_nonneg ω, abs_nonneg (γ - ω)]

/-- At a point of the strip with real part `γ`, `|κ̂₂,ω(x)| ≤ C_κ (1+|ω|)² / (1+|γ-ω|)²`. -/
theorem norm_paperFT_modBumpPolarFree_le (ω : ℝ) {x : ℂ} (hx : |x.im| ≤ 1 / 2) :
    ‖paperFT (modBumpPolarFree ω) x‖ ≤
      bumpDecayConst * (1 + |ω|) ^ 2 / (1 + |x.re - ω|) ^ 2 := by
  rw [paperFT_modBumpPolarFree, norm_mul, norm_neg]
  have hw : |(x - ω).im| ≤ 1 / 2 := by simpa using hx
  have hk := norm_paperFT_weilBumpC_le hw
  have hre : (x - (ω : ℂ)).re = x.re - ω := by simp
  rw [hre] at hk
  have hC := bumpDecayConst_nonneg
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
  calc ‖x ^ 2 + 1 / 4‖ * ‖paperFT weilBumpC (x - ω)‖
      ≤ ((1 + |ω|) ^ 2 * (1 + |x.re - ω|) ^ 2) * (bumpDecayConst / (1 + |x.re - ω|) ^ 4) :=
        mul_le_mul (hq.trans hsq) hk (norm_nonneg _) (by positivity)
    _ = bumpDecayConst * (1 + |ω|) ^ 2 / (1 + |x.re - ω|) ^ 2 := by
        field_simp

/-- **Weil energy of the modulated radical test.**  Both evaluation points of every zero see only the
tail of `Φ`, so
`‖W(f_{L,ω}, f_{L,ω})‖ ≤ ε_L² C_κ² (1+|ω|)^4 · 24 A₀ log(|ω|+3)`, `ε_L = ∫ |Φ_{>L-1/4}| e^{|u|/2}`. -/
theorem norm_W_modRadicalTest_le {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (L ω : ℝ) :
    ‖zetaZeroConfig.W (modRadicalTest L ω) (modRadicalTest L ω)‖ ≤
      (∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|)) ^ 2 * bumpDecayConst ^ 2 *
        (1 + |ω|) ^ 4 * (24 * A₀ * Real.log (|ω| + 3)) := by
  set ε := ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|) with hε
  have hε0 : 0 ≤ ε := integral_nonneg fun _ => by positivity
  have hC := bumpDecayConst_nonneg
  obtain ⟨hsumm, hsumle⟩ := window_tsum_le zetaZeroConfig hA₀ hloc ω
  set K := ε ^ 2 * bumpDecayConst ^ 2 * (1 + |ω|) ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (modRadicalTest L ω) (modRadicalTest L ω) ρ‖ ≤
        K * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3) := by
    intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    obtain ⟨hc1, hc2⟩ := paperFT_riemannPhiCore_at_zero hmem L
    have hre1 : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
    have hre2 : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
      rw [Complex.conj_re, WeilEF.gammaOf_re]
    have hv : ∀ x : ℂ, |x.im| ≤ 1 / 2 → x.re = (ρ : ℂ).im →
        paperFT (riemannPhiCore L) x = -paperFT (riemannPhiTail L) x →
        ‖paperFT (modRadicalTest L ω) x‖ ≤
          ε * (bumpDecayConst * (1 + |ω|) ^ 2 / (1 + |(ρ : ℂ).im - ω|) ^ 2) := by
      intro x hx hxre hcore
      rw [paperFT_modRadicalTest, hcore, norm_mul, norm_neg]
      have h1 := norm_paperFT_riemannPhiTail_le (L := L) (b := 1 / 2) (by norm_num) hx
      have h2 := norm_paperFT_modBumpPolarFree_le ω hx
      rw [hxre] at h2
      exact mul_le_mul h1 h2 (norm_nonneg _) hε0
    have hv1 := hv _ hIm hre1 hc1
    have hv2 := hv _ hIm' hre2 hc2
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    set D := 1 + |(ρ : ℂ).im - ω| with hD
    have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg ((ρ : ℂ).im - ω)]
    have hq : ε * (bumpDecayConst * (1 + |ω|) ^ 2 / D ^ 2) *
        (ε * (bumpDecayConst * (1 + |ω|) ^ 2 / D ^ 2)) ≤ K * (1 / D ^ 3) := by
      rw [hK]
      have hD4 : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
      have e : ε * (bumpDecayConst * (1 + |ω|) ^ 2 / D ^ 2) *
          (ε * (bumpDecayConst * (1 + |ω|) ^ 2 / D ^ 2)) =
          ε ^ 2 * bumpDecayConst ^ 2 * (1 + |ω|) ^ 4 * (1 / D ^ 4) := by
        field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hK0
      exact one_div_le_one_div_of_le (by positivity) hD4
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (modRadicalTest L ω) (gammaOf ρ)‖ *
          ‖paperFT (modRadicalTest L ω) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (ε * (bumpDecayConst * (1 + |ω|) ^ 2 / D ^ 2)) *
            (ε * (bumpDecayConst * (1 + |ω|) ^ 2 / D ^ 2)) := by gcongr
      _ = (zetaZeroConfig.mult ρ : ℝ) * (ε * (bumpDecayConst * (1 + |ω|) ^ 2 / D ^ 2) *
            (ε * (bumpDecayConst * (1 + |ω|) ^ 2 / D ^ 2))) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (K * (1 / D ^ 3)) := mul_le_mul_of_nonneg_left hq hm
      _ = K * ((zetaZeroConfig.mult ρ : ℝ) / D ^ 3) := by ring
  have hsum' : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (modRadicalTest L ω) (modRadicalTest L ω) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsumm.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsumm.mul_left _)).trans ?_
  rw [tsum_mul_left]
  calc K * ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3
      ≤ K * (24 * A₀ * Real.log (|ω| + 3)) := mul_le_mul_of_nonneg_left hsumle hK0
    _ = _ := by rw [hK]


/-! ## Lower bounds on the real line -/

/-- For real `|s| ≤ 1/2`: `‖κ̂(s)‖ ≥ cos(1/8) ∫ κ`. -/
theorem norm_paperFT_weilBumpC_real_ge {s : ℝ} (hs : |s| ≤ 1 / 2) :
    Real.cos (1 / 8) * (∫ u, weilBump u) ≤ ‖paperFT weilBumpC (s : ℂ)‖ := by
  have hint : Integrable (fun u : ℝ => weilBumpC u * Complex.exp (I * (s : ℂ) * u)) :=
    ((contDiff_weilBumpC.continuous).mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_weilBumpC.mul_right
  have hre : (paperFT weilBumpC (s : ℂ)).re = ∫ u, weilBump u * Real.cos (s * u) := by
    unfold paperFT
    have h1 := integral_re hint
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    congr 1; funext u
    have e : Complex.exp (I * (s : ℂ) * (u : ℂ)) =
        ((Real.cos (s * u) : ℝ) : ℂ) + ((Real.sin (s * u) : ℝ) : ℂ) * I := by
      rw [show I * (s : ℂ) * (u : ℂ) = ((s * u : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [e]
    simp only [weilBumpC, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im]
    ring
  have hbump_int : Integrable (fun u : ℝ => weilBump u) :=
    weilBump.continuous.integrable_of_hasCompactSupport weilBump.hasCompactSupport
  have hge : ∫ u, weilBump u * Real.cos (1 / 8) ≤ ∫ u, weilBump u * Real.cos (s * u) := by
    refine integral_mono (hbump_int.mul_const _) ?_ fun u => ?_
    · exact (weilBump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        weilBump.hasCompactSupport.mul_right
    · simp only
      by_cases hu : weilBump u = 0
      · simp [hu]
      · have hu' : |u| < 1 / 4 := by
          by_contra h; push Not at h
          have := weilBumpC_eq_zero h
          simp only [weilBumpC, Complex.ofReal_eq_zero] at this; exact hu this
        have hsu : |s * u| ≤ 1 / 8 := by
          rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg u]
        have hcos : Real.cos (1 / 8) ≤ Real.cos (s * u) := by
          rw [← Real.cos_abs (s * u)]
          apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
            hsu
        exact mul_le_mul_of_nonneg_left hcos weilBump.nonneg
  rw [integral_mul_const] at hge
  calc Real.cos (1 / 8) * (∫ u, weilBump u) = (∫ u, weilBump u) * Real.cos (1 / 8) := by ring
    _ ≤ (paperFT weilBumpC (s : ℂ)).re := by rw [hre]; exact hge
    _ ≤ ‖paperFT weilBumpC (s : ℂ)‖ := Complex.re_le_norm _

/-- For real `τ` with `|τ - ω| ≤ 1/2`:
`‖f̂_{L,ω}(τ)‖ ≥ (‖Ξ(τ)‖ - ε_L)(τ² + 1/4) cos(1/8) ∫κ`, `Ξ(τ) = Φ̂(τ)`. -/
theorem norm_paperFT_modRadicalTest_real_ge (L ω : ℝ) {τ : ℝ} (hτ : |τ - ω| ≤ 1 / 2) :
    (‖riemannPhiTransform (1 / 2 + I * τ)‖ -
        ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|)) *
      ((τ ^ 2 + 1 / 4) * (Real.cos (1 / 8) * (∫ u, weilBump u))) ≤
      ‖paperFT (modRadicalTest L ω) (τ : ℂ)‖ := by
  set ε := ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|)
  rw [paperFT_modRadicalTest, norm_mul, paperFT_riemannPhiCore_eq, paperFT_modBumpPolarFree,
    norm_mul, norm_neg]
  have htail : ‖paperFT (riemannPhiTail L) (τ : ℂ)‖ ≤ ε :=
    norm_paperFT_riemannPhiTail_le (L := L) (b := 1 / 2) (by norm_num) (by simp)
  have hcore : ‖riemannPhiTransform (1 / 2 + I * τ)‖ - ε ≤
      ‖riemannPhiTransform (1 / 2 + I * τ) - paperFT (riemannPhiTail L) (τ : ℂ)‖ := by
    have := norm_sub_norm_le (riemannPhiTransform (1 / 2 + I * τ))
      (paperFT (riemannPhiTail L) (τ : ℂ))
    linarith
  have hq : ‖(τ : ℂ) ^ 2 + 1 / 4‖ = τ ^ 2 + 1 / 4 := by
    rw [show (τ : ℂ) ^ 2 + 1 / 4 = ((τ ^ 2 + 1 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hk := norm_paperFT_weilBumpC_real_ge (s := τ - ω) hτ
  rw [show ((τ : ℂ) - (ω : ℂ)) = ((τ - ω : ℝ) : ℂ) by push_cast; ring, hq]
  have hI0 : 0 ≤ ∫ u, weilBump u := integral_nonneg fun u => weilBump.nonneg
  have hc0 : 0 ≤ Real.cos (1 / 8) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  rcases le_or_gt (‖riemannPhiTransform (1 / 2 + I * τ)‖ - ε) 0 with hneg | hpos
  · have : (‖riemannPhiTransform (1 / 2 + I * τ)‖ - ε) *
        ((τ ^ 2 + 1 / 4) * (Real.cos (1 / 8) * (∫ u, weilBump u))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
    exact this.trans (by positivity)
  · exact mul_le_mul hcore (mul_le_mul_of_nonneg_left hk (by positivity)) (by positivity)
      (norm_nonneg _)


/-! ## `Ξ` on the critical line away from the zeros -/

/-- `c_Ξ = π^{-1/4} · (√π · 2^{1/2} · √π / Γ(3/4)) / 6`. -/
def xiLineConst : ℝ :=
  Real.pi ^ (-(1 / 4 : ℝ)) * (Real.sqrt Real.pi * (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi /
    Real.Gamma (3 / 4)) / 6

theorem xiLineConst_pos : 0 < xiLineConst := by
  unfold xiLineConst
  have hG : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hpi := Real.pi_pos
  positivity

/-- **Lower bound for `Ξ` on the critical line.**  If every zero ordinate is at distance `≥ δ` from
`τ ≥ 4`, then `‖Ξ(τ)‖ ≥ c_Ξ τ² e^{-πτ/2} exp(-(3/2) C log τ / δ)`. -/
theorem norm_riemannPhiTransform_line_ge {τ δ : ℝ} (hτ : 4 ≤ τ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfar : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - τ|) :
    xiLineConst * τ ^ 2 * Real.exp (-(Real.pi * τ / 2)) *
        Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ)) ≤
      ‖riemannPhiTransform (1 / 2 + I * τ)‖ := by
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
  -- the archimedean factor
  have hU : xiLineConst * 6 * τ ^ 2 / 2 * Real.exp (-(Real.pi * τ / 2)) ≤ ‖xiUnit s‖ := by
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
    have hΓ := norm_Gamma_quarter_add_half_height_lower τ
    have hs2 : s / 2 = ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [hs2]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ)] at hΓ
    have hG : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
    have hpq : 0 < Real.pi ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos Real.pi_pos _
    have hτ2 : τ ^ 2 ≤ τ ^ 2 + 1 / 4 := by linarith
    unfold xiLineConst
    calc Real.pi ^ (-(1 / 4 : ℝ)) * (Real.sqrt Real.pi * (2 : ℝ) ^ (1 / 2 : ℝ) *
            Real.sqrt Real.pi / Real.Gamma (3 / 4)) / 6 * 6 * τ ^ 2 / 2 *
            Real.exp (-(Real.pi * τ / 2))
        = (τ ^ 2 / 2) * (Real.pi ^ (-(1 / 4 : ℝ)) *
            (Real.sqrt Real.pi * Real.exp (-(Real.pi * τ / 2)) * (2 : ℝ) ^ (1 / 2 : ℝ) *
              Real.sqrt Real.pi / Real.Gamma (3 / 4))) := by ring
      _ ≤ ((τ ^ 2 + 1 / 4) / 2) * (Real.pi ^ (-(1 / 4 : ℝ)) *
            ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) := by
          apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hΓ hpq.le) (by positivity)
            (by positivity)
      _ = _ := by ring
  have hz0 : 0 ≤ (1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ)) := by
    positivity
  calc xiLineConst * τ ^ 2 * Real.exp (-(Real.pi * τ / 2)) *
        Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ))
      = (xiLineConst * 6 * τ ^ 2 / 2 * Real.exp (-(Real.pi * τ / 2))) *
          ((1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / δ))) := by ring
    _ ≤ ‖xiUnit s‖ * ‖riemannZeta s‖ :=
        mul_le_mul hU hζ hz0 (norm_nonneg _)

end

end RHTower
