import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheBoundaryQuotientForgetsTheInnerMass
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.NearExtremalMollifiersAreRigid
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiInverseSquareSummability
import Mathlib.Analysis.Complex.MeanValue

/-!
# How boundary dilation quotients read inner mass

Raw boundary second moments `avg |P(v)/P(ρv)|²` tend to `1` as `ρ → 1⁻` for every finite curve
datum (`tendsto_circleAverage_abelRatio_unconditional`), even when an exterior Frobenius root
`‖β‖ > 1` creates positive inner mass `posLog ‖β‖ > 0`. This module resolves the mechanism behind
that forgetting and establishes its exact counterpart for `ζ(s)`:

1. **Beurling–Sarason–Hardy phase transition (`sq_norm_le_circleAverage_subcritical`,
   `supercritical_pythagorean_split`, `tendsto_circleAverage_modelPart_sq`).**
   For an exterior root `‖β‖ > 1` (`α = β⁻¹`, `0 < ‖α‖ < 1`), the single-factor quotient
   `q_ρ(v) = (1 − βv)/(1 − ρβv)` obeys the holomorphic Szegő–Beurling floor
   `avg ‖q_ρ‖² ≥ ‖β‖² = exp(2 posLog ‖β‖) > 1` throughout the subcritical regime `0 ≤ ρ < ‖β‖⁻¹`.
   Across `ρ = ‖β‖⁻¹`, the pole `(ρβ)⁻¹` crosses `𝕋` into `𝔻`. For `‖β‖⁻¹ < ρ < 1`, `q_ρ` splits
   pointwise and `L²(𝕋)`-orthogonally across `b_α H²(𝔻) ⊕ K_{b_α} ⊕ H²_-(𝔻)` into
   `beurlingPart β ρ`, `modelPart β ρ`, and `antiHoloPart β ρ` with exact circle-average squares
   `ρ⁻² ‖β‖⁻²`, `ρ⁻²(1 − ‖β‖⁻²)`, and `(1 − ρ⁻¹)² / (ρ² ‖β‖² − 1)`. As `ρ → 1⁻`, the total `L²`
   mean tends to `1`, while the Sarason model-space projection tends to
   `1 − ‖β‖⁻² = 1 − exp(−2 posLog ‖β‖) > 0` (`φ⁻¹` on `goldenDatum`), reading `posLog ‖β‖`
   directly from the boundary quotient.

2. **Shifted inner field, macroscopic single-shift RH criterion, and first-order dilation jet of `ζ`
   (`hasSum_shiftedInnerField`, `riemannHypothesis_iff_log_dilation_quotient_eq`,
   `tendsto_firstOrder_dilation_jet`, `riemannHypothesis_iff_firstOrder_jet_eq`).**
   For `0 ≤ δ ≤ 1/2`, the shifted inner field `I_δ(w)` equals the Green potential of zeros with
   `Re ρ > 1/2 + δ` shifted left by `δ`. At `w = 1`, for every single macroscopic shift
   `δ ∈ (0, 1/2)`,
   `∫ (log ‖ζ(1/2 + iτ)‖ − log ‖ζ(1/2 + δ + iτ)‖) P₁(τ) dτ = (I(1) − I_δ(1)) + log((1 − δ)/(δ ‖ζ(1 + δ)‖))`,
   with `I(1) − I_δ(1) ≥ 0` and equality if and only if `RiemannHypothesis`. As `δ → 0⁺`,
   dividing by `δ` converges unconditionally to
   `−(1 + γ) + ∑'_{ρ : ZetaRightZero} m_ρ Re(ρ⁻¹ + (1 − ρ)⁻¹)`,
   deciding `RiemannHypothesis` by equality with `−(1 + γ)`.

3. **Unshadowed `L²` blowup (`not_integrable_zeta_dilationQuotient_sq`).**
   Unlike finite curves, an off-line zero `ρ₀` (`1/2 < Re ρ₀ < 1`) unshadowed on the critical line
   (`ζ(1/2 + i Im ρ₀) ≠ 0`) forces non-integrability of
   `τ ↦ (‖ζ(1/2 + iτ)‖ / ‖ζ(1/2 + δ + iτ)‖)² P₁(τ)` at the critical shift `δ = Re ρ₀ − 1/2`.
-/

open Complex Metric Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open ArithmeticCastelnuovoSeveri _root_.RHTower

noncomputable section

/-! ### Elementary mean-value and log-squeeze helpers -/

private theorem log_one_add_bounds {y : ℝ} (hy : 0 < 1 + y) :
    y / (1 + y) ≤ Real.log (1 + y) ∧ Real.log (1 + y) ≤ y := by
  refine ⟨?_, by linarith [Real.log_le_sub_one_of_pos hy]⟩
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at h
  have h1 : (1 + y)⁻¹ - 1 = -(y / (1 + y)) := by
    field_simp [hy.ne']
    ring
  linarith

private theorem circleAverage_eq_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    Real.circleAverage f 0 1 = f 0 := by
  have hdc : DiffContOnCl ℂ f (ball 0 |1|) := by
    rw [abs_one]
    exact ⟨hf.mono ball_subset_closedBall, by
      rw [closure_ball 0 one_ne_zero]; exact hf.continuousOn⟩
  exact hdc.circleAverage

private theorem circleAverage_re_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    CircleIntegrable (fun z => (f z).re) 0 1 ∧
      Real.circleAverage (fun z => (f z).re) 0 1 = (f 0).re := by
  have hcont : ContinuousOn f (sphere 0 1) := hf.continuousOn.mono sphere_subset_closedBall
  have hci : CircleIntegrable f 0 1 := hcont.circleIntegrable zero_le_one
  have hci_re : CircleIntegrable (fun z => (f z).re) 0 1 :=
    (Complex.continuous_re.comp_continuousOn hcont).circleIntegrable zero_le_one
  refine ⟨hci_re, ?_⟩
  have hcomm := Complex.reCLM.circleAverage_comp_comm hci
  simpa only [Function.comp_def, Complex.reCLM_apply, circleAverage_eq_of_differentiableOn hf]
    using hcomm

private theorem norm_sq_le_circleAverage_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    ‖f 0‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 1 := by
  have hcont : ContinuousOn f (sphere 0 1) := hf.continuousOn.mono sphere_subset_closedBall
  have hg_diff : DifferentiableOn ℂ (fun z => conj (f 0) * (f z - f 0)) (closedBall 0 1) :=
    (differentiableOn_const _).mul (hf.sub (differentiableOn_const _))
  obtain ⟨hci_re, hre_avg⟩ := circleAverage_re_of_differentiableOn hg_diff
  have hci_sub : CircleIntegrable (fun z => ‖f z - f 0‖ ^ 2) 0 1 :=
    (((hcont.sub continuousOn_const).norm.pow 2)).circleIntegrable zero_le_one
  have hci_lin : CircleIntegrable (fun z => 2 * (conj (f 0) * (f z - f 0)).re) 0 1 :=
    IntervalIntegrable.const_mul hci_re 2
  have hci_c : CircleIntegrable (fun _ : ℂ => ‖f 0‖ ^ 2) 0 1 := intervalIntegrable_const
  have hci_12 : CircleIntegrable
      (fun z => ‖f z - f 0‖ ^ 2 + 2 * (conj (f 0) * (f z - f 0)).re) 0 1 :=
    IntervalIntegrable.add hci_sub hci_lin
  have hpt : ∀ z : ℂ, ‖f z‖ ^ 2 =
      ‖f z - f 0‖ ^ 2 + 2 * (conj (f 0) * (f z - f 0)).re + ‖f 0‖ ^ 2 := fun z => by
    have h1 := norm_add_sq (f z - f 0) (f 0)
    simpa only [sub_add_cancel] using h1
  have hfun : (fun z => ‖f z‖ ^ 2) =
      fun z => ‖f z - f 0‖ ^ 2 + 2 * (conj (f 0) * (f z - f 0)).re + ‖f 0‖ ^ 2 := funext hpt
  rw [hfun, Real.circleAverage_fun_add hci_12 hci_c, Real.circleAverage_fun_add hci_sub hci_lin,
    Real.circleAverage_const]
  have hlin0 : Real.circleAverage (fun z => 2 * (conj (f 0) * (f z - f 0)).re) 0 1 = 0 := by
    have hsmul := Real.circleAverage_fun_smul (a := (2 : ℝ))
      (f := fun z => (conj (f 0) * (f z - f 0)).re) (c := 0) (R := 1)
    simp only [smul_eq_mul] at hsmul
    rw [hsmul, hre_avg]
    simp
  have hsub_nn : 0 ≤ Real.circleAverage (fun z => ‖f z - f 0‖ ^ 2) 0 1 :=
    Real.circleAverage_nonneg_of_nonneg fun _ _ => sq_nonneg _
  linarith

private theorem one_sub_mul_ne_zero {w z : ℂ} (hw : ‖w‖ < 1) (hz : z ∈ closedBall (0 : ℂ) 1) :
    1 - w * z ≠ 0 := by
  have hz1 : ‖z‖ ≤ 1 := by simpa using hz
  have hwz : ‖w * z‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg w) hz1).trans_lt hw
  intro h0
  have h1 : w * z = 1 := by linear_combination -h0
  rw [h1, norm_one] at hwz
  exact lt_irrefl 1 hwz

/-! ### 1. Beurling–Sarason–Hardy phase transition of exterior curve factors -/

/-- The single-factor boundary dilation quotient `q_ρ(v) = (1 − βv)/(1 − ρβv)`. -/
def factorQuotient (β : ℂ) (ρ : ℝ) (v : ℂ) : ℂ :=
  (1 - β * v) / (1 - (ρ : ℂ) * β * v)

/-- Normalized Blaschke factor `b_α(v) = (v − α)/(1 − ᾱ v)` of an interior root `‖α‖ < 1`. -/
def blaschkeFactor (α v : ℂ) : ℂ :=
  (v - α) / (1 - conj α * v)

/-- Unit reproducing kernel `k_α(v) = √(1 − ‖α‖²)/(1 − ᾱ v)` of the model space `K_{b_α}`. -/
def defectKernel (α v : ℂ) : ℂ :=
  ((1 - ‖α‖ ^ 2).sqrt : ℂ) / (1 - conj α * v)

/-- Holomorphic Beurling component `(−ρ⁻¹ ᾱ) b_α(v)` in `b_α H²(𝔻)` (`α = β⁻¹`). -/
def beurlingPart (β : ℂ) (ρ : ℝ) (v : ℂ) : ℂ :=
  -((ρ : ℂ)⁻¹ * conj β⁻¹) * blaschkeFactor β⁻¹ v

/-- Sarason model-space defect component `(ρ⁻¹ √(1 − ‖α‖²)) k_α(v)` in `K_{b_α}` (`α = β⁻¹`). -/
def modelPart (β : ℂ) (ρ : ℝ) (v : ℂ) : ℂ :=
  ((ρ : ℂ)⁻¹ * ((1 - ‖β⁻¹‖ ^ 2).sqrt : ℂ)) * defectKernel β⁻¹ v

/-- Strict `H²_-(𝔻)` component `(1 − ρ⁻¹)/(1 − ρβv)` once `ρ ‖β‖ > 1`. -/
def antiHoloPart (β : ℂ) (ρ : ℝ) (v : ℂ) : ℂ :=
  (1 - (ρ : ℂ)⁻¹) / (1 - (ρ : ℂ) * β * v)

theorem norm_sub_eq_norm_one_sub_conj_mul {w v : ℂ} (hv : ‖v‖ = 1) :
    ‖v - w‖ = ‖1 - conj w * v‖ := by
  have hv_conj : v * conj v = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]
    norm_num
  have h1 : 1 - conj w * v = v * conj (v - w) := by
    rw [map_sub, mul_sub]
    linear_combination -hv_conj
  rw [h1, norm_mul, hv, one_mul, Complex.norm_conj]

theorem norm_blaschkeFactor_eq_one {α v : ℂ} (hα : ‖α‖ < 1) (hv : ‖v‖ = 1) :
    ‖blaschkeFactor α v‖ = 1 := by
  have hne : 1 - conj α * v ≠ 0 :=
    one_sub_mul_ne_zero (by simpa using hα) (by simp [hv])
  rw [blaschkeFactor, norm_div, norm_sub_eq_norm_one_sub_conj_mul hv,
    div_self (norm_ne_zero_iff.mpr hne)]

/-- **Subcritical Szegő–Beurling floor.** Throughout `0 ≤ ρ < ‖β‖⁻¹` (`‖β‖ > 1`), the dilation
quotient stays in `b_{β⁻¹} H²(𝔻)` with circle-average square at least `‖β‖² = exp(2 posLog ‖β‖)`. -/
theorem sq_norm_le_circleAverage_subcritical {β : ℂ} (hβ : 1 < ‖β‖) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ‖β‖⁻¹) :
    Real.exp (2 * Real.posLog ‖β‖) = ‖β‖ ^ 2 ∧
      ‖β‖ ^ 2 ≤ Real.circleAverage (fun v => ‖factorQuotient β ρ v‖ ^ 2) 0 1 := by
  have hβ0 : 0 < ‖β‖ := zero_lt_one.trans hβ
  have hβ_ne : β ≠ 0 := norm_ne_zero_iff.mp hβ0.ne'
  have hexp : Real.exp (2 * Real.posLog ‖β‖) = ‖β‖ ^ 2 := by
    rw [Real.posLog_eq_log (by rw [abs_of_pos hβ0]; exact hβ.le), ← Real.log_rpow hβ0,
      Real.exp_log (Real.rpow_pos_of_pos hβ0 2), Real.rpow_two]
  refine ⟨hexp, ?_⟩
  have hρβ : ‖(ρ : ℂ) * β‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0]
    calc ρ * ‖β‖ < ‖β‖⁻¹ * ‖β‖ := mul_lt_mul_of_pos_right hρ hβ0
      _ = 1 := inv_mul_cancel₀ hβ0.ne'
  have hα : ‖β⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hβ
  have hΨ_diff : DifferentiableOn ℂ
      (fun z => -β * (1 - conj β⁻¹ * z) / (1 - (ρ : ℂ) * β * z)) (closedBall 0 1) := by
    refine ((differentiableOn_const (-β)).mul
      ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id))).div
      ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id)) ?_
    intro z hz
    exact one_sub_mul_ne_zero (w := (ρ : ℂ) * β) hρβ hz
  have hΨ0 : ‖(-β * (1 - conj β⁻¹ * (0 : ℂ)) / (1 - (ρ : ℂ) * β * (0 : ℂ)))‖ ^ 2 = ‖β‖ ^ 2 := by
    simp
  have hle := norm_sq_le_circleAverage_of_differentiableOn hΨ_diff
  rw [hΨ0] at hle
  refine hle.trans (le_of_eq (Real.circleAverage_congr_sphere fun v hv => ?_))
  have hv1 : ‖v‖ = 1 := by simpa using hv
  have hden_α : 1 - conj β⁻¹ * v ≠ 0 :=
    one_sub_mul_ne_zero (by simpa using hα) (by simp [hv1])
  have hfac : (-β * (1 - conj β⁻¹ * v) / (1 - (ρ : ℂ) * β * v)) * blaschkeFactor β⁻¹ v =
      factorQuotient β ρ v := by
    rw [blaschkeFactor, factorQuotient]
    have hnum : -β * (v - β⁻¹) = 1 - β * v := by
      field_simp [hβ_ne]
      ring
    calc (-β * (1 - conj β⁻¹ * v) / (1 - (ρ : ℂ) * β * v)) * ((v - β⁻¹) / (1 - conj β⁻¹ * v))
        = (-β * (v - β⁻¹)) * ((1 - conj β⁻¹ * v) / (1 - conj β⁻¹ * v)) / (1 - (ρ : ℂ) * β * v) := by
          ring
      _ = (-β * (v - β⁻¹)) * 1 / (1 - (ρ : ℂ) * β * v) := by rw [div_self hden_α]
      _ = (1 - β * v) / (1 - (ρ : ℂ) * β * v) := by rw [mul_one, hnum]
  rw [← hfac, norm_mul, norm_blaschkeFactor_eq_one hα hv1, mul_one]

/-- Carathéodory–Poisson identity: `(1 − ‖w‖²) / ‖1 − w̄ v‖²` has unit circle average for `‖w‖ < 1`. -/
theorem circleAverage_poisson_kernel_disc {w : ℂ} (hw : ‖w‖ < 1) :
    Real.circleAverage (fun v : ℂ => (1 - ‖w‖ ^ 2) / ‖1 - conj w * v‖ ^ 2) (0 : ℂ) 1 = 1 := by
  have hΦ_diff : DifferentiableOn ℂ (fun z => (1 + conj w * z) / (1 - conj w * z))
      (closedBall 0 1) := by
    refine ((differentiableOn_const 1).add ((differentiableOn_const _).mul differentiableOn_id)).div
      ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id)) ?_
    intro z hz
    exact one_sub_mul_ne_zero (by simpa using hw) hz
  obtain ⟨-, hre⟩ := circleAverage_re_of_differentiableOn hΦ_diff
  have h0 : (((1 : ℂ) + conj w * 0) / (1 - conj w * 0)).re = 1 := by simp
  rw [h0] at hre
  have hcongr : EqOn (fun v : ℂ => (1 - ‖w‖ ^ 2) / ‖1 - conj w * v‖ ^ 2)
      (fun v : ℂ => ((1 + conj w * v) / (1 - conj w * v)).re) (sphere 0 |1|) := by
    intro v hv
    have hv1 : ‖v‖ = 1 := by simpa using hv
    set u : ℂ := conj w * v
    have hu_norm : ‖u‖ = ‖w‖ := by simp [u, hv1]
    have h1u : 1 - u ≠ 0 := one_sub_mul_ne_zero (by simpa using hw) (by simp [hv1])
    dsimp only
    rw [← hu_norm, ← Complex.normSq_eq_norm_sq (1 - u), Complex.div_re]
    have hns : Complex.normSq u = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
    rw [← hns, Complex.normSq_apply u, Complex.normSq_apply (1 - u)]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    have hden : (1 - u.re) * (1 - u.re) + -u.im * -u.im ≠ 0 := by
      have := Complex.normSq_pos.mpr h1u
      rw [Complex.normSq_apply] at this
      simpa only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
        using this.ne'
    field_simp [hden]
    ring
  exact (Real.circleAverage_congr_sphere hcongr).trans hre

theorem circleAverage_norm_defectKernel_sq {α : ℂ} (hα : ‖α‖ < 1) :
    Real.circleAverage (fun v : ℂ => ‖defectKernel α v‖ ^ 2) (0 : ℂ) 1 = 1 := by
  have hα2 : 0 ≤ 1 - ‖α‖ ^ 2 := by nlinarith [norm_nonneg α]
  have hcongr : EqOn (fun v : ℂ => ‖defectKernel α v‖ ^ 2)
      (fun v : ℂ => (1 - ‖α‖ ^ 2) / ‖1 - conj α * v‖ ^ 2) (sphere 0 |1|) := by
    intro v _
    dsimp only
    rw [defectKernel, norm_div, div_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hα2]
  exact (Real.circleAverage_congr_sphere hcongr).trans (circleAverage_poisson_kernel_disc hα)

/-- Pointwise Beurling–Sarason–Hardy decomposition of `q_ρ` on `𝕋` in the supercritical regime. -/
theorem factorQuotient_eq_supercritical_sum {β : ℂ} (hβ : 1 < ‖β‖) {ρ : ℝ}
    (hρ : ‖β‖⁻¹ < ρ) {v : ℂ} (hv : ‖v‖ = 1) :
    factorQuotient β ρ v = beurlingPart β ρ v + modelPart β ρ v + antiHoloPart β ρ v := by
  have hβ0 : 0 < ‖β‖ := zero_lt_one.trans hβ
  have hρ0 : 0 < ρ := (inv_pos.mpr hβ0).trans hρ
  have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
  have hα : ‖β⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hβ
  have hα2 : 0 ≤ 1 - ‖β⁻¹‖ ^ 2 := by nlinarith [norm_nonneg β⁻¹]
  have hden_α : 1 - conj β⁻¹ * v ≠ 0 :=
    one_sub_mul_ne_zero (by simpa using hα) (by simp [hv])
  have hρβ1 : 1 < ρ * ‖β‖ := (inv_lt_iff_one_lt_mul₀ hβ0).mp hρ
  have hden_ρ : 1 - (ρ : ℂ) * β * v ≠ 0 := by
    intro h0
    have h1 : (ρ : ℂ) * β * v = 1 := by linear_combination -h0
    have hn := congrArg norm h1
    rw [norm_mul, norm_mul, hv, mul_one, norm_one, Complex.norm_real,
      Real.norm_of_nonneg hρ0.le] at hn
    linarith
  have hbm : beurlingPart β ρ v + modelPart β ρ v = (ρ : ℂ)⁻¹ := by
    rw [beurlingPart, modelPart, blaschkeFactor, defectKernel]
    have hsq : (((1 - ‖β⁻¹‖ ^ 2).sqrt : ℂ)) * (((1 - ‖β⁻¹‖ ^ 2).sqrt : ℂ)) =
        ((1 - ‖β⁻¹‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hα2]
    have hca : conj β⁻¹ * β⁻¹ = ((‖β⁻¹‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul', Complex.ofReal_pow]
    calc -((ρ : ℂ)⁻¹ * conj β⁻¹) * ((v - β⁻¹) / (1 - conj β⁻¹ * v)) +
            (ρ : ℂ)⁻¹ * ↑(1 - ‖β⁻¹‖ ^ 2).sqrt * (↑(1 - ‖β⁻¹‖ ^ 2).sqrt / (1 - conj β⁻¹ * v))
        = (ρ : ℂ)⁻¹ * ((-conj β⁻¹ * v + conj β⁻¹ * β⁻¹ +
            ↑(1 - ‖β⁻¹‖ ^ 2).sqrt * ↑(1 - ‖β⁻¹‖ ^ 2).sqrt) / (1 - conj β⁻¹ * v)) := by ring
      _ = (ρ : ℂ)⁻¹ * ((1 - conj β⁻¹ * v) / (1 - conj β⁻¹ * v)) := by
          rw [hsq, hca]; push_cast; ring
      _ = (ρ : ℂ)⁻¹ := by rw [div_self hden_α, mul_one]
  have hρ_inv : (ρ : ℂ)⁻¹ * (ρ : ℂ) = 1 := inv_mul_cancel₀ hρC
  rw [hbm, factorQuotient, antiHoloPart]
  calc (1 - β * v) / (1 - (ρ : ℂ) * β * v)
      = ((ρ : ℂ)⁻¹ * (1 - (ρ : ℂ) * β * v) + (1 - (ρ : ℂ)⁻¹)) / (1 - (ρ : ℂ) * β * v) := by
          congr 1
          calc 1 - β * v = 1 - ((ρ : ℂ)⁻¹ * (ρ : ℂ)) * (β * v) := by rw [hρ_inv, one_mul]
            _ = (ρ : ℂ)⁻¹ * (1 - (ρ : ℂ) * β * v) + (1 - (ρ : ℂ)⁻¹) := by ring
    _ = (ρ : ℂ)⁻¹ * ((1 - (ρ : ℂ) * β * v) / (1 - (ρ : ℂ) * β * v)) +
          (1 - (ρ : ℂ)⁻¹) / (1 - (ρ : ℂ) * β * v) := by rw [add_div, mul_div_assoc]
    _ = (ρ : ℂ)⁻¹ + (1 - (ρ : ℂ)⁻¹) / (1 - (ρ : ℂ) * β * v) := by rw [div_self hden_ρ, mul_one]

private theorem conj_inv_one_sub_mul_eq_on_sphere {β : ℂ} (hβ : 1 < ‖β‖) {ρ : ℝ}
    (hρ : ‖β‖⁻¹ < ρ) {v : ℂ} (hv : ‖v‖ = 1) :
    conj ((1 - (ρ : ℂ) * β * v)⁻¹) =
      (-conj (((ρ : ℂ) * β)⁻¹) * v) / (1 - conj (((ρ : ℂ) * β)⁻¹) * v) := by
  have hβ0 : 0 < ‖β‖ := zero_lt_one.trans hβ
  have hρ0 : 0 < ρ := (inv_pos.mpr hβ0).trans hρ
  set w : ℂ := ((ρ : ℂ) * β)⁻¹
  have hρβ_ne : (ρ : ℂ) * β ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ0.ne') (norm_ne_zero_iff.mp hβ0.ne')
  have hw_mul : ((ρ : ℂ) * β) * w = 1 := mul_inv_cancel₀ hρβ_ne
  have hv_conj : conj v * v = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]
    norm_num
  have hcw_ne : conj w ≠ 0 := fun h0 =>
    inv_ne_zero hρβ_ne (by simpa only [Complex.conj_conj, map_zero] using congrArg conj h0)
  rw [map_inv₀, inv_eq_iff_eq_inv, inv_div]
  rw [eq_div_iff (mul_ne_zero (neg_ne_zero.mpr hcw_ne)
    (norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)))]
  rw [map_sub, map_one, map_mul]
  have hcw : conj ((ρ : ℂ) * β) * conj w = 1 := by
    simpa only [map_mul, map_one] using congrArg conj hw_mul
  calc (1 - conj ((ρ : ℂ) * β) * conj v) * (-conj w * v)
      = -conj w * v + (conj ((ρ : ℂ) * β) * conj w) * (conj v * v) := by ring
    _ = 1 - conj w * v := by rw [hcw, hv_conj]; ring

private theorem pythagorean_of_orthog_on_sphere {A B H : ℂ → ℂ}
    (hA : ContinuousOn A (sphere 0 1)) (hB : ContinuousOn B (sphere 0 1))
    (hH : DifferentiableOn ℂ H (closedBall 0 1)) (hH0 : H 0 = 0)
    (heq : ∀ v : ℂ, ‖v‖ = 1 → conj (B v) * A v = H v) :
    Real.circleAverage (fun v => (conj (B v) * A v).re) 0 1 = 0 ∧
      Real.circleAverage (fun v => ‖A v + B v‖ ^ 2) 0 1 =
        Real.circleAverage (fun v => ‖A v‖ ^ 2) 0 1 +
          Real.circleAverage (fun v => ‖B v‖ ^ 2) 0 1 := by
  obtain ⟨-, hreH⟩ := circleAverage_re_of_differentiableOn hH
  rw [hH0, Complex.zero_re] at hreH
  have horth : Real.circleAverage (fun v => (conj (B v) * A v).re) 0 1 = 0 := by
    rw [← hreH]
    refine Real.circleAverage_congr_sphere fun v hv => ?_
    rw [heq v (by simpa using hv)]
  refine ⟨horth, ?_⟩
  have hciA : CircleIntegrable (fun v => ‖A v‖ ^ 2) 0 1 :=
    (hA.norm.pow 2).circleIntegrable zero_le_one
  have hciB : CircleIntegrable (fun v => ‖B v‖ ^ 2) 0 1 :=
    (hB.norm.pow 2).circleIntegrable zero_le_one
  have hciCross : CircleIntegrable (fun v => 2 * (conj (B v) * A v).re) 0 1 := by
    have hcontC : ContinuousOn (fun v => 2 * (conj (B v) * A v).re) (sphere 0 1) :=
      continuousOn_const.mul
        (Complex.continuous_re.comp_continuousOn ((Complex.continuous_conj.comp_continuousOn hB).mul hA))
    exact hcontC.circleIntegrable zero_le_one
  have hci12 : CircleIntegrable (fun v => ‖A v‖ ^ 2 + 2 * (conj (B v) * A v).re) 0 1 :=
    IntervalIntegrable.add hciA hciCross
  have hpt : ∀ v : ℂ, ‖A v + B v‖ ^ 2 = ‖A v‖ ^ 2 + 2 * (conj (B v) * A v).re + ‖B v‖ ^ 2 :=
    fun v => norm_add_sq (A v) (B v)
  have hfun : (fun v => ‖A v + B v‖ ^ 2) =
      fun v => ‖A v‖ ^ 2 + 2 * (conj (B v) * A v).re + ‖B v‖ ^ 2 := funext hpt
  rw [hfun, Real.circleAverage_fun_add hci12 hciB, Real.circleAverage_fun_add hciA hciCross]
  have h2 : Real.circleAverage (fun v => 2 * (conj (B v) * A v).re) 0 1 = 0 := by
    have hsmul := Real.circleAverage_fun_smul (a := (2 : ℝ))
      (f := fun v => (conj (B v) * A v).re) (c := 0) (R := 1)
    simp only [smul_eq_mul] at hsmul
    rw [hsmul, horth, mul_zero]
  linarith

private theorem circleAverage_norm_beurlingPart_sq {β : ℂ} (hβ : 1 < ‖β‖) {ρ : ℝ}
    (hρ : ‖β‖⁻¹ < ρ) :
    Real.circleAverage (fun v => ‖beurlingPart β ρ v‖ ^ 2) 0 1 = ρ⁻¹ ^ 2 * ‖β‖⁻¹ ^ 2 := by
  have hβ0 : 0 < ‖β‖ := zero_lt_one.trans hβ
  have hρ0 : 0 < ρ := (inv_pos.mpr hβ0).trans hρ
  have hα : ‖β⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hβ
  have hcongr : EqOn (fun v => ‖beurlingPart β ρ v‖ ^ 2)
      (fun _ => ρ⁻¹ ^ 2 * ‖β‖⁻¹ ^ 2) (sphere 0 |1|) := by
    intro v hv
    have hv1 : ‖v‖ = 1 := by simpa using hv
    dsimp only
    rw [beurlingPart, norm_mul, norm_neg, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hρ0.le, Complex.norm_conj, norm_inv,
      norm_blaschkeFactor_eq_one hα hv1, mul_one, mul_pow]
  rw [Real.circleAverage_congr_sphere hcongr, Real.circleAverage_const]

private theorem circleAverage_norm_modelPart_sq {β : ℂ} (hβ : 1 < ‖β‖) {ρ : ℝ}
    (hρ : ‖β‖⁻¹ < ρ) :
    Real.circleAverage (fun v => ‖modelPart β ρ v‖ ^ 2) 0 1 = ρ⁻¹ ^ 2 * (1 - ‖β‖⁻¹ ^ 2) := by
  have hβ0 : 0 < ‖β‖ := zero_lt_one.trans hβ
  have hρ0 : 0 < ρ := (inv_pos.mpr hβ0).trans hρ
  have hα : ‖β⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hβ
  have hα2 : 0 ≤ 1 - ‖β⁻¹‖ ^ 2 := by nlinarith [norm_nonneg β⁻¹]
  have hc : ‖(ρ : ℂ)⁻¹ * ((1 - ‖β⁻¹‖ ^ 2).sqrt : ℂ)‖ ^ 2 = ρ⁻¹ ^ 2 * (1 - ‖β‖⁻¹ ^ 2) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ0.le,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hα2, norm_inv]
  have hfun : (fun v => ‖modelPart β ρ v‖ ^ 2) =
      fun v => (ρ⁻¹ ^ 2 * (1 - ‖β‖⁻¹ ^ 2)) * ‖defectKernel β⁻¹ v‖ ^ 2 := by
    funext v
    rw [modelPart, norm_mul, mul_pow, hc]
  rw [hfun]
  have hsmul := Real.circleAverage_fun_smul (a := ρ⁻¹ ^ 2 * (1 - ‖β‖⁻¹ ^ 2))
    (f := fun v => ‖defectKernel β⁻¹ v‖ ^ 2) (c := 0) (R := 1)
  simp only [smul_eq_mul] at hsmul
  rw [hsmul, circleAverage_norm_defectKernel_sq hα, mul_one]

private theorem circleAverage_norm_antiHoloPart_sq {β : ℂ} (hβ : 1 < ‖β‖) {ρ : ℝ}
    (hρ : ‖β‖⁻¹ < ρ) :
    Real.circleAverage (fun v => ‖antiHoloPart β ρ v‖ ^ 2) 0 1 =
      (1 - ρ⁻¹) ^ 2 / (ρ ^ 2 * ‖β‖ ^ 2 - 1) := by
  have hβ0 : 0 < ‖β‖ := zero_lt_one.trans hβ
  have hρ0 : 0 < ρ := (inv_pos.mpr hβ0).trans hρ
  have hρβ1 : 1 < ρ * ‖β‖ := (inv_lt_iff_one_lt_mul₀ hβ0).mp hρ
  have hρβ_ne : (ρ : ℂ) * β ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ0.ne') (norm_ne_zero_iff.mp hβ0.ne')
  have hw : ‖((ρ : ℂ) * β)⁻¹‖ < 1 := by
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    exact inv_lt_one_of_one_lt₀ hρβ1
  have hgap : 0 < ρ ^ 2 * ‖β‖ ^ 2 - 1 := by nlinarith [hρβ1]
  have hw2 : 1 - ‖((ρ : ℂ) * β)⁻¹‖ ^ 2 = (ρ ^ 2 * ‖β‖ ^ 2 - 1) / (ρ ^ 2 * ‖β‖ ^ 2) := by
    have hw_eq : ‖((ρ : ℂ) * β)⁻¹‖ ^ 2 = 1 / (ρ ^ 2 * ‖β‖ ^ 2) := by
      rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      field_simp [hρ0.ne', hβ0.ne']
    rw [hw_eq]
    field_simp [hρ0.ne', hβ0.ne']
  have hcongr : EqOn (fun v => ‖antiHoloPart β ρ v‖ ^ 2)
      (fun v => ((1 - ρ⁻¹) ^ 2 / (ρ ^ 2 * ‖β‖ ^ 2 - 1)) *
        ((1 - ‖((ρ : ℂ) * β)⁻¹‖ ^ 2) / ‖1 - conj ((ρ : ℂ) * β)⁻¹ * v‖ ^ 2)) (sphere 0 |1|) := by
    intro v hv
    have hv1 : ‖v‖ = 1 := by simpa using hv
    have hden_eq : ‖1 - (ρ : ℂ) * β * v‖ ^ 2 =
        ρ ^ 2 * ‖β‖ ^ 2 * ‖1 - conj ((ρ : ℂ) * β)⁻¹ * v‖ ^ 2 := by
      have hfac : 1 - (ρ : ℂ) * β * v = -((ρ : ℂ) * β) * (v - ((ρ : ℂ) * β)⁻¹) := by
        calc 1 - (ρ : ℂ) * β * v
            = ((ρ : ℂ) * β) * ((ρ : ℂ) * β)⁻¹ - (ρ : ℂ) * β * v := by
                rw [mul_inv_cancel₀ hρβ_ne]
          _ = -((ρ : ℂ) * β) * (v - ((ρ : ℂ) * β)⁻¹) := by ring
      rw [hfac, norm_mul, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hρ0.le, norm_sub_eq_norm_one_sub_conj_mul hv1]
      ring
    have hnum_eq : ‖(1 : ℂ) - (ρ : ℂ)⁻¹‖ ^ 2 = (1 - ρ⁻¹) ^ 2 := by
      have hc : (1 : ℂ) - (ρ : ℂ)⁻¹ = ((1 - ρ⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    dsimp only
    rw [antiHoloPart, norm_div, div_pow, hnum_eq, hden_eq, hw2]
    have hden_w : ‖1 - conj ((ρ : ℂ) * β)⁻¹ * v‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (one_sub_mul_ne_zero (by simpa using hw) (by simp [hv1])))
    field_simp [hgap.ne', hρ0.ne', hβ0.ne', hden_w]
  rw [Real.circleAverage_congr_sphere hcongr]
  have hsmul := Real.circleAverage_fun_smul (a := (1 - ρ⁻¹) ^ 2 / (ρ ^ 2 * ‖β‖ ^ 2 - 1))
    (f := fun v => (1 - ‖((ρ : ℂ) * β)⁻¹‖ ^ 2) / ‖1 - conj ((ρ : ℂ) * β)⁻¹ * v‖ ^ 2) (c := 0) (R := 1)
  simp only [smul_eq_mul] at hsmul
  rw [hsmul, circleAverage_poisson_kernel_disc hw, mul_one]

private theorem orthog_blaschke_scaled {a b d α : ℂ} (hα : ‖α‖ < 1) :
    Real.circleAverage (fun v =>
        (conj (b * (d / (1 - conj α * v))) * (a * blaschkeFactor α v)).re) 0 1 = 0 ∧
      Real.circleAverage (fun v =>
        ‖a * blaschkeFactor α v + b * (d / (1 - conj α * v))‖ ^ 2) 0 1 =
        Real.circleAverage (fun v => ‖a * blaschkeFactor α v‖ ^ 2) 0 1 +
          Real.circleAverage (fun v => ‖b * (d / (1 - conj α * v))‖ ^ 2) 0 1 := by
  have hden_cb : ∀ z ∈ closedBall (0 : ℂ) 1, 1 - conj α * z ≠ 0 :=
    fun z hz => one_sub_mul_ne_zero (by simpa only [Complex.norm_conj] using hα) hz
  have hdiff_blaschke : DifferentiableOn ℂ (blaschkeFactor α) (closedBall 0 1) :=
    (differentiableOn_id.sub (differentiableOn_const _)).div
      ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id))
      hden_cb
  have hdiff_ker : DifferentiableOn ℂ (fun z => d / (1 - conj α * z)) (closedBall 0 1) :=
    (differentiableOn_const d).div
      ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id))
      hden_cb
  have hcont_A : ContinuousOn (fun v => a * blaschkeFactor α v) (sphere 0 1) :=
    (continuousOn_const.mul hdiff_blaschke.continuousOn).mono sphere_subset_closedBall
  have hcont_B : ContinuousOn (fun v => b * (d / (1 - conj α * v))) (sphere 0 1) :=
    (continuousOn_const.mul hdiff_ker.continuousOn).mono sphere_subset_closedBall
  have hH_diff : DifferentiableOn ℂ
      (fun z => (conj b * conj d * a) * z / (1 - conj α * z)) (closedBall 0 1) :=
    ((differentiableOn_const _).mul differentiableOn_id).div
      ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id))
      hden_cb
  have hH0 : (conj b * conj d * a) * (0 : ℂ) / (1 - conj α * 0) = 0 := by rw [mul_zero, zero_div]
  refine pythagorean_of_orthog_on_sphere
    (H := fun z => (conj b * conj d * a) * z / (1 - conj α * z))
    hcont_A hcont_B hH_diff hH0 fun v hv1 => ?_
  have hv_conj : v * conj v = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv1]; norm_num
  have hsub_eq : v - α = v * conj (1 - conj α * v) := by
    calc v - α
        = v - α * (v * conj v) := by rw [hv_conj, mul_one]
      _ = v * (1 - α * conj v) := by ring
      _ = v * conj (1 - conj α * v) := by rw [map_sub, map_one, map_mul, Complex.conj_conj]
  have hden_v : v ∈ closedBall (0 : ℂ) 1 := by rw [mem_closedBall_zero_iff, hv1]
  have hden_c : conj (1 - conj α * v) ≠ 0 := fun h0 =>
    hden_cb v hden_v (by simpa only [Complex.conj_conj, map_zero] using congrArg conj h0)
  rw [blaschkeFactor, map_mul, map_div₀, hsub_eq]
  calc (conj b * (conj d / conj (1 - conj α * v))) *
          (a * (v * conj (1 - conj α * v) / (1 - conj α * v)))
      = ((conj b * conj d * a) * v / (1 - conj α * v)) *
          (conj (1 - conj α * v) / conj (1 - conj α * v)) := by ring
    _ = (conj b * conj d * a) * v / (1 - conj α * v) := by rw [div_self hden_c, mul_one]

private theorem orthog_antiHoloPart_of_differentiableOn {β : ℂ} (hβ : 1 < ‖β‖) {ρ : ℝ}
    (hρ : ‖β‖⁻¹ < ρ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    Real.circleAverage (fun v => (conj (antiHoloPart β ρ v) * f v).re) 0 1 = 0 ∧
      Real.circleAverage (fun v => ‖f v + antiHoloPart β ρ v‖ ^ 2) 0 1 =
        Real.circleAverage (fun v => ‖f v‖ ^ 2) 0 1 +
          Real.circleAverage (fun v => ‖antiHoloPart β ρ v‖ ^ 2) 0 1 := by
  have hβ0 : 0 < ‖β‖ := zero_lt_one.trans hβ
  have hρ0 : 0 < ρ := (inv_pos.mpr hβ0).trans hρ
  have hρβ1 : 1 < ρ * ‖β‖ := (inv_lt_iff_one_lt_mul₀ hβ0).mp hρ
  have hw : ‖((ρ : ℂ) * β)⁻¹‖ < 1 := by
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    exact inv_lt_one_of_one_lt₀ hρβ1
  have hden_w_cb : ∀ z ∈ closedBall (0 : ℂ) 1, 1 - conj ((ρ : ℂ) * β)⁻¹ * z ≠ 0 :=
    fun z hz => one_sub_mul_ne_zero (by simpa using hw) hz
  have hcont_anti : ContinuousOn (antiHoloPart β ρ) (sphere 0 1) := by
    refine continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) fun v hv => ?_
    have hv1 : ‖v‖ = 1 := by simpa using hv
    intro h0
    have h1 : (ρ : ℂ) * β * v = 1 := by linear_combination -h0
    have hn := congrArg norm h1
    rw [norm_mul, norm_mul, hv1, mul_one, norm_one, Complex.norm_real,
      Real.norm_of_nonneg hρ0.le] at hn
    linarith
  let g : ℂ → ℂ := fun z =>
    conj (1 - (ρ : ℂ)⁻¹) * (-conj ((ρ : ℂ) * β)⁻¹ * z) / (1 - conj ((ρ : ℂ) * β)⁻¹ * z)
  have hg_diff : DifferentiableOn ℂ g (closedBall 0 1) :=
    ((differentiableOn_const _).mul ((differentiableOn_const _).mul differentiableOn_id)).div
      ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id))
      hden_w_cb
  have hH0 : g 0 * f 0 = 0 := by simp only [g, mul_zero, zero_div, zero_mul]
  refine pythagorean_of_orthog_on_sphere (H := fun z => g z * f z)
    (hf.continuousOn.mono sphere_subset_closedBall) hcont_anti (hg_diff.mul hf) hH0
    fun v hv1 => ?_
  have hanti : conj (antiHoloPart β ρ v) = g v := by
    rw [antiHoloPart, div_eq_mul_inv, map_mul, conj_inv_one_sub_mul_eq_on_sphere hβ hρ hv1,
      ← mul_div_assoc (conj (1 - (ρ : ℂ)⁻¹))]
  rw [hanti]

private theorem differentiableOn_blaschkeFactor {α : ℂ} (hα : ‖α‖ < 1) :
    DifferentiableOn ℂ (blaschkeFactor α) (closedBall 0 1) := by
  have hden_cb : ∀ z ∈ closedBall (0 : ℂ) 1, 1 - conj α * z ≠ 0 :=
    fun z hz => one_sub_mul_ne_zero (by simpa only [Complex.norm_conj] using hα) hz
  exact (differentiableOn_id.sub (differentiableOn_const _)).div
    ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id))
    hden_cb

private theorem differentiableOn_const_div_linear (d : ℂ) {α : ℂ} (hα : ‖α‖ < 1) :
    DifferentiableOn ℂ (fun z => d / (1 - conj α * z)) (closedBall 0 1) := by
  have hden_cb : ∀ z ∈ closedBall (0 : ℂ) 1, 1 - conj α * z ≠ 0 :=
    fun z hz => one_sub_mul_ne_zero (by simpa only [Complex.norm_conj] using hα) hz
  exact (differentiableOn_const d).div
    ((differentiableOn_const 1).sub ((differentiableOn_const _).mul differentiableOn_id))
    hden_cb

private theorem differentiableOn_defectKernel {α : ℂ} (hα : ‖α‖ < 1) :
    DifferentiableOn ℂ (defectKernel α) (closedBall 0 1) := by
  unfold defectKernel
  exact differentiableOn_const_div_linear _ hα

private theorem differentiableOn_beurlingPart {β : ℂ} (hβ : 1 < ‖β‖) (ρ : ℝ) :
    DifferentiableOn ℂ (beurlingPart β ρ) (closedBall 0 1) := by
  have hα : ‖β⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hβ
  unfold beurlingPart
  exact (differentiableOn_blaschkeFactor hα).const_mul _

private theorem differentiableOn_modelPart {β : ℂ} (hβ : 1 < ‖β‖) (ρ : ℝ) :
    DifferentiableOn ℂ (modelPart β ρ) (closedBall 0 1) := by
  have hα : ‖β⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hβ
  unfold modelPart
  exact (differentiableOn_defectKernel hα).const_mul _

private theorem orthog_beurling_model {β : ℂ} (hβ : 1 < ‖β‖) (ρ : ℝ) :
    Real.circleAverage (fun v => (conj (modelPart β ρ v) * beurlingPart β ρ v).re) 0 1 = 0 ∧
      Real.circleAverage (fun v => ‖beurlingPart β ρ v + modelPart β ρ v‖ ^ 2) 0 1 =
        Real.circleAverage (fun v => ‖beurlingPart β ρ v‖ ^ 2) 0 1 +
          Real.circleAverage (fun v => ‖modelPart β ρ v‖ ^ 2) 0 1 := by
  have hα : ‖β⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hβ
  unfold modelPart beurlingPart defectKernel
  exact orthog_blaschke_scaled hα

/-- **Supercritical Beurling–Sarason–Hardy orthogonal split.** Once `‖β‖⁻¹ < ρ` (`‖β‖ > 1`),
`q_ρ` splits pairwise `L²(𝕋)`-orthogonally into `beurlingPart`, `modelPart`, and `antiHoloPart`
with closed-form circle-average norms. -/
theorem supercritical_pythagorean_split {β : ℂ} (hβ : 1 < ‖β‖) {ρ : ℝ}
    (hρ : ‖β‖⁻¹ < ρ) :
    Real.circleAverage (fun v => ‖beurlingPart β ρ v‖ ^ 2) 0 1 = ρ⁻¹ ^ 2 * ‖β‖⁻¹ ^ 2 ∧
      Real.circleAverage (fun v => ‖modelPart β ρ v‖ ^ 2) 0 1 = ρ⁻¹ ^ 2 * (1 - ‖β‖⁻¹ ^ 2) ∧
      Real.circleAverage (fun v => ‖antiHoloPart β ρ v‖ ^ 2) 0 1 =
        (1 - ρ⁻¹) ^ 2 / (ρ ^ 2 * ‖β‖ ^ 2 - 1) ∧
      Real.circleAverage (fun v => (conj (modelPart β ρ v) * beurlingPart β ρ v).re) 0 1 = 0 ∧
      Real.circleAverage (fun v => (conj (antiHoloPart β ρ v) * beurlingPart β ρ v).re) 0 1 = 0 ∧
      Real.circleAverage (fun v => (conj (antiHoloPart β ρ v) * modelPart β ρ v).re) 0 1 = 0 ∧
      Real.circleAverage (fun v => ‖factorQuotient β ρ v‖ ^ 2) 0 1 =
        Real.circleAverage (fun v => ‖beurlingPart β ρ v‖ ^ 2) 0 1 +
          Real.circleAverage (fun v => ‖modelPart β ρ v‖ ^ 2) 0 1 +
          Real.circleAverage (fun v => ‖antiHoloPart β ρ v‖ ^ 2) 0 1 := by
  have hdiff_beurl := differentiableOn_beurlingPart hβ ρ
  have hdiff_model := differentiableOn_modelPart hβ ρ
  obtain ⟨horth_bm, hpyth_bm⟩ := orthog_beurling_model hβ ρ
  obtain ⟨horth_ab, -⟩ := orthog_antiHoloPart_of_differentiableOn hβ hρ hdiff_beurl
  obtain ⟨horth_am, -⟩ := orthog_antiHoloPart_of_differentiableOn hβ hρ hdiff_model
  obtain ⟨-, hpyth_all⟩ := orthog_antiHoloPart_of_differentiableOn hβ hρ
    (hdiff_beurl.fun_add hdiff_model)
  have hcongr_q : EqOn (fun v => ‖factorQuotient β ρ v‖ ^ 2)
      (fun v => ‖(beurlingPart β ρ v + modelPart β ρ v) + antiHoloPart β ρ v‖ ^ 2)
      (sphere 0 |1|) := fun v hv => by
    dsimp only
    rw [factorQuotient_eq_supercritical_sum hβ hρ (by simpa using hv)]
  refine ⟨circleAverage_norm_beurlingPart_sq hβ hρ,
    circleAverage_norm_modelPart_sq hβ hρ,
    circleAverage_norm_antiHoloPart_sq hβ hρ, horth_bm, horth_ab, horth_am, ?_⟩
  rw [Real.circleAverage_congr_sphere hcongr_q, hpyth_all, hpyth_bm]

/-- **Reading inner mass from the boundary quotient.** As `ρ → 1⁻` for `‖β‖ > 1`, the model-space
defect projection `avg ‖modelPart β ρ‖²` converges to `1 − ‖β‖⁻² = 1 − exp(−2 posLog ‖β‖) > 0`,
while `avg ‖antiHoloPart β ρ‖² → 0` and `avg ‖factorQuotient β ρ‖² → 1`. -/
theorem tendsto_circleAverage_modelPart_sq {β : ℂ} (hβ : 1 < ‖β‖) :
    1 - ‖β‖⁻¹ ^ 2 = 1 - Real.exp (-2 * Real.posLog ‖β‖) ∧
      0 < 1 - ‖β‖⁻¹ ^ 2 ∧
      Tendsto (fun ρ : ℝ => Real.circleAverage (fun v => ‖modelPart β ρ v‖ ^ 2) 0 1)
        (𝓝[<] 1) (𝓝 (1 - ‖β‖⁻¹ ^ 2)) ∧
      Tendsto (fun ρ : ℝ => Real.circleAverage (fun v => ‖antiHoloPart β ρ v‖ ^ 2) 0 1)
        (𝓝[<] 1) (𝓝 0) ∧
      Tendsto (fun ρ : ℝ => Real.circleAverage (fun v => ‖factorQuotient β ρ v‖ ^ 2) 0 1)
        (𝓝[<] 1) (𝓝 1) := by
  have hβ0 : 0 < ‖β‖ := zero_lt_one.trans hβ
  have hexp : ‖β‖⁻¹ ^ 2 = Real.exp (-2 * Real.posLog ‖β‖) := by
    rw [Real.posLog_eq_log (by rw [abs_of_pos hβ0]; exact hβ.le),
      show -2 * Real.log ‖β‖ = -(2 * Real.log ‖β‖) by ring, Real.exp_neg,
      ← Real.log_rpow hβ0, Real.exp_log (Real.rpow_pos_of_pos hβ0 2), Real.rpow_two, inv_pow]
  have hpos : 0 < 1 - ‖β‖⁻¹ ^ 2 := by
    have h1 : ‖β‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
    nlinarith [inv_nonneg.mpr hβ0.le]
  have hev : ∀ᶠ ρ : ℝ in 𝓝[<] 1, ‖β‖⁻¹ < ρ ∧ ρ < 1 :=
    Ioo_mem_nhdsLT (inv_lt_one_of_one_lt₀ hβ)
  have ht_id : Tendsto (fun ρ : ℝ => ρ) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht_inv : Tendsto (fun ρ : ℝ => ρ⁻¹) (𝓝[<] 1) (𝓝 1) := by
    simpa only [inv_one] using ht_id.inv₀ one_ne_zero
  have ht_model : Tendsto (fun ρ : ℝ => ρ⁻¹ ^ 2 * (1 - ‖β‖⁻¹ ^ 2))
      (𝓝[<] 1) (𝓝 (1 - ‖β‖⁻¹ ^ 2)) := by
    have h := (ht_inv.pow 2).mul_const (1 - ‖β‖⁻¹ ^ 2)
    simpa only [one_pow, one_mul] using h
  have ht_beurl : Tendsto (fun ρ : ℝ => ρ⁻¹ ^ 2 * ‖β‖⁻¹ ^ 2)
      (𝓝[<] 1) (𝓝 (‖β‖⁻¹ ^ 2)) := by
    have h := (ht_inv.pow 2).mul_const (‖β‖⁻¹ ^ 2)
    simpa only [one_pow, one_mul] using h
  have ht_anti : Tendsto (fun ρ : ℝ => (1 - ρ⁻¹) ^ 2 / (ρ ^ 2 * ‖β‖ ^ 2 - 1))
      (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun ρ : ℝ => (1 - ρ⁻¹) ^ 2 / (ρ ^ 2 * ‖β‖ ^ 2 - 1)) 1 := by
      refine ContinuousAt.div
        ((continuousAt_const.sub (continuousAt_id.inv₀ one_ne_zero)).pow 2)
        (((continuousAt_id.pow 2).mul continuousAt_const).sub continuousAt_const) ?_
      nlinarith [hβ]
    have h0 : (1 - (1 : ℝ)⁻¹) ^ 2 / ((1 : ℝ) ^ 2 * ‖β‖ ^ 2 - 1) = 0 := by simp
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨by rw [hexp], hpos, ?_, ?_, ?_⟩
  · refine ht_model.congr' ?_
    filter_upwards [hev] with ρ ⟨h1, _⟩
    exact (supercritical_pythagorean_split hβ h1).2.1.symm
  · refine ht_anti.congr' ?_
    filter_upwards [hev] with ρ ⟨h1, _⟩
    exact (supercritical_pythagorean_split hβ h1).2.2.1.symm
  · have ht_sum : Tendsto (fun ρ : ℝ =>
        ρ⁻¹ ^ 2 * ‖β‖⁻¹ ^ 2 + ρ⁻¹ ^ 2 * (1 - ‖β‖⁻¹ ^ 2) +
          (1 - ρ⁻¹) ^ 2 / (ρ ^ 2 * ‖β‖ ^ 2 - 1)) (𝓝[<] 1) (𝓝 1) := by
      have h := (ht_beurl.add ht_model).add ht_anti
      have h1 : ‖β‖⁻¹ ^ 2 + (1 - ‖β‖⁻¹ ^ 2) + 0 = (1 : ℝ) := by ring
      rwa [h1] at h
    refine ht_sum.congr' ?_
    filter_upwards [hev] with ρ ⟨h1, _⟩
    obtain ⟨hb, hm, ha, -, -, -, htot⟩ := supercritical_pythagorean_split hβ h1
    rw [htot, hb, hm, ha]

/-- **Golden calibration.** On the exterior factor `β₀ = φ` of `goldenDatum`, the boundary model-space
defect limit is `φ⁻¹ = 1 − φ⁻² > 0`, recovering `innerMass goldenDatum = log φ` while the full
`L²(𝕋)` quotient mean forgets it (`→ 1`). -/
theorem golden_exterior_modelPart_limit :
    Tendsto (fun ρ : ℝ => Real.circleAverage (fun v => ‖modelPart (goldenDatum.β 0) ρ v‖ ^ 2) 0 1)
      (𝓝[<] 1) (𝓝 Real.goldenRatio⁻¹) := by
  have h0 : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hnorm : ‖goldenDatum.β 0‖ = Real.goldenRatio := by
    change ‖((Real.goldenRatio : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg h0.le]
  have hβ1 : 1 < ‖goldenDatum.β 0‖ := by rw [hnorm]; exact Real.one_lt_goldenRatio
  have hlim := (tendsto_circleAverage_modelPart_sq hβ1).2.2.1
  have hval : 1 - ‖goldenDatum.β 0‖⁻¹ ^ 2 = Real.goldenRatio⁻¹ := by
    rw [hnorm]
    apply mul_right_cancel₀ (pow_ne_zero 2 h0.ne')
    have hinv : Real.goldenRatio⁻¹ * Real.goldenRatio = 1 := inv_mul_cancel₀ h0.ne'
    calc (1 - Real.goldenRatio⁻¹ ^ 2) * Real.goldenRatio ^ 2
        = Real.goldenRatio ^ 2 - (Real.goldenRatio⁻¹ * Real.goldenRatio) ^ 2 := by ring
      _ = (Real.goldenRatio + 1) - 1 ^ 2 := by rw [Real.goldenRatio_sq, hinv]
      _ = (Real.goldenRatio⁻¹ * Real.goldenRatio) * Real.goldenRatio := by rw [hinv]; ring
      _ = Real.goldenRatio⁻¹ * Real.goldenRatio ^ 2 := by ring
  rwa [hval] at hlim

/-! ### 2. Shifted inner field, macroscopic single-shift RH criterion, and first-order jet -/

/-- Horizontal shift `(s + δ − 1) ζ(s + δ)` of the entire zeta datum. -/
def zetaEntireShift (δ : ℝ) (s : ℂ) : ℂ :=
  zetaEntire (s + δ)

/-- The shifted inner field `I_δ(w)` read along the line `Re s = 1/2 + δ`. -/
def shiftedInnerField (δ : ℝ) (w : ℂ) : ℝ :=
  (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ) +
    Real.log ‖w - (δ : ℂ)‖ - Real.log ‖zetaEntire (w + (δ : ℂ))‖

/-- Contribution of a right zero `ρ` to `I_δ(w)`: active iff `Re ρ > 1/2 + δ`. -/
def shiftedZeroTerm (δ : ℝ) (w : ℂ) (ρ : ZetaRightZero) : ℝ :=
  if 1 / 2 + δ < (ρ : ℂ).re then zeroMult ρ * greenKernel w ((ρ : ℂ) - δ) else 0

theorem isHalfPlaneDatum_zetaEntireShift {δ : ℝ} (hδ : 0 ≤ δ) :
    IsHalfPlaneDatum (zetaEntireShift δ) := by
  obtain ⟨K, hK1, hK⟩ := isHalfPlaneDatum_zetaEntire.growth
  refine ⟨differentiable_zetaEntire.comp (differentiable_id.add_const (δ : ℂ)),
    K * (1 + δ) ^ 2, by nlinarith, fun s hs => ?_⟩
  have hre : 1 / 2 ≤ (s + (δ : ℂ)).re := by simp; linarith
  have h1 := hK (s + (δ : ℂ)) hre
  have h2 : ‖s + (δ : ℂ)‖ + 2 ≤ (1 + δ) * (‖s‖ + 2) := by
    have hn : ‖s + (δ : ℂ)‖ ≤ ‖s‖ + δ := by
      refine (norm_add_le s (δ : ℂ)).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hδ]
    nlinarith [norm_nonneg s]
  have hsq : (‖s + (δ : ℂ)‖ + 2) ^ 2 ≤ ((1 + δ) * (‖s‖ + 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  calc ‖zetaEntireShift δ s‖ ≤ K * (‖s + (δ : ℂ)‖ + 2) ^ 2 := h1
    _ ≤ K * ((1 + δ) * (‖s‖ + 2)) ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
    _ = K * (1 + δ) ^ 2 * (‖s‖ + 2) ^ 2 := by ring

theorem isCentre_zetaEntireShift {δ : ℝ} (hδ : 0 ≤ δ) {w : ℂ} (hw : 1 / 2 < w.re)
    (h0 : zetaEntire (w + (δ : ℂ)) ≠ 0) :
    IsCentre (zetaEntireShift δ) w := by
  have hw' : 1 / 2 < (w + (δ : ℂ)).re := by simp; linarith
  obtain ⟨-, -, c, σ₁, hc, hray⟩ := isCentre_zetaEntire hw' h0
  refine ⟨hw, h0, c, σ₁, hc, fun σ hσ => ?_⟩
  have heq : (σ : ℂ) + (w.im : ℂ) * I + (δ : ℂ) =
      (((σ + δ : ℝ)) : ℂ) + ((w + (δ : ℂ)).im : ℂ) * I := by
    simp [Complex.add_im]
    ring
  change c ≤ ‖zetaEntire ((σ : ℂ) + (w.im : ℂ) * I + (δ : ℂ))‖
  rw [heq]
  exact hray (σ + δ) (by linarith)

private theorem norm_shifted_line_sub_one (δ τ : ℝ) :
    ‖(1 / 2 + (δ : ℂ) + τ * I) - 1‖ = ‖(1 / 2 + τ * I : ℂ) - (δ : ℂ)‖ := by
  have heq : (1 / 2 + (δ : ℂ) + τ * I) - 1 = -conj ((1 / 2 + τ * I : ℂ) - (δ : ℂ)) := by
    apply Complex.ext
    · simp; ring
    · simp
  rw [heq, norm_neg, Complex.norm_conj]

private theorem integral_log_norm_line_sub_poisson {δ : ℝ} (hδ1 : δ ≤ 1 / 2)
    {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ => Real.log ‖(1 / 2 + τ * I : ℂ) - (δ : ℂ)‖ * halfPlanePoissonKernel w τ) ∧
      ∫ τ : ℝ, Real.log ‖(1 / 2 + τ * I : ℂ) - (δ : ℂ)‖ * halfPlanePoissonKernel w τ =
        Real.log ‖w - (δ : ℂ)‖ := by
  have hdatum : IsHalfPlaneDatum (fun z : ℂ => z - (δ : ℂ)) := by
    refine ⟨differentiable_id.sub_const (δ : ℂ), 1 + |δ|, by linarith [abs_nonneg δ], fun s _ => ?_⟩
    have hn : ‖s - (δ : ℂ)‖ ≤ ‖s‖ + |δ| := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using norm_sub_le s (δ : ℂ)
    have hsq : ‖s‖ + 1 ≤ (‖s‖ + 2) ^ 2 := by nlinarith [norm_nonneg s]
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 1 + |δ|)
    nlinarith [hn, hmul, norm_nonneg s, abs_nonneg δ]
  have hw_ne : w - (δ : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp at hre
    linarith
  have hcentre : IsCentre (fun z : ℂ => z - (δ : ℂ)) w := by
    refine ⟨hw, hw_ne, 1, δ + 1, one_pos, fun σ hσ => ?_⟩
    have h := Complex.abs_re_le_norm (((σ : ℂ) + (w.im : ℂ) * I) - (δ : ℂ))
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero] at h
    rw [abs_of_nonneg (by linarith)] at h
    linarith
  refine integrable_and_integral_log_of_no_right_zeros hdatum hcentre fun ρ hρ h0 => ?_
  have hre := congrArg Complex.re h0
  simp at hre
  linarith

private theorem ae_log_zetaEntireShift_line (δ : ℝ) :
    ∀ᵐ τ : ℝ, Real.log ‖zetaEntire (1 / 2 + (δ : ℂ) + τ * I)‖ =
      Real.log ‖(1 / 2 + τ * I : ℂ) - (δ : ℂ)‖ +
        Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ := by
  have hinj : Function.Injective (fun τ : ℝ => (1 / 2 : ℂ) + (δ : ℂ) + τ * I) := by
    intro a b hab
    have := congrArg Complex.im hab
    simpa using this
  have hcount : ({0} ∪ {τ : ℝ | zetaEntire (1 / 2 + (δ : ℂ) + τ * I) = 0}).Countable :=
    (countable_singleton 0).union (countable_setOf_zetaEntire_eq_zero.preimage hinj)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hcount.measure_zero _)] with τ hτ
  have hτ0 : τ ≠ 0 := fun h0 => hτ (Or.inl h0)
  have hE_ne : zetaEntire (1 / 2 + (δ : ℂ) + τ * I) ≠ 0 := fun h0 => hτ (Or.inr h0)
  have hs1 : (1 / 2 + (δ : ℂ) + τ * I) ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    simp at him
    exact hτ0 him
  have hzeta_ne : riemannZeta (1 / 2 + (δ : ℂ) + τ * I) ≠ 0 :=
    fun hz => hE_ne (zetaEntire_eq_zero_iff.mpr hz)
  rw [zetaEntire_eq hs1, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1)) (norm_ne_zero_iff.mpr hzeta_ne),
    norm_shifted_line_sub_one]

/-- **Shifted Poisson–Jensen identity.** For `0 ≤ δ ≤ 1/2` and any `w` (`Re w > 1/2`) with
`zetaEntire(w + δ) ≠ 0`, `shiftedInnerField δ w` is the Green potential of right zeros with
`Re ρ > 1/2 + δ`, shifted left by `δ`. -/
theorem hasSum_shiftedInnerField {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    {w : ℂ} (hw : 1 / 2 < w.re) (h0 : zetaEntire (w + (δ : ℂ)) ≠ 0) :
    Integrable (fun τ : ℝ =>
      Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ) ∧
      HasSum (shiftedZeroTerm δ w) (shiftedInnerField δ w) := by
  obtain ⟨hint_E, hsum_E⟩ := hasSum_poissonJensen (isHalfPlaneDatum_zetaEntireShift hδ0)
    (isCentre_zetaEntireShift hδ0 hw h0)
  obtain ⟨hint_L, hval_L⟩ := integral_log_norm_line_sub_poisson hδ1 hw
  have hae : (fun τ : ℝ =>
      Real.log ‖zetaEntireShift δ (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ -
        Real.log ‖(1 / 2 + τ * I : ℂ) - (δ : ℂ)‖ * halfPlanePoissonKernel w τ) =ᵐ[volume]
      fun τ => Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ := by
    filter_upwards [ae_log_zetaEntireShift_line δ] with τ hτ
    have hpt : (1 / 2 + τ * I : ℂ) + (δ : ℂ) = 1 / 2 + (δ : ℂ) + τ * I := by ring
    change Real.log ‖zetaEntire ((1 / 2 + τ * I : ℂ) + (δ : ℂ))‖ * halfPlanePoissonKernel w τ - _ = _
    rw [hpt, hτ]
    ring
  have hint_Z : Integrable (fun τ : ℝ =>
      Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ) :=
    (hint_E.sub hint_L).congr hae
  have hint_eq : ∫ τ : ℝ, Real.log ‖zetaEntireShift δ (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ =
      (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ) +
        Real.log ‖w - (δ : ℂ)‖ := by
    have hsub_eq := integral_congr_ae hae
    rw [integral_sub hint_E hint_L, hval_L] at hsub_eq
    linarith
  refine ⟨hint_Z, ?_⟩
  rw [hint_eq] at hsum_E
  -- Equivalence between `RightZeros (zetaEntireShift δ)` and `{ρ : ZetaRightZero | 1/2 + δ < Re ρ}`
  let e : RightZeros (zetaEntireShift δ) ≃ {ρ : ZetaRightZero // 1 / 2 + δ < (ρ : ℂ).re} :=
    { toFun := fun s => ⟨⟨(s : ℂ) + (δ : ℂ), zetaEntire_eq_zero_iff.mp s.2.1,
          by simp; linarith [s.2.2]⟩, by simp; linarith [s.2.2]⟩
      invFun := fun ρ => ⟨(ρ.1 : ℂ) - (δ : ℂ),
        by simp [zetaEntireShift, zetaEntire_eq_zero_iff.mpr ρ.1.2.1],
        by simp; linarith [ρ.2]⟩
      left_inv := fun s => by apply Subtype.ext; simp
      right_inv := fun ρ => by apply Subtype.ext; apply Subtype.ext; simp }
  have ht := e.symm.hasSum_iff.mpr hsum_E
  have hfun : ((fun s : RightZeros (zetaEntireShift δ) =>
      (analyticOrderNatAt (zetaEntireShift δ) s : ℝ) * greenKernel w s) ∘ e.symm) =
      (fun ρ : {ρ : ZetaRightZero // 1 / 2 + δ < (ρ : ℂ).re} =>
        shiftedZeroTerm δ w ρ.1) := by
    funext ρ
    have hord_eq : analyticOrderAt (zetaEntireShift δ) ((ρ.1 : ℂ) - (δ : ℂ)) =
        analyticOrderAt zetaEntire (ρ.1 : ℂ) := by
      have han : AnalyticAt ℂ (fun z : ℂ => z + (δ : ℂ)) ((ρ.1 : ℂ) - (δ : ℂ)) :=
        analyticAt_id.add analyticAt_const
      have hd : deriv (fun z : ℂ => z + (δ : ℂ)) ((ρ.1 : ℂ) - (δ : ℂ)) ≠ 0 := by
        rw [((hasDerivAt_id' ((ρ.1 : ℂ) - (δ : ℂ))).add_const (δ : ℂ)).deriv]
        exact one_ne_zero
      have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := zetaEntire) han hd
      unfold zetaEntireShift
      simpa only [Function.comp_def, sub_add_cancel] using hcomp
    have hmult : (analyticOrderNatAt (zetaEntireShift δ) ((ρ.1 : ℂ) - (δ : ℂ)) : ℝ) =
        zeroMult ρ.1 := by
      rw [zeroMult, ← analyticOrderNatAt_zetaEntire ρ.1.ne_one]
      simp only [analyticOrderNatAt, hord_eq]
    change (analyticOrderNatAt (zetaEntireShift δ) ((ρ.1 : ℂ) - (δ : ℂ)) : ℝ) *
      greenKernel w ((ρ.1 : ℂ) - (δ : ℂ)) = _
    rw [hmult, shiftedZeroTerm, if_pos ρ.2]
  rw [hfun] at ht
  have hsupp : Function.support (shiftedZeroTerm δ w) ⊆
      {ρ : ZetaRightZero | 1 / 2 + δ < (ρ : ℂ).re} := by
    intro ρ hρ
    by_contra hnot
    have hnot' : ¬ (1 / 2 + δ < (ρ : ℂ).re) := hnot
    exact hρ (by rw [shiftedZeroTerm, if_neg hnot'])
  exact (hasSum_subtype_iff_of_support_subset hsupp).mp ht

theorem ZetaRightZero.re_lt_one (ρ : ZetaRightZero) : (ρ : ℂ).re < 1 :=
  lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h ρ.2.1

private theorem greenKernel_one_eq (z : ℂ) :
    greenKernel 1 z = Real.log (‖z‖ / ‖z - 1‖) := by
  simp [greenKernel]

private theorem norm_sub_ofReal_sq (z : ℂ) (a : ℝ) :
    ‖z - (a : ℂ)‖ ^ 2 = (z.re - a) ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

private theorem norm_sq_re_im (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa using norm_sub_ofReal_sq z 0

private theorem greenKernel_one_strict_mono_shift {ρ : ZetaRightZero} {δ : ℝ}
    (hδ0 : 0 < δ) (hρδ : 1 / 2 + δ < (ρ : ℂ).re) :
    greenKernel 1 ((ρ : ℂ) - (δ : ℂ)) < greenKernel 1 (ρ : ℂ) := by
  have hu₂1 : (ρ : ℂ).re < 1 := ρ.re_lt_one
  have hu₁_half : 1 / 2 < (ρ : ℂ).re - δ := by linarith
  have h_n1 : ‖(ρ : ℂ) - (δ : ℂ)‖ ^ 2 = ((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2 :=
    norm_sub_ofReal_sq (ρ : ℂ) δ
  have h_d1 : ‖((ρ : ℂ) - (δ : ℂ)) - 1‖ ^ 2 = (((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
    have h := norm_sub_ofReal_sq ((ρ : ℂ) - (δ : ℂ)) 1
    simpa only [Complex.ofReal_one, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero] using h
  have h_n2 : ‖(ρ : ℂ)‖ ^ 2 = (ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2 := norm_sq_re_im (ρ : ℂ)
  have h_d2 : ‖(ρ : ℂ) - 1‖ ^ 2 = ((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
    simpa only [Complex.ofReal_one] using norm_sub_ofReal_sq (ρ : ℂ) 1
  have hd1_pos : 0 < (((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
    nlinarith [hδ0, hu₂1, sq_nonneg (ρ : ℂ).im]
  have hd2_pos : 0 < ((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
    nlinarith [hu₂1, sq_nonneg (ρ : ℂ).im]
  have hn1_pos : 0 < ((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2 := by
    nlinarith [hu₁_half, sq_nonneg (ρ : ℂ).im]
  have hcross : (((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2) * (((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2) <
      ((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2) * ((((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2) := by
    have hdiff : ((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2) * ((((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2) -
        (((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2) * (((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2) =
        δ * (2 * (ρ : ℂ).im ^ 2 + ((ρ : ℂ).re - δ) * (1 - (ρ : ℂ).re) +
          (ρ : ℂ).re * (1 - ((ρ : ℂ).re - δ))) := by ring
    have hfactor : 0 < 2 * (ρ : ℂ).im ^ 2 + ((ρ : ℂ).re - δ) * (1 - (ρ : ℂ).re) +
        (ρ : ℂ).re * (1 - ((ρ : ℂ).re - δ)) := by
      nlinarith [sq_nonneg (ρ : ℂ).im, hu₁_half, hδ0, hu₂1]
    nlinarith [hdiff, mul_pos hδ0 hfactor]
  have hsq_lt : (‖(ρ : ℂ) - (δ : ℂ)‖ / ‖((ρ : ℂ) - (δ : ℂ)) - 1‖) ^ 2 <
      (‖(ρ : ℂ)‖ / ‖(ρ : ℂ) - 1‖) ^ 2 := by
    rw [div_pow, div_pow, h_n1, h_d1, h_n2, h_d2, div_lt_div_iff₀ hd1_pos hd2_pos]
    exact hcross
  have hn1_norm : 0 < ‖(ρ : ℂ) - (δ : ℂ)‖ := by
    by_contra hle
    have h0 : ‖(ρ : ℂ) - (δ : ℂ)‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    nlinarith [h_n1, hn1_pos, h0]
  have hd1_norm : 0 < ‖((ρ : ℂ) - (δ : ℂ)) - 1‖ := by
    by_contra hle
    have h0 : ‖((ρ : ℂ) - (δ : ℂ)) - 1‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    nlinarith [h_d1, hd1_pos, h0]
  rw [greenKernel_one_eq, greenKernel_one_eq]
  exact Real.log_lt_log (div_pos hn1_norm hd1_norm) (lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq_lt)

/-- Exact decomposition of the logarithmic dilation integral at `w = 1` for `δ ∈ (0, 1/2]`. -/
theorem integral_log_dilation_quotient_eq {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (∫ τ : ℝ, (Real.log ‖riemannZeta (1 / 2 + τ * I)‖ -
        Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ) =
      (innerField 1 - shiftedInnerField δ 1) +
        Real.log ((1 - δ) / (δ * ‖riemannZeta (1 + (δ : ℂ))‖)) ∧
      HasSum (fun ρ : ZetaRightZero => zeroMult ρ * greenKernel 1 ρ - shiftedZeroTerm δ 1 ρ)
        (innerField 1 - shiftedInnerField δ 1) := by
  have hw1 : (1 / 2 : ℝ) < (1 : ℂ).re := by simp; norm_num
  have h1δ_re : 1 ≤ ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
  have hzeta_ne : riemannZeta (1 + (δ : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1δ_re
  have hEδ_ne : zetaEntire ((1 : ℂ) + (δ : ℂ)) ≠ 0 := zetaEntire_ne_zero_of_zeta_ne_zero hzeta_ne
  obtain ⟨hint_shift, hsum_shift⟩ := hasSum_shiftedInnerField hδ0.le hδ1 hw1 hEδ_ne
  have hint_0 := integrable_log_zeta_poisson hw1
  have hsum_0 := hasSum_innerField hw1 zetaEntire_one_ne_zero
  refine ⟨?_, hsum_0.sub hsum_shift⟩
  have hsub_pt : (fun τ : ℝ => (Real.log ‖riemannZeta (1 / 2 + τ * I)‖ -
      Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ) =
      fun τ : ℝ => Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel 1 τ -
        Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel 1 τ := by
    funext τ; ring
  rw [hsub_pt, integral_sub hint_0 hint_shift]
  have h1_sub : ‖(1 : ℂ) - (δ : ℂ)‖ = 1 - δ := by
    have hc : (1 : ℂ) - (δ : ℂ) = ((1 - δ : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hE_val : ‖zetaEntire ((1 : ℂ) + (δ : ℂ))‖ = δ * ‖riemannZeta (1 + (δ : ℂ))‖ := by
    have hne1 : (1 : ℂ) + (δ : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [zetaEntire_eq hne1, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hδ0.le]
  have hlog_comb : Real.log (1 - δ) - Real.log (δ * ‖riemannZeta (1 + (δ : ℂ))‖) =
      Real.log ((1 - δ) / (δ * ‖riemannZeta (1 + (δ : ℂ))‖)) :=
    (Real.log_div (by linarith) (mul_pos hδ0 (norm_pos_iff.mpr hzeta_ne)).ne').symm
  rw [innerField, shiftedInnerField, norm_one, Real.log_one, zetaEntire_eval_one, norm_one,
    Real.log_one, h1_sub, hE_val, ← hlog_comb]
  ring

/-- **Macroscopic single-shift RH equivalence.** Every single horizontal shift `δ ∈ (0, 1/2)`
already decides the Riemann Hypothesis via the logarithmic Poisson mean of the dilation quotient:
no limit in `δ` is required, because `greenKernel 1 (ρ − δ) < greenKernel 1 ρ` strictly on the strip. -/
theorem riemannHypothesis_iff_log_dilation_quotient_eq {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    (0 ≤ innerField 1 - shiftedInnerField δ 1) ∧
      (RiemannHypothesis ↔
        (∫ τ : ℝ, (Real.log ‖riemannZeta (1 / 2 + τ * I)‖ -
            Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ) =
          Real.log ((1 - δ) / (δ * ‖riemannZeta (1 + (δ : ℂ))‖))) := by
  obtain ⟨hid, hsum⟩ := integral_log_dilation_quotient_eq hδ0 hδ1.le
  have hterm_pos : ∀ ρ : ZetaRightZero,
      0 < zeroMult ρ * greenKernel 1 ρ - shiftedZeroTerm δ 1 ρ := fun ρ => by
    rw [shiftedZeroTerm]
    split_ifs with hρδ
    · rw [← mul_sub]
      exact mul_pos (zeroMult_pos ρ) (sub_pos.mpr (greenKernel_one_strict_mono_shift hδ0 hρδ))
    · rw [sub_zero]
      exact mul_pos (zeroMult_pos ρ) (greenKernel_pos (by simp; norm_num) ρ.2.2 ρ.ne_one)
  have hnn : 0 ≤ innerField 1 - shiftedInnerField δ 1 :=
    hsum.nonneg fun ρ => (hterm_pos ρ).le
  refine ⟨hnn, ?_⟩
  rw [hid]
  constructor
  · intro hRH
    have hemp : IsEmpty ZetaRightZero := ⟨fun ρ =>
      (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) ρ ρ.2.2 ρ.2.1⟩
    have h0 : innerField 1 - shiftedInnerField δ 1 = 0 := hsum.unique hasSum_empty
    linarith
  · intro heq
    have hdiff0 : innerField 1 - shiftedInnerField δ 1 = 0 := by linarith
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
    intro z hz hzz
    let ρ : ZetaRightZero := ⟨z, hzz, hz⟩
    have hle := sum_le_hasSum ({ρ} : Finset ZetaRightZero)
      (fun a _ => (hterm_pos a).le) hsum
    rw [Finset.sum_singleton, hdiff0] at hle
    exact absurd hle (not_le.mpr (hterm_pos ρ))

/-- Divided Green-kernel difference `Δ_δ(ρ) = δ⁻¹ (G(1, ρ) − 1_{Re ρ > 1/2 + δ} G(1, ρ − δ))`. -/
def greenSlopeTerm (δ : ℝ) (ρ : ZetaRightZero) : ℝ :=
  δ⁻¹ * (greenKernel 1 ρ - if 1 / 2 + δ < (ρ : ℂ).re then greenKernel 1 ((ρ : ℂ) - (δ : ℂ)) else 0)

private theorem real_log_shift_bound {x y δ : ℝ} (hδ : 0 < δ) (hu : 1 / 2 < x - δ) (hx1 : x < 1) :
    δ⁻¹ * ((1 / 2) * Real.log (((x ^ 2 + y ^ 2) / ((x - 1) ^ 2 + y ^ 2)) /
      (((x - δ) ^ 2 + y ^ 2) / (((x - δ) - 1) ^ 2 + y ^ 2)))) ≤
      2 / ((x - 1) ^ 2 + y ^ 2) := by
  have hA : 0 < x ^ 2 + y ^ 2 := by nlinarith [hu, hδ, sq_nonneg y]
  have hB : 0 < (x - 1) ^ 2 + y ^ 2 := by nlinarith [hx1, sq_nonneg y]
  have hC : 0 < (x - δ) ^ 2 + y ^ 2 := by nlinarith [hu, sq_nonneg y]
  have hD : 0 < ((x - δ) - 1) ^ 2 + y ^ 2 := by nlinarith [hu, hx1, hδ, sq_nonneg y]
  have hpoly : (x ^ 2 + y ^ 2) * (((x - δ) - 1) ^ 2 + y ^ 2) -
      ((x - 1) ^ 2 + y ^ 2) * ((x - δ) ^ 2 + y ^ 2) ≤ 4 * δ * ((x - δ) ^ 2 + y ^ 2) := by
    have h1 : (x ^ 2 + y ^ 2) * (((x - δ) - 1) ^ 2 + y ^ 2) -
        ((x - 1) ^ 2 + y ^ 2) * ((x - δ) ^ 2 + y ^ 2) =
        δ * (2 * y ^ 2 + (x - δ) * (1 - x) + x * (1 - (x - δ))) := by ring
    have h2 : 2 * y ^ 2 + (x - δ) * (1 - x) + x * (1 - (x - δ)) ≤
        4 * ((x - δ) ^ 2 + y ^ 2) := by
      nlinarith [sq_nonneg y, hu, hx1, hδ]
    rw [h1, show 4 * δ * ((x - δ) ^ 2 + y ^ 2) = δ * (4 * ((x - δ) ^ 2 + y ^ 2)) by ring]
    exact mul_le_mul_of_nonneg_left h2 hδ.le
  have hfrac : ∀ {a b c d : ℝ}, b ≠ 0 → c ≠ 0 →
      (a / b) / (c / d) - 1 = (a * d - b * c) / (b * c) := fun {a b c d} hb hc => by
    rw [div_eq_mul_inv (a / b), inv_div, div_mul_div_comm, sub_div, div_self (mul_ne_zero hb hc)]
  have hlog := Real.log_le_sub_one_of_pos (div_pos (div_pos hA hB) (div_pos hC hD))
  have hsub_le : ((x ^ 2 + y ^ 2) / ((x - 1) ^ 2 + y ^ 2)) /
      (((x - δ) ^ 2 + y ^ 2) / (((x - δ) - 1) ^ 2 + y ^ 2)) - 1 ≤
      (4 * δ) / ((x - 1) ^ 2 + y ^ 2) := by
    rw [hfrac hB.ne' hC.ne', div_le_div_iff₀ (mul_pos hB hC) hB]
    have h3 := mul_le_mul_of_nonneg_right hpoly hB.le
    linarith
  calc δ⁻¹ * ((1 / 2) * Real.log (((x ^ 2 + y ^ 2) / ((x - 1) ^ 2 + y ^ 2)) /
          (((x - δ) ^ 2 + y ^ 2) / (((x - δ) - 1) ^ 2 + y ^ 2))))
      ≤ δ⁻¹ * ((1 / 2) * ((4 * δ) / ((x - 1) ^ 2 + y ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hlog.trans hsub_le) (by norm_num))
          (inv_nonneg.mpr hδ.le)
    _ = (δ⁻¹ * δ) * (2 / ((x - 1) ^ 2 + y ^ 2)) := by simp only [div_eq_mul_inv]; ring
    _ = 2 / ((x - 1) ^ 2 + y ^ 2) := by rw [inv_mul_cancel₀ hδ.ne', one_mul]

private theorem real_log_boundary_bound {x y δ : ℝ} (hδ : 0 < δ) (hx : 1 / 2 < x)
    (hxδ : x ≤ 1 / 2 + δ) (hx1 : x < 1) :
    δ⁻¹ * ((1 / 2) * Real.log ((x ^ 2 + y ^ 2) / ((x - 1) ^ 2 + y ^ 2))) ≤
      2 / ((x - 1) ^ 2 + y ^ 2) := by
  have hA : 0 < x ^ 2 + y ^ 2 := by nlinarith [hx, sq_nonneg y]
  have hB : 0 < (x - 1) ^ 2 + y ^ 2 := by nlinarith [hx1, sq_nonneg y]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hA hB)
  have hsub : (x ^ 2 + y ^ 2) / ((x - 1) ^ 2 + y ^ 2) - 1 =
      (2 * x - 1) / ((x - 1) ^ 2 + y ^ 2) := by
    have hnum : 2 * x - 1 = (x ^ 2 + y ^ 2) - ((x - 1) ^ 2 + y ^ 2) := by ring
    rw [hnum, sub_div, div_self hB.ne']
  have hlog' : Real.log ((x ^ 2 + y ^ 2) / ((x - 1) ^ 2 + y ^ 2)) ≤
      (2 * x - 1) / ((x - 1) ^ 2 + y ^ 2) := by rwa [hsub] at hlog
  have hdiv_le : (2 * x - 1) / ((x - 1) ^ 2 + y ^ 2) ≤ (4 * δ) / ((x - 1) ^ 2 + y ^ 2) :=
    div_le_div_of_nonneg_right (by linarith) hB.le
  calc δ⁻¹ * ((1 / 2) * Real.log ((x ^ 2 + y ^ 2) / ((x - 1) ^ 2 + y ^ 2)))
      ≤ δ⁻¹ * ((1 / 2) * ((4 * δ) / ((x - 1) ^ 2 + y ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hlog'.trans hdiv_le) (by norm_num))
          (inv_nonneg.mpr hδ.le)
    _ = (δ⁻¹ * δ) * (2 / ((x - 1) ^ 2 + y ^ 2)) := by simp only [div_eq_mul_inv]; ring
    _ = 2 / ((x - 1) ^ 2 + y ^ 2) := by rw [inv_mul_cancel₀ hδ.ne', one_mul]

private theorem greenSlopeTerm_nonneg_and_le {δ : ℝ} (hδ : 0 < δ) (ρ : ZetaRightZero) :
    0 ≤ greenSlopeTerm δ ρ ∧ greenSlopeTerm δ ρ ≤ 2 / ‖(ρ : ℂ) - 1‖ ^ 2 := by
  have hx_half : 1 / 2 < (ρ : ℂ).re := ρ.2.2
  have hx1 : (ρ : ℂ).re < 1 := ρ.re_lt_one
  have hnorm_sub : ‖(ρ : ℂ) - 1‖ ^ 2 = ((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
    simpa only [Complex.ofReal_one] using norm_sub_ofReal_sq (ρ : ℂ) 1
  have hnorm_ρ : ‖(ρ : ℂ)‖ ^ 2 = (ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2 := norm_sq_re_im (ρ : ℂ)
  have hd_pos : 0 < ‖(ρ : ℂ) - 1‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ρ.ne_one)) 2
  have hn2_pos : 0 < (ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2 := by nlinarith [hx_half, sq_nonneg (ρ : ℂ).im]
  have hd2_pos : 0 < ((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by rw [← hnorm_sub]; exact hd_pos
  have hG_ρ : greenKernel 1 (ρ : ℂ) =
      (1 / 2) * Real.log (((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2) / (((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2)) := by
    rw [greenKernel_one_eq, ← hnorm_ρ, ← hnorm_sub, ← div_pow, Real.log_pow]
    push_cast; ring
  rw [greenSlopeTerm, hnorm_sub]
  split_ifs with hρδ
  · refine ⟨mul_nonneg (inv_nonneg.mpr hδ.le)
        (sub_nonneg.mpr (greenKernel_one_strict_mono_shift hδ hρδ).le), ?_⟩
    have hu₁_half : 1 / 2 < (ρ : ℂ).re - δ := by linarith
    have hn1_sq : ‖(ρ : ℂ) - (δ : ℂ)‖ ^ 2 = ((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2 :=
      norm_sub_ofReal_sq (ρ : ℂ) δ
    have hd1_sq : ‖((ρ : ℂ) - (δ : ℂ)) - 1‖ ^ 2 = (((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
      simpa only [Complex.ofReal_one, Complex.sub_re, Complex.ofReal_re,
        Complex.sub_im, Complex.ofReal_im, sub_zero] using norm_sub_ofReal_sq ((ρ : ℂ) - (δ : ℂ)) 1
    have hn1_pos : 0 < ((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2 := by
      nlinarith [hu₁_half, sq_nonneg (ρ : ℂ).im]
    have hd1_pos : 0 < (((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
      nlinarith [hu₁_half, hx1, hδ, sq_nonneg (ρ : ℂ).im]
    have hG_shift : greenKernel 1 ((ρ : ℂ) - (δ : ℂ)) =
        (1 / 2) * Real.log ((((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2) /
          ((((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2)) := by
      rw [greenKernel_one_eq, ← hn1_sq, ← hd1_sq, ← div_pow, Real.log_pow]
      push_cast; ring
    rw [hG_ρ, hG_shift, ← mul_sub,
      ← Real.log_div (div_pos hn2_pos hd2_pos).ne' (div_pos hn1_pos hd1_pos).ne']
    exact real_log_shift_bound hδ hu₁_half hx1
  · rw [sub_zero]
    have hG0 : 0 ≤ greenKernel 1 (ρ : ℂ) :=
      (greenKernel_pos (by simp; norm_num) ρ.2.2 ρ.ne_one).le
    refine ⟨mul_nonneg (inv_nonneg.mpr hδ.le) hG0, ?_⟩
    rw [hG_ρ]
    exact real_log_boundary_bound hδ hx_half (not_lt.mp hρδ) hx1

private theorem tendsto_greenSlopeTerm (ρ : ZetaRightZero) :
    Tendsto (fun δ : ℝ => greenSlopeTerm δ ρ) (𝓝[>] 0)
      (𝓝 (((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re)) := by
  have hx_half : 1 / 2 < (ρ : ℂ).re := ρ.2.2
  have hx1 : (ρ : ℂ).re < 1 := ρ.re_lt_one
  have hn2_pos : 0 < (ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2 := by nlinarith [hx_half, sq_nonneg (ρ : ℂ).im]
  have hd2_pos : 0 < ((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by nlinarith [hx1, sq_nonneg (ρ : ℂ).im]
  have hnorm_ρ : ‖(ρ : ℂ)‖ ^ 2 = (ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2 := norm_sq_re_im (ρ : ℂ)
  have hnorm_sub : ‖(ρ : ℂ) - 1‖ ^ 2 = ((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
    simpa only [Complex.ofReal_one] using norm_sub_ofReal_sq (ρ : ℂ) 1
  have htarget : ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re =
      ((ρ : ℂ).im ^ 2 + (ρ : ℂ).re * (1 - (ρ : ℂ).re)) /
        ((((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2) * ((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2)) := by
    rw [Complex.add_re, Complex.inv_re, Complex.inv_re, Complex.normSq_apply (ρ : ℂ),
      Complex.normSq_apply (1 - (ρ : ℂ))]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
    have hd_alt : (1 - (ρ : ℂ).re) * (1 - (ρ : ℂ).re) + -(ρ : ℂ).im * -(ρ : ℂ).im =
        ((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by ring
    have hn_alt : (ρ : ℂ).re * (ρ : ℂ).re + (ρ : ℂ).im * (ρ : ℂ).im =
        (ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2 := by ring
    change (ρ : ℂ).re / ((ρ : ℂ).re * (ρ : ℂ).re + (ρ : ℂ).im * (ρ : ℂ).im) +
      (1 - (ρ : ℂ).re) / ((1 - (ρ : ℂ).re) * (1 - (ρ : ℂ).re) + -(ρ : ℂ).im * -(ρ : ℂ).im) = _
    rw [hd_alt, hn_alt]
    field_simp [hn2_pos.ne', hd2_pos.ne']
    ring
  rw [htarget]
  let S : ℝ → ℝ := fun δ =>
    (2 * (ρ : ℂ).im ^ 2 + ((ρ : ℂ).re - δ) * (1 - (ρ : ℂ).re) +
        (ρ : ℂ).re * (1 - ((ρ : ℂ).re - δ))) /
      (2 * (((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2) * (((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2))
  let R : ℝ → ℝ := fun δ =>
    (((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2) / (((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2)) /
      ((((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2) / ((((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2))
  have ht_S : Tendsto S (𝓝[>] 0)
      (𝓝 (((ρ : ℂ).im ^ 2 + (ρ : ℂ).re * (1 - (ρ : ℂ).re)) /
        ((((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2) * ((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2)))) := by
    have hc : ContinuousAt S 0 := by
      dsimp only [S]
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      have : 2 * (((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2) * (((ρ : ℂ).re - 0) ^ 2 + (ρ : ℂ).im ^ 2) > 0 := by
        simpa using mul_pos (mul_pos two_pos hd2_pos) hn2_pos
      exact this.ne'
    have h0 : S 0 = ((ρ : ℂ).im ^ 2 + (ρ : ℂ).re * (1 - (ρ : ℂ).re)) /
        ((((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2) * ((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2)) := by
      dsimp only [S]
      rw [sub_zero]
      field_simp [hd2_pos.ne', hn2_pos.ne']
      ring
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht_R : Tendsto R (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt R 0 := by
      dsimp only [R]
      refine ContinuousAt.div continuousAt_const ?_ ?_
      · refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
        simpa using hd2_pos.ne'
      · simpa using (div_pos hn2_pos hd2_pos).ne'
    have h0 : R 0 = 1 := by
      dsimp only [R]
      rw [sub_zero]
      exact div_self (div_pos hn2_pos hd2_pos).ne'
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht_low : Tendsto (fun δ : ℝ => S δ / R δ) (𝓝[>] 0)
      (𝓝 (((ρ : ℂ).im ^ 2 + (ρ : ℂ).re * (1 - (ρ : ℂ).re)) /
        ((((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2) * ((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2)))) := by
    have h := ht_S.div ht_R one_ne_zero
    rwa [div_one] at h
  have hev_step : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      0 < δ ∧ 0 < R δ ∧ greenSlopeTerm δ ρ = δ⁻¹ * ((1 / 2) * Real.log (R δ)) ∧
        (R δ - 1) / (2 * δ) = S δ := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hx_half)] with δ ⟨hδ0, hδb⟩
    have hρδ : 1 / 2 + δ < (ρ : ℂ).re := by linarith
    have hu₁_half : 1 / 2 < (ρ : ℂ).re - δ := by linarith
    have hn1_pos : 0 < ((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2 := by
      nlinarith [hu₁_half, sq_nonneg (ρ : ℂ).im]
    have hd1_pos : 0 < (((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
      nlinarith [hu₁_half, hx1, hδ0, sq_nonneg (ρ : ℂ).im]
    have hR_pos : 0 < R δ := by dsimp only [R]; positivity
    have hG_eq : greenSlopeTerm δ ρ = δ⁻¹ * ((1 / 2) * Real.log (R δ)) := by
      rw [greenSlopeTerm, if_pos hρδ]
      have hn1_sq := norm_sub_ofReal_sq (ρ : ℂ) δ
      have hd1_sq : ‖((ρ : ℂ) - (δ : ℂ)) - 1‖ ^ 2 = (((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2 := by
        have h := norm_sub_ofReal_sq ((ρ : ℂ) - (δ : ℂ)) 1
        simpa only [Complex.ofReal_one, Complex.sub_re, Complex.ofReal_re,
          Complex.sub_im, Complex.ofReal_im, sub_zero] using h
      have h1 : greenKernel 1 (ρ : ℂ) =
          (1 / 2) * Real.log (((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2) / (((ρ : ℂ).re - 1) ^ 2 + (ρ : ℂ).im ^ 2)) := by
        rw [greenKernel_one_eq, ← hnorm_ρ, ← hnorm_sub, ← div_pow, Real.log_pow]; push_cast; ring
      have h2 : greenKernel 1 ((ρ : ℂ) - (δ : ℂ)) =
          (1 / 2) * Real.log ((((ρ : ℂ).re - δ) ^ 2 + (ρ : ℂ).im ^ 2) /
            ((((ρ : ℂ).re - δ) - 1) ^ 2 + (ρ : ℂ).im ^ 2)) := by
        rw [greenKernel_one_eq, ← hn1_sq, ← hd1_sq, ← div_pow, Real.log_pow]; push_cast; ring
      dsimp only [R]
      rw [h1, h2, ← mul_sub,
        ← Real.log_div (div_pos hn2_pos hd2_pos).ne' (div_pos hn1_pos hd1_pos).ne']
    have hR_id : (R δ - 1) / (2 * δ) = S δ := by
      dsimp only [R, S]
      field_simp [hd2_pos.ne', hn1_pos.ne', hd1_pos.ne', hδ0.ne']
      ring
    exact ⟨hδ0, hR_pos, hG_eq, hR_id⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ht_low ht_S ?_ ?_
  · filter_upwards [hev_step] with δ ⟨hδ0, hR_pos, hG_eq, hR_id⟩
    have hlow := (log_one_add_bounds (y := R δ - 1) (by linarith)).1
    rw [show 1 + (R δ - 1) = R δ by ring] at hlow
    rw [hG_eq, ← hR_id]
    have hmul := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ δ⁻¹ * (1 / 2) by positivity)
    calc (R δ - 1) / (2 * δ) / R δ
        = δ⁻¹ * (1 / 2) * ((R δ - 1) / R δ) := by ring
      _ ≤ δ⁻¹ * (1 / 2) * Real.log (R δ) := hmul
      _ = δ⁻¹ * ((1 / 2) * Real.log (R δ)) := by ring
  · filter_upwards [hev_step] with δ ⟨hδ0, hR_pos, hG_eq, hR_id⟩
    have hup := Real.log_le_sub_one_of_pos hR_pos
    rw [hG_eq, ← hR_id]
    have hmul := mul_le_mul_of_nonneg_left hup (show (0 : ℝ) ≤ δ⁻¹ * (1 / 2) by positivity)
    calc δ⁻¹ * ((1 / 2) * Real.log (R δ))
        = δ⁻¹ * (1 / 2) * Real.log (R δ) := by ring
      _ ≤ δ⁻¹ * (1 / 2) * (R δ - 1) := hmul
      _ = (R δ - 1) / (2 * δ) := by ring

/-- Unconditional summability of `m_ρ / ‖ρ − 1‖²` over `ZetaRightZero`. -/
theorem summable_zeroMult_div_norm_sub_one_sq :
    Summable (fun ρ : ZetaRightZero => zeroMult ρ * (2 / ‖(ρ : ℂ) - 1‖ ^ 2)) := by
  -- Uniform clearance from `1` since `zetaEntire` is continuous at `1` with `zetaEntire 1 = 1`
  obtain ⟨r₀, hr₀_pos, hr₀⟩ :=
    Metric.continuousAt_iff.mp differentiable_zetaEntire.continuous.continuousAt (1 / 2) (by norm_num)
  have hclear : ∀ ρ : ZetaRightZero, r₀ ≤ ‖(ρ : ℂ) - 1‖ := fun ρ => by
    by_contra hlt
    push Not at hlt
    have hd := hr₀ (by simpa [dist_eq_norm] using hlt)
    rw [zetaEntire_eq_zero_iff.mpr ρ.2.1, zetaEntire_eval_one, dist_zero_left, norm_one] at hd
    linarith
  -- Inject `ZetaRightZero` into `RiemannGaussian.NontrivialZetaZero`
  let emb : ZetaRightZero → _root_.RiemannGaussian.NontrivialZetaZero := fun ρ =>
    ⟨(ρ : ℂ), ρ.2.1, ?_, ρ.ne_one⟩
  swap
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [ρ.2.2]
  have hinj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (Subtype.val : _root_.RiemannGaussian.NontrivialZetaZero → ℂ) h)
  have hbase := _root_.RiemannGaussian.summable_distinct_zetaZeroInverseSquareNorm.comp_injective hinj
  have hbase_eq : (fun ρ : ZetaRightZero => zeroMult ρ / (1 + ‖(ρ : ℂ)‖ ^ 2)) =
      ((fun sigma : _root_.RiemannGaussian.NontrivialZetaZero =>
        (_root_.RiemannGaussian.analyticZetaZeroMultiplicity sigma : ℝ) /
          (1 + ‖(sigma.1 : ℂ)‖ ^ 2)) ∘ emb) := by
    funext ρ
    rfl
  have hsum_inv : Summable (fun ρ : ZetaRightZero => zeroMult ρ / (1 + ‖(ρ : ℂ)‖ ^ 2)) := by
    rw [hbase_eq]; exact hbase
  set C : ℝ := max (10 / r₀ ^ 2) 8
  have hC0 : 0 ≤ C := by positivity
  refine (hsum_inv.mul_left (2 * C)).of_nonneg_of_le
    (fun ρ => mul_nonneg (zeroMult_pos ρ).le (by positivity)) fun ρ => ?_
  have h1 : 1 / ‖(ρ : ℂ) - 1‖ ^ 2 ≤ C / (1 + ‖(ρ : ℂ)‖ ^ 2) := by
    have hd_pos : 0 < ‖(ρ : ℂ) - 1‖ ^ 2 := pow_pos (lt_of_lt_of_le hr₀_pos (hclear ρ)) 2
    by_cases hbig : ‖(ρ : ℂ)‖ ≤ 2
    · have h5 : 1 + ‖(ρ : ℂ)‖ ^ 2 ≤ 5 := by nlinarith [norm_nonneg (ρ : ℂ)]
      have hr_sq : r₀ ^ 2 ≤ ‖(ρ : ℂ) - 1‖ ^ 2 :=
        pow_le_pow_left₀ hr₀_pos.le (hclear ρ) 2
      have hC_ge : 10 / r₀ ^ 2 ≤ C := le_max_left _ _
      rw [div_le_div_iff₀ hd_pos (by positivity)]
      have h10 : 1 + ‖(ρ : ℂ)‖ ^ 2 ≤ (10 / r₀ ^ 2) * r₀ ^ 2 := by
        have : (10 / r₀ ^ 2) * r₀ ^ 2 = 10 := by field_simp [hr₀_pos.ne']
        linarith
      nlinarith [mul_le_mul hC_ge hr_sq (by positivity) hC0]
    · push Not at hbig
      have htri : ‖(ρ : ℂ)‖ - 1 ≤ ‖(ρ : ℂ) - 1‖ := by
        simpa using norm_sub_norm_le (ρ : ℂ) 1
      have hhalf : ‖(ρ : ℂ)‖ / 2 ≤ ‖(ρ : ℂ) - 1‖ := by linarith
      have hsq : (‖(ρ : ℂ)‖ / 2) ^ 2 ≤ ‖(ρ : ℂ) - 1‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hhalf 2
      have hC_ge : (8 : ℝ) ≤ C := le_max_right _ _
      rw [div_le_div_iff₀ hd_pos (by positivity)]
      nlinarith [hsq, hbig, hC_ge]
  calc zeroMult ρ * (2 / ‖(ρ : ℂ) - 1‖ ^ 2)
      = 2 * zeroMult ρ * (1 / ‖(ρ : ℂ) - 1‖ ^ 2) := by ring
    _ ≤ 2 * zeroMult ρ * (C / (1 + ‖(ρ : ℂ)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg two_pos.le (zeroMult_pos ρ).le)
    _ = 2 * C * (zeroMult ρ / (1 + ‖(ρ : ℂ)‖ ^ 2)) := by ring

private theorem tendsto_archimedean_dilation_slope :
    Tendsto (fun δ : ℝ => δ⁻¹ * Real.log ((1 - δ) / (δ * ‖riemannZeta (1 + (δ : ℂ))‖)))
      (𝓝[>] 0) (𝓝 (-(1 + Real.eulerMascheroniConstant))) := by
  -- Split `log((1 − δ) / (δ ‖ζ(1 + δ)‖)) = log(1 − δ) − log ‖zetaEntire(1 + δ)‖` for `0 < δ < 1`
  have ht_id : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  -- Part A: `δ⁻¹ * log(1 − δ) → −1`
  have ht_one_sub : Tendsto (fun δ : ℝ => δ⁻¹ * Real.log (1 - δ)) (𝓝[>] 0) (𝓝 (-1)) := by
    have hlow_lim : Tendsto (fun δ : ℝ => -1 / (1 - δ)) (𝓝[>] 0) (𝓝 (-1)) := by
      have hc : ContinuousAt (fun δ : ℝ => -1 / (1 - δ)) 0 :=
        ContinuousAt.div continuousAt_const (continuousAt_const.sub continuousAt_id) (by norm_num)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim tendsto_const_nhds ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with δ ⟨hδ0, hδ1⟩
      have hb := (log_one_add_bounds (y := -δ) (by linarith)).1
      rw [show 1 + -δ = 1 - δ by ring] at hb
      have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hδ0.le)
      have heq : δ⁻¹ * (-δ / (1 - δ)) = -1 / (1 - δ) := by field_simp [hδ0.ne']
      linarith
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with δ ⟨hδ0, hδ1⟩
      have hb := (log_one_add_bounds (y := -δ) (by linarith)).2
      rw [show 1 + -δ = 1 - δ by ring] at hb
      have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hδ0.le)
      have heq : δ⁻¹ * (-δ) = -1 := by field_simp [hδ0.ne']
      linarith
  -- Part B: `δ⁻¹ * log ‖zetaEntire(1 + δ)‖ → γ`
  have ht_E : Tendsto (fun δ : ℝ => δ⁻¹ * Real.log ‖zetaEntire (1 + (δ : ℂ))‖)
      (𝓝[>] 0) (𝓝 Real.eulerMascheroniConstant) := by
    have hsl : Tendsto (slope zetaEntire 1) (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
      hasDerivAt_iff_tendsto_slope.mp hasDerivAt_zetaEntire_one
    have hmap : Tendsto (fun δ : ℝ => (1 : ℂ) + (δ : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun δ : ℝ => (1 : ℂ) + (δ : ℂ)) :=
          continuous_const.add Complex.continuous_ofReal
        have ht0 : Tendsto (fun δ : ℝ => (1 : ℂ) + (δ : ℂ)) (𝓝[>] 0)
            (𝓝 ((1 : ℂ) + ((0 : ℝ) : ℂ))) :=
          hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        simpa only [Complex.ofReal_zero, add_zero] using ht0
      · filter_upwards [self_mem_nhdsWithin] with δ (hδ0 : 0 < δ)
        intro h1
        have := congrArg Complex.re h1
        simp at this
        linarith
    have hquot : Tendsto (fun δ : ℝ => (zetaEntire (1 + (δ : ℂ)) - 1) / (δ : ℂ))
        (𝓝[>] 0) (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
      (hsl.comp hmap).congr fun δ => by simp [slope_def_field, zetaEntire_eval_one]
    set u : ℝ → ℝ := fun δ =>
      2 * (zetaEntire (1 + (δ : ℂ)) - 1).re + ‖zetaEntire (1 + (δ : ℂ)) - 1‖ ^ 2
    have hnorm_sq : ∀ δ : ℝ, ‖zetaEntire (1 + (δ : ℂ))‖ ^ 2 = 1 + u δ := fun δ => by
      have h1 := norm_add_sq (1 : ℂ) (zetaEntire (1 + (δ : ℂ)) - 1)
      have h2 : (1 : ℂ) + (zetaEntire (1 + (δ : ℂ)) - 1) = zetaEntire (1 + (δ : ℂ)) := by ring
      have h3 : (conj (zetaEntire (1 + (δ : ℂ)) - 1) * 1).re =
          (zetaEntire (1 + (δ : ℂ)) - 1).re := by simp
      rw [h2, norm_one, one_pow, h3] at h1
      linarith
    have hu_slope : Tendsto (fun δ : ℝ => u δ / (2 * δ)) (𝓝[>] 0)
        (𝓝 Real.eulerMascheroniConstant) := by
      have hre_q : Tendsto (fun δ : ℝ => ((zetaEntire (1 + (δ : ℂ)) - 1) / (δ : ℂ)).re)
          (𝓝[>] 0) (𝓝 Real.eulerMascheroniConstant) :=
        (Complex.continuous_re.continuousAt (x := (Real.eulerMascheroniConstant : ℂ))).tendsto.comp hquot
      have hnorm_q : Tendsto (fun δ : ℝ =>
          (δ / 2) * ‖(zetaEntire (1 + (δ : ℂ)) - 1) / (δ : ℂ)‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
        simpa using (ht_id.div_const 2).mul ((hquot.norm).pow 2)
      rw [← add_zero Real.eulerMascheroniConstant]
      refine (hre_q.add hnorm_q).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ (hδ0 : 0 < δ)
      have hre_div : ((zetaEntire (1 + (δ : ℂ)) - 1) / (δ : ℂ)).re =
          (zetaEntire (1 + (δ : ℂ)) - 1).re / δ := by
        rw [div_eq_mul_inv _ (δ : ℂ), ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, ← div_eq_mul_inv _ δ]
      have hn_div : ‖(zetaEntire (1 + (δ : ℂ)) - 1) / (δ : ℂ)‖ ^ 2 =
          ‖zetaEntire (1 + (δ : ℂ)) - 1‖ ^ 2 / δ ^ 2 := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hδ0.le, div_pow]
      simp only [u]
      rw [hre_div, hn_div]
      field_simp [hδ0.ne']
    have h1u : Tendsto (fun δ : ℝ => 1 + u δ) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun δ : ℝ => ‖zetaEntire (1 + (δ : ℂ))‖ ^ 2) 0 := by
        have hd : Continuous fun δ : ℝ => ‖zetaEntire (1 + (δ : ℂ))‖ ^ 2 :=
          ((differentiable_zetaEntire.continuous.comp
            (continuous_const.add Complex.continuous_ofReal)).norm.pow 2)
        exact hd.continuousAt
      have h0 : ‖zetaEntire (1 + ((0 : ℝ) : ℂ))‖ ^ 2 = 1 := by simp [zetaEntire_eval_one]
      have ht0 : Tendsto (fun δ : ℝ => ‖zetaEntire (1 + (δ : ℂ))‖ ^ 2) (𝓝[>] 0) (𝓝 1) := by
        rw [← h0]
        exact hc.tendsto.mono_left nhdsWithin_le_nhds
      exact ht0.congr hnorm_sq
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using hu_slope.div h1u one_ne_zero) hu_slope ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ0 : 0 < δ)
      have h1δ_re : 1 ≤ ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
      have hE_pos : 0 < ‖zetaEntire (1 + (δ : ℂ))‖ :=
        norm_pos_iff.mpr (zetaEntire_ne_zero_of_zeta_ne_zero
          (riemannZeta_ne_zero_of_one_le_re h1δ_re))
      have h1u_pos : 0 < 1 + u δ := by rw [← hnorm_sq]; positivity
      have hb := (log_one_add_bounds h1u_pos).1
      have hlog_eq : Real.log ‖zetaEntire (1 + (δ : ℂ))‖ = (1 / 2) * Real.log (1 + u δ) := by
        rw [← hnorm_sq, Real.log_pow]; push_cast; ring
      rw [hlog_eq]
      have hm := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ δ⁻¹ * (1 / 2) by positivity)
      calc (u δ / (2 * δ)) / (1 + u δ)
          = δ⁻¹ * (1 / 2) * (u δ / (1 + u δ)) := by ring
        _ ≤ δ⁻¹ * (1 / 2) * Real.log (1 + u δ) := hm
        _ = δ⁻¹ * (1 / 2 * Real.log (1 + u δ)) := by ring
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ0 : 0 < δ)
      have h1δ_re : 1 ≤ ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
      have hE_pos : 0 < ‖zetaEntire (1 + (δ : ℂ))‖ :=
        norm_pos_iff.mpr (zetaEntire_ne_zero_of_zeta_ne_zero
          (riemannZeta_ne_zero_of_one_le_re h1δ_re))
      have h1u_pos : 0 < 1 + u δ := by rw [← hnorm_sq]; positivity
      have hb := (log_one_add_bounds h1u_pos).2
      have hlog_eq : Real.log ‖zetaEntire (1 + (δ : ℂ))‖ = (1 / 2) * Real.log (1 + u δ) := by
        rw [← hnorm_sq, Real.log_pow]; push_cast; ring
      rw [hlog_eq]
      have hm := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ δ⁻¹ * (1 / 2) by positivity)
      calc δ⁻¹ * (1 / 2 * Real.log (1 + u δ))
          = δ⁻¹ * (1 / 2) * Real.log (1 + u δ) := by ring
        _ ≤ δ⁻¹ * (1 / 2) * u δ := hm
        _ = u δ / (2 * δ) := by ring
  -- Combine Parts A and B
  have hcomb : Tendsto (fun δ : ℝ =>
      δ⁻¹ * Real.log (1 - δ) - δ⁻¹ * Real.log ‖zetaEntire (1 + (δ : ℂ))‖)
      (𝓝[>] 0) (𝓝 (-(1 + Real.eulerMascheroniConstant))) := by
    simpa only [show (-1 : ℝ) - Real.eulerMascheroniConstant = -(1 + Real.eulerMascheroniConstant)
      by ring] using ht_one_sub.sub ht_E
  refine hcomb.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with δ ⟨hδ0, hδ1⟩
  have h1δ_re : 1 ≤ ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
  have hzeta_ne : riemannZeta (1 + (δ : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1δ_re
  have hne1 : (1 : ℂ) + (δ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hE_val : ‖zetaEntire (1 + (δ : ℂ))‖ = δ * ‖riemannZeta (1 + (δ : ℂ))‖ := by
    rw [zetaEntire_eq hne1, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hδ0.le]
  rw [hE_val, Real.log_div (by linarith) (mul_pos hδ0 (norm_pos_iff.mpr hzeta_ne)).ne', mul_sub]

/-- **First-order boundary dilation jet of `ζ`.** Unconditionally, the right-hand derivative at
`δ = 0⁺` of the Poisson-weighted logarithmic dilation quotient separates the archimedean constant
`−(1 + γ)` from the Li–Herglotz sum over right zeros. -/
theorem tendsto_firstOrder_dilation_jet :
    Summable (fun ρ : ZetaRightZero => zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re) ∧
      Tendsto (fun δ : ℝ =>
        δ⁻¹ * ∫ τ : ℝ, (Real.log ‖riemannZeta (1 / 2 + τ * I)‖ -
          Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ)
        (𝓝[>] 0)
        (𝓝 (-(1 + Real.eulerMascheroniConstant) +
          ∑' ρ : ZetaRightZero, zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re)) := by
  have hdom_sum := summable_zeroMult_div_norm_sub_one_sq
  have hlim_pos : ∀ ρ : ZetaRightZero, 0 < ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re := fun ρ => by
    have hx_half : 1 / 2 < (ρ : ℂ).re := ρ.2.2
    have hx1 : (ρ : ℂ).re < 1 := ρ.re_lt_one
    rw [Complex.add_re, Complex.inv_re, Complex.inv_re]
    have h1 : 0 < (ρ : ℂ).re / Complex.normSq (ρ : ℂ) :=
      div_pos (by linarith) (Complex.normSq_pos.mpr (by
        intro h0; rw [h0] at hx_half; simp at hx_half; linarith))
    have h2 : 0 < (1 - (ρ : ℂ).re) / Complex.normSq (1 - (ρ : ℂ)) :=
      div_pos (by linarith) (Complex.normSq_pos.mpr (sub_ne_zero.mpr ρ.ne_one.symm))
    simpa only [Complex.sub_re, Complex.one_re] using add_pos h1 h2
  have hlim_le : ∀ ρ : ZetaRightZero,
      zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re ≤ zeroMult ρ * (2 / ‖(ρ : ℂ) - 1‖ ^ 2) :=
    fun ρ => mul_le_mul_of_nonneg_left
      (le_of_tendsto (tendsto_greenSlopeTerm ρ) (by
        filter_upwards [self_mem_nhdsWithin] with δ hδ using (greenSlopeTerm_nonneg_and_le hδ ρ).2))
      (zeroMult_pos ρ).le
  have hsum_target : Summable (fun ρ : ZetaRightZero =>
      zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re) :=
    hdom_sum.of_nonneg_of_le (fun ρ => mul_nonneg (zeroMult_pos ρ).le (hlim_pos ρ).le) hlim_le
  refine ⟨hsum_target, ?_⟩
  have ht_zeros : Tendsto (fun δ : ℝ =>
      ∑' ρ : ZetaRightZero, zeroMult ρ * greenSlopeTerm δ ρ) (𝓝[>] 0)
      (𝓝 (∑' ρ : ZetaRightZero, zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re)) := by
    refine tendsto_tsum_of_dominated_convergence hdom_sum
      (fun ρ => (tendsto_greenSlopeTerm ρ).const_mul (zeroMult ρ)) ?_
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) ρ
    rw [Real.norm_of_nonneg (mul_nonneg (zeroMult_pos ρ).le (greenSlopeTerm_nonneg_and_le hδ ρ).1)]
    exact mul_le_mul_of_nonneg_left (greenSlopeTerm_nonneg_and_le hδ ρ).2 (zeroMult_pos ρ).le
  have hcomb := tendsto_archimedean_dilation_slope.add ht_zeros
  refine hcomb.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with δ ⟨hδ0, hδ1⟩
  obtain ⟨hid, hsum_diff⟩ := integral_log_dilation_quotient_eq hδ0 hδ1.le
  have hsum_scaled : HasSum (fun ρ : ZetaRightZero => zeroMult ρ * greenSlopeTerm δ ρ)
      (δ⁻¹ * (innerField 1 - shiftedInnerField δ 1)) := by
    refine (hsum_diff.mul_left δ⁻¹).congr_fun fun ρ => ?_
    simp only [greenSlopeTerm, shiftedZeroTerm]
    split_ifs <;> ring
  rw [hid, mul_add, ← hsum_scaled.tsum_eq]
  ring

/-- **Infinitesimal jet RH criterion.** `RiemannHypothesis` holds if and only if the `δ → 0⁺`
boundary dilation jet equals `−(1 + γ)`. -/
theorem riemannHypothesis_iff_firstOrder_jet_eq :
    RiemannHypothesis ↔
      Tendsto (fun δ : ℝ =>
        δ⁻¹ * ∫ τ : ℝ, (Real.log ‖riemannZeta (1 / 2 + τ * I)‖ -
          Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ)
        (𝓝[>] 0) (𝓝 (-(1 + Real.eulerMascheroniConstant))) := by
  obtain ⟨hsum, hjet⟩ := tendsto_firstOrder_dilation_jet
  have hpos : ∀ ρ : ZetaRightZero,
      0 < zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re := fun ρ => by
    refine mul_pos (zeroMult_pos ρ) ?_
    rw [Complex.add_re, Complex.inv_re, Complex.inv_re]
    have hx_half : 1 / 2 < (ρ : ℂ).re := ρ.2.2
    have hx1 : (ρ : ℂ).re < 1 := ρ.re_lt_one
    have h1 : 0 < (ρ : ℂ).re / Complex.normSq (ρ : ℂ) :=
      div_pos (by linarith) (Complex.normSq_pos.mpr (by
        intro h0; rw [h0] at hx_half; simp at hx_half; linarith))
    have h2 : 0 < (1 - (ρ : ℂ).re) / Complex.normSq (1 - (ρ : ℂ)) :=
      div_pos (by linarith) (Complex.normSq_pos.mpr (sub_ne_zero.mpr ρ.ne_one.symm))
    simpa only [Complex.sub_re, Complex.one_re] using add_pos h1 h2
  constructor
  · intro hRH
    have hemp : IsEmpty ZetaRightZero := ⟨fun ρ =>
      (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) ρ ρ.2.2 ρ.2.1⟩
    have htsum0 : (∑' ρ : ZetaRightZero,
        zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re) = 0 := tsum_empty
    simpa [htsum0] using hjet
  · intro hlim
    have heq : -(1 + Real.eulerMascheroniConstant) +
        (∑' ρ : ZetaRightZero, zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re) =
        -(1 + Real.eulerMascheroniConstant) :=
      tendsto_nhds_unique hjet hlim
    have htsum0 : (∑' ρ : ZetaRightZero,
        zeroMult ρ * ((ρ : ℂ)⁻¹ + (1 - (ρ : ℂ))⁻¹).re) = 0 := by linarith
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
    intro z hz hzz
    let ρ : ZetaRightZero := ⟨z, hzz, hz⟩
    have hle := hsum.sum_le_tsum ({ρ} : Finset ZetaRightZero) fun a _ => (hpos a).le
    rw [Finset.sum_singleton, htsum0] at hle
    exact absurd hle (not_le.mpr (hpos ρ))

/-! ### 3. Unshadowed `L²` blowup separating `ζ` from finite curves -/

private theorem not_integrable_of_inv_sq_lower_bound {F : ℝ → ℝ} (hF_nn : ∀ τ, 0 ≤ F τ)
    {γ₀ r K : ℝ} (hr : 0 < r) (hK : 0 < K)
    (hlow : ∀ τ, γ₀ < τ → τ ≤ γ₀ + r → K * ((τ - γ₀) ^ 2)⁻¹ ≤ F τ) :
    ¬ Integrable F volume := by
  intro hint
  let M : ℝ := |∫ τ : ℝ, F τ|
  have hM_nn : 0 ≤ M := abs_nonneg _
  have hden_pos : 0 < M + K * r⁻¹ + 1 := by
    have hKr : 0 < K * r⁻¹ := mul_pos hK (inv_pos.mpr hr)
    linarith
  let ε : ℝ := min (r / 2) (K / (M + K * r⁻¹ + 1))
  have hε_pos : 0 < ε := lt_min (half_pos hr) (div_pos hK hden_pos)
  have hε_r : ε ≤ r / 2 := min_le_left _ _
  have hab : γ₀ + ε ≤ γ₀ + r := by linarith
  have hderiv : ∀ x ∈ uIcc (γ₀ + ε) (γ₀ + r),
      HasDerivAt (fun τ : ℝ => -K * (τ - γ₀)⁻¹) (K * ((x - γ₀) ^ 2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx_ne : x - γ₀ ≠ 0 := by linarith [hx.1]
    have h1 := ((hasDerivAt_id x).sub_const γ₀).inv hx_ne
    have h2 := h1.const_mul (-K)
    exact h2.congr_deriv (by simp only [id_eq, div_eq_mul_inv]; ring)
  have hint_inv : IntervalIntegrable (fun x : ℝ => K * ((x - γ₀) ^ 2)⁻¹)
      volume (γ₀ + ε) (γ₀ + r) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    refine continuousOn_const.mul
      (ContinuousOn.inv₀ ((continuousOn_id.sub continuousOn_const).pow 2) ?_)
    intro x hx
    exact pow_ne_zero 2 (by linarith [hx.1])
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_inv
  simp only [add_sub_cancel_left] at hftc
  have hmono : (∫ x in (γ₀ + ε)..(γ₀ + r), K * ((x - γ₀) ^ 2)⁻¹) ≤
      ∫ x in (γ₀ + ε)..(γ₀ + r), F x :=
    intervalIntegral.integral_mono_on hab hint_inv hint.intervalIntegrable fun x hx =>
      hlow x (by linarith [hx.1]) hx.2
  have hle_glob : (∫ x in (γ₀ + ε)..(γ₀ + r), F x) ≤ ∫ x : ℝ, F x := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_le_integral hint (Eventually.of_forall hF_nn)
  have hε_bound : ε ≤ K / (M + K * r⁻¹ + 1) := min_le_right _ _
  have hdiv_ge : M + K * r⁻¹ + 1 ≤ K * ε⁻¹ := by
    rw [← div_eq_mul_inv K ε, le_div_iff₀ hε_pos, mul_comm]
    exact (le_div_iff₀ hden_pos).mp hε_bound
  have htot : -K * r⁻¹ - (-K * ε⁻¹) ≤ M := by
    calc -K * r⁻¹ - (-K * ε⁻¹)
        = ∫ x in (γ₀ + ε)..(γ₀ + r), K * ((x - γ₀) ^ 2)⁻¹ := hftc.symm
      _ ≤ ∫ x : ℝ, F x := hmono.trans hle_glob
      _ ≤ M := le_abs_self _
  linarith

private theorem exists_zeta_dilation_inv_sq_lower_bound {ρ₀ : ℂ} (hζ0 : riemannZeta ρ₀ = 0)
    (hre_up : ρ₀.re < 1) (hline_ne : riemannZeta (1 / 2 + (ρ₀.im : ℂ) * I) ≠ 0) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ ∀ τ : ℝ, ρ₀.im < τ → τ ≤ ρ₀.im + r →
      K * ((τ - ρ₀.im) ^ 2)⁻¹ ≤
        (‖riemannZeta (1 / 2 + τ * I)‖ /
          ‖riemannZeta (1 / 2 + ((ρ₀.re - 1 / 2 : ℝ) : ℂ) + τ * I)‖) ^ 2 *
            halfPlanePoissonKernel 1 τ := by
  have hρ₀1 : ρ₀ ≠ 1 := fun h => by rw [h] at hre_up; simp at hre_up
  obtain ⟨r₁, hr₁_pos, hr₁_ball⟩ :=
    Metric.isOpen_iff.mp
      (((isCompact_closedBall ρ₀ 1).inter_riemannZetaZeros_finite).sdiff
        (t := {ρ₀})).isClosed.isOpen_compl ρ₀ (by simp)
  have hsl := (hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_riemannZeta hρ₀1).hasDerivAt).norm
  let L : ℝ := ‖deriv riemannZeta ρ₀‖ + 1
  have hL_pos : 0 < L := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  obtain ⟨r₂, hr₂_pos, hr₂_sl⟩ := Metric.mem_nhdsWithin_iff.mp
    (hsl.eventually (gt_mem_nhds (lt_add_one ‖deriv riemannZeta ρ₀‖)))
  let c₀ : ℝ := ‖riemannZeta (1 / 2 + (ρ₀.im : ℂ) * I)‖ / 2
  have hc₀_pos : 0 < c₀ := half_pos (norm_pos_iff.mpr hline_ne)
  have hcont_line : ContinuousAt (fun τ : ℝ => ‖riemannZeta (1 / 2 + τ * I)‖) ρ₀.im := by
    have hc1 : ContinuousAt riemannZeta (1 / 2 + (ρ₀.im : ℂ) * I) :=
      (differentiableAt_riemannZeta (line_ne_one ρ₀.im)).continuousAt
    have hc2 : ContinuousAt (fun τ : ℝ => (1 / 2 : ℂ) + τ * I) ρ₀.im := by fun_prop
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun τ : ℝ => (1 / 2 : ℂ) + τ * I) hc1 hc2).norm
  obtain ⟨r₃, hr₃_pos, hr₃_low⟩ := Metric.mem_nhds_iff.mp
    (hcont_line.eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hline_ne))))
  let r : ℝ := min (min (r₁ / 2) (r₂ / 2)) (min (r₃ / 2) (1 / 2))
  have hr_pos : 0 < r := lt_min
    (lt_min (half_pos hr₁_pos) (half_pos hr₂_pos))
    (lt_min (half_pos hr₃_pos) (by norm_num))
  have hr_r₁ : r < r₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (half_lt_self hr₁_pos)
  have hr_r₂ : r < r₂ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self hr₂_pos)
  have hr_r₃ : r < r₃ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hr₃_pos)
  have hr_1 : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let p₀ : ℝ := (2 * π)⁻¹ * (1 / (1 / 4 + (|ρ₀.im| + 1) ^ 2))
  have hp₀_pos : 0 < p₀ := by positivity
  have hp_low : ∀ τ : ℝ, ρ₀.im ≤ τ → τ ≤ ρ₀.im + r → p₀ ≤ halfPlanePoissonKernel 1 τ :=
    fun τ h1 h2 => by
      rw [halfPlanePoissonKernel_one]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (mul_pos two_pos Real.pi_pos).le)
      refine one_div_le_one_div_of_le (add_pos_of_pos_of_nonneg (by norm_num) (sq_nonneg τ)) ?_
      have habs : |τ| ≤ |ρ₀.im| + 1 := by
        rw [abs_le]
        constructor <;> linarith [le_abs_self ρ₀.im, neg_le_abs ρ₀.im]
      have hsq : τ ^ 2 ≤ (|ρ₀.im| + 1) ^ 2 := by
        rw [← sq_abs τ]
        exact pow_le_pow_left₀ (abs_nonneg τ) habs 2
      linarith
  refine ⟨r, c₀ ^ 2 * p₀ / L ^ 2, hr_pos, div_pos (mul_pos (sq_pos_of_pos hc₀_pos) hp₀_pos)
    (sq_pos_of_pos hL_pos), fun τ hτ1 hτ2 => ?_⟩
  let z : ℂ := 1 / 2 + ((ρ₀.re - 1 / 2 : ℝ) : ℂ) + τ * I
  have hz_sub : z - ρ₀ = ((τ - ρ₀.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [z]
  have hz_norm : ‖z - ρ₀‖ = τ - ρ₀.im := by
    rw [hz_sub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr hτ1.le)]
  have hz_ne : z ≠ ρ₀ := fun h0 => by
    have := congrArg (fun w => ‖w - ρ₀‖) h0
    simp only [sub_self, norm_zero] at this
    linarith [hz_norm]
  have hz_not_zero : riemannZeta z ≠ 0 := fun hzz =>
    hr₁_ball (by rw [mem_ball, dist_eq_norm, hz_norm]; linarith)
      ⟨⟨by rw [mem_closedBall, dist_eq_norm, hz_norm]; linarith, hzz⟩, hz_ne⟩
  have hz_pos : 0 < ‖riemannZeta z‖ := norm_pos_iff.mpr hz_not_zero
  have hz_lip : ‖riemannZeta z‖ ≤ L * (τ - ρ₀.im) := by
    have hsl_z : ‖slope riemannZeta ρ₀ z‖ < L :=
      hr₂_sl ⟨by rw [mem_ball, dist_eq_norm, hz_norm]; linarith, hz_ne⟩
    rw [slope_def_field, hζ0, sub_zero, norm_div, hz_norm,
      div_lt_iff₀ (sub_pos.mpr hτ1)] at hsl_z
    exact hsl_z.le
  have hnum_low : c₀ ≤ ‖riemannZeta (1 / 2 + τ * I)‖ :=
    le_of_lt (hr₃_low (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hτ1)]; linarith))
  have hquot_low : c₀ / (L * (τ - ρ₀.im)) ≤ ‖riemannZeta (1 / 2 + τ * I)‖ / ‖riemannZeta z‖ :=
    (div_le_div_of_nonneg_right hnum_low (mul_nonneg hL_pos.le (sub_pos.mpr hτ1).le)).trans
      (div_le_div_of_nonneg_left (norm_nonneg _) hz_pos hz_lip)
  have hsq_low : (c₀ / (L * (τ - ρ₀.im))) ^ 2 ≤
      (‖riemannZeta (1 / 2 + τ * I)‖ / ‖riemannZeta z‖) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hc₀_pos.le (mul_nonneg hL_pos.le (sub_pos.mpr hτ1).le))
      hquot_low 2
  have hmul_low := mul_le_mul hsq_low (hp_low τ hτ1.le hτ2) hp₀_pos.le (sq_nonneg _)
  have hlhs : (c₀ / (L * (τ - ρ₀.im))) ^ 2 * p₀ =
      (c₀ ^ 2 * p₀ / L ^ 2) * ((τ - ρ₀.im) ^ 2)⁻¹ := by
    field_simp [hL_pos.ne', (sub_pos.mpr hτ1).ne']
  rwa [hlhs] at hmul_low

/-- **Unshadowed `L²` blowup.** If `ρ₀` is an off-line zero (`1/2 < Re ρ₀ < 1`) unshadowed on the
critical line (`ζ(1/2 + i Im ρ₀) ≠ 0`), then at the critical shift `δ = Re ρ₀ − 1/2` the `L²`
boundary dilation quotient fails to be integrable against `P₁`. -/
theorem not_integrable_zeta_dilationQuotient_sq {ρ₀ : ℂ} (hζ0 : riemannZeta ρ₀ = 0)
    (_hre_low : 1 / 2 < ρ₀.re) (hre_up : ρ₀.re < 1)
    (hline_ne : riemannZeta (1 / 2 + (ρ₀.im : ℂ) * I) ≠ 0) :
    ¬ Integrable (fun τ : ℝ =>
      (‖riemannZeta (1 / 2 + τ * I)‖ /
        ‖riemannZeta (1 / 2 + ((ρ₀.re - 1 / 2 : ℝ) : ℂ) + τ * I)‖) ^ 2 *
          halfPlanePoissonKernel 1 τ) volume := by
  obtain ⟨r, K, hr_pos, hK_pos, hlow⟩ :=
    exists_zeta_dilation_inv_sq_lower_bound hζ0 hre_up hline_ne
  exact not_integrable_of_inv_sq_lower_bound
    (fun τ => mul_nonneg (sq_nonneg _) (halfPlanePoissonKernel_pos (by simp; norm_num) τ).le)
    hr_pos hK_pos hlow

#print axioms sq_norm_le_circleAverage_subcritical
#print axioms supercritical_pythagorean_split
#print axioms tendsto_circleAverage_modelPart_sq
#print axioms golden_exterior_modelPart_limit
#print axioms hasSum_shiftedInnerField
#print axioms riemannHypothesis_iff_log_dilation_quotient_eq
#print axioms summable_zeroMult_div_norm_sub_one_sq
#print axioms tendsto_firstOrder_dilation_jet
#print axioms riemannHypothesis_iff_firstOrder_jet_eq
#print axioms not_integrable_zeta_dilationQuotient_sq

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
