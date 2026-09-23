import GaloisForLFunctions.RHTower.SuzukiGammaMollifiedEquation
import GaloisForLFunctions.HTGeometry.L1FromWeightedL2
import GaloisForLFunctions.HTGeometry.WeakLimitBoundedFamily
import GaloisForLFunctions.HTGeometry.SmoothCompactL2Dense
import GaloisForLFunctions.HTGeometry.MollifierL2Contraction

/-!
# The weak-domain upgrade for the Suzuki Gamma equation

The load-bearing step of the weighted-tail coercivity card: if the weak equation
`(2L + R_σ − τ)U + V = G`, `U = V′ − σV`, holds in its tested form, with `V, G ∈ L²`, `V`
supported in `[L₀, ∞)`, `0 ≤ σ < 1`, and the budget `κ_σ + |τ| < 2L₀`, then the distributional
derivative combination `U` **is** square-integrable: there is `u ∈ L²` with
`∫ u φ = −∫ V φ′ − σ ∫ V φ` for every smooth compactly supported test `φ`.  Consequently `V ∈ H¹`.

The proof is the paper's section 4 run end to end in Lean: mollify the equation pointwise, bound
the mollified family uniformly through the coercive pairing — the `2L` support term wins against
the Gamma jump's `κ_σ` loss and the seam's `τ` — and pass to the weak limit against the dense
smooth compactly supported subspace of `L²`.  No Fourier transform appears anywhere: the jump's
numerical range and its `L²` bound are both physical-space statements.
-/

open MeasureTheory Set GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace GaloisForLFunctions.RHTower

/-! ## Square-sum helpers -/

theorem integrable_sq_add' {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun x => f x ^ (2 : ℕ))) (hg2 : Integrable (fun x => g x ^ (2 : ℕ))) :
    Integrable (fun x => (f x + g x) ^ (2 : ℕ)) := by
  have hsum : Integrable (fun x => 2 * f x ^ (2 : ℕ) + 2 * g x ^ (2 : ℕ)) :=
    (hf2.const_mul 2).add (hg2.const_mul 2)
  refine Integrable.mono' hsum (aestronglyMeasurable_sq (hfm.add hgm)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_add_le_two _ _

theorem integrable_sq_const_mul {f : ℝ → ℝ} (c : ℝ)
    (hf2 : Integrable (fun x => f x ^ (2 : ℕ))) :
    Integrable (fun x => (c * f x) ^ (2 : ℕ)) := by
  refine (hf2.const_mul (c ^ (2 : ℕ))).congr ?_
  filter_upwards with x
  ring

/-! ## The mollified-derivative kernel and its data -/

/-- The convolution kernel of the mollified weak derivative, `g_ε = ρ_ε′ − σρ_ε`. -/
noncomputable def suzukiDerivKernel (σ ε : ℝ) : ℝ → ℝ :=
  fun u => deriv (suzukiMollifier ε) u - σ * suzukiMollifier ε u

theorem suzukiMollifiedDeriv_eq (σ ε : ℝ) (V : ℝ → ℝ) :
    suzukiMollifiedDeriv σ ε V = lineConvolution (suzukiDerivKernel σ ε) V := rfl

theorem contDiff_suzukiDerivKernel (σ ε : ℝ) : ContDiff ℝ 1 (suzukiDerivKernel σ ε) := by
  unfold suzukiDerivKernel
  exact ((contDiff_deriv_suzukiMollifier ε).of_le (by exact_mod_cast le_top)).sub
    (contDiff_const.mul ((contDiff_suzukiMollifier ε).of_le (by exact_mod_cast le_top)))

theorem continuous_suzukiDerivKernel (σ ε : ℝ) : Continuous (suzukiDerivKernel σ ε) :=
  (contDiff_suzukiDerivKernel σ ε).continuous

theorem suzukiDerivKernel_eq_zero {σ ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : ε < |u|) :
    suzukiDerivKernel σ ε u = 0 := by
  unfold suzukiDerivKernel
  rw [deriv_suzukiMollifier_eq_zero hε hu, suzukiMollifier_eq_zero hε hu]
  ring

theorem hasCompactSupport_suzukiDerivKernel {σ ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (suzukiDerivKernel σ ε) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun u hu => ?_
  refine suzukiDerivKernel_eq_zero hε ?_
  rw [mem_Icc, not_and_or] at hu
  rcases hu with hu | hu
  · rw [not_le] at hu
    exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
  · rw [not_le] at hu
    exact lt_of_lt_of_le hu (le_abs_self u)

/-! ## The mollified derivative: regularity, support, energy -/

section MollifiedDerivData

variable {σ ε : ℝ} {V : ℝ → ℝ}

theorem continuous_suzukiMollifiedDeriv (hε : 0 < ε)
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ (2 : ℕ))) :
    Continuous (suzukiMollifiedDeriv σ ε V) := by
  rw [suzukiMollifiedDeriv_eq]
  exact continuous_lineConvolution (continuous_suzukiDerivKernel σ ε)
    (hasCompactSupport_suzukiDerivKernel hε)
    (locallyIntegrable_of_sq_integrable hVm hV2)

theorem integrable_sq_suzukiMollifiedDeriv (hε : 0 < ε)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ))) :
    Integrable (fun x => suzukiMollifiedDeriv σ ε V x ^ (2 : ℕ)) := by
  rw [suzukiMollifiedDeriv_eq]
  exact integrable_sq_lineConvolution (continuous_suzukiDerivKernel σ ε)
    (hasCompactSupport_suzukiDerivKernel hε) hVmm hV2

theorem suzukiMollifiedDeriv_eq_zero {L₀ : ℝ} (hε : 0 < ε)
    (hsupp : ∀ t : ℝ, t < L₀ → V t = 0) {x : ℝ} (hx : x < L₀ - ε) :
    suzukiMollifiedDeriv σ ε V x = 0 := by
  rw [suzukiMollifiedDeriv_eq]
  exact lineConvolution_eq_zero_of_lt (fun u hu => suzukiDerivKernel_eq_zero hε hu) hsupp hx

theorem abs_suzukiMollifiedDeriv_le (hε : 0 < ε)
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ (2 : ℕ))) (x : ℝ) :
    |suzukiMollifiedDeriv σ ε V x|
      ≤ Real.sqrt ((∫ u, suzukiDerivKernel σ ε u ^ (2 : ℕ)) * ∫ t, V t ^ (2 : ℕ)) := by
  rw [suzukiMollifiedDeriv_eq]
  exact abs_lineConvolution_le (continuous_suzukiDerivKernel σ ε).aestronglyMeasurable
    (((continuous_suzukiDerivKernel σ ε).pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_sq (hasCompactSupport_suzukiDerivKernel hε)))
    hVm hV2 x

theorem abs_suzukiMollifiedDeriv_sub_le (hε : 0 < ε)
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ (2 : ℕ))) (x y : ℝ) :
    |suzukiMollifiedDeriv σ ε V x - suzukiMollifiedDeriv σ ε V y|
      ≤ Real.sqrt ((∫ u, deriv (suzukiDerivKernel σ ε) u ^ (2 : ℕ)) * ∫ t, V t ^ (2 : ℕ)) * |x - y| := by
  rw [suzukiMollifiedDeriv_eq]
  exact abs_lineConvolution_sub_le (contDiff_suzukiDerivKernel σ ε)
    (hasCompactSupport_suzukiDerivKernel hε) hVm hV2 x y

end MollifiedDerivData

/-! ## The `(20)` mass identities for the defect kernel -/

/-- The `L¹` mass of the base first-moment kernel. -/
noncomputable def suzukiMomentMass : ℝ := ∫ u, |firstMomentKernel suzukiBaseMollifier u|

/-- The `L¹` mass of the derivative of the base first-moment kernel. -/
noncomputable def suzukiMomentDerivMass : ℝ :=
  ∫ u, |firstMomentDeriv suzukiBaseMollifier (deriv suzukiBaseMollifier) u|

/-- The scale-uniform defect-kernel mass. -/
noncomputable def suzukiDefectMass : ℝ := suzukiMomentDerivMass + suzukiMomentMass

theorem suzukiMomentMass_nonneg : 0 ≤ suzukiMomentMass :=
  integral_nonneg fun _ => abs_nonneg _

theorem suzukiMomentMass_le_one : suzukiMomentMass ≤ 1 :=
  integral_abs_firstMomentKernel_bump_le one_pos

theorem suzukiMomentDerivMass_nonneg : 0 ≤ suzukiMomentDerivMass :=
  integral_nonneg fun _ => abs_nonneg _

theorem suzukiDefectMass_nonneg : 0 ≤ suzukiDefectMass :=
  add_nonneg suzukiMomentDerivMass_nonneg suzukiMomentMass_nonneg

theorem hasDerivAt_suzukiBaseMollifier (u : ℝ) :
    HasDerivAt suzukiBaseMollifier (deriv suzukiBaseMollifier u) u :=
  ((contDiff_suzukiBaseMollifier.differentiable (by simp)) u).hasDerivAt

theorem integral_abs_firstMomentKernel_suzukiMollifier {ε : ℝ} (hε : 0 < ε) :
    (∫ u, |firstMomentKernel (suzukiMollifier ε) u|) = ε * suzukiMomentMass :=
  integral_abs_firstMomentKernel_scaled hε

theorem deriv_firstMomentKernel_suzukiMollifier {ε : ℝ} :
    deriv (firstMomentKernel (suzukiMollifier ε)) = fun t =>
      ε⁻¹ * firstMomentDeriv suzukiBaseMollifier (deriv suzukiBaseMollifier) (t / ε) :=
  funext fun t =>
    (hasDerivAt_firstMomentKernel_scaled
      (fun u => hasDerivAt_suzukiBaseMollifier u) t).deriv

theorem integral_abs_deriv_firstMomentKernel_suzukiMollifier {ε : ℝ} (hε : 0 < ε) :
    (∫ u, |deriv (firstMomentKernel (suzukiMollifier ε)) u|) = suzukiMomentDerivMass := by
  rw [deriv_firstMomentKernel_suzukiMollifier]
  exact integral_abs_firstMomentDeriv_scaled hε

/-! ## The defect kernel and the defect's uniform `L²` bound -/

/-- The defect kernel `k_ε′ − σk_ε`. -/
noncomputable def suzukiDefectKernel (σ ε : ℝ) : ℝ → ℝ :=
  fun u => deriv (firstMomentKernel (suzukiMollifier ε)) u
    - σ * firstMomentKernel (suzukiMollifier ε) u

theorem suzukiMollifiedDefect_eq (σ ε : ℝ) (V : ℝ → ℝ) :
    suzukiMollifiedDefect σ ε V = lineConvolution (suzukiDefectKernel σ ε) V := rfl

theorem continuous_firstMomentKernel_suzukiMollifier (ε : ℝ) :
    Continuous (firstMomentKernel (suzukiMollifier ε)) := by
  have : Continuous fun t : ℝ => t * suzukiMollifier ε t :=
    continuous_id.mul (contDiff_suzukiMollifier ε).continuous
  exact this

theorem hasCompactSupport_firstMomentKernel_suzukiMollifier {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (firstMomentKernel (suzukiMollifier ε)) := by
  have := (hasCompactSupport_suzukiMollifier hε).mul_left (f := fun t : ℝ => t)
  exact this

theorem continuous_firstMomentDeriv_base :
    Continuous (firstMomentDeriv suzukiBaseMollifier (deriv suzukiBaseMollifier)) := by
  unfold firstMomentDeriv
  exact contDiff_suzukiBaseMollifier.continuous.add
    (continuous_id.mul
      (contDiff_infty_iff_deriv.mp contDiff_suzukiBaseMollifier).2.continuous)

theorem continuous_deriv_firstMomentKernel_suzukiMollifier (ε : ℝ) :
    Continuous (deriv (firstMomentKernel (suzukiMollifier ε))) := by
  rw [deriv_firstMomentKernel_suzukiMollifier]
  exact continuous_const.mul
    (continuous_firstMomentDeriv_base.comp (continuous_id.div_const ε))

theorem hasCompactSupport_deriv_firstMomentKernel_suzukiMollifier {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (deriv (firstMomentKernel (suzukiMollifier ε))) :=
  (hasCompactSupport_firstMomentKernel_suzukiMollifier hε).deriv

theorem continuous_suzukiDefectKernel (ε σ : ℝ) : Continuous (suzukiDefectKernel σ ε) := by
  unfold suzukiDefectKernel
  exact (continuous_deriv_firstMomentKernel_suzukiMollifier ε).sub
    (continuous_const.mul (continuous_firstMomentKernel_suzukiMollifier ε))

theorem hasCompactSupport_suzukiDefectKernel {σ ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (suzukiDefectKernel σ ε) := by
  unfold suzukiDefectKernel
  refine (hasCompactSupport_deriv_firstMomentKernel_suzukiMollifier hε).sub ?_
  have := (hasCompactSupport_firstMomentKernel_suzukiMollifier hε).mul_left
    (f := fun _ : ℝ => σ)
  exact this

/-- **The `(20)` bound.**  The defect kernel's mass is bounded uniformly in the width. -/
theorem integral_abs_suzukiDefectKernel_le {σ ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    (∫ u, |suzukiDefectKernel σ ε u|) ≤ suzukiDefectMass := by
  have hint1 : Integrable (fun u => |deriv (firstMomentKernel (suzukiMollifier ε)) u|) :=
    ((continuous_deriv_firstMomentKernel_suzukiMollifier ε).integrable_of_hasCompactSupport
      (hasCompactSupport_deriv_firstMomentKernel_suzukiMollifier hε)).abs
  have hint2 : Integrable (fun u => |firstMomentKernel (suzukiMollifier ε) u|) :=
    ((continuous_firstMomentKernel_suzukiMollifier ε).integrable_of_hasCompactSupport
      (hasCompactSupport_firstMomentKernel_suzukiMollifier hε)).abs
  have hmono : (∫ u, |suzukiDefectKernel σ ε u|)
      ≤ ∫ u, |deriv (firstMomentKernel (suzukiMollifier ε)) u|
        + σ * |firstMomentKernel (suzukiMollifier ε) u| := by
    have hker : Integrable (fun u => |suzukiDefectKernel σ ε u|) :=
      ((continuous_suzukiDefectKernel ε σ).integrable_of_hasCompactSupport
        (hasCompactSupport_suzukiDefectKernel hε)).abs
    refine integral_mono hker (hint1.add (hint2.const_mul σ)) fun u => ?_
    unfold suzukiDefectKernel
    calc |deriv (firstMomentKernel (suzukiMollifier ε)) u
          - σ * firstMomentKernel (suzukiMollifier ε) u|
        ≤ |deriv (firstMomentKernel (suzukiMollifier ε)) u|
          + |σ * firstMomentKernel (suzukiMollifier ε) u| := abs_sub _ _
      _ = |deriv (firstMomentKernel (suzukiMollifier ε)) u|
          + σ * |firstMomentKernel (suzukiMollifier ε) u| := by
          rw [abs_mul, abs_of_nonneg hσ0]
  have hsplit : (∫ u, |deriv (firstMomentKernel (suzukiMollifier ε)) u|
        + σ * |firstMomentKernel (suzukiMollifier ε) u|)
      = suzukiMomentDerivMass + σ * (ε * suzukiMomentMass) := by
    rw [integral_add hint1 (hint2.const_mul σ), integral_const_mul,
      integral_abs_deriv_firstMomentKernel_suzukiMollifier hε,
      integral_abs_firstMomentKernel_suzukiMollifier hε]
  have hfinal : suzukiMomentDerivMass + σ * (ε * suzukiMomentMass) ≤ suzukiDefectMass := by
    unfold suzukiDefectMass
    have h1 : σ * (ε * suzukiMomentMass) ≤ suzukiMomentMass := by
      have h2 : σ * ε ≤ 1 := by nlinarith
      nlinarith [suzukiMomentMass_nonneg, mul_nonneg hσ0 hε.le]
    linarith
  calc (∫ u, |suzukiDefectKernel σ ε u|)
      ≤ ∫ u, |deriv (firstMomentKernel (suzukiMollifier ε)) u|
        + σ * |firstMomentKernel (suzukiMollifier ε) u| := hmono
    _ = suzukiMomentDerivMass + σ * (ε * suzukiMomentMass) := hsplit
    _ ≤ suzukiDefectMass := hfinal

/-! ## Uniform `L²` control of the mollified data and defect -/

/-- Mollification by the family is an `L²` contraction. -/
theorem integral_sq_suzukiMollified_le {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf2 : Integrable (fun t => f t ^ (2 : ℕ))) :
    (∫ x, lineConvolution (suzukiMollifier ε) f x ^ (2 : ℕ)) ≤ ∫ t, f t ^ (2 : ℕ) := by
  have hconv : Integrable (fun x => mollify (suzukiMollifier ε) f x ^ (2 : ℕ)) := by
    rw [mollify_eq_lineConvolution]
    exact integrable_sq_lineConvolution (contDiff_suzukiMollifier ε).continuous
      (hasCompactSupport_suzukiMollifier hε) hfm hf2
  have h := integral_sq_mollify_le_of_isProbabilityDensity
    (contDiff_suzukiMollifier ε).continuous.measurable hfm
    (suzukiMollifier_nonneg hε) (integrable_suzukiMollifier hε)
    (integral_suzukiMollifier hε) hf2 hconv
  rwa [mollify_eq_lineConvolution] at h

theorem integrable_sq_suzukiMollified {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf2 : Integrable (fun t => f t ^ (2 : ℕ))) :
    Integrable (fun x => lineConvolution (suzukiMollifier ε) f x ^ (2 : ℕ)) :=
  integrable_sq_lineConvolution (contDiff_suzukiMollifier ε).continuous
    (hasCompactSupport_suzukiMollifier hε) hfm hf2

theorem integrable_sq_suzukiMollifiedDefect {σ ε : ℝ} (hε : 0 < ε) {V : ℝ → ℝ}
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ))) :
    Integrable (fun x => suzukiMollifiedDefect σ ε V x ^ (2 : ℕ)) := by
  rw [suzukiMollifiedDefect_eq]
  exact integrable_sq_lineConvolution (continuous_suzukiDefectKernel ε σ)
    (hasCompactSupport_suzukiDefectKernel hε) hVmm hV2

/-- **The defect is uniformly small in `L²`.** -/
theorem integral_sq_suzukiMollifiedDefect_le {σ ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {V : ℝ → ℝ}
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ))) :
    (∫ x, suzukiMollifiedDefect σ ε V x ^ (2 : ℕ))
      ≤ suzukiDefectMass ^ (2 : ℕ) * ∫ t, V t ^ (2 : ℕ) := by
  rw [suzukiMollifiedDefect_eq]
  have hyoung := integral_sq_lineConvolution_le
    (continuous_suzukiDefectKernel ε σ).measurable hVmm
    (((continuous_suzukiDefectKernel ε σ).integrable_of_hasCompactSupport
      (hasCompactSupport_suzukiDefectKernel hε)).abs)
    hV2
    (integrable_sq_lineConvolution (continuous_suzukiDefectKernel ε σ)
      (hasCompactSupport_suzukiDefectKernel hε) hVmm hV2)
  have hmass := integral_abs_suzukiDefectKernel_le hε hε1 hσ0 hσ1
  have hnn : (0 : ℝ) ≤ ∫ u, |suzukiDefectKernel σ ε u| :=
    integral_nonneg fun u => abs_nonneg _
  have hVnn : (0 : ℝ) ≤ ∫ t, V t ^ (2 : ℕ) := integral_nonneg fun t => sq_nonneg _
  calc (∫ x, lineConvolution (suzukiDefectKernel σ ε) V x ^ (2 : ℕ))
      ≤ (∫ u, |suzukiDefectKernel σ ε u|) ^ (2 : ℕ) * ∫ t, V t ^ (2 : ℕ) := hyoung
    _ ≤ suzukiDefectMass ^ (2 : ℕ) * ∫ t, V t ^ (2 : ℕ) := by
        refine mul_le_mul_of_nonneg_right ?_ hVnn
        exact pow_le_pow_left₀ hnn hmass 2

/-! ## The jump of the mollified derivative is square-integrable -/

/-- **The Gamma jump of `U_ε` is in `L²`.**  The translate modulus of the convolution is linear
at small scales, so the `L²` scale majorant applies. -/
theorem integrable_sq_shiftedGammaJump_suzukiMollifiedDeriv {σ ε : ℝ} {V : ℝ → ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ)))
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Integrable (fun x => shiftedGammaJump σ (suzukiMollifiedDeriv σ ε V) x ^ (2 : ℕ)) := by
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  have hPm : Measurable (suzukiMollifiedDeriv σ ε V) :=
    (continuous_suzukiMollifiedDeriv hε hVm hV2).measurable
  have hP2 : Integrable (fun x => suzukiMollifiedDeriv σ ε V x ^ (2 : ℕ)) :=
    integrable_sq_suzukiMollifiedDeriv hε hVmm hV2
  have hgc := continuous_suzukiDerivKernel σ ε
  have hgC1 := contDiff_suzukiDerivKernel σ ε
  have hg'c : Continuous (deriv (suzukiDerivKernel σ ε)) := hgC1.continuous_deriv le_rfl
  have hg'cs : HasCompactSupport (deriv (suzukiDerivKernel σ ε)) :=
    (hasCompactSupport_suzukiDerivKernel hε).deriv
  obtain ⟨Mg, hMg0, hMg⟩ := exists_abs_le_of_hasCompactSupport hg'c hg'cs
  have hgK : ∀ u v : ℝ, |suzukiDerivKernel σ ε u - suzukiDerivKernel σ ε v|
      ≤ Mg * |u - v| := fun u v => abs_sub_le_of_deriv_bound hgC1 hMg u v
  have hgsupp1 : ∀ u : ℝ, (1 : ℝ) < |u| → suzukiDerivKernel σ ε u = 0 := fun u hu =>
    suzukiDerivKernel_eq_zero hε (lt_of_le_of_lt hε1 hu)
  have hCV : (0 : ℝ) ≤ ∫ t, V t ^ (2 : ℕ) := integral_nonneg fun t => sq_nonneg _
  set CV : ℝ := Real.sqrt (∫ t, V t ^ (2 : ℕ)) with hCVdef
  have hCV0 : 0 ≤ CV := Real.sqrt_nonneg _
  set C₁ : ℝ := 3 * Mg * CV + 1 with hC₁def
  set C₂ : ℝ := Real.sqrt (∫ x, suzukiMollifiedDeriv σ ε V x ^ (2 : ℕ)) + 1 with hC₂def
  have hC₁ : 0 < C₁ := by
    rw [hC₁def]
    positivity
  have hC₂ : 0 < C₂ := by
    rw [hC₂def]
    positivity
  have htrans : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (∫ x, (suzukiMollifiedDeriv σ ε V (x + s) - suzukiMollifiedDeriv σ ε V x) ^ (2 : ℕ))
        ≤ (C₁ * s) ^ (2 : ℕ) := by
    intro s hs0 hs1
    have hyoung : (∫ x, (suzukiMollifiedDeriv σ ε V (x + s)
          - suzukiMollifiedDeriv σ ε V x) ^ (2 : ℕ))
        ≤ (∫ u, |suzukiDerivKernel σ ε (u + s) - suzukiDerivKernel σ ε u|) ^ (2 : ℕ)
          * ∫ t, V t ^ (2 : ℕ) := by
      rw [suzukiMollifiedDeriv_eq]
      exact integral_sq_lineConvolution_translate_le hgc
        (hasCompactSupport_suzukiDerivKernel hε) hVmm hV2 s
    have hkernel : (∫ u, |suzukiDerivKernel σ ε (u + s) - suzukiDerivKernel σ ε u|)
        ≤ 3 * Mg * s := by
      have h := integral_abs_kernel_translate_le hgK hgsupp1 zero_le_one hs0
      calc (∫ u, |suzukiDerivKernel σ ε (u + s) - suzukiDerivKernel σ ε u|)
          ≤ Mg * s * (2 * 1 + s) := h
        _ ≤ 3 * Mg * s := by nlinarith [mul_nonneg hMg0 hs0]
    have hknn : (0 : ℝ) ≤ ∫ u, |suzukiDerivKernel σ ε (u + s) - suzukiDerivKernel σ ε u| :=
      integral_nonneg fun u => abs_nonneg _
    calc (∫ x, (suzukiMollifiedDeriv σ ε V (x + s) - suzukiMollifiedDeriv σ ε V x) ^ (2 : ℕ))
        ≤ (∫ u, |suzukiDerivKernel σ ε (u + s) - suzukiDerivKernel σ ε u|) ^ (2 : ℕ)
          * ∫ t, V t ^ (2 : ℕ) := hyoung
      _ ≤ (3 * Mg * s) ^ (2 : ℕ) * ∫ t, V t ^ (2 : ℕ) := by
          refine mul_le_mul_of_nonneg_right ?_ hCV
          exact pow_le_pow_left₀ hknn hkernel 2
      _ = (3 * Mg * CV * s) ^ (2 : ℕ) := by
          rw [hCVdef]
          rw [show (3 * Mg * Real.sqrt (∫ t, V t ^ (2 : ℕ)) * s) ^ (2 : ℕ)
              = (3 * Mg * s) ^ (2 : ℕ) * Real.sqrt (∫ t, V t ^ (2 : ℕ)) ^ (2 : ℕ) from by ring,
            Real.sq_sqrt hCV]
      _ ≤ (C₁ * s) ^ (2 : ℕ) := by
          have h1 : 0 ≤ 3 * Mg * CV * s := by positivity
          have h2 : 3 * Mg * CV * s ≤ C₁ * s := by
            rw [hC₁def]
            nlinarith
          exact pow_le_pow_left₀ h1 h2 2
  have hE : (∫ x, suzukiMollifiedDeriv σ ε V x ^ (2 : ℕ)) ≤ C₂ ^ (2 : ℕ) := by
    rw [hC₂def]
    have hPnn : (0 : ℝ) ≤ ∫ x, suzukiMollifiedDeriv σ ε V x ^ (2 : ℕ) :=
      integral_nonneg fun x => sq_nonneg _
    nlinarith [Real.sq_sqrt hPnn, Real.sqrt_nonneg (∫ x, suzukiMollifiedDeriv σ ε V x ^ (2 : ℕ))]
  have h := (integrable_sq_gammaScaleIntegral hPm hP2 htrans hE hC₁ hC₂ hσ0 hσ1).1
  unfold shiftedGammaJump
  exact h

/-! ## The uniform energy bound -/

/-- Closing the coercive square: `cA ≤ D√A` forces `c²A ≤ D²`. -/
theorem sq_energy_close {c A D : ℝ} (hc : 0 < c) (hA0 : 0 ≤ A)
    (h : c * A ≤ D * Real.sqrt A) : c ^ (2 : ℕ) * A ≤ D ^ (2 : ℕ) := by
  have hs0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hsq : Real.sqrt A ^ (2 : ℕ) = A := Real.sq_sqrt hA0
  rcases eq_or_lt_of_le hs0 with hzero | hpos
  · have hA00 : A = 0 := by
      rw [← hsq, ← hzero]
      ring
    rw [hA00, mul_zero]
    exact sq_nonneg _
  · have hstep : c * Real.sqrt A ≤ D := by
      have h' : c * Real.sqrt A * Real.sqrt A ≤ D * Real.sqrt A := by
        calc c * Real.sqrt A * Real.sqrt A = c * A := by linear_combination c * hsq
          _ ≤ D * Real.sqrt A := h
      exact le_of_mul_le_mul_right h' hpos
    calc c ^ (2 : ℕ) * A = (c * Real.sqrt A) ^ (2 : ℕ) := by linear_combination (-(c ^ (2 : ℕ))) * hsq
      _ ≤ D ^ (2 : ℕ) := pow_le_pow_left₀ (mul_nonneg hc.le hs0) hstep 2

/-- `(a+b+c)² ≤ 3a² + 3b² + 3c²`. -/
theorem sq_add_three_le (a b c : ℝ) :
    (a + b + c) ^ (2 : ℕ) ≤ 3 * a ^ (2 : ℕ) + 3 * b ^ (2 : ℕ) + 3 * c ^ (2 : ℕ) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- **The uniform energy bound.**  On the coercive budget
`c ≤ 2(L₀ − ε) − κ_σ − |τ|`, the mollified weak derivative's energy is bounded by the data,
uniformly in the width: `c² ∫U_ε² ≤ 3∫G² + (3 + 12 Λ²)∫V²`, `Λ` the defect-kernel mass. -/
theorem suzukiGamma_uniform_energy_bound {σ τ L₀ ε c : ℝ} {V G : ℝ → ℝ}
    (heq : SuzukiGammaTestedEquation σ τ V G)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ)))
    (hGmm : Measurable G) (hG2 : Integrable (fun t => G t ^ (2 : ℕ)))
    (hsupp : ∀ t : ℝ, t < L₀ → V t = 0)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : 0 < c) (hcle : c ≤ 2 * (L₀ - ε) - suzukiGammaShiftKappa σ - |τ|) :
    c ^ (2 : ℕ) * ∫ x, suzukiMollifiedDeriv σ ε V x ^ (2 : ℕ)
      ≤ 3 * (∫ t, G t ^ (2 : ℕ)) + (3 + 12 * suzukiDefectMass ^ (2 : ℕ)) * ∫ t, V t ^ (2 : ℕ) := by
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  set U : ℝ → ℝ := suzukiMollifiedDeriv σ ε V with hUdef
  set W : ℝ → ℝ := suzukiMollifiedDefect σ ε V with hWdef
  set Vm : ℝ → ℝ := lineConvolution (suzukiMollifier ε) V with hVmdef
  set Gm : ℝ → ℝ := lineConvolution (suzukiMollifier ε) G with hGmdef
  set J : ℝ → ℝ := shiftedGammaJump σ (suzukiMollifiedDeriv σ ε V) with hJdef
  have hEq : ∀ x, 2 * x * U x - 2 * W x + J x - τ * U x + Vm x = Gm x := fun x =>
    suzukiGamma_mollified_equation heq hVmm hV2 hσ0 hσ1 hε x
  -- regularity of the players
  have hUc : Continuous U := continuous_suzukiMollifiedDeriv hε hVm hV2
  have hUa : AEStronglyMeasurable U volume := hUc.aestronglyMeasurable
  have hU2 : Integrable (fun x => U x ^ (2 : ℕ)) := integrable_sq_suzukiMollifiedDeriv hε hVmm hV2
  have hJ2 : Integrable (fun x => J x ^ (2 : ℕ)) :=
    integrable_sq_shiftedGammaJump_suzukiMollifiedDeriv hε hε1 hVmm hV2 hσ0 hσ1
  have hJa : AEStronglyMeasurable J volume := by
    have hm : Measurable fun x =>
        ∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ (suzukiMollifiedDeriv σ ε V) x s
          * gammaTransportKernel s :=
      measurable_gammaScaleIntegral σ hUc.measurable
    exact hm.aestronglyMeasurable
  have hWc : Continuous W := by
    rw [hWdef, suzukiMollifiedDefect_eq]
    exact continuous_lineConvolution (continuous_suzukiDefectKernel ε σ)
      (hasCompactSupport_suzukiDefectKernel hε)
      (locallyIntegrable_of_sq_integrable hVm hV2)
  have hWa : AEStronglyMeasurable W volume := hWc.aestronglyMeasurable
  have hW2 : Integrable (fun x => W x ^ (2 : ℕ)) := integrable_sq_suzukiMollifiedDefect hε hVmm hV2
  have hVmc : Continuous Vm :=
    continuous_lineConvolution (contDiff_suzukiMollifier ε).continuous
      (hasCompactSupport_suzukiMollifier hε) (locallyIntegrable_of_sq_integrable hVm hV2)
  have hVma : AEStronglyMeasurable Vm volume := hVmc.aestronglyMeasurable
  have hVm2 : Integrable (fun x => Vm x ^ (2 : ℕ)) := integrable_sq_suzukiMollified hε hVmm hV2
  have hGmc : Continuous Gm :=
    continuous_lineConvolution (contDiff_suzukiMollifier ε).continuous
      (hasCompactSupport_suzukiMollifier hε)
      (locallyIntegrable_of_sq_integrable hGmm.aestronglyMeasurable hG2)
  have hGma : AEStronglyMeasurable Gm volume := hGmc.aestronglyMeasurable
  have hGm2 : Integrable (fun x => Gm x ^ (2 : ℕ)) := integrable_sq_suzukiMollified hε hGmm hG2
  -- the position-weighted copy of U is square-integrable, from the equation
  have hidU2 : Integrable (fun x => (x * U x) ^ (2 : ℕ)) := by
    have hs1a : AEStronglyMeasurable (fun x => Gm x + 2 * W x) volume :=
      hGma.add (hWa.const_mul 2)
    have hs1 : Integrable (fun x => (Gm x + 2 * W x) ^ (2 : ℕ)) :=
      integrable_sq_add' hGma (hWa.const_mul 2) hGm2 (integrable_sq_const_mul 2 hW2)
    have hs2a : AEStronglyMeasurable (fun x => Gm x + 2 * W x + τ * U x) volume :=
      hs1a.add (hUa.const_mul τ)
    have hs2 : Integrable (fun x => (Gm x + 2 * W x + τ * U x) ^ (2 : ℕ)) :=
      integrable_sq_add' hs1a (hUa.const_mul τ) hs1 (integrable_sq_const_mul τ hU2)
    have hs3a : AEStronglyMeasurable (fun x => Gm x + 2 * W x + τ * U x + (-1) * J x)
        volume := hs2a.add (hJa.const_mul (-1))
    have hs3 : Integrable (fun x => (Gm x + 2 * W x + τ * U x + (-1) * J x) ^ (2 : ℕ)) :=
      integrable_sq_add' hs2a (hJa.const_mul (-1)) hs2 (integrable_sq_const_mul (-1) hJ2)
    have hs4 : Integrable
        (fun x => (Gm x + 2 * W x + τ * U x + (-1) * J x + (-1) * Vm x) ^ (2 : ℕ)) :=
      integrable_sq_add' hs3a (hVma.const_mul (-1)) hs3 (integrable_sq_const_mul (-1) hVm2)
    have hs5 : Integrable (fun x =>
        ((1 / 2) * (Gm x + 2 * W x + τ * U x + (-1) * J x + (-1) * Vm x)) ^ (2 : ℕ)) :=
      integrable_sq_const_mul (1 / 2) hs4
    refine hs5.congr ?_
    filter_upwards with x
    have h := hEq x
    have hval : (1 / 2 : ℝ) * (Gm x + 2 * W x + τ * U x + (-1) * J x + (-1) * Vm x)
        = x * U x := by linarith
    rw [hval]
  have hidUa : AEStronglyMeasurable (fun x => x * U x) volume :=
    aestronglyMeasurable_id.mul hUa
  -- `U ∈ L¹`, so the numerical range applies
  have hUL1 : Integrable U :=
    integrable_of_sq_integrable_of_mul_sq_integrable hUa hU2 hidU2
  have hUB := abs_suzukiMollifiedDeriv_le (σ := σ) hε hVm hV2
  have hUK := abs_suzukiMollifiedDeriv_sub_le (σ := σ) hε hVm hV2
  have hNR : -(suzukiGammaShiftKappa σ * ∫ x, U x ^ (2 : ℕ)) ≤ ∫ x, J x * U x := by
    have h := neg_suzukiGammaShiftKappa_mul_le_gammaJumpPairing
      (U := suzukiMollifiedDeriv σ ε V)
      hUc.measurable (fun x y => hUK x y) (fun x => hUB x) hσ0 hσ1 hUL1 hU2
    calc -(suzukiGammaShiftKappa σ * ∫ x, U x ^ (2 : ℕ))
        ≤ ∫ L, shiftedGammaJump σ (suzukiMollifiedDeriv σ ε V) L
            * suzukiMollifiedDeriv σ ε V L := h
      _ = ∫ x, J x * U x := rfl
  -- the support lower bound for the position pairing
  have hIP1 : Integrable (fun x => x * U x * U x) :=
    integrable_mul_of_sq_integrable hidUa hUa hidU2 hU2
  have hIx : (L₀ - ε) * (∫ x, U x ^ (2 : ℕ)) ≤ ∫ x, x * U x * U x := by
    have hint : Integrable (fun x => (x - (L₀ - ε)) * U x ^ (2 : ℕ)) := by
      refine (hIP1.sub (hU2.const_mul (L₀ - ε))).congr ?_
      filter_upwards with x
      show x * U x * U x - (L₀ - ε) * U x ^ (2 : ℕ) = (x - (L₀ - ε)) * U x ^ (2 : ℕ)
      ring
    have hnn : 0 ≤ ∫ x, (x - (L₀ - ε)) * U x ^ (2 : ℕ) := by
      refine integral_nonneg fun x => ?_
      rcases lt_or_ge x (L₀ - ε) with hx | hx
      · have hzero : U x = 0 := suzukiMollifiedDeriv_eq_zero hε hsupp hx
        rw [hzero]
        simp
      · have h1 : 0 ≤ x - (L₀ - ε) := by linarith
        exact mul_nonneg h1 (sq_nonneg _)
    have hsplit : (∫ x, (x - (L₀ - ε)) * U x ^ (2 : ℕ))
        = (∫ x, x * U x * U x) - (L₀ - ε) * ∫ x, U x ^ (2 : ℕ) := by
      calc (∫ x, (x - (L₀ - ε)) * U x ^ (2 : ℕ))
          = ∫ x, x * U x * U x - (L₀ - ε) * U x ^ (2 : ℕ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            show (x - (L₀ - ε)) * U x ^ (2 : ℕ) = x * U x * U x - (L₀ - ε) * U x ^ (2 : ℕ)
            ring
        _ = (∫ x, x * U x * U x) - ∫ x, (L₀ - ε) * U x ^ (2 : ℕ) :=
            integral_sub hIP1 (hU2.const_mul (L₀ - ε))
        _ = (∫ x, x * U x * U x) - (L₀ - ε) * ∫ x, U x ^ (2 : ℕ) := by
            rw [integral_const_mul]
    linarith [hsplit ▸ hnn]
  -- the integrated pairing
  have hIP2 : Integrable (fun x => W x * U x) :=
    integrable_mul_of_sq_integrable hWa hUa hW2 hU2
  have hIP3 : Integrable (fun x => J x * U x) :=
    integrable_mul_of_sq_integrable hJa hUa hJ2 hU2
  have hIP4 : Integrable (fun x => U x * U x) := by
    refine hU2.congr ?_
    filter_upwards with x
    rw [pow_two]
  have hIP5 : Integrable (fun x => Vm x * U x) :=
    integrable_mul_of_sq_integrable hVma hUa hVm2 hU2
  have hIP6 : Integrable (fun x => Gm x * U x) :=
    integrable_mul_of_sq_integrable hGma hUa hGm2 hU2
  have hpair : 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) + (∫ x, J x * U x)
      - τ * (∫ x, U x * U x) + (∫ x, Vm x * U x) = ∫ x, Gm x * U x := by
    have hptw : ∀ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x
        - τ * (U x * U x) + Vm x * U x = Gm x * U x := by
      intro x
      have h := hEq x
      linear_combination U x * h
    have e1 : Integrable (fun x => 2 * (x * U x * U x)) := hIP1.const_mul 2
    have e2 : Integrable (fun x => 2 * (W x * U x)) := hIP2.const_mul 2
    have e12 : Integrable (fun x => 2 * (x * U x * U x) - 2 * (W x * U x)) := e1.sub e2
    have e123 : Integrable (fun x => 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x) :=
      e12.add hIP3
    have e4 : Integrable (fun x => τ * (U x * U x)) := hIP4.const_mul τ
    have e1234 : Integrable (fun x =>
        2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x - τ * (U x * U x)) :=
      e123.sub e4
    have q1 : (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x))
        = 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) := by
      calc (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x))
          = (∫ x, 2 * (x * U x * U x)) - ∫ x, 2 * (W x * U x) := integral_sub e1 e2
        _ = 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) := by
            rw [integral_const_mul, integral_const_mul]
    have q2 : (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x)
        = 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) + ∫ x, J x * U x := by
      calc (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x)
          = (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x)) + ∫ x, J x * U x :=
            integral_add e12 hIP3
        _ = 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) + ∫ x, J x * U x := by
            rw [q1]
    have q3 : (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x - τ * (U x * U x))
        = 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) + (∫ x, J x * U x)
          - τ * ∫ x, U x * U x := by
      calc (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x - τ * (U x * U x))
          = (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x)
            - ∫ x, τ * (U x * U x) := integral_sub e123 e4
        _ = 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) + (∫ x, J x * U x)
            - τ * ∫ x, U x * U x := by
            rw [q2, integral_const_mul]
    have q4 : (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x - τ * (U x * U x)
          + Vm x * U x)
        = 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) + (∫ x, J x * U x)
          - τ * (∫ x, U x * U x) + ∫ x, Vm x * U x := by
      calc (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x - τ * (U x * U x)
            + Vm x * U x)
          = (∫ x, 2 * (x * U x * U x) - 2 * (W x * U x) + J x * U x - τ * (U x * U x))
            + ∫ x, Vm x * U x := integral_add e1234 hIP5
        _ = 2 * (∫ x, x * U x * U x) - 2 * (∫ x, W x * U x) + (∫ x, J x * U x)
            - τ * (∫ x, U x * U x) + ∫ x, Vm x * U x := by
            rw [q3]
    rw [← q4]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hptw x)
  -- Cauchy–Schwarz on the data pairings
  set A : ℝ := ∫ x, U x ^ (2 : ℕ) with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  set sA : ℝ := Real.sqrt A with hsAdef
  have habsCS : ∀ (F : ℝ → ℝ), AEStronglyMeasurable F volume →
      Integrable (fun x => F x ^ (2 : ℕ)) →
      |∫ x, F x * U x| ≤ Real.sqrt (∫ x, F x ^ (2 : ℕ)) * sA := by
    intro F hFm hF2
    have h := sq_integral_mul_le (μ := (volume : Measure ℝ)) hFm hUa hF2 hU2
    calc |∫ x, F x * U x| = Real.sqrt ((∫ x, F x * U x) ^ (2 : ℕ)) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∫ x, F x ^ (2 : ℕ)) * A) := Real.sqrt_le_sqrt h
      _ = Real.sqrt (∫ x, F x ^ (2 : ℕ)) * sA := by
          rw [hsAdef, Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  -- data bounds
  have hCVnn : (0 : ℝ) ≤ ∫ t, V t ^ (2 : ℕ) := integral_nonneg fun t => sq_nonneg _
  have hCGnn : (0 : ℝ) ≤ ∫ t, G t ^ (2 : ℕ) := integral_nonneg fun t => sq_nonneg _
  set CV : ℝ := Real.sqrt (∫ t, V t ^ (2 : ℕ)) with hCVdef
  set CG : ℝ := Real.sqrt (∫ t, G t ^ (2 : ℕ)) with hCGdef
  have hGmB : Real.sqrt (∫ x, Gm x ^ (2 : ℕ)) ≤ CG := by
    rw [hCGdef]
    exact Real.sqrt_le_sqrt (integral_sq_suzukiMollified_le hε hGmm hG2)
  have hVmB : Real.sqrt (∫ x, Vm x ^ (2 : ℕ)) ≤ CV := by
    rw [hCVdef]
    exact Real.sqrt_le_sqrt (integral_sq_suzukiMollified_le hε hVmm hV2)
  have hWB : Real.sqrt (∫ x, W x ^ (2 : ℕ)) ≤ suzukiDefectMass * CV := by
    have h := integral_sq_suzukiMollifiedDefect_le hε hε1 hσ0 hσ1 hVmm hV2
    have hb : (0 : ℝ) ≤ suzukiDefectMass * CV :=
      mul_nonneg suzukiDefectMass_nonneg (Real.sqrt_nonneg _)
    calc Real.sqrt (∫ x, W x ^ (2 : ℕ))
        ≤ Real.sqrt (suzukiDefectMass ^ (2 : ℕ) * ∫ t, V t ^ (2 : ℕ)) := Real.sqrt_le_sqrt h
      _ = suzukiDefectMass * CV := by
          rw [hCVdef, Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq suzukiDefectMass_nonneg]
  -- coercive assembly
  have hcoercive : c * A ≤ (CG + 2 * (suzukiDefectMass * CV) + CV) * sA := by
    have h1 : c * A ≤ 2 * (∫ x, x * U x * U x) + (∫ x, J x * U x)
        - τ * (∫ x, U x * U x) := by
      have hUU : (∫ x, U x * U x) = A := by
        rw [hAdef]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show U x * U x = U x ^ (2 : ℕ)
        rw [pow_two]
      rw [hUU]
      have hτ : -|τ| * A ≤ -τ * A := by
        have h := le_abs_self τ
        nlinarith [hA0]
      nlinarith [hIx, hNR, hτ, mul_le_mul_of_nonneg_right hcle hA0]
    have h2 : 2 * (∫ x, x * U x * U x) + (∫ x, J x * U x) - τ * (∫ x, U x * U x)
        = (∫ x, Gm x * U x) + 2 * (∫ x, W x * U x) - ∫ x, Vm x * U x := by
      linarith [hpair]
    have h3 : (∫ x, Gm x * U x) + 2 * (∫ x, W x * U x) - (∫ x, Vm x * U x)
        ≤ (CG + 2 * (suzukiDefectMass * CV) + CV) * sA := by
      have hG' := habsCS Gm hGma hGm2
      have hW' := habsCS W hWa hW2
      have hV' := habsCS Vm hVma hVm2
      have hsA0 : 0 ≤ sA := Real.sqrt_nonneg _
      have hGle : (∫ x, Gm x * U x) ≤ CG * sA := by
        calc (∫ x, Gm x * U x) ≤ |∫ x, Gm x * U x| := le_abs_self _
          _ ≤ Real.sqrt (∫ x, Gm x ^ (2 : ℕ)) * sA := hG'
          _ ≤ CG * sA := mul_le_mul_of_nonneg_right hGmB hsA0
      have hWle : (∫ x, W x * U x) ≤ suzukiDefectMass * CV * sA := by
        calc (∫ x, W x * U x) ≤ |∫ x, W x * U x| := le_abs_self _
          _ ≤ Real.sqrt (∫ x, W x ^ (2 : ℕ)) * sA := hW'
          _ ≤ suzukiDefectMass * CV * sA := mul_le_mul_of_nonneg_right hWB hsA0
      have hVle : -(∫ x, Vm x * U x) ≤ CV * sA := by
        calc -(∫ x, Vm x * U x) ≤ |∫ x, Vm x * U x| := neg_le_abs _
          _ ≤ Real.sqrt (∫ x, Vm x ^ (2 : ℕ)) * sA := hV'
          _ ≤ CV * sA := mul_le_mul_of_nonneg_right hVmB hsA0
      nlinarith [hGle, hWle, hVle]
    linarith
  -- close the square
  have hfinal : c ^ (2 : ℕ) * A ≤ (CG + 2 * (suzukiDefectMass * CV) + CV) ^ (2 : ℕ) :=
    sq_energy_close hc hA0 hcoercive
  have hexpand : (CG + 2 * (suzukiDefectMass * CV) + CV) ^ (2 : ℕ)
      ≤ 3 * (∫ t, G t ^ (2 : ℕ)) + (3 + 12 * suzukiDefectMass ^ (2 : ℕ)) * ∫ t, V t ^ (2 : ℕ) := by
    have hCG2 : CG ^ (2 : ℕ) = ∫ t, G t ^ (2 : ℕ) := Real.sq_sqrt hCGnn
    have hCV2 : CV ^ (2 : ℕ) = ∫ t, V t ^ (2 : ℕ) := Real.sq_sqrt hCVnn
    calc (CG + 2 * (suzukiDefectMass * CV) + CV) ^ (2 : ℕ)
        ≤ 3 * CG ^ (2 : ℕ) + 3 * (2 * (suzukiDefectMass * CV)) ^ (2 : ℕ) + 3 * CV ^ (2 : ℕ) :=
          sq_add_three_le CG (2 * (suzukiDefectMass * CV)) CV
      _ = 3 * (∫ t, G t ^ (2 : ℕ)) + (3 + 12 * suzukiDefectMass ^ (2 : ℕ)) * ∫ t, V t ^ (2 : ℕ) := by
          rw [← hCG2, ← hCV2]
          ring
  calc c ^ (2 : ℕ) * ∫ x, suzukiMollifiedDeriv σ ε V x ^ (2 : ℕ) = c ^ (2 : ℕ) * A := by rw [hAdef]
    _ ≤ (CG + 2 * (suzukiDefectMass * CV) + CV) ^ (2 : ℕ) := hfinal
    _ ≤ 3 * (∫ t, G t ^ (2 : ℕ)) + (3 + 12 * suzukiDefectMass ^ (2 : ℕ)) * ∫ t, V t ^ (2 : ℕ) := hexpand

/-! ## The transported test: regularity and support -/

/-- The transported test is a reflected convolution. -/
theorem kernelTest_eq_lineConvolution (ρ φ : ℝ → ℝ) :
    (fun t => ∫ u, ρ u * φ (t + u)) = lineConvolution (fun u => ρ (-u)) φ := by
  funext t
  rw [lineConvolution]
  have h := integral_neg_eq_self (fun u => ρ u * φ (t + u)) (volume : Measure ℝ)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ρ (-u) * φ (t + -u) = ρ (-u) * φ (t - u)
  rw [show t + -u = t - u from by ring]

theorem continuous_kernelTest {ρ φ : ℝ → ℝ}
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (hφc : Continuous φ) :
    Continuous fun t => ∫ u, ρ u * φ (t + u) := by
  rw [kernelTest_eq_lineConvolution]
  have hrc : Continuous fun u : ℝ => ρ (-u) := hρc.comp continuous_neg
  have hrcs : HasCompactSupport fun u : ℝ => ρ (-u) := by
    have := hρcs.comp_homeomorph (Homeomorph.neg ℝ)
    simpa [Function.comp_def] using this
  exact continuous_lineConvolution hrc hrcs hφc.locallyIntegrable

theorem kernelTest_eq_zero {ρ φ : ℝ → ℝ} {r A : ℝ}
    (hρ : ∀ u : ℝ, r < |u| → ρ u = 0) (hφ : ∀ w : ℝ, A < |w| → φ w = 0)
    {t : ℝ} (ht : A + r < |t|) : (∫ u, ρ u * φ (t + u)) = 0 := by
  have hzero : ∀ u : ℝ, ρ u * φ (t + u) = 0 := by
    intro u
    rcases le_or_gt |u| r with hu | hu
    · have hw : A < |t + u| := by
        have h1 : |t| ≤ |t + u| + |u| := by
          calc |t| = |t + u + -u| := by ring_nf
            _ ≤ |t + u| + |-u| := abs_add_le _ _
            _ = |t + u| + |u| := by rw [abs_neg]
        linarith
      rw [hφ _ hw, mul_zero]
    · rw [hρ _ hu, zero_mul]
  simp only [hzero]
  exact integral_zero _ _

/-! ## The pairing identity and its limit -/

/-- **The pairing identity.**  The mollified weak derivative pairs against a test as the profile
against the transported test: the kernel derivative moves onto the test by parts. -/
theorem integral_suzukiMollifiedDeriv_mul_test {σ ε : ℝ} {V φ : ℝ → ℝ}
    (hε : 0 < ε) (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ)))
    (hφ : ContDiff ℝ 1 φ) (hφsupp : HasCompactSupport φ) :
    (∫ x, suzukiMollifiedDeriv σ ε V x * φ x)
      = -(∫ t, V t * ∫ u, suzukiMollifier ε u * deriv φ (t + u))
        - σ * ∫ t, V t * ∫ u, suzukiMollifier ε u * φ (t + u) := by
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  set ρ : ℝ → ℝ := suzukiMollifier ε with hρdef
  have hρc : Continuous ρ := (contDiff_suzukiMollifier ε).continuous
  have hρcs : HasCompactSupport ρ := hasCompactSupport_suzukiMollifier hε
  have hρ'c : Continuous (deriv ρ) := (contDiff_deriv_suzukiMollifier ε).continuous
  have hρ'cs : HasCompactSupport (deriv ρ) := hρcs.deriv
  have hgc := continuous_suzukiDerivKernel σ ε
  have hgcs := hasCompactSupport_suzukiDerivKernel (σ := σ) hε
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  -- transpose the convolution onto the test side
  have hpair : (∫ x, suzukiMollifiedDeriv σ ε V x * φ x)
      = ∫ t, V t * ∫ u, suzukiDerivKernel σ ε u * φ (t + u) := by
    rw [suzukiMollifiedDeriv_eq]
    exact integral_lineConvolution_mul_test hgc hgcs hVmm hV2 hφc hφsupp
  -- resolve the transported kernel: derivative by parts, no `ρ′` survives
  have hinner : ∀ t : ℝ, (∫ u, suzukiDerivKernel σ ε u * φ (t + u))
      = -(∫ u, ρ u * deriv φ (t + u)) - σ * ∫ u, ρ u * φ (t + u) := by
    intro t
    have hi1 : Integrable fun u => deriv ρ u * φ (t + u) :=
      Continuous.integrable_of_hasCompactSupport
        (hρ'c.mul (hφc.comp (continuous_const.add continuous_id))) (hρ'cs.mul_right)
    have hi2 : Integrable fun u => σ * (ρ u * φ (t + u)) :=
      (Continuous.integrable_of_hasCompactSupport
        (hρc.mul (hφc.comp (continuous_const.add continuous_id)))
        (hρcs.mul_right)).const_mul σ
    calc (∫ u, suzukiDerivKernel σ ε u * φ (t + u))
        = ∫ u, deriv ρ u * φ (t + u) - σ * (ρ u * φ (t + u)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          show suzukiDerivKernel σ ε u * φ (t + u)
              = deriv ρ u * φ (t + u) - σ * (ρ u * φ (t + u))
          unfold suzukiDerivKernel
          ring
      _ = (∫ u, deriv ρ u * φ (t + u)) - ∫ u, σ * (ρ u * φ (t + u)) :=
          integral_sub hi1 hi2
      _ = -(∫ u, ρ u * deriv φ (t + u)) - σ * ∫ u, ρ u * φ (t + u) := by
          rw [integral_deriv_kernel_test
            ((contDiff_suzukiMollifier ε).of_le (by exact_mod_cast le_top)) hρcs hφ t,
            integral_const_mul]
  -- split the profile pairing
  have hψc : Continuous fun t => ∫ u, ρ u * φ (t + u) :=
    continuous_kernelTest hρc hρcs hφc
  have hψ'c : Continuous fun t => ∫ u, ρ u * deriv φ (t + u) :=
    continuous_kernelTest hρc hρcs hφ'c
  obtain ⟨Aφ, hAφ⟩ := hφsupp.isBounded.subset_closedBall (0 : ℝ)
  have hφz : ∀ w : ℝ, |Aφ| + 1 < |w| → φ w = 0 := by
    intro w hw
    by_contra hne
    have hmem : w ∈ tsupport φ := subset_closure (by exact hne)
    have := hAφ hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have h2 : |w| ≤ |Aφ| := le_trans this (le_abs_self Aφ)
    linarith
  have hφ'z : ∀ w : ℝ, |Aφ| + 1 < |w| → deriv φ w = 0 := by
    intro w hw
    refine deriv_eq_zero_of_notMem_tsupport
      (fun x => ((hφ.differentiable one_ne_zero) x).hasDerivAt) ?_
    intro hmem
    have := hAφ hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have h2 : |w| ≤ |Aφ| := le_trans this (le_abs_self Aφ)
    linarith
  have hρz : ∀ u : ℝ, ε < |u| → ρ u = 0 := fun u hu => suzukiMollifier_eq_zero hε hu
  have hψcs : HasCompactSupport fun t => ∫ u, ρ u * φ (t + u) := by
    refine HasCompactSupport.intro
      (isCompact_Icc (a := -(|Aφ| + 1 + ε) - 1) (b := |Aφ| + 1 + ε + 1)) fun t ht => ?_
    refine kernelTest_eq_zero hρz hφz ?_
    rw [mem_Icc, not_and_or] at ht
    rcases ht with ht | ht
    · rw [not_le] at ht
      calc |Aφ| + 1 + ε < -t := by linarith
        _ ≤ |t| := neg_le_abs t
    · rw [not_le] at ht
      calc |Aφ| + 1 + ε < t := by linarith
        _ ≤ |t| := le_abs_self t
  have hψ'cs : HasCompactSupport fun t => ∫ u, ρ u * deriv φ (t + u) := by
    refine HasCompactSupport.intro
      (isCompact_Icc (a := -(|Aφ| + 1 + ε) - 1) (b := |Aφ| + 1 + ε + 1)) fun t ht => ?_
    refine kernelTest_eq_zero hρz hφ'z ?_
    rw [mem_Icc, not_and_or] at ht
    rcases ht with ht | ht
    · rw [not_le] at ht
      calc |Aφ| + 1 + ε < -t := by linarith
        _ ≤ |t| := neg_le_abs t
    · rw [not_le] at ht
      calc |Aφ| + 1 + ε < t := by linarith
        _ ≤ |t| := le_abs_self t
  have hIψ : Integrable fun t => V t * ∫ u, ρ u * φ (t + u) :=
    integrable_mul_of_sq_integrable hVm hψc.aestronglyMeasurable hV2
      ((hψc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hψcs))
  have hIψ' : Integrable fun t => V t * ∫ u, ρ u * deriv φ (t + u) :=
    integrable_mul_of_sq_integrable hVm hψ'c.aestronglyMeasurable hV2
      ((hψ'c.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hψ'cs))
  calc (∫ x, suzukiMollifiedDeriv σ ε V x * φ x)
      = ∫ t, V t * ∫ u, suzukiDerivKernel σ ε u * φ (t + u) := hpair
    _ = ∫ t, (-(V t * ∫ u, ρ u * deriv φ (t + u))
          - σ * (V t * ∫ u, ρ u * φ (t + u))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show V t * ∫ u, suzukiDerivKernel σ ε u * φ (t + u)
            = -(V t * ∫ u, ρ u * deriv φ (t + u)) - σ * (V t * ∫ u, ρ u * φ (t + u))
        rw [hinner t]
        ring
    _ = -(∫ t, V t * ∫ u, ρ u * deriv φ (t + u))
          - σ * ∫ t, V t * ∫ u, ρ u * φ (t + u) := by
        have hIneg : Integrable fun t => -(V t * ∫ u, ρ u * deriv φ (t + u)) := hIψ'.neg
        have hIσ : Integrable fun t => σ * (V t * ∫ u, ρ u * φ (t + u)) := hIψ.const_mul σ
        calc (∫ t, -(V t * ∫ u, ρ u * deriv φ (t + u))
              - σ * (V t * ∫ u, ρ u * φ (t + u)))
            = (∫ t, -(V t * ∫ u, ρ u * deriv φ (t + u)))
              - ∫ t, σ * (V t * ∫ u, ρ u * φ (t + u)) := integral_sub hIneg hIσ
          _ = -(∫ t, V t * ∫ u, ρ u * deriv φ (t + u))
              - σ * ∫ t, V t * ∫ u, ρ u * φ (t + u) := by
              rw [integral_neg, integral_const_mul]

/-- **The transported-test limit.**  As the width shrinks, pairing the profile against the
transported test converges to pairing against the test itself. -/
theorem tendsto_integral_mul_kernelTest {V φ : ℝ → ℝ} {εs : ℕ → ℝ}
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ)))
    (hφ : ContDiff ℝ 1 φ) (hφsupp : HasCompactSupport φ)
    (hpos : ∀ n, 0 < εs n) (hle : ∀ n, εs n ≤ 1)
    (h0 : Filter.Tendsto εs Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ t, V t * ∫ u, suzukiMollifier (εs n) u * φ (t + u))
      Filter.atTop (nhds (∫ t, V t * φ t)) := by
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hφ'cs : HasCompactSupport (deriv φ) := hφsupp.deriv
  obtain ⟨Mφ, hMφ0, hMφ⟩ := exists_abs_le_of_hasCompactSupport hφ'c hφ'cs
  have hmod : ∀ t u : ℝ, |φ (t + u) - φ t| ≤ Mφ * |u| := fun t u =>
    abs_translate_sub_le_of_deriv_bound hφ hMφ t u
  obtain ⟨Aφ, hAφ⟩ := hφsupp.isBounded.subset_closedBall (0 : ℝ)
  have hφz : ∀ w : ℝ, |Aφ| + 1 < |w| → φ w = 0 := by
    intro w hw
    by_contra hne
    have hmem : w ∈ tsupport φ := subset_closure (by exact hne)
    have := hAφ hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have h2 : |w| ≤ |Aφ| := le_trans this (le_abs_self Aφ)
    linarith
  set K : Set ℝ := Icc (-(|Aφ| + 3)) (|Aφ| + 3) with hKdef
  have hVK : IntegrableOn (fun t => |V t|) K := by
    have hloc : LocallyIntegrable V volume := locallyIntegrable_of_sq_integrable hVm hV2
    exact (hloc.integrableOn_isCompact isCompact_Icc).abs
  set CK : ℝ := ∫ t in K, |V t| with hCKdef
  have hCK0 : 0 ≤ CK := integral_nonneg fun t => abs_nonneg _
  -- the difference bound at each width
  have hdiff : ∀ n, |(∫ t, V t * ∫ u, suzukiMollifier (εs n) u * φ (t + u))
      - ∫ t, V t * φ t| ≤ Mφ * εs n * CK := by
    intro n
    set ρ : ℝ → ℝ := suzukiMollifier (εs n) with hρdef
    have hρc : Continuous ρ := (contDiff_suzukiMollifier (εs n)).continuous
    have hρcs : HasCompactSupport ρ := hasCompactSupport_suzukiMollifier (hpos n)
    have hρz : ∀ u : ℝ, εs n < |u| → ρ u = 0 := fun u hu =>
      suzukiMollifier_eq_zero (hpos n) hu
    have hψc : Continuous fun t => ∫ u, ρ u * φ (t + u) :=
      continuous_kernelTest hρc hρcs hφc
    have hψapprox : ∀ t : ℝ, |(∫ u, ρ u * φ (t + u)) - φ t| ≤ Mφ * εs n := by
      intro t
      refine abs_kernelTest_sub_le (hpos n).le hρc hρz
        (suzukiMollifier_nonneg (hpos n)) (integrable_suzukiMollifier (hpos n))
        (integral_suzukiMollifier (hpos n)) hφc ?_ t
      intro t' u hu
      calc |φ (t' + u) - φ t'| ≤ Mφ * |u| := hmod t' u
        _ ≤ Mφ * εs n := mul_le_mul_of_nonneg_left hu hMφ0
    -- the difference vanishes off `K`
    have hdz : ∀ t : ℝ, t ∉ K → (∫ u, ρ u * φ (t + u)) - φ t = 0 := by
      intro t ht
      have htabs : |Aφ| + 2 < |t| := by
        rw [hKdef, mem_Icc, not_and_or] at ht
        rcases ht with ht | ht
        · rw [not_le] at ht
          calc |Aφ| + 2 < -t := by linarith
            _ ≤ |t| := neg_le_abs t
        · rw [not_le] at ht
          calc |Aφ| + 2 < t := by linarith
            _ ≤ |t| := le_abs_self t
      have h1 : (∫ u, ρ u * φ (t + u)) = 0 := by
        refine kernelTest_eq_zero hρz hφz ?_
        have := hle n
        linarith
      have h2 : φ t = 0 := by
        refine hφz t ?_
        linarith
      rw [h1, h2, sub_zero]
    have hIψ : Integrable fun t => V t * ∫ u, ρ u * φ (t + u) := by
      have hψcs : HasCompactSupport fun t => ∫ u, ρ u * φ (t + u) := by
        refine HasCompactSupport.intro
          (isCompact_Icc (a := -(|Aφ| + 3)) (b := |Aφ| + 3)) fun t ht => ?_
        refine kernelTest_eq_zero hρz hφz ?_
        rw [mem_Icc, not_and_or] at ht
        have hεn := hle n
        rcases ht with ht | ht
        · rw [not_le] at ht
          calc |Aφ| + 1 + εs n < -t := by linarith
            _ ≤ |t| := neg_le_abs t
        · rw [not_le] at ht
          calc |Aφ| + 1 + εs n < t := by linarith
            _ ≤ |t| := le_abs_self t
      exact integrable_mul_of_sq_integrable hVm hψc.aestronglyMeasurable hV2
        ((hψc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hψcs))
    have hIφ : Integrable fun t => V t * φ t :=
      integrable_mul_of_sq_integrable hVm hφc.aestronglyMeasurable hV2
        ((hφc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hφsupp))
    have hsub : (∫ t, V t * ∫ u, ρ u * φ (t + u)) - ∫ t, V t * φ t
        = ∫ t, V t * ((∫ u, ρ u * φ (t + u)) - φ t) := by
      rw [← integral_sub hIψ hIφ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show V t * (∫ u, ρ u * φ (t + u)) - V t * φ t
          = V t * ((∫ u, ρ u * φ (t + u)) - φ t)
      ring
    rw [hsub]
    have hzero : ∀ t : ℝ, t ∉ K → V t * ((∫ u, ρ u * φ (t + u)) - φ t) = 0 := by
      intro t ht
      rw [hdz t ht, mul_zero]
    have hrestrict : (∫ t, V t * ((∫ u, ρ u * φ (t + u)) - φ t))
        = ∫ t in K, V t * ((∫ u, ρ u * φ (t + u)) - φ t) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    rw [hrestrict]
    have hbound : ∀ t ∈ K, ‖V t * ((∫ u, ρ u * φ (t + u)) - φ t)‖ ≤ |V t| * (Mφ * εs n) := by
      intro t _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hψapprox t) (abs_nonneg _)
    have hVMK : IntegrableOn (fun t => |V t| * (Mφ * εs n)) K := hVK.mul_const _
    calc |∫ t in K, V t * ((∫ u, ρ u * φ (t + u)) - φ t)|
        ≤ ∫ t in K, |V t| * (Mφ * εs n) := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le hVMK ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
          exact hbound t ht
      _ = Mφ * εs n * CK := by
          rw [integral_mul_const]
          ring
  -- squeeze
  have hlim : Filter.Tendsto (fun n => Mφ * εs n * CK) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => Mφ * εs n) Filter.atTop (nhds (Mφ * 0)) :=
      h0.const_mul Mφ
    have h2 := h1.mul_const CK
    simpa using h2
  have hsqueeze := squeeze_zero_norm (f := fun n =>
      (∫ t, V t * ∫ u, suzukiMollifier (εs n) u * φ (t + u)) - ∫ t, V t * φ t)
    (fun n => by
      rw [Real.norm_eq_abs]
      exact hdiff n) hlim
  have := hsqueeze.add_const (∫ t, V t * φ t)
  simpa using this

/-! ## `Lp` bridging -/

/-- The `L²` inner product of a represented class against any class is the integral pairing of
the representative against the coercion. -/
theorem inner_toLp_left_eq {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (w : Lp ℝ 2 (volume : Measure ℝ)) :
    (inner ℝ (hf.toLp f) w : ℝ) = ∫ x, f x * w x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- An `L²` energy bound is an `Lp` norm bound. -/
theorem norm_toLp_le_of_integral_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) {b : ℝ} (hb : 0 ≤ b)
    (h : (∫ x, f x ^ (2 : ℕ)) ≤ b ^ (2 : ℕ)) : ‖hf.toLp f‖ ≤ b := by
  have hinner : (inner ℝ (hf.toLp f) (hf.toLp f) : ℝ) = ∫ x, f x * f x := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  have hnormsq : ‖hf.toLp f‖ ^ (2 : ℕ) = ∫ x, f x * f x := by
    rw [← real_inner_self_eq_norm_sq, hinner]
  have hsq : (∫ x, f x * f x) = ∫ x, f x ^ (2 : ℕ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f x * f x = f x ^ (2 : ℕ)
    rw [pow_two]
  have h2 : ‖hf.toLp f‖ ^ (2 : ℕ) ≤ b ^ (2 : ℕ) := by
    rw [hnormsq, hsq]
    exact h
  nlinarith [norm_nonneg (hf.toLp f)]

/-! ## The capstone -/

/-- **The weak-domain upgrade** — the coercivity card's `(6)`.  On the coercive budget
`κ_σ + |τ| < 2L₀`, the tested weak equation `(2L + R_σ − τ)U + V = G` with `V, G ∈ L²`, `V`
supported in `[L₀, ∞)`, and `0 ≤ σ < 1` forces the distributional derivative combination
`U = V′ − σV` to be square-integrable: there is `u ∈ L²` with
`∫ u φ = −∫ V φ′ − σ ∫ V φ` for every smooth compactly supported test `φ`.
Equivalently, `V ∈ H¹` with weak derivative `σV + u ∈ L²`. -/
theorem suzukiGamma_weakDomain_upgrade {σ τ L₀ : ℝ} {V G : ℝ → ℝ}
    (heq : SuzukiGammaTestedEquation σ τ V G)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ)))
    (hGmm : Measurable G) (hG2 : Integrable (fun t => G t ^ (2 : ℕ)))
    (hsupp : ∀ t : ℝ, t < L₀ → V t = 0)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hbudget : suzukiGammaShiftKappa σ + |τ| < 2 * L₀) :
    ∃ u : ℝ → ℝ, MemLp u 2 (volume : Measure ℝ) ∧
      ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ t, u t * φ t) = -(∫ t, V t * deriv φ t) - σ * ∫ t, V t * φ t := by
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  -- the budget slack and the shrinking widths
  set slack : ℝ := 2 * L₀ - suzukiGammaShiftKappa σ - |τ| with hslackdef
  have hslack : 0 < slack := by
    rw [hslackdef]
    linarith
  set ε₀ : ℝ := min 1 (slack / 4) with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min one_pos (by positivity)
  have hε₀le1 : ε₀ ≤ 1 := min_le_left _ _
  have hε₀slack : ε₀ ≤ slack / 4 := min_le_right _ _
  set εs : ℕ → ℝ := fun n => ε₀ / (n + 1) with hεsdef
  have hεs_pos : ∀ n, 0 < εs n := by
    intro n
    show 0 < ε₀ / (n + 1)
    positivity
  have hεs_le : ∀ n, εs n ≤ ε₀ := by
    intro n
    show ε₀ / (n + 1) ≤ ε₀
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith [hε₀pos.le, (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hεs_le1 : ∀ n, εs n ≤ 1 := fun n => le_trans (hεs_le n) hε₀le1
  have hεs0 : Filter.Tendsto εs Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h.const_mul ε₀
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    show ε₀ * (1 / ((n : ℝ) + 1)) = ε₀ / ((n : ℝ) + 1)
    ring
  -- the coercive constant
  set c : ℝ := slack / 2 with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    positivity
  have hcle : ∀ n, c ≤ 2 * (L₀ - εs n) - suzukiGammaShiftKappa σ - |τ| := by
    intro n
    have h1 := hεs_le n
    have h2 : 2 * (L₀ - εs n) - suzukiGammaShiftKappa σ - |τ| = slack - 2 * εs n := by
      rw [hslackdef]
      ring
    rw [h2, hcdef]
    linarith [hε₀slack]
  -- the uniformly bounded family in `L²`
  have hmem : ∀ n, MemLp (suzukiMollifiedDeriv σ (εs n) V) 2 (volume : Measure ℝ) := by
    intro n
    exact (memLp_two_iff_integrable_sq
      (continuous_suzukiMollifiedDeriv (hεs_pos n) hVm hV2).aestronglyMeasurable).mpr
      (integrable_sq_suzukiMollifiedDeriv (hεs_pos n) hVmm hV2)
  set M₀ : ℝ := 3 * (∫ t, G t ^ (2 : ℕ)) + (3 + 12 * suzukiDefectMass ^ (2 : ℕ)) * ∫ t, V t ^ (2 : ℕ)
    with hM₀def
  have hM₀0 : 0 ≤ M₀ := by
    have h1 : (0 : ℝ) ≤ ∫ t, G t ^ (2 : ℕ) := integral_nonneg fun t => sq_nonneg _
    have h2 : (0 : ℝ) ≤ ∫ t, V t ^ (2 : ℕ) := integral_nonneg fun t => sq_nonneg _
    rw [hM₀def]
    nlinarith [sq_nonneg suzukiDefectMass]
  set M : ℝ := Real.sqrt M₀ / c with hMdef
  have hM0 : 0 ≤ M := div_nonneg (Real.sqrt_nonneg _) hc.le
  have hnormle : ∀ n, ‖(hmem n).toLp _‖ ≤ M := by
    intro n
    refine norm_toLp_le_of_integral_sq_le (hmem n) hM0 ?_
    have h := suzukiGamma_uniform_energy_bound heq hVmm hV2 hGmm hG2 hsupp hσ0 hσ1
      (hεs_pos n) (hεs_le1 n) hc (hcle n)
    have hM2 : M ^ (2 : ℕ) = M₀ / c ^ (2 : ℕ) := by
      rw [hMdef, div_pow, Real.sq_sqrt hM₀0]
    rw [hM2, le_div_iff₀ (by positivity : (0 : ℝ) < c ^ (2 : ℕ))]
    calc (∫ x, suzukiMollifiedDeriv σ (εs n) V x ^ (2 : ℕ)) * c ^ (2 : ℕ)
        = c ^ (2 : ℕ) * ∫ x, suzukiMollifiedDeriv σ (εs n) V x ^ (2 : ℕ) := by ring
      _ ≤ M₀ := h
  -- the key limit against every smooth compactly supported test
  have hKEY : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Filter.Tendsto (fun n => ∫ x, suzukiMollifiedDeriv σ (εs n) V x * φ x)
        Filter.atTop (nhds (-(∫ t, V t * deriv φ t) - σ * ∫ t, V t * φ t)) := by
    intro φ hφsm hφsupp
    have hφ1 : ContDiff ℝ 1 φ := hφsm.of_le (by exact_mod_cast le_top)
    have hφ'1 : ContDiff ℝ 1 (deriv φ) :=
      (contDiff_infty_iff_deriv.mp hφsm).2.of_le (by exact_mod_cast le_top)
    have hid : ∀ n, (∫ x, suzukiMollifiedDeriv σ (εs n) V x * φ x)
        = -(∫ t, V t * ∫ u, suzukiMollifier (εs n) u * deriv φ (t + u))
          - σ * ∫ t, V t * ∫ u, suzukiMollifier (εs n) u * φ (t + u) := fun n =>
      integral_suzukiMollifiedDeriv_mul_test (hεs_pos n) hVmm hV2 hφ1 hφsupp
    have hlim1 := tendsto_integral_mul_kernelTest hVmm hV2 hφ'1 hφsupp.deriv
      hεs_pos hεs_le1 hεs0
    have hlim2 := tendsto_integral_mul_kernelTest hVmm hV2 hφ1 hφsupp
      hεs_pos hεs_le1 hεs0
    have hcomb := (hlim1.neg).sub (hlim2.const_mul σ)
    exact Filter.Tendsto.congr (fun n => (hid n).symm) hcomb
  -- weak convergence against the dense smooth subspace
  have hconv : ∀ φLp ∈ smoothCompactSubmodule, ∃ l : ℝ,
      Filter.Tendsto (fun n => (inner ℝ ((hmem n).toLp _) φLp : ℝ))
        Filter.atTop (nhds l) := by
    rintro φLp ⟨g, hgae, hgsupp, hgsm⟩
    refine ⟨-(∫ t, V t * deriv g t) - σ * ∫ t, V t * g t, ?_⟩
    have hip : ∀ n, (inner ℝ ((hmem n).toLp _) φLp : ℝ)
        = ∫ x, suzukiMollifiedDeriv σ (εs n) V x * g x := by
      intro n
      rw [inner_toLp_left_eq (hmem n) φLp]
      refine integral_congr_ae ?_
      filter_upwards [hgae] with x hx
      rw [hx]
    exact Filter.Tendsto.congr (fun n => (hip n).symm) (hKEY g hgsm hgsupp)
  obtain ⟨w, hwnorm, hw⟩ := exists_weakLimit_of_bounded (𝕜 := ℝ) hnormle
    dense_smoothCompactSubmodule hconv
  refine ⟨⇑w, Lp.memLp w, ?_⟩
  intro φ hφsm hφsupp
  have hφmem : MemLp φ 2 (volume : Measure ℝ) :=
    hφsm.continuous.memLp_of_hasCompactSupport hφsupp
  have hφin : hφmem.toLp φ ∈ smoothCompactSubmodule :=
    ⟨φ, hφmem.coeFn_toLp, hφsupp, hφsm⟩
  have hlimw := hw (hφmem.toLp φ)
  have hip : ∀ n, (inner ℝ ((hmem n).toLp _) (hφmem.toLp φ) : ℝ)
      = ∫ x, suzukiMollifiedDeriv σ (εs n) V x * φ x := by
    intro n
    rw [inner_toLp_left_eq (hmem n) (hφmem.toLp φ)]
    refine integral_congr_ae ?_
    filter_upwards [hφmem.coeFn_toLp] with x hx
    rw [hx]
  have hlimval : Filter.Tendsto (fun n => (inner ℝ ((hmem n).toLp _) (hφmem.toLp φ) : ℝ))
      Filter.atTop (nhds (-(∫ t, V t * deriv φ t) - σ * ∫ t, V t * φ t)) :=
    Filter.Tendsto.congr (fun n => (hip n).symm) (hKEY φ hφsm hφsupp)
  have huniq := tendsto_nhds_unique hlimw hlimval
  have hwip : (inner ℝ w (hφmem.toLp φ) : ℝ) = ∫ t, w t * φ t := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hφmem.coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  rw [← hwip]
  exact huniq

/-- **`V ∈ H¹`.**  On the coercive budget the profile has a square-integrable weak derivative:
`v′ = σV + u` satisfies `∫ v′ φ = −∫ V φ′` for every smooth compactly supported test. -/
theorem suzukiGamma_profile_H1 {σ τ L₀ : ℝ} {V G : ℝ → ℝ}
    (heq : SuzukiGammaTestedEquation σ τ V G)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ)))
    (hGmm : Measurable G) (hG2 : Integrable (fun t => G t ^ (2 : ℕ)))
    (hsupp : ∀ t : ℝ, t < L₀ → V t = 0)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hbudget : suzukiGammaShiftKappa σ + |τ| < 2 * L₀) :
    ∃ v' : ℝ → ℝ, MemLp v' 2 (volume : Measure ℝ) ∧
      ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ t, v' t * φ t) = -(∫ t, V t * deriv φ t) := by
  obtain ⟨u, humem, hu⟩ := suzukiGamma_weakDomain_upgrade heq hVmm hV2 hGmm hG2 hsupp
    hσ0 hσ1 hbudget
  have hVmem : MemLp V 2 (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq hVmm.aestronglyMeasurable).mpr hV2
  refine ⟨fun t => σ * V t + u t, ?_, ?_⟩
  · have h1 : MemLp (fun t => σ * V t) 2 (volume : Measure ℝ) := hVmem.const_mul σ
    exact h1.add humem
  · intro φ hφsm hφsupp
    have hφc : Continuous φ := hφsm.continuous
    have hφ2 : Integrable (fun t => φ t ^ (2 : ℕ)) :=
      (hφc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hφsupp)
    have hu2 : Integrable (fun t => u t ^ (2 : ℕ)) :=
      (memLp_two_iff_integrable_sq humem.aestronglyMeasurable).mp humem
    have hIV : Integrable (fun t => σ * (V t * φ t)) :=
      (integrable_mul_of_sq_integrable hVmm.aestronglyMeasurable
        hφc.aestronglyMeasurable hV2 hφ2).const_mul σ
    have hIu : Integrable (fun t => u t * φ t) :=
      integrable_mul_of_sq_integrable humem.aestronglyMeasurable
        hφc.aestronglyMeasurable hu2 hφ2
    calc (∫ t, (σ * V t + u t) * φ t)
        = ∫ t, σ * (V t * φ t) + u t * φ t := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show (σ * V t + u t) * φ t = σ * (V t * φ t) + u t * φ t
          ring
      _ = (∫ t, σ * (V t * φ t)) + ∫ t, u t * φ t := integral_add hIV hIu
      _ = σ * (∫ t, V t * φ t) + ∫ t, u t * φ t := by rw [integral_const_mul]
      _ = -(∫ t, V t * deriv φ t) := by
          rw [hu φ hφsm hφsupp]
          ring

end GaloisForLFunctions.RHTower
