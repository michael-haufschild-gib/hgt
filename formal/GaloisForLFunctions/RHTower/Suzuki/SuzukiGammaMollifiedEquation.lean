import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedGammaForm
import GaloisForLFunctions.HTGeometry.CompactKernelL2Convolution
import GaloisForLFunctions.HTGeometry.GammaJumpL2Bound
import GaloisForLFunctions.HTGeometry.MollifierTestPairing
import GaloisForLFunctions.HTGeometry.ScaledMollifierMoments
import GaloisForLFunctions.HTGeometry.BumpMollifierFamily

/-!
# The mollified Suzuki equation

The Suzuki weak equation `(2L + R_σ − τ)U + V = G` with `U = V′ − σV` a distribution is taken in
its tested form: every pairing is moved onto a smooth compactly supported test function — the
derivative by one sign, the Gamma jump by its transpose `R_σᵀ = R_{−σ}`, multiplication by `2L`
and the seam scalar `τ` verbatim.  Testing against the translated scaled mollifier `ρ_ε(x − ·)`
and running the kernel algebra produces the mollified equation *pointwise*:

`2x U_ε(x) − 2W_ε(x) + (R_σ U_ε)(x) − τ U_ε(x) + V_ε(x) = G_ε(x)`,

where `U_ε = (ρ_ε′ − σρ_ε) ⋆ V` is the mollified weak derivative, `V_ε, G_ε` the mollified data,
and `W_ε = (k_ε′ − σk_ε) ⋆ V` the position-commutator defect, `k_ε(u) = u ρ_ε(u)`.

The position commutator and the transfer of the derivative onto the kernel are pointwise kernel
algebra.  The only analytic step is one Fubini exchange for the Gamma jump, whose scale sections
are controlled by the `L²` majorant of the second difference.
-/

open MeasureTheory Set GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace GaloisForLFunctions.RHTower

/-! ## The scaled smooth mollifier family -/

/-- The smooth unit-mass base profile of width one. -/
noncomputable def suzukiBaseMollifier : ℝ → ℝ := bumpMollifier one_pos

theorem contDiff_suzukiBaseMollifier : ContDiff ℝ ∞ suzukiBaseMollifier := by
  unfold suzukiBaseMollifier bumpMollifier
  exact (widthBump one_pos).contDiff_normed (n := ⊤)

theorem suzukiBaseMollifier_nonneg (t : ℝ) : 0 ≤ suzukiBaseMollifier t :=
  nonneg_bumpMollifier one_pos t

theorem suzukiBaseMollifier_eq_zero {t : ℝ} (ht : 1 < |t|) : suzukiBaseMollifier t = 0 :=
  bumpMollifier_eq_zero one_pos ht

theorem integral_suzukiBaseMollifier : (∫ t, suzukiBaseMollifier t) = 1 :=
  integral_bumpMollifier one_pos

/-- The width-`ε` member of the family. -/
noncomputable def suzukiMollifier (ε : ℝ) : ℝ → ℝ := scaledMollifier suzukiBaseMollifier ε

theorem suzukiMollifier_def (ε t : ℝ) :
    suzukiMollifier ε t = ε⁻¹ * suzukiBaseMollifier (t / ε) := rfl

theorem contDiff_suzukiMollifier (ε : ℝ) : ContDiff ℝ ∞ (suzukiMollifier ε) := by
  have h1 : ContDiff ℝ ∞ fun t : ℝ => suzukiBaseMollifier (t / ε) :=
    contDiff_suzukiBaseMollifier.comp (contDiff_id.div_const ε)
  exact contDiff_const.mul h1

theorem suzukiMollifier_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ suzukiMollifier ε t :=
  mul_nonneg (inv_pos.mpr hε).le (suzukiBaseMollifier_nonneg _)

theorem suzukiMollifier_eq_zero {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : ε < |t|) :
    suzukiMollifier ε t = 0 := by
  rw [suzukiMollifier_def, suzukiBaseMollifier_eq_zero, mul_zero]
  rw [abs_div, abs_of_pos hε, lt_div_iff₀ hε, one_mul]
  exact ht

theorem hasCompactSupport_suzukiMollifier {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (suzukiMollifier ε) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun t ht => ?_
  refine suzukiMollifier_eq_zero hε ?_
  rw [mem_Icc, not_and_or] at ht
  rcases ht with ht | ht
  · rw [not_le] at ht
    exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
  · rw [not_le] at ht
    exact lt_of_lt_of_le ht (le_abs_self t)

theorem integral_suzukiMollifier {ε : ℝ} (hε : 0 < ε) : (∫ t, suzukiMollifier ε t) = 1 := by
  rw [suzukiMollifier, integral_scaledMollifier hε, integral_suzukiBaseMollifier]

theorem integrable_suzukiMollifier {ε : ℝ} (hε : 0 < ε) : Integrable (suzukiMollifier ε) :=
  ((contDiff_suzukiMollifier ε).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_suzukiMollifier hε)

theorem hasDerivAt_suzukiMollifier (ε : ℝ) (t : ℝ) :
    HasDerivAt (suzukiMollifier ε) (deriv (suzukiMollifier ε) t) t :=
  (((contDiff_suzukiMollifier ε).differentiable (by simp)) t).hasDerivAt

theorem contDiff_deriv_suzukiMollifier (ε : ℝ) :
    ContDiff ℝ ∞ (deriv (suzukiMollifier ε)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_suzukiMollifier ε)).2

theorem hasCompactSupport_deriv_suzukiMollifier {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (deriv (suzukiMollifier ε)) :=
  (hasCompactSupport_suzukiMollifier hε).deriv

theorem tsupport_suzukiMollifier_subset {ε : ℝ} (hε : 0 < ε) :
    tsupport (suzukiMollifier ε) ⊆ Icc (-ε) ε := by
  refine closure_minimal ?_ isClosed_Icc
  intro u hu
  by_contra hout
  rw [mem_Icc, not_and_or] at hout
  refine hu ?_
  refine suzukiMollifier_eq_zero hε ?_
  rcases hout with h | h
  · rw [not_le] at h
    exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
  · rw [not_le] at h
    exact lt_of_lt_of_le h (le_abs_self u)

theorem deriv_suzukiMollifier_eq_zero {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : ε < |t|) :
    deriv (suzukiMollifier ε) t = 0 := by
  refine deriv_eq_zero_of_notMem_tsupport (fun u => hasDerivAt_suzukiMollifier ε u) ?_
  intro hmem
  have hmem' := tsupport_suzukiMollifier_subset hε hmem
  rw [mem_Icc] at hmem'
  have : |t| ≤ ε := abs_le.mpr hmem'
  linarith

/-! ## Two-point Lipschitz bound from a derivative bound -/

theorem abs_sub_le_of_deriv_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : ContDiff ℝ 1 f) (hM : ∀ x, |deriv f x| ≤ M) (u v : ℝ) :
    |f u - f v| ≤ M * |u - v| := by
  have hderiv : ∀ z ∈ (univ : Set ℝ),
      HasDerivWithinAt f (deriv f z) univ z := fun z _ =>
    ((hf.differentiable one_ne_zero) z).hasDerivAt.hasDerivWithinAt
  have hbound : ∀ z ∈ (univ : Set ℝ), ‖deriv f z‖ ≤ M := fun z _ => by
    rw [Real.norm_eq_abs]
    exact hM z
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound convex_univ
    (mem_univ v) (mem_univ u)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-! ## The tested weak equation -/

/-- **The tested form of the Suzuki weak equation** `(2L + R_σ − τ)U + V = G`,
`U = V′ − σV` in distributions.  Every pairing is moved onto the test function: the derivative
by one sign, multiplication by `2L` verbatim, the Gamma jump by its transpose `R_σᵀ = R_{−σ}`,
the seam scalar `τ` verbatim. -/
def SuzukiGammaTestedEquation (σ τ : ℝ) (V G : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    2 * (-(∫ t, V t * (φ t + t * deriv φ t)) - σ * ∫ t, V t * (t * φ t))
      + (-(∫ t, V t * shiftedGammaJump (-σ) (deriv φ) t)
          - σ * ∫ t, V t * shiftedGammaJump (-σ) φ t)
      - τ * (-(∫ t, V t * deriv φ t) - σ * ∫ t, V t * φ t)
      + (∫ t, V t * φ t)
      = ∫ t, G t * φ t

/-! ## Transposing the jump through the translated test -/

/-- Transposing the jump through a reflected translate: `R_{−σ}` on the test side is `R_σ` on the
kernel side, read at the reflected point. -/
theorem shiftedGammaJump_neg_comp_sub (σ : ℝ) (ρ : ℝ → ℝ) (x t : ℝ) :
    shiftedGammaJump (-σ) (fun u => ρ (x - u)) t = shiftedGammaJump σ ρ (x - t) := by
  unfold shiftedGammaJump
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show shiftedSecondDifference (-σ) (fun u => ρ (x - u)) t s * gammaTransportKernel s
      = shiftedSecondDifference σ ρ (x - t) s * gammaTransportKernel s
  congr 1
  unfold shiftedSecondDifference
  show 2 * ρ (x - t) - Real.exp (-(-σ * s)) * ρ (x - (t + s))
        - Real.exp (-σ * s) * ρ (x - (t - s))
      = 2 * ρ (x - t) - Real.exp (-(σ * s)) * ρ (x - t + s)
        - Real.exp (σ * s) * ρ (x - t - s)
  rw [show x - (t + s) = x - t - s from by ring, show x - (t - s) = x - t + s from by ring,
    show -(-σ * s) = σ * s from by ring, show -σ * s = -(σ * s) from by ring]
  ring

/-- The jump of a negated profile is the negated jump. -/
theorem shiftedGammaJump_neg_profile (σ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) :
    shiftedGammaJump σ (fun u => -ρ u) t = -shiftedGammaJump σ ρ t := by
  unfold shiftedGammaJump
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show shiftedSecondDifference σ (fun u => -ρ u) t s * gammaTransportKernel s
      = -(shiftedSecondDifference σ ρ t s * gammaTransportKernel s)
  unfold shiftedSecondDifference
  ring

/-- The jump is linear across a profile combination `g₁ − c·g₂`, wherever both scale integrands
are integrable. -/
theorem shiftedGammaJump_sub_smul {σ c : ℝ} {g₁ g₂ : ℝ → ℝ} {y : ℝ}
    (h1 : IntegrableOn (fun s => shiftedSecondDifference σ g₁ y s * gammaTransportKernel s)
      (Ioi 0))
    (h2 : IntegrableOn (fun s => shiftedSecondDifference σ g₂ y s * gammaTransportKernel s)
      (Ioi 0)) :
    shiftedGammaJump σ (fun u => g₁ u - c * g₂ u) y
      = shiftedGammaJump σ g₁ y - c * shiftedGammaJump σ g₂ y := by
  unfold shiftedGammaJump
  rw [← integral_const_mul, ← integral_sub h1 (h2.const_mul c)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show shiftedSecondDifference σ (fun u => g₁ u - c * g₂ u) y s * gammaTransportKernel s
      = shiftedSecondDifference σ g₁ y s * gammaTransportKernel s
        - c * (shiftedSecondDifference σ g₂ y s * gammaTransportKernel s)
  unfold shiftedSecondDifference
  ring

/-- The second difference of a compactly supported kernel vanishes beyond the support widened by
the scale. -/
theorem shiftedSecondDifference_eq_zero {g : ℝ → ℝ} {R : ℝ}
    (hsupp : ∀ u : ℝ, R < |u| → g u = 0) {σ y s : ℝ} (hy : R + |s| < |y|) :
    shiftedSecondDifference σ g y s = 0 := by
  have habs : (0 : ℝ) ≤ |s| := abs_nonneg s
  have h0 : g y = 0 := hsupp y (by linarith)
  have h1 : g (y + s) = 0 := by
    refine hsupp _ ?_
    have h2 : |y| ≤ |y + s| + |s| := by
      calc |y| = |y + s + -s| := by ring_nf
        _ ≤ |y + s| + |-s| := abs_add_le _ _
        _ = |y + s| + |s| := by rw [abs_neg]
    linarith
  have h2 : g (y - s) = 0 := by
    refine hsupp _ ?_
    have h3 : |y| ≤ |y - s| + |s| := by
      calc |y| = |y - s + s| := by ring_nf
        _ ≤ |y - s| + |s| := abs_add_le _ _
    linarith
  unfold shiftedSecondDifference
  rw [h0, h1, h2]
  ring

/-! ## The jump Fubini -/

/-- **The Gamma-jump exchange.**  Pairing the profile against the jump of a compactly supported
Lipschitz kernel read at reflected points is the jump of the convolution:
`∫ V(t) (R_σ g)(x−t) dt = (R_σ (g ⋆ V))(x)`.  One Fubini, with the scale sections controlled by
the `L²` majorant of the second difference. -/
theorem integral_mul_shiftedGammaJump_comp_sub {g V : ℝ → ℝ} {K R σ : ℝ}
    (hgc : Continuous g)
    (hgK : ∀ u v : ℝ, |g u - g v| ≤ K * |u - v|)
    (hgsupp : ∀ u : ℝ, R < |u| → g u = 0) (hR : 0 ≤ R)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ)))
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (x : ℝ) :
    (∫ t, V t * shiftedGammaJump σ g (x - t))
      = shiftedGammaJump σ (lineConvolution g V) x := by
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun u hu => ?_
    refine hgsupp u ?_
    rw [mem_Icc, not_and_or] at hu
    rcases hu with hu | hu
    · rw [not_le] at hu
      exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
    · rw [not_le] at hu
      exact lt_of_lt_of_le hu (le_abs_self u)
  have hg2 : Integrable (fun u => g u ^ (2 : ℕ)) :=
    (hgc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hgcs)
  have hgEnn : (0 : ℝ) ≤ ∫ u, g u ^ (2 : ℕ) := integral_nonneg fun u => sq_nonneg _
  -- the translate modulus and energy constants
  set C₁ : ℝ := Real.sqrt (K ^ (2 : ℕ) * (2 * R + 1)) + 1 with hC₁def
  set C₂ : ℝ := Real.sqrt (∫ u, g u ^ (2 : ℕ)) + 1 with hC₂def
  have hC₁ : 0 < C₁ := by
    rw [hC₁def]
    positivity
  have hC₂ : 0 < C₂ := by
    rw [hC₂def]
    positivity
  have htrans : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (∫ u, (g (u + s) - g u) ^ (2 : ℕ)) ≤ (C₁ * s) ^ (2 : ℕ) := by
    intro s hs0 hs1
    have h := integral_sq_translate_sub_le_of_lipschitz hgK hgsupp hR hs0 hs1
    have hbase : (0 : ℝ) ≤ K ^ (2 : ℕ) * (2 * R + 1) := by positivity
    have hsq : K ^ (2 : ℕ) * (2 * R + 1) ≤ C₁ ^ (2 : ℕ) := by
      rw [hC₁def]
      nlinarith [Real.sq_sqrt hbase, Real.sqrt_nonneg (K ^ (2 : ℕ) * (2 * R + 1))]
    calc (∫ u, (g (u + s) - g u) ^ (2 : ℕ)) ≤ K ^ (2 : ℕ) * (2 * R + 1) * s ^ (2 : ℕ) := h
      _ ≤ C₁ ^ (2 : ℕ) * s ^ (2 : ℕ) := by nlinarith [sq_nonneg s]
      _ = (C₁ * s) ^ (2 : ℕ) := by ring
  have hE : (∫ u, g u ^ (2 : ℕ)) ≤ C₂ ^ (2 : ℕ) := by
    rw [hC₂def]
    nlinarith [Real.sq_sqrt hgEnn, Real.sqrt_nonneg (∫ u, g u ^ (2 : ℕ))]
  -- the joint integrand
  set μs : Measure ℝ := volume.restrict (Ioi 0) with hμs
  set H : ℝ × ℝ → ℝ := fun p =>
    V p.1 * (shiftedSecondDifference σ g (x - p.1) p.2 * gammaTransportKernel p.2) with hH
  have hDm := measurable_uncurry_shiftedSecondDifference σ hgc.measurable
  have hHm : AEStronglyMeasurable H ((volume : Measure ℝ).prod μs) := by
    refine Measurable.aestronglyMeasurable ?_
    have hcomp : Measurable fun p : ℝ × ℝ => shiftedSecondDifference σ g (x - p.1) p.2 :=
      hDm.comp ((measurable_const.sub measurable_fst).prodMk measurable_snd)
    exact (hVmm.comp measurable_fst).mul
      (hcomp.mul (measurable_gammaTransportKernel.comp measurable_snd))
  -- section integrability in the base point
  have hDslice : ∀ s : ℝ, Continuous fun t => shiftedSecondDifference σ g (x - t) s := by
    intro s
    unfold shiftedSecondDifference
    have h1 : Continuous fun t : ℝ => g (x - t) :=
      hgc.comp (continuous_const.sub continuous_id)
    have h2 : Continuous fun t : ℝ => g (x - t + s) :=
      hgc.comp ((continuous_const.sub continuous_id).add continuous_const)
    have h3 : Continuous fun t : ℝ => g (x - t - s) :=
      hgc.comp ((continuous_const.sub continuous_id).sub continuous_const)
    exact ((continuous_const.mul h1).sub (continuous_const.mul h2)).sub
      (continuous_const.mul h3)
  have hDslice_supp : ∀ s : ℝ,
      HasCompactSupport fun t => shiftedSecondDifference σ g (x - t) s := by
    intro s
    refine HasCompactSupport.intro
      (isCompact_Icc (a := x - (R + |s|) - 1) (b := x + (R + |s|) + 1)) fun t ht => ?_
    refine shiftedSecondDifference_eq_zero hgsupp ?_
    rw [mem_Icc, not_and_or] at ht
    rcases ht with ht | ht
    · rw [not_le] at ht
      have : R + |s| + 1 < x - t := by linarith
      calc R + |s| < x - t := by linarith
        _ ≤ |x - t| := le_abs_self _
    · rw [not_le] at ht
      have : R + |s| + 1 < t - x := by linarith
      calc R + |s| < t - x := by linarith
        _ = -(x - t) := by ring
        _ ≤ |x - t| := neg_le_abs _
  have hslice : ∀ s : ℝ, Integrable fun t => H (t, s) := by
    intro s
    have hker : Integrable fun t =>
        V t * shiftedSecondDifference σ g (x - t) s :=
      integrable_mul_of_sq_integrable hVm (hDslice s).aestronglyMeasurable hV2
        (((hDslice s).pow 2).integrable_of_hasCompactSupport
          (hasCompactSupport_sq (hDslice_supp s)))
    have := hker.mul_const (gammaTransportKernel s)
    refine this.congr ?_
    filter_upwards with t
    show V t * shiftedSecondDifference σ g (x - t) s * gammaTransportKernel s = H (t, s)
    rw [hH]
    ring
  -- the scale-section mass bound
  have hCV : (0 : ℝ) ≤ ∫ t, V t ^ (2 : ℕ) := integral_nonneg fun t => sq_nonneg _
  set CV : ℝ := Real.sqrt (∫ t, V t ^ (2 : ℕ)) with hCVdef
  have hsection : ∀ s ∈ Ioi (0 : ℝ), (∫ t, ‖H (t, s)‖)
      ≤ CV * gammaJumpScaleWeight C₁ C₂ σ s := by
    intro s hs
    have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
    have habs : (∫ t, ‖H (t, s)‖)
        = (∫ t, |V t * shiftedSecondDifference σ g (x - t) s|) * gammaTransportKernel s := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show ‖H (t, s)‖ = |V t * shiftedSecondDifference σ g (x - t) s| * gammaTransportKernel s
      rw [hH, Real.norm_eq_abs]
      show |V t * (shiftedSecondDifference σ g (x - t) s * gammaTransportKernel s)|
          = |V t * shiftedSecondDifference σ g (x - t) s| * gammaTransportKernel s
      simp only [abs_mul, abs_of_pos hkpos]
      ring
    have hCS : (∫ t, |V t * shiftedSecondDifference σ g (x - t) s|)
        ≤ CV * gammaJumpL2Majorant C₁ C₂ σ s := by
      have hVabsm : AEStronglyMeasurable (fun t => |V t|) volume :=
        (continuous_abs.measurable.comp hVmm).aestronglyMeasurable
      have hDabsm : AEStronglyMeasurable
          (fun t => |shiftedSecondDifference σ g (x - t) s|) volume :=
        ((hDslice s).abs).aestronglyMeasurable
      have hVabs2 : Integrable (fun t => |V t| ^ (2 : ℕ)) := by
        refine hV2.congr ?_
        filter_upwards with t
        show V t ^ (2 : ℕ) = |V t| ^ (2 : ℕ)
        rw [sq_abs]
      have hDabs2 : Integrable (fun t => |shiftedSecondDifference σ g (x - t) s| ^ (2 : ℕ)) := by
        refine (((hDslice s).pow 2).integrable_of_hasCompactSupport
          (hasCompactSupport_sq (hDslice_supp s))).congr ?_
        filter_upwards with t
        show shiftedSecondDifference σ g (x - t) s ^ (2 : ℕ)
            = |shiftedSecondDifference σ g (x - t) s| ^ (2 : ℕ)
        rw [sq_abs]
      have hcs := sq_integral_mul_le (μ := (volume : Measure ℝ)) hVabsm hDabsm hVabs2 hDabs2
      have heqabs : (∫ t, |V t| * |shiftedSecondDifference σ g (x - t) s|)
          = ∫ t, |V t * shiftedSecondDifference σ g (x - t) s| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show |V t| * |shiftedSecondDifference σ g (x - t) s|
            = |V t * shiftedSecondDifference σ g (x - t) s|
        rw [abs_mul]
      have heqV : (∫ t, |V t| ^ (2 : ℕ)) = ∫ t, V t ^ (2 : ℕ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show |V t| ^ (2 : ℕ) = V t ^ (2 : ℕ)
        rw [sq_abs]
      have heqD : (∫ t, |shiftedSecondDifference σ g (x - t) s| ^ (2 : ℕ))
          = ∫ y, shiftedSecondDifference σ g y s ^ (2 : ℕ) := by
        have h1 : (∫ t, |shiftedSecondDifference σ g (x - t) s| ^ (2 : ℕ))
            = ∫ t, shiftedSecondDifference σ g (x - t) s ^ (2 : ℕ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show |shiftedSecondDifference σ g (x - t) s| ^ (2 : ℕ)
              = shiftedSecondDifference σ g (x - t) s ^ (2 : ℕ)
          rw [sq_abs]
        rw [h1]
        exact integral_sub_left_eq_self (fun y => shiftedSecondDifference σ g y s ^ (2 : ℕ)) volume x
      rw [heqabs, heqV, heqD] at hcs
      have hDbound := integral_sq_shiftedSecondDifference_le
        hgc.aestronglyMeasurable hg2 htrans hE hC₁.le hC₂.le hσ0 hs
      have hnn : (0 : ℝ) ≤ ∫ t, |V t * shiftedSecondDifference σ g (x - t) s| :=
        integral_nonneg fun t => abs_nonneg _
      have hν0 : 0 < gammaJumpL2Majorant C₁ C₂ σ s :=
        gammaJumpL2Majorant_pos hC₁ hC₂ hσ0 hs
      have hfinal : (∫ t, |V t * shiftedSecondDifference σ g (x - t) s|) ^ (2 : ℕ)
          ≤ (CV * gammaJumpL2Majorant C₁ C₂ σ s) ^ (2 : ℕ) := by
        calc (∫ t, |V t * shiftedSecondDifference σ g (x - t) s|) ^ (2 : ℕ)
            ≤ (∫ t, V t ^ (2 : ℕ)) * ∫ y, shiftedSecondDifference σ g y s ^ (2 : ℕ) := hcs
          _ ≤ (∫ t, V t ^ (2 : ℕ)) * gammaJumpL2Majorant C₁ C₂ σ s ^ (2 : ℕ) :=
              mul_le_mul_of_nonneg_left hDbound hCV
          _ = (CV * gammaJumpL2Majorant C₁ C₂ σ s) ^ (2 : ℕ) := by
              rw [hCVdef, mul_pow, Real.sq_sqrt hCV]
      have hb : (0 : ℝ) ≤ CV * gammaJumpL2Majorant C₁ C₂ σ s := by
        rw [hCVdef]
        positivity
      calc (∫ t, |V t * shiftedSecondDifference σ g (x - t) s|)
          = Real.sqrt ((∫ t, |V t * shiftedSecondDifference σ g (x - t) s|) ^ (2 : ℕ)) :=
            (Real.sqrt_sq hnn).symm
        _ ≤ Real.sqrt ((CV * gammaJumpL2Majorant C₁ C₂ σ s) ^ (2 : ℕ)) :=
            Real.sqrt_le_sqrt hfinal
        _ = CV * gammaJumpL2Majorant C₁ C₂ σ s := Real.sqrt_sq hb
    calc (∫ t, ‖H (t, s)‖)
        = (∫ t, |V t * shiftedSecondDifference σ g (x - t) s|) * gammaTransportKernel s :=
          habs
      _ ≤ (CV * gammaJumpL2Majorant C₁ C₂ σ s) * gammaTransportKernel s :=
          mul_le_mul_of_nonneg_right hCS hkpos.le
      _ = CV * gammaJumpScaleWeight C₁ C₂ σ s := by
          unfold gammaJumpScaleWeight
          ring
  -- joint integrability
  have hHint : Integrable H ((volume : Measure ℝ).prod μs) := by
    rw [integrable_prod_iff' hHm]
    constructor
    · filter_upwards with s
      exact hslice s
    · have hmaj : Integrable (fun s => CV * gammaJumpScaleWeight C₁ C₂ σ s) μs := by
        rw [hμs]
        exact (integrableOn_gammaJumpScaleWeight hC₁.le hC₂.le hσ0 hσ1).const_mul CV
      have haesm : AEStronglyMeasurable (fun s => ∫ t, ‖H (t, s)‖) μs := by
        have hswapm : AEStronglyMeasurable (fun q : ℝ × ℝ => ‖H (q.2, q.1)‖)
            (μs.prod volume) :=
          hHm.norm.comp_measurePreserving Measure.measurePreserving_swap
        exact hswapm.integral_prod_right'
      refine Integrable.mono' hmaj haesm ?_
      rw [hμs]
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact hsection s hs
  -- the exchange
  have hswap := integral_integral_swap
    (f := fun t s => H (t, s)) (μ := (volume : Measure ℝ)) (ν := μs)
    (by
      refine hHint.congr ?_
      filter_upwards with p
      rfl)
  -- identify the two sides
  have hLHS : (∫ t, V t * shiftedGammaJump σ g (x - t)) = ∫ t, ∫ s, H (t, s) ∂μs := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show V t * shiftedGammaJump σ g (x - t) = ∫ s, H (t, s) ∂μs
    unfold shiftedGammaJump
    rw [hμs, ← integral_const_mul]
  have hflipmul : ∀ (h : ℝ → ℝ), Continuous h → HasCompactSupport h → ∀ z : ℝ,
      (∫ t, V t * h (z - t)) = lineConvolution h V z := by
    intro h hc hcs z
    rw [lineConvolution_flip]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show V t * h (z - t) = h (z - t) * V t
    ring
  have hRHS : (∫ s, ∫ t, H (t, s) ∂volume ∂μs)
      = shiftedGammaJump σ (lineConvolution g V) x := by
    unfold shiftedGammaJump
    rw [hμs]
    refine integral_congr_ae ?_
    filter_upwards with s
    have hsplit : (∫ t, H (t, s))
        = (∫ t, V t * shiftedSecondDifference σ g (x - t) s) * gammaTransportKernel s := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show H (t, s) = V t * shiftedSecondDifference σ g (x - t) s * gammaTransportKernel s
      rw [hH]
      ring
    have ha : Real.exp (-(σ * s)) = Real.exp (-(σ * s)) := rfl
    have hint1 : Integrable fun t => V t * g (x - t) :=
      integrable_mul_kernel_comp_sub hgc.aestronglyMeasurable hg2 hVm hV2 x
    have hint2 : Integrable fun t => V t * g (x + s - t) :=
      integrable_mul_kernel_comp_sub hgc.aestronglyMeasurable hg2 hVm hV2 (x + s)
    have hint3 : Integrable fun t => V t * g (x - s - t) :=
      integrable_mul_kernel_comp_sub hgc.aestronglyMeasurable hg2 hVm hV2 (x - s)
    have hinner : (∫ t, V t * shiftedSecondDifference σ g (x - t) s)
        = shiftedSecondDifference σ (lineConvolution g V) x s := by
      have hexpand : (fun t => V t * shiftedSecondDifference σ g (x - t) s)
          = fun t => 2 * (V t * g (x - t))
            - Real.exp (-(σ * s)) * (V t * g (x + s - t))
            - Real.exp (σ * s) * (V t * g (x - s - t)) := by
        funext t
        unfold shiftedSecondDifference
        have e1 : x - t + s = x + s - t := by ring
        have e2 : x - t - s = x - s - t := by ring
        rw [e1, e2]
        ring
      rw [hexpand]
      have hi1 : Integrable fun t => 2 * (V t * g (x - t)) := hint1.const_mul 2
      have hi2 : Integrable fun t => Real.exp (-(σ * s)) * (V t * g (x + s - t)) :=
        hint2.const_mul _
      have hi3 : Integrable fun t => Real.exp (σ * s) * (V t * g (x - s - t)) :=
        hint3.const_mul _
      have hi12 : Integrable fun t => 2 * (V t * g (x - t))
          - Real.exp (-(σ * s)) * (V t * g (x + s - t)) := hi1.sub hi2
      calc (∫ t, 2 * (V t * g (x - t)) - Real.exp (-(σ * s)) * (V t * g (x + s - t))
              - Real.exp (σ * s) * (V t * g (x - s - t)))
          = (∫ t, 2 * (V t * g (x - t)) - Real.exp (-(σ * s)) * (V t * g (x + s - t)))
              - ∫ t, Real.exp (σ * s) * (V t * g (x - s - t)) := integral_sub hi12 hi3
        _ = ((∫ t, 2 * (V t * g (x - t)))
              - ∫ t, Real.exp (-(σ * s)) * (V t * g (x + s - t)))
              - ∫ t, Real.exp (σ * s) * (V t * g (x - s - t)) := by
            rw [integral_sub hi1 hi2]
        _ = 2 * (∫ t, V t * g (x - t))
              - Real.exp (-(σ * s)) * (∫ t, V t * g (x + s - t))
              - Real.exp (σ * s) * ∫ t, V t * g (x - s - t) := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
        _ = shiftedSecondDifference σ (lineConvolution g V) x s := by
            rw [hflipmul g hgc hgcs x, hflipmul g hgc hgcs (x + s),
              hflipmul g hgc hgcs (x - s)]
            unfold shiftedSecondDifference
            ring
    rw [hsplit, hinner]
  rw [hLHS, hswap, hRHS]

/-! ## The mollified objects -/

/-- The mollified weak derivative `U_ε = (ρ_ε′ − σρ_ε) ⋆ V`. -/
noncomputable def suzukiMollifiedDeriv (σ ε : ℝ) (V : ℝ → ℝ) : ℝ → ℝ :=
  lineConvolution (fun u => deriv (suzukiMollifier ε) u - σ * suzukiMollifier ε u) V

/-- The position-commutator defect `W_ε = (k_ε′ − σk_ε) ⋆ V`, `k_ε(u) = u ρ_ε(u)`. -/
noncomputable def suzukiMollifiedDefect (σ ε : ℝ) (V : ℝ → ℝ) : ℝ → ℝ :=
  lineConvolution (fun u => deriv (firstMomentKernel (suzukiMollifier ε)) u
    - σ * firstMomentKernel (suzukiMollifier ε) u) V

/-- The convolution is linear across a kernel combination `g₁ − c·g₂`. -/
theorem lineConvolution_kernel_sub_mul {g₁ g₂ V : ℝ → ℝ} {c y : ℝ}
    (h1 : Integrable fun t => g₁ t * V (y - t))
    (h2 : Integrable fun t => g₂ t * V (y - t)) :
    lineConvolution (fun u => g₁ u - c * g₂ u) V y
      = lineConvolution g₁ V y - c * lineConvolution g₂ V y := by
  unfold lineConvolution
  calc (∫ t, (g₁ t - c * g₂ t) * V (y - t))
      = ∫ t, g₁ t * V (y - t) - c * (g₂ t * V (y - t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show (g₁ t - c * g₂ t) * V (y - t)
            = g₁ t * V (y - t) - c * (g₂ t * V (y - t))
        ring
    _ = (∫ t, g₁ t * V (y - t)) - ∫ t, c * (g₂ t * V (y - t)) :=
        integral_sub h1 (h2.const_mul c)
    _ = (∫ t, g₁ t * V (y - t)) - c * ∫ t, g₂ t * V (y - t) := by
        rw [integral_const_mul]

/-! ## The pointwise mollified equation -/

/-- **The mollified equation, pointwise.**  Testing the weak equation against the translated
scaled mollifier and running the kernel algebra gives, at every base point `x`:

`2x U_ε(x) − 2W_ε(x) + (R_σ U_ε)(x) − τ U_ε(x) + V_ε(x) = G_ε(x)`. -/
theorem suzukiGamma_mollified_equation {σ τ ε : ℝ} {V G : ℝ → ℝ}
    (heq : SuzukiGammaTestedEquation σ τ V G)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ (2 : ℕ)))
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hε : 0 < ε) (x : ℝ) :
    2 * x * suzukiMollifiedDeriv σ ε V x - 2 * suzukiMollifiedDefect σ ε V x
      + shiftedGammaJump σ (suzukiMollifiedDeriv σ ε V) x
      - τ * suzukiMollifiedDeriv σ ε V x
      + lineConvolution (suzukiMollifier ε) V x
      = lineConvolution (suzukiMollifier ε) G x := by
  set ρ : ℝ → ℝ := suzukiMollifier ε with hρdef
  set ρd : ℝ → ℝ := deriv (suzukiMollifier ε) with hρddef
  set kk : ℝ → ℝ := firstMomentKernel (suzukiMollifier ε) with hkkdef
  set kkd : ℝ → ℝ := deriv (firstMomentKernel (suzukiMollifier ε)) with hkkddef
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  have hVloc : LocallyIntegrable V volume := locallyIntegrable_of_sq_integrable hVm hV2
  -- kernel regularity
  have hρc : Continuous ρ := (contDiff_suzukiMollifier ε).continuous
  have hρcs : HasCompactSupport ρ := hasCompactSupport_suzukiMollifier hε
  have hρdc : Continuous ρd := (contDiff_deriv_suzukiMollifier ε).continuous
  have hρdcs : HasCompactSupport ρd := hasCompactSupport_deriv_suzukiMollifier hε
  have hkkc : Continuous kk := by
    have : Continuous fun t : ℝ => t * suzukiMollifier ε t := continuous_id.mul hρc
    exact this
  have hkkcs : HasCompactSupport kk := by
    have := hρcs.mul_left (f := fun t : ℝ => t)
    exact this
  have hkkderiv : ∀ y : ℝ, HasDerivAt kk (ρ y + y * ρd y) y := by
    intro y
    have := hasDerivAt_firstMomentKernel
      (ρ := suzukiMollifier ε) (ρ' := fun u => deriv (suzukiMollifier ε) u)
      (fun u => hasDerivAt_suzukiMollifier ε u) y
    simpa [firstMomentDeriv] using this
  have hkkdeq : kkd = fun y => ρ y + y * ρd y := funext fun y => (hkkderiv y).deriv
  have hkkdc : Continuous kkd := by
    rw [hkkdeq]
    exact hρc.add (continuous_id.mul hρdc)
  have hkkdcs : HasCompactSupport kkd := hkkcs.deriv
  -- integrability instances
  have hsqI : ∀ (h : ℝ → ℝ), Continuous h → HasCompactSupport h →
      Integrable fun u => h u ^ (2 : ℕ) := fun h hc hcs =>
    (hc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hcs)
  have hI : ∀ (h : ℝ → ℝ), Continuous h → HasCompactSupport h → ∀ z : ℝ,
      Integrable fun t => V t * h (z - t) := fun h hc hcs z =>
    integrable_mul_kernel_comp_sub hc.aestronglyMeasurable (hsqI h hc hcs) hVm hV2 z
  have hIdir : ∀ (h : ℝ → ℝ), Continuous h → HasCompactSupport h → ∀ z : ℝ,
      Integrable fun t => h t * V (z - t) := fun h hc hcs z =>
    integrable_kernel_mul_sq hc.aestronglyMeasurable (hsqI h hc hcs) hVm hV2 z
  have hflipmul : ∀ (h : ℝ → ℝ) (z : ℝ),
      (∫ t, V t * h (z - t)) = lineConvolution h V z := by
    intro h z
    rw [lineConvolution_flip]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show V t * h (z - t) = h (z - t) * V t
    ring
  -- the test function
  set φx : ℝ → ℝ := fun t => ρ (x - t) with hφxdef
  have hφxsmooth : ContDiff ℝ ∞ φx :=
    (contDiff_suzukiMollifier ε).comp (contDiff_const.sub contDiff_id)
  have hφxsupp : HasCompactSupport φx := by
    refine HasCompactSupport.intro (isCompact_Icc (a := x - ε) (b := x + ε)) fun t ht => ?_
    show ρ (x - t) = 0
    refine suzukiMollifier_eq_zero hε ?_
    rw [mem_Icc, not_and_or] at ht
    rcases ht with ht | ht
    · rw [not_le] at ht
      calc ε < x - t := by linarith
        _ ≤ |x - t| := le_abs_self _
    · rw [not_le] at ht
      calc ε < -(x - t) := by linarith
        _ ≤ |x - t| := neg_le_abs _
  have hφxd : ∀ t, HasDerivAt φx (-ρd (x - t)) t := by
    intro t
    have hb : HasDerivAt (fun t : ℝ => x - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub x
    have hcomp : HasDerivAt (suzukiMollifier ε ∘ fun t : ℝ => x - t)
        (deriv (suzukiMollifier ε) (x - t) * (-1)) t :=
      HasDerivAt.comp t (hasDerivAt_suzukiMollifier ε (x - t)) hb
    have hcomp' : HasDerivAt φx (deriv (suzukiMollifier ε) (x - t) * (-1)) t := hcomp
    simpa using hcomp'
  have hderiv_φx : deriv φx = fun t => -ρd (x - t) := funext fun t => (hφxd t).deriv
  -- instantiate the tested equation
  have E := heq φx hφxsmooth hφxsupp
  -- the data identities
  have hTV : (∫ t, V t * φx t) = lineConvolution ρ V x := hflipmul ρ x
  have hTG : (∫ t, G t * φx t) = lineConvolution ρ G x := by
    rw [lineConvolution_flip]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show G t * ρ (x - t) = ρ (x - t) * G t
    ring
  have hTdφ : (∫ t, V t * deriv φx t) = -lineConvolution ρd V x := by
    rw [hderiv_φx]
    calc (∫ t, V t * -ρd (x - t)) = ∫ t, -(V t * ρd (x - t)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show V t * -ρd (x - t) = -(V t * ρd (x - t))
          ring
      _ = -∫ t, V t * ρd (x - t) := integral_neg _
      _ = -lineConvolution ρd V x := by rw [hflipmul ρd x]
  have hTtφ : (∫ t, V t * (t * φx t))
      = x * lineConvolution ρ V x - lineConvolution kk V x := by
    calc (∫ t, V t * (t * φx t))
        = ∫ t, x * (V t * ρ (x - t)) - V t * kk (x - t) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show V t * (t * ρ (x - t)) = x * (V t * ρ (x - t)) - V t * kk (x - t)
          have hk : kk (x - t) = (x - t) * ρ (x - t) := rfl
          rw [hk]
          ring
      _ = (∫ t, x * (V t * ρ (x - t))) - ∫ t, V t * kk (x - t) :=
          integral_sub ((hI ρ hρc hρcs x).const_mul x) (hI kk hkkc hkkcs x)
      _ = x * lineConvolution ρ V x - lineConvolution kk V x := by
          rw [integral_const_mul, hflipmul ρ x, hflipmul kk x]
  have hTtdφ : (∫ t, V t * (t * deriv φx t))
      = -(x * lineConvolution ρd V x) + lineConvolution kkd V x
        - lineConvolution ρ V x := by
    rw [hderiv_φx]
    calc (∫ t, V t * (t * (fun t => -ρd (x - t)) t))
        = ∫ t, -(x * (V t * ρd (x - t))) + V t * kkd (x - t) - V t * ρ (x - t) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show V t * (t * -ρd (x - t))
              = -(x * (V t * ρd (x - t))) + V t * kkd (x - t) - V t * ρ (x - t)
          have hk : kkd (x - t) = ρ (x - t) + (x - t) * ρd (x - t) := by rw [hkkdeq]
          rw [hk]
          ring
      _ = (∫ t, -(x * (V t * ρd (x - t))) + V t * kkd (x - t))
            - ∫ t, V t * ρ (x - t) :=
          integral_sub (((hI ρd hρdc hρdcs x).const_mul x).neg.add (hI kkd hkkdc hkkdcs x))
            (hI ρ hρc hρcs x)
      _ = ((∫ t, -(x * (V t * ρd (x - t)))) + ∫ t, V t * kkd (x - t))
            - ∫ t, V t * ρ (x - t) := by
          have hIneg : Integrable fun t => -(x * (V t * ρd (x - t))) :=
            ((hI ρd hρdc hρdcs x).const_mul x).neg
          rw [integral_add hIneg (hI kkd hkkdc hkkdcs x)]
      _ = -(x * lineConvolution ρd V x) + lineConvolution kkd V x
            - lineConvolution ρ V x := by
          rw [integral_neg, integral_const_mul, hflipmul ρd x, hflipmul kkd x, hflipmul ρ x]
  have hTsum : (∫ t, V t * (φx t + t * deriv φx t))
      = (∫ t, V t * φx t) + ∫ t, V t * (t * deriv φx t) := by
    have hint2 : Integrable fun t => V t * (t * deriv φx t) := by
      rw [hderiv_φx]
      refine ((((hI ρd hρdc hρdcs x).const_mul x).neg.add
        (hI kkd hkkdc hkkdcs x)).sub (hI ρ hρc hρcs x)).congr ?_
      filter_upwards with t
      show -(x * (V t * ρd (x - t))) + V t * kkd (x - t) - V t * ρ (x - t)
          = V t * (t * (fun t => -ρd (x - t)) t)
      have hk : kkd (x - t) = ρ (x - t) + (x - t) * ρd (x - t) := by rw [hkkdeq]
      rw [hk]
      ring
    calc (∫ t, V t * (φx t + t * deriv φx t))
        = ∫ t, V t * φx t + V t * (t * deriv φx t) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show V t * (φx t + t * deriv φx t) = V t * φx t + V t * (t * deriv φx t)
          ring
      _ = (∫ t, V t * φx t) + ∫ t, V t * (t * deriv φx t) :=
          integral_add (hI ρ hρc hρcs x) hint2
  -- jump identities
  have hJdφ : ∀ t, shiftedGammaJump (-σ) (deriv φx) t = -shiftedGammaJump σ ρd (x - t) := by
    intro t
    rw [hderiv_φx]
    calc shiftedGammaJump (-σ) (fun u => -ρd (x - u)) t
        = -shiftedGammaJump (-σ) (fun u => ρd (x - u)) t :=
          shiftedGammaJump_neg_profile (-σ) (fun u => ρd (x - u)) t
      _ = -shiftedGammaJump σ ρd (x - t) := by
          rw [shiftedGammaJump_neg_comp_sub σ ρd x t]
  -- Lipschitz and support data for the two Fubini exchanges
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_abs_le_of_hasCompactSupport hρdc hρdcs
  have hρK : ∀ u v : ℝ, |ρ u - ρ v| ≤ M₁ * |u - v| := fun u v =>
    abs_sub_le_of_deriv_bound ((contDiff_suzukiMollifier ε).of_le (by exact_mod_cast le_top)) hM₁ u v
  have hρddc : Continuous (deriv ρd) :=
    (contDiff_infty_iff_deriv.mp (contDiff_deriv_suzukiMollifier ε)).2.continuous
  have hρddcs : HasCompactSupport (deriv ρd) := hρdcs.deriv
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_abs_le_of_hasCompactSupport hρddc hρddcs
  have hρdK : ∀ u v : ℝ, |ρd u - ρd v| ≤ M₂ * |u - v| := fun u v =>
    abs_sub_le_of_deriv_bound ((contDiff_deriv_suzukiMollifier ε).of_le (by exact_mod_cast le_top)) hM₂ u v
  have hρsupp : ∀ u : ℝ, ε < |u| → ρ u = 0 := fun u hu => suzukiMollifier_eq_zero hε hu
  have hρdsupp : ∀ u : ℝ, ε < |u| → ρd u = 0 := fun u hu =>
    deriv_suzukiMollifier_eq_zero hε hu
  have hFub1 : (∫ t, V t * shiftedGammaJump σ ρd (x - t))
      = shiftedGammaJump σ (lineConvolution ρd V) x :=
    integral_mul_shiftedGammaJump_comp_sub hρdc hρdK hρdsupp hε.le hVmm hV2 hσ0 hσ1 x
  have hFub2 : (∫ t, V t * shiftedGammaJump σ ρ (x - t))
      = shiftedGammaJump σ (lineConvolution ρ V) x :=
    integral_mul_shiftedGammaJump_comp_sub hρc hρK hρsupp hε.le hVmm hV2 hσ0 hσ1 x
  have hTJdφ : (∫ t, V t * shiftedGammaJump (-σ) (deriv φx) t)
      = -shiftedGammaJump σ (lineConvolution ρd V) x := by
    calc (∫ t, V t * shiftedGammaJump (-σ) (deriv φx) t)
        = ∫ t, -(V t * shiftedGammaJump σ ρd (x - t)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show V t * shiftedGammaJump (-σ) (deriv φx) t
              = -(V t * shiftedGammaJump σ ρd (x - t))
          rw [hJdφ t]
          ring
      _ = -∫ t, V t * shiftedGammaJump σ ρd (x - t) := integral_neg _
      _ = -shiftedGammaJump σ (lineConvolution ρd V) x := by rw [hFub1]
  have hTJφ : (∫ t, V t * shiftedGammaJump (-σ) φx t)
      = shiftedGammaJump σ (lineConvolution ρ V) x := by
    calc (∫ t, V t * shiftedGammaJump (-σ) φx t)
        = ∫ t, V t * shiftedGammaJump σ ρ (x - t) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show V t * shiftedGammaJump (-σ) φx t = V t * shiftedGammaJump σ ρ (x - t)
          rw [hφxdef]
          rw [shiftedGammaJump_neg_comp_sub σ ρ x t]
      _ = shiftedGammaJump σ (lineConvolution ρ V) x := hFub2
  -- the mollified objects in convolution atoms
  have hUval : ∀ y : ℝ, suzukiMollifiedDeriv σ ε V y
      = lineConvolution ρd V y - σ * lineConvolution ρ V y := by
    intro y
    unfold suzukiMollifiedDeriv
    exact lineConvolution_kernel_sub_mul (hIdir ρd hρdc hρdcs y) (hIdir ρ hρc hρcs y)
  have hWval : suzukiMollifiedDefect σ ε V x
      = lineConvolution kkd V x - σ * lineConvolution kk V x := by
    unfold suzukiMollifiedDefect
    exact lineConvolution_kernel_sub_mul (hIdir kkd hkkdc hkkdcs x) (hIdir kk hkkc hkkcs x)
  -- the jump of the mollified derivative
  have hjump1 : IntegrableOn (fun s =>
      shiftedSecondDifference σ (lineConvolution ρd V) x s * gammaTransportKernel s)
      (Ioi 0) := by
    refine integrableOn_shiftedSecondDifference_mul_kernel
      (continuous_lineConvolution hρdc hρdcs hVloc).measurable
      (fun u v => abs_lineConvolution_sub_le
        ((contDiff_deriv_suzukiMollifier ε).of_le (by exact_mod_cast le_top)) hρdcs hVm hV2 u v)
      (fun z => abs_lineConvolution_le hρdc.aestronglyMeasurable
        (hsqI ρd hρdc hρdcs) hVm hV2 z) hσ0 hσ1 x
  have hjump2 : IntegrableOn (fun s =>
      shiftedSecondDifference σ (lineConvolution ρ V) x s * gammaTransportKernel s)
      (Ioi 0) := by
    refine integrableOn_shiftedSecondDifference_mul_kernel
      (continuous_lineConvolution hρc hρcs hVloc).measurable
      (fun u v => abs_lineConvolution_sub_le
        ((contDiff_suzukiMollifier ε).of_le (by exact_mod_cast le_top)) hρcs hVm hV2 u v)
      (fun z => abs_lineConvolution_le hρc.aestronglyMeasurable
        (hsqI ρ hρc hρcs) hVm hV2 z) hσ0 hσ1 x
  have hUjump : shiftedGammaJump σ (suzukiMollifiedDeriv σ ε V) x
      = shiftedGammaJump σ (lineConvolution ρd V) x
        - σ * shiftedGammaJump σ (lineConvolution ρ V) x := by
    have hfun : suzukiMollifiedDeriv σ ε V
        = fun y => lineConvolution ρd V y - σ * lineConvolution ρ V y :=
      funext fun y => hUval y
    rw [hfun]
    exact shiftedGammaJump_sub_smul hjump1 hjump2
  -- assemble
  rw [hTsum, hTV, hTG, hTdφ, hTtφ, hTtdφ, hTJdφ, hTJφ] at E
  rw [hUval x, hWval, hUjump]
  linear_combination E

end GaloisForLFunctions.RHTower
