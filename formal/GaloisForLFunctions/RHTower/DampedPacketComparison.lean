import GaloisForLFunctions.HTGeometry.MassGaugeDampedBandRatio
import GaloisForLFunctions.RHTower.DampedCausalCompression

/-!
# The packet comparison defect

The damped propagator applied to a Gaussian packet is compared with the band model, whose action is
an exact scalar multiple of a shifted Gaussian packet.  The defect splits into three pieces:

* on the band the symbols differ by at most `‖N‖ e^{ση}` times the band error, and the Gaussian
  weight makes `e^{4πσy - 2πy²}` integrable, so no `e^{σρ}` loss occurs;
* off the band the propagator contributes at most `e^{λu}` against the Gaussian frequency tail;
* off the band the model contributes its own scalar against the shifted Gaussian tail.

The band comparison is taken as an input, so this module is pure integral bookkeeping and the
analytic content stays in the band-ratio lemmas.
-/

open MeasureTheory Filter Topology Complex GaloisForLFunctions.HTGeometry

open scoped FourierTransform

namespace RHTower

open RHTower.MellinL2

noncomputable section

/-- The defect between the propagated packet and the model output. -/
def packetDefect {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (u r T : ℝ) :
    Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_dampedSuperluminalSymbol ha hlambda.le sigma u) (Real.exp_nonneg _)
      (norm_dampedSuperluminalSymbol_abs_le ha hlambda hsigma u)
      (fourierGaussPacket (r / (2 * Real.pi)) T)
    - dampedModelConst a lambda sigma u r
      • fourierGaussPacket (r / (2 * Real.pi) - sigma) (T - u)

theorem coeFn_packetDefect {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u r T : ℝ) :
    (packetDefect ha hlambda hsigma u r T : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)] fun w =>
        dampedSuperluminalSymbol a lambda sigma u w
            * (fourierGaussPacket (r / (2 * Real.pi)) T : ℝ → ℂ) w
          - dampedModelConst a lambda sigma u r
            * (fourierGaussPacket (r / (2 * Real.pi) - sigma) (T - u) : ℝ → ℂ) w := by
  have h1 := lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (measurable_dampedSuperluminalSymbol ha hlambda.le sigma u) (Real.exp_nonneg _)
    (norm_dampedSuperluminalSymbol_abs_le ha hlambda hsigma u)
    (fourierGaussPacket (r / (2 * Real.pi)) T)
  have h2 := Lp.coeFn_sub
    (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_dampedSuperluminalSymbol ha hlambda.le sigma u) (Real.exp_nonneg _)
      (norm_dampedSuperluminalSymbol_abs_le ha hlambda hsigma u)
      (fourierGaussPacket (r / (2 * Real.pi)) T))
    (dampedModelConst a lambda sigma u r
      • fourierGaussPacket (r / (2 * Real.pi) - sigma) (T - u))
  have h3 := Lp.coeFn_smul (dampedModelConst a lambda sigma u r)
    (fourierGaussPacket (r / (2 * Real.pi) - sigma) (T - u))
  filter_upwards [h1, h2, h3] with w e1 e2 e3
  rw [packetDefect, e2, Pi.sub_apply, e1, e3, Pi.smul_apply, smul_eq_mul]

/-- **The comparison defect, split over the band.** -/
theorem norm_packetDefect_sq_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {u r T rho beta : ℝ}
    (hrhosigma : sigma ≤ rho) (hr : r ≠ 0)
    (hband : ∀ w : ℝ, |w + r / (2 * Real.pi)| ≤ rho →
      ‖dampedSuperluminalSymbol a lambda sigma u w - dampedModelSymbol a lambda sigma u r w‖
        ≤ ‖massGaugeDampedSymbol a lambda sigma u (-r)‖
          * Real.exp (2 * Real.pi * sigma * (w + r / (2 * Real.pi))) * beta) :
    ‖packetDefect ha hlambda hsigma u r T‖ ^ (2 : ℕ)
      ≤ ‖massGaugeDampedSymbol a lambda sigma u (-r)‖ ^ (2 : ℕ) * beta ^ (2 : ℕ)
          * (Real.exp (2 * Real.pi * sigma ^ (2 : ℕ)) * Real.sqrt 2⁻¹)
        + (2 * Real.exp (|u| * lambda) ^ (2 : ℕ) * Real.exp (-(Real.pi * rho ^ (2 : ℕ)))
          + 2 * ‖dampedModelConst a lambda sigma u r‖ ^ (2 : ℕ)
            * Real.exp (-(Real.pi * (rho - sigma) ^ (2 : ℕ)))) := by
  classical
  set R : ℝ := r / (2 * Real.pi) with hRdef
  set N : ℝ := ‖massGaugeDampedSymbol a lambda sigma u (-r)‖ with hNdef
  set K : ℂ := dampedModelConst a lambda sigma u r with hKdef
  set F : Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2 := fourierGaussPacket R T with hFdef
  set H : Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2 :=
    fourierGaussPacket (R - sigma) (T - u) with hHdef
  set S : Set ℝ := {w : ℝ | |w + R| ≤ rho} with hSdef
  have hmeasS : MeasurableSet S :=
    measurableSet_le ((measurable_id.add_const R).norm) measurable_const
  set D : ℝ → ℝ := fun w =>
    ‖dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w - K * (H : ℝ → ℂ) w‖ ^ (2 : ℕ)
    with hDdef
  have hnormsq : ‖packetDefect ha hlambda hsigma u r T‖ ^ (2 : ℕ) = ∫ w : ℝ, D w := by
    rw [norm_lpTwo_sq (μ := (volume : Measure ℝ))]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_packetDefect ha hlambda hsigma u r T] with w hw
    rw [hw]
  have hFint : Integrable (fun w : ℝ => ‖(F : ℝ → ℂ) w‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).1 (Lp.memLp F)
  have hHint : Integrable (fun w : ℝ => ‖(H : ℝ → ℂ) w‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable H)).1 (Lp.memLp H)
  have hmajint : Integrable (fun w : ℝ =>
      2 * Real.exp (|u| * lambda) ^ (2 : ℕ) * ‖(F : ℝ → ℂ) w‖ ^ (2 : ℕ) + 2 * ‖K‖ ^ (2 : ℕ) * ‖(H : ℝ → ℂ) w‖ ^ (2 : ℕ)) :=
    (hFint.const_mul _).add (hHint.const_mul _)
  have hdom : ∀ w : ℝ, D w
      ≤ 2 * Real.exp (|u| * lambda) ^ (2 : ℕ) * ‖(F : ℝ → ℂ) w‖ ^ (2 : ℕ)
        + 2 * ‖K‖ ^ (2 : ℕ) * ‖(H : ℝ → ℂ) w‖ ^ (2 : ℕ) := by
    intro w
    have h1 : ‖dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w
        - K * (H : ℝ → ℂ) w‖ ^ (2 : ℕ)
        ≤ 2 * ‖dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w‖ ^ (2 : ℕ)
          + 2 * ‖K * (H : ℝ → ℂ) w‖ ^ (2 : ℕ) := by
      have hsub := norm_sub_le (dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w)
        (K * (H : ℝ → ℂ) w)
      have hsq : ‖dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w
          - K * (H : ℝ → ℂ) w‖ ^ (2 : ℕ)
          ≤ (‖dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w‖
            + ‖K * (H : ℝ → ℂ) w‖) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) hsub 2
      nlinarith [hsq, sq_nonneg (‖dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w‖
        - ‖K * (H : ℝ → ℂ) w‖)]
    have h2 : ‖dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w‖ ^ (2 : ℕ)
        ≤ Real.exp (|u| * lambda) ^ (2 : ℕ) * ‖(F : ℝ → ℂ) w‖ ^ (2 : ℕ) := by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _)
          (norm_dampedSuperluminalSymbol_abs_le ha hlambda hsigma u w) 2) (by positivity)
    have h3 : ‖K * (H : ℝ → ℂ) w‖ ^ (2 : ℕ) = ‖K‖ ^ (2 : ℕ) * ‖(H : ℝ → ℂ) w‖ ^ (2 : ℕ) := by
      rw [norm_mul, mul_pow]
    rw [hDdef]
    simp only
    nlinarith [h1, h2, h3]
  have hDnn : ∀ w : ℝ, 0 ≤ D w := fun w => by positivity
  have hDint : Integrable D := by
    refine Integrable.mono hmajint ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (((measurable_dampedSuperluminalSymbol ha hlambda.le sigma u).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable F)).sub
        (aestronglyMeasurable_const.mul (Lp.aestronglyMeasurable H))).norm.pow 2
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hDnn w),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.exp (|u| * lambda) ^ (2 : ℕ)
          * ‖(F : ℝ → ℂ) w‖ ^ (2 : ℕ) + 2 * ‖K‖ ^ (2 : ℕ) * ‖(H : ℝ → ℂ) w‖ ^ (2 : ℕ))]
      exact hdom w
  rw [hnormsq, ← integral_add_compl hmeasS hDint]
  have hbandint : ∫ w in S, D w
      ≤ N ^ (2 : ℕ) * beta ^ (2 : ℕ) * (Real.exp (2 * Real.pi * sigma ^ (2 : ℕ)) * Real.sqrt 2⁻¹) := by
    have hmodel := coeFn_dampedModel_mul_packet a lambda sigma u r T hr
    have hFnorm := coeFn_fourierGaussPacket_norm R T
    have hFshift := coeFn_gaussLp_shift R
    have hptbound : ∀ᵐ w : ℝ, w ∈ S →
        D w ≤ N ^ (2 : ℕ) * beta ^ (2 : ℕ) * Real.exp (4 * Real.pi * sigma * (w + R)
          - 2 * Real.pi * (w + R) ^ (2 : ℕ)) := by
      filter_upwards [hmodel, hFnorm, hFshift] with w hm hn hs hmem
      have hFval : ‖(F : ℝ → ℂ) w‖ = Real.exp (-(Real.pi * (w + R) ^ (2 : ℕ))) := by
        rw [hFdef, hn, hs, norm_gaussLp_apply]
      have hsplit : dampedSuperluminalSymbol a lambda sigma u w * (F : ℝ → ℂ) w
          - K * (H : ℝ → ℂ) w
          = (dampedSuperluminalSymbol a lambda sigma u w
            - dampedModelSymbol a lambda sigma u r w) * (F : ℝ → ℂ) w := by
        rw [sub_mul, hKdef, hHdef, hFdef, ← hm]
      have hb := hband w hmem
      rw [hDdef]
      simp only
      rw [hsplit, norm_mul, hFval, mul_pow]
      have hstep : ‖dampedSuperluminalSymbol a lambda sigma u w
          - dampedModelSymbol a lambda sigma u r w‖ ^ (2 : ℕ)
          ≤ (N * Real.exp (2 * Real.pi * sigma * (w + R)) * beta) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
      have e1 : Real.exp (2 * Real.pi * sigma * (w + R)) ^ (2 : ℕ)
          = Real.exp (4 * Real.pi * sigma * (w + R)) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      have e2 : Real.exp (-(Real.pi * (w + R) ^ (2 : ℕ))) ^ (2 : ℕ)
          = Real.exp (-(2 * Real.pi * (w + R) ^ (2 : ℕ))) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      have hval : (N * Real.exp (2 * Real.pi * sigma * (w + R)) * beta) ^ (2 : ℕ)
          * Real.exp (-(Real.pi * (w + R) ^ (2 : ℕ))) ^ (2 : ℕ)
          = N ^ (2 : ℕ) * beta ^ (2 : ℕ) * Real.exp (4 * Real.pi * sigma * (w + R)
            - 2 * Real.pi * (w + R) ^ (2 : ℕ)) := by
        calc (N * Real.exp (2 * Real.pi * sigma * (w + R)) * beta) ^ (2 : ℕ)
              * Real.exp (-(Real.pi * (w + R) ^ (2 : ℕ))) ^ (2 : ℕ)
            = N ^ (2 : ℕ) * beta ^ (2 : ℕ) * (Real.exp (2 * Real.pi * sigma * (w + R)) ^ (2 : ℕ)
                * Real.exp (-(Real.pi * (w + R) ^ (2 : ℕ))) ^ (2 : ℕ)) := by ring
          _ = N ^ (2 : ℕ) * beta ^ (2 : ℕ) * (Real.exp (4 * Real.pi * sigma * (w + R))
                * Real.exp (-(2 * Real.pi * (w + R) ^ (2 : ℕ)))) := by rw [e1, e2]
          _ = N ^ (2 : ℕ) * beta ^ (2 : ℕ) * Real.exp (4 * Real.pi * sigma * (w + R)
                - 2 * Real.pi * (w + R) ^ (2 : ℕ)) := by
              rw [← Real.exp_add]
              congr 2
      calc ‖dampedSuperluminalSymbol a lambda sigma u w
            - dampedModelSymbol a lambda sigma u r w‖ ^ (2 : ℕ)
              * Real.exp (-(Real.pi * (w + R) ^ (2 : ℕ))) ^ (2 : ℕ)
          ≤ (N * Real.exp (2 * Real.pi * sigma * (w + R)) * beta) ^ (2 : ℕ)
              * Real.exp (-(Real.pi * (w + R) ^ (2 : ℕ))) ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ = N ^ (2 : ℕ) * beta ^ (2 : ℕ) * Real.exp (4 * Real.pi * sigma * (w + R)
            - 2 * Real.pi * (w + R) ^ (2 : ℕ)) := hval
    have hgint : Integrable (fun w : ℝ => N ^ (2 : ℕ) * beta ^ (2 : ℕ)
        * Real.exp (4 * Real.pi * sigma * (w + R) - 2 * Real.pi * (w + R) ^ (2 : ℕ))) := by
      have hbase : Integrable (fun y : ℝ =>
          Real.exp (4 * Real.pi * sigma * y - 2 * Real.pi * y ^ (2 : ℕ))) := by
        have hpt : ∀ y : ℝ, Real.exp (4 * Real.pi * sigma * y - 2 * Real.pi * y ^ (2 : ℕ))
            = Real.exp (2 * Real.pi * sigma ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * (y - sigma) ^ (2 : ℕ)) := by
          intro y
          rw [← Real.exp_add]
          congr 1
          ring
        rw [funext hpt]
        exact ((integrable_exp_neg_mul_sq
          (by positivity : (0 : ℝ) < 2 * Real.pi)).comp_sub_right sigma).const_mul _
      exact ((hbase.comp_add_right R).const_mul _)
    calc ∫ w in S, D w
        ≤ ∫ w in S, N ^ (2 : ℕ) * beta ^ (2 : ℕ) * Real.exp (4 * Real.pi * sigma * (w + R)
            - 2 * Real.pi * (w + R) ^ (2 : ℕ)) := by
          refine setIntegral_mono_ae_restrict hDint.integrableOn hgint.integrableOn ?_
          filter_upwards [ae_restrict_of_ae hptbound, self_mem_ae_restrict hmeasS] with w h1 h2
          exact h1 h2
      _ ≤ ∫ w : ℝ, N ^ (2 : ℕ) * beta ^ (2 : ℕ) * Real.exp (4 * Real.pi * sigma * (w + R)
            - 2 * Real.pi * (w + R) ^ (2 : ℕ)) := by
          refine setIntegral_le_integral hgint (Filter.Eventually.of_forall fun w => ?_)
          positivity
      _ = N ^ (2 : ℕ) * beta ^ (2 : ℕ) * (Real.exp (2 * Real.pi * sigma ^ (2 : ℕ)) * Real.sqrt 2⁻¹) := by
          rw [integral_const_mul]
          congr 1
          rw [integral_add_right_eq_self
            (fun y : ℝ => Real.exp (4 * Real.pi * sigma * y - 2 * Real.pi * y ^ (2 : ℕ))) R]
          exact integral_exp_linear_mul_gauss sigma
  have hoffint : ∫ w in Sᶜ, D w
      ≤ 2 * Real.exp (|u| * lambda) ^ (2 : ℕ) * Real.exp (-(Real.pi * rho ^ (2 : ℕ)))
        + 2 * ‖K‖ ^ (2 : ℕ) * Real.exp (-(Real.pi * (rho - sigma) ^ (2 : ℕ))) := by
    have hsubF : Sᶜ ⊆ {w : ℝ | rho ≤ |w + R|} := by
      intro w hw
      rw [hSdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
      simp only [Set.mem_setOf_eq]
      exact le_of_lt hw
    have hsubH : Sᶜ ⊆ {w : ℝ | rho - sigma ≤ |w + (R - sigma)|} := by
      intro w hw
      rw [hSdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
      have habs : |w + R| - sigma ≤ |w + (R - sigma)| := by
        have := abs_sub_abs_le_abs_sub (w + R) (sigma : ℝ)
        have hrw : w + R - sigma = w + (R - sigma) := by ring
        rw [hrw] at this
        have habss : |(sigma : ℝ)| = sigma := abs_of_nonneg hsigma
        rw [habss] at this
        linarith
      simp only [Set.mem_setOf_eq]
      linarith
    have hmeasF : MeasurableSet {w : ℝ | rho ≤ |w + R|} :=
      measurableSet_le measurable_const ((measurable_id.add_const R).norm)
    have hmeasH : MeasurableSet {w : ℝ | rho - sigma ≤ |w + (R - sigma)|} :=
      measurableSet_le measurable_const ((measurable_id.add_const (R - sigma)).norm)
    have hF1 : ∫ w in Sᶜ, ‖(F : ℝ → ℂ) w‖ ^ (2 : ℕ) ≤ Real.exp (-(Real.pi * rho ^ (2 : ℕ))) := by
      refine le_trans (setIntegral_mono_set hFint.integrableOn
        (Filter.Eventually.of_forall fun w => by positivity)
        (Filter.Eventually.of_forall hsubF)) ?_
      rcases le_or_gt 0 rho with hr0 | hr0
      · exact fourierGaussPacket_band_defect_le (R := R) (T := T) hr0
      · exfalso
        linarith [hsigma, hrhosigma]
    have hH1 : ∫ w in Sᶜ, ‖(H : ℝ → ℂ) w‖ ^ (2 : ℕ)
        ≤ Real.exp (-(Real.pi * (rho - sigma) ^ (2 : ℕ))) := by
      refine le_trans (setIntegral_mono_set hHint.integrableOn
        (Filter.Eventually.of_forall fun w => by positivity)
        (Filter.Eventually.of_forall hsubH)) ?_
      exact fourierGaussPacket_band_defect_le (R := R - sigma) (T := T - u) (by linarith)
    calc ∫ w in Sᶜ, D w
        ≤ ∫ w in Sᶜ, (2 * Real.exp (|u| * lambda) ^ (2 : ℕ) * ‖(F : ℝ → ℂ) w‖ ^ (2 : ℕ)
            + 2 * ‖K‖ ^ (2 : ℕ) * ‖(H : ℝ → ℂ) w‖ ^ (2 : ℕ)) :=
          setIntegral_mono_on hDint.integrableOn hmajint.integrableOn hmeasS.compl
            (fun w _ => hdom w)
      _ = 2 * Real.exp (|u| * lambda) ^ (2 : ℕ) * (∫ w in Sᶜ, ‖(F : ℝ → ℂ) w‖ ^ (2 : ℕ))
            + 2 * ‖K‖ ^ (2 : ℕ) * ∫ w in Sᶜ, ‖(H : ℝ → ℂ) w‖ ^ (2 : ℕ) := by
          rw [integral_add ((hFint.const_mul _).integrableOn) ((hHint.const_mul _).integrableOn),
            integral_const_mul, integral_const_mul]
      _ ≤ 2 * Real.exp (|u| * lambda) ^ (2 : ℕ) * Real.exp (-(Real.pi * rho ^ (2 : ℕ)))
            + 2 * ‖K‖ ^ (2 : ℕ) * Real.exp (-(Real.pi * (rho - sigma) ^ (2 : ℕ))) := by
          have hc1 : (0 : ℝ) ≤ 2 * Real.exp (|u| * lambda) ^ (2 : ℕ) := by positivity
          have hc2 : (0 : ℝ) ≤ 2 * ‖K‖ ^ (2 : ℕ) := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hF1 hc1)
            (mul_le_mul_of_nonneg_left hH1 hc2)
  linarith [hbandint, hoffint]


/-- **The band hypothesis from the quantitative band lemmas.**  On a band of radius `ρ` in the
normalised frequency variable, with `2πρ ≤ r/2` and the band exponent below one, the damped symbol
differs from the band model by at most `‖N‖ e^{2πσ(w+R)}` times twice the band exponent. -/
theorem band_comparison_of_bounds {a lambda : ℝ}
    {sigma u r rho : ℝ} (hsigma : 0 ≤ sigma) (hu : 0 ≤ u) (hr : 0 < r)
    (hband2 : 2 * Real.pi * rho ≤ r / 2)
    (hbeta1 : (sigma + u) * (a ^ (2 : ℕ) * (2 * Real.pi * rho) / r ^ (2 : ℕ) + 3 * a ^ (4 : ℕ) / r ^ (3 : ℕ)) ≤ 1) :
    ∀ w : ℝ, |w + r / (2 * Real.pi)| ≤ rho →
      ‖dampedSuperluminalSymbol a lambda sigma u w - dampedModelSymbol a lambda sigma u r w‖
        ≤ ‖massGaugeDampedSymbol a lambda sigma u (-r)‖
          * Real.exp (2 * Real.pi * sigma * (w + r / (2 * Real.pi)))
          * (2 * ((sigma + u)
            * (a ^ (2 : ℕ) * (2 * Real.pi * rho) / r ^ (2 : ℕ) + 3 * a ^ (4 : ℕ) / r ^ (3 : ℕ)))) := by
  intro w hw
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set R : ℝ := r / (2 * Real.pi) with hRdef
  set eta : ℝ := 2 * Real.pi * (w + R) with hetadef
  have hRr : 2 * Real.pi * R = r := by
    rw [hRdef]
    field_simp
  have hetaabs : |eta| = 2 * Real.pi * |w + R| := by
    rw [hetadef, abs_mul, abs_of_pos hpi]
  have hetale : |eta| ≤ 2 * Real.pi * rho := by
    rw [hetaabs]
    exact mul_le_mul_of_nonneg_left hw hpi.le
  have hetahalf : |eta| ≤ r / 2 := le_trans hetale hband2
  have hshift : eta - r = 2 * Real.pi * w := by
    rw [hetadef, ← hRr]
    ring
  have hexpo := norm_dampedBandExponent_le (a := a) (lambda := lambda) hsigma hu hr hetahalf
  have hmono : (sigma + u) * (a ^ (2 : ℕ) * |eta| / r ^ (2 : ℕ) + 3 * a ^ (4 : ℕ) / r ^ (3 : ℕ))
      ≤ (sigma + u) * (a ^ (2 : ℕ) * (2 * Real.pi * rho) / r ^ (2 : ℕ) + 3 * a ^ (4 : ℕ) / r ^ (3 : ℕ)) := by
    have hstep : a ^ (2 : ℕ) * |eta| / r ^ (2 : ℕ) ≤ a ^ (2 : ℕ) * (2 * Real.pi * rho) / r ^ (2 : ℕ) := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hetale (by positivity)
    have hnn : (0 : ℝ) ≤ sigma + u := by linarith
    nlinarith [hstep, hnn]
  have hsmall : ‖((sigma : ℂ) + (u : ℝ) * Complex.I)
      * (massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r)
        + (eta : ℂ))‖ ≤ 1 := le_trans (le_trans hexpo hmono) hbeta1
  have hkey := norm_dampedBand_sub_model_le (a := a) (lambda := lambda)
    (sigma := sigma) (u := u) (r := r) (eta := eta) hsmall
  have hsym : dampedSuperluminalSymbol a lambda sigma u w
      = massGaugeDampedSymbol a lambda sigma u (eta - r) := by
    rw [dampedSuperluminalSymbol, hshift]
  have hmod : dampedModelSymbol a lambda sigma u r w
      = massGaugeDampedSymbol a lambda sigma u (-r)
        * Complex.exp (((sigma : ℂ) + (u : ℝ) * Complex.I) * ((eta : ℝ) : ℂ)) := by
    rw [dampedModelSymbol, hetadef]
  rw [hsym, hmod]
  refine le_trans hkey ?_
  have hphase : Real.exp (sigma * eta) = Real.exp (2 * Real.pi * sigma * (w + R)) := by
    congr 1
    rw [hetadef]
    ring
  rw [hphase]
  have hnn : (0 : ℝ) ≤ ‖massGaugeDampedSymbol a lambda sigma u (-r)‖
      * Real.exp (2 * Real.pi * sigma * (w + R)) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hnn
  have := le_trans hexpo hmono
  linarith


/-! ## The operator lower bound -/

theorem norm_dampedHalfWave_sub_model {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u r T : ℝ) :
    ‖dampedHalfWave ha hlambda hsigma u (gaussPacket (r / (2 * Real.pi)) T)
        - dampedModelConst a lambda sigma u r
          • gaussPacket (r / (2 * Real.pi) - sigma) (T - u)‖
      = ‖packetDefect ha hlambda hsigma u r T‖ := by
  have hf : fourierL2 ℝ (gaussPacket (r / (2 * Real.pi)) T)
      = fourierGaussPacket (r / (2 * Real.pi)) T := by
    rw [fourierGaussPacket, fourierL2_eq]
  have hh : fourierL2 ℝ (gaussPacket (r / (2 * Real.pi) - sigma) (T - u))
      = fourierGaussPacket (r / (2 * Real.pi) - sigma) (T - u) := by
    rw [fourierGaussPacket, fourierL2_eq]
  have h1 : dampedHalfWave ha hlambda hsigma u (gaussPacket (r / (2 * Real.pi)) T)
      = fourierL2inv ℝ (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (measurable_dampedSuperluminalSymbol ha hlambda.le sigma u) (Real.exp_nonneg _)
        (norm_dampedSuperluminalSymbol_abs_le ha hlambda hsigma u)
        (fourierGaussPacket (r / (2 * Real.pi)) T)) := by
    rw [dampedHalfWave, fourierMulCLM_apply, hf]
  have h2 : dampedModelConst a lambda sigma u r
      • gaussPacket (r / (2 * Real.pi) - sigma) (T - u)
      = fourierL2inv ℝ (dampedModelConst a lambda sigma u r
        • fourierGaussPacket (r / (2 * Real.pi) - sigma) (T - u)) := by
    rw [← hh, map_smul, fourierL2inv_fourierL2]
  rw [h1, h2, ← map_sub, norm_fourierL2inv_apply, packetDefect]

/-- **(24.49) lower half, packet form.**  The compressed damped propagator dominates the model
scalar, up to the comparison defect and the two window defects. -/
theorem le_norm_dampedCompression_mul {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u r T H : ℝ) :
    ‖dampedModelConst a lambda sigma u r‖ * ‖gaussLp‖
        - ‖dampedModelConst a lambda sigma u r‖
          * ‖gaussPacket (r / (2 * Real.pi) - sigma) (T - u)
            - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H))
              (gaussPacket (r / (2 * Real.pi) - sigma) (T - u))‖
        - ‖packetDefect ha hlambda hsigma u r T‖
        - Real.exp (|u| * lambda)
          * ‖gaussPacket (r / (2 * Real.pi)) T
            - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H))
              (gaussPacket (r / (2 * Real.pi)) T)‖
      ≤ ‖dampedCompression ha hlambda hsigma u H‖ * ‖gaussLp‖ := by
  set P := windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H)) with hP
  set S := dampedHalfWave ha hlambda hsigma u with hS
  set f := gaussPacket (r / (2 * Real.pi)) T with hf
  set h := gaussPacket (r / (2 * Real.pi) - sigma) (T - u) with hh
  set K := dampedModelConst a lambda sigma u r with hK
  have hPnorm : ‖P‖ ≤ 1 := norm_windowCutoff_le _
  have hSnorm : ‖S‖ ≤ Real.exp (|u| * lambda) := norm_dampedHalfWave_le ha hlambda hsigma u
  have hfnorm : ‖f‖ = ‖gaussLp‖ := norm_gaussPacket _ _
  have hhnorm : ‖h‖ = ‖gaussLp‖ := norm_gaussPacket _ _
  have hdefect : ‖S f - K • h‖ = ‖packetDefect ha hlambda hsigma u r T‖ :=
    norm_dampedHalfWave_sub_model ha hlambda hsigma u r T
  -- the compression applied to the packet
  have hcomp : dampedCompression ha hlambda hsigma u H f = P (S (P f)) := rfl
  have hop : ‖P (S (P f))‖ ≤ ‖dampedCompression ha hlambda hsigma u H‖ * ‖f‖ := by
    rw [← hcomp]
    exact (dampedCompression ha hlambda hsigma u H).le_opNorm f
  -- split the input
  have hin : P f = f - (f - P f) := by abel
  have hstep1 : ‖P (S (P f))‖ ≥ ‖P (S f)‖ - Real.exp (|u| * lambda) * ‖f - P f‖ := by
    have hexpand : P (S (P f)) = P (S f) - P (S (f - P f)) := by
      rw [hin]
      simp [map_sub]
    have hbound : ‖P (S (f - P f))‖ ≤ Real.exp (|u| * lambda) * ‖f - P f‖ := by
      refine le_trans (P.le_opNorm _) ?_
      have h1 : ‖S (f - P f)‖ ≤ Real.exp (|u| * lambda) * ‖f - P f‖ :=
        le_trans (S.le_opNorm _) (mul_le_mul_of_nonneg_right hSnorm (norm_nonneg _))
      calc ‖P‖ * ‖S (f - P f)‖ ≤ 1 * (Real.exp (|u| * lambda) * ‖f - P f‖) :=
            mul_le_mul hPnorm h1 (norm_nonneg _) zero_le_one
        _ = Real.exp (|u| * lambda) * ‖f - P f‖ := by ring
    have := norm_sub_norm_le (P (S f)) (P (S (f - P f)))
    rw [← hexpand] at this
    linarith [this, hbound]
  have hstep2 : ‖P (S f)‖ ≥ ‖K‖ * ‖P h‖ - ‖packetDefect ha hlambda hsigma u r T‖ := by
    have hexpand : P (S f) = K • P h + P (S f - K • h) := by
      rw [map_sub, map_smul]
      abel
    have hbound : ‖P (S f - K • h)‖ ≤ ‖packetDefect ha hlambda hsigma u r T‖ := by
      refine le_trans (P.le_opNorm _) ?_
      rw [← hdefect]
      calc ‖P‖ * ‖S f - K • h‖ ≤ 1 * ‖S f - K • h‖ :=
            mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
        _ = ‖S f - K • h‖ := by ring
    have hsm : ‖K • P h‖ = ‖K‖ * ‖P h‖ := by
      rw [norm_smul]
    have := norm_sub_norm_le (K • P h) (-(P (S f - K • h)))
    have hrw : K • P h - -(P (S f - K • h)) = P (S f) := by
      rw [hexpand]
      abel
    rw [hrw, norm_neg, hsm] at this
    linarith [this, hbound]
  have hstep3 : ‖P h‖ ≥ ‖gaussLp‖ - ‖h - P h‖ := by
    have := norm_sub_norm_le h (h - P h)
    have hrw : h - (h - P h) = P h := by abel
    rw [hrw, hhnorm] at this
    linarith [this]
  have hKnn : (0 : ℝ) ≤ ‖K‖ := norm_nonneg _
  have hchain : ‖K‖ * ‖gaussLp‖ - ‖K‖ * ‖h - P h‖
      - ‖packetDefect ha hlambda hsigma u r T‖
      - Real.exp (|u| * lambda) * ‖f - P f‖ ≤ ‖P (S (P f))‖ := by
    have h3 : ‖K‖ * (‖gaussLp‖ - ‖h - P h‖) ≤ ‖K‖ * ‖P h‖ :=
      mul_le_mul_of_nonneg_left hstep3 hKnn
    nlinarith [hstep1, hstep2, h3]
  calc ‖K‖ * ‖gaussLp‖ - ‖K‖ * ‖h - P h‖
        - ‖packetDefect ha hlambda hsigma u r T‖
        - Real.exp (|u| * lambda) * ‖f - P f‖
      ≤ ‖P (S (P f))‖ := hchain
    _ ≤ ‖dampedCompression ha hlambda hsigma u H‖ * ‖f‖ := hop
    _ = ‖dampedCompression ha hlambda hsigma u H‖ * ‖gaussLp‖ := by rw [hfnorm]


end

end RHTower
