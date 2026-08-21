import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityCauchySourceEscape
import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource

/-!
# Schwarz-paired divisor fibers lie on the Weil parity null cone

Two involutions govern the source route: critical-line reflection sends `alpha` to `conj alpha`,
whereas source Schwarz pairing sends `alpha` to `-conj alpha`. For a non-real, nonzero fiber, the
Schwarz-paired boundary test supported on `alpha` and `-conj alpha` is disjoint from its
critical-line reflection. Its Weil square is therefore exactly zero.

The zero is non-vacuous on every hypothetical off-line Xi quartet: reflection-even and
reflection-odd energies are equal and both strictly positive. Thus positive-paired Cauchy closure
lands on the Krein null cone at the divisor boundary. Any RH producer using this closure must
control a transverse first jet or curvature; boundary-value positivity alone has no strict
reserve.
-/

open Complex

namespace RHTower

noncomputable section

def xiWeilSchwarzPairedFiberTest (alpha z : ℂ) : ℂ :=
  xiWeilFiberIndicator alpha z +
    xiWeilFiberIndicator (-(starRingEnd ℂ) alpha) z

theorem xiWeilSchwarzPairedFiberTest_squareSummable (alpha : ℂ) :
    XiWeilSquareSummable (xiWeilSchwarzPairedFiberTest alpha) := by
  exact (xiWeilFiberIndicator_squareSummable alpha).add
    (xiWeilFiberIndicator_squareSummable (-(starRingEnd ℂ) alpha))

theorem xiWeilSchwarzPairedFiberTest_product_eq_zero
    {alpha : ℂ} (h0 : alpha ≠ 0)
    (h : (starRingEnd ℂ) alpha ≠ alpha) (z : ℂ) :
    xiWeilSchwarzPairedFiberTest alpha z *
      xiWeilSharp (xiWeilSchwarzPairedFiberTest alpha) z = 0 := by
  have hca0 : (starRingEnd ℂ) alpha ≠ 0 := map_ne_zero (starRingEnd ℂ) |>.2 h0
  have hcneg : (starRingEnd ℂ) alpha ≠ -(starRingEnd ℂ) alpha := by
    intro heq
    apply hca0
    have htwo : (2 : ℂ) * (starRingEnd ℂ) alpha = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hnega : -alpha ≠ alpha := by
    intro heq
    apply h0
    have htwo : (2 : ℂ) * alpha = 0 := by
      calc
        (2 : ℂ) * alpha = alpha - (-alpha) := by ring
        _ = 0 := by rw [heq]; ring
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  by_cases hza : z = alpha
  · subst z
    simp [xiWeilSchwarzPairedFiberTest, xiWeilSharp,
      xiWeilFiberIndicator, h, hcneg]
  · by_cases hzb : z = -(starRingEnd ℂ) alpha
    · subst z
      simp [xiWeilSchwarzPairedFiberTest, xiWeilSharp,
        xiWeilFiberIndicator, Ne.symm h, hnega]
    · simp [xiWeilSchwarzPairedFiberTest, xiWeilSharp,
        xiWeilFiberIndicator, hza, hzb]

theorem xiWeilPolarization_schwarzPairedFiber_eq_zero
    {alpha : ℂ} (h0 : alpha ≠ 0)
    (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilPolarization (xiWeilSchwarzPairedFiberTest alpha)
      (xiWeilSchwarzPairedFiberTest alpha) = 0 := by
  rw [xiWeilPolarization]
  simp_rw [xiWeilSchwarzPairedFiberTest_product_eq_zero h0 h]
  simp

theorem xiWeilSchwarzPairedFiber_evenEnergy_eq_oddEnergy
    {alpha : ℂ} (h0 : alpha ≠ 0)
    (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilEvenEnergy (xiWeilSchwarzPairedFiberTest alpha) =
      xiWeilOddEnergy (xiWeilSchwarzPairedFiberTest alpha) := by
  have hp := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    (xiWeilSchwarzPairedFiberTest_squareSummable alpha)
  rw [xiWeilPolarization_schwarzPairedFiber_eq_zero h0 h] at hp
  have hre := congrArg Complex.re hp
  norm_num at hre
  linarith

theorem xiWeilHilbertQuadratic_schwarzPairedFiber_eq_zero
    {alpha : ℂ} (h0 : alpha ≠ 0)
    (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilHilbertQuadratic
      (xiWeilEvaluationLp (xiWeilSchwarzPairedFiberTest alpha)
        (xiWeilSchwarzPairedFiberTest_squareSummable alpha)) = 0 := by
  rw [xiWeilHilbertQuadratic_evaluation_eq_polarization_re,
    xiWeilPolarization_schwarzPairedFiber_eq_zero h0 h]
  rfl

theorem xiWeilSchwarzPairedFiber_evenEnergy_pos
    (q : XiZeroCopy)
    (h : (starRingEnd ℂ) (xiSpectralPoint q) ≠ xiSpectralPoint q) :
    0 < xiWeilEvenEnergy
      (xiWeilSchwarzPairedFiberTest (xiSpectralPoint q)) := by
  let alpha : ℂ := xiSpectralPoint q
  let F : ℂ → ℂ := xiWeilSchwarzPairedFiberTest alpha
  have hF : XiWeilSquareSummable F :=
    xiWeilSchwarzPairedFiberTest_squareSummable alpha
  have hsum := xiWeilEvenPart_squareSummable hF
  have h0 : alpha ≠ 0 := xiSpectralPoint_ne_zero q
  have hca0 : (starRingEnd ℂ) alpha ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 h0
  have hcneg : (starRingEnd ℂ) alpha ≠ -(starRingEnd ℂ) alpha := by
    intro heq
    apply hca0
    have htwo : (2 : ℂ) * (starRingEnd ℂ) alpha = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have h' : (starRingEnd ℂ) alpha ≠ alpha := by
    simpa only [alpha] using h
  have hterm : 0 < ‖xiWeilEvenPart F alpha‖ ^ 2 := by
    by_cases hs : alpha = -(starRingEnd ℂ) alpha
    · have hFa : F alpha = 2 := by
        change (if alpha = alpha then 1 else 0) +
          (if alpha = -(starRingEnd ℂ) alpha then 1 else 0) = 2
        rw [if_pos rfl, if_pos hs]
        norm_num
      have hFc : F ((starRingEnd ℂ) alpha) = 0 := by
        change (if (starRingEnd ℂ) alpha = alpha then 1 else 0) +
          (if (starRingEnd ℂ) alpha = -(starRingEnd ℂ) alpha then 1 else 0) = 0
        rw [if_neg h', if_neg hcneg]
        norm_num
      rw [xiWeilEvenPart, hFa, hFc]
      norm_num
    · have hFa : F alpha = 1 := by
        change (if alpha = alpha then 1 else 0) +
          (if alpha = -(starRingEnd ℂ) alpha then 1 else 0) = 1
        rw [if_pos rfl, if_neg hs]
        norm_num
      have hFc : F ((starRingEnd ℂ) alpha) = 0 := by
        change (if (starRingEnd ℂ) alpha = alpha then 1 else 0) +
          (if (starRingEnd ℂ) alpha = -(starRingEnd ℂ) alpha then 1 else 0) = 0
        rw [if_neg h', if_neg hcneg]
        norm_num
      rw [xiWeilEvenPart, hFa, hFc]
      norm_num
  change 0 < ∑' q' : XiZeroCopy,
    ‖xiWeilEvenPart F (xiSpectralPoint q')‖ ^ 2
  exact hsum.tsum_pos (fun q' => sq_nonneg _) q (by simpa [alpha] using hterm)

theorem xiWeilSchwarzPairedFiber_oddEnergy_pos
    (q : XiZeroCopy)
    (h : (starRingEnd ℂ) (xiSpectralPoint q) ≠ xiSpectralPoint q) :
    0 < xiWeilOddEnergy
      (xiWeilSchwarzPairedFiberTest (xiSpectralPoint q)) := by
  rw [← xiWeilSchwarzPairedFiber_evenEnergy_eq_oddEnergy
    (xiSpectralPoint_ne_zero q) h]
  exact xiWeilSchwarzPairedFiber_evenEnergy_pos q h

end
end RHTower

