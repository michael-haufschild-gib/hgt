import GaloisForLFunctions.HTGeometry.BoundedPhaseNPlusToeplitz
import GaloisForLFunctions.HTGeometry.DiskMultiplierInnerOuterFactor
import GaloisForLFunctions.HTGeometry.DiskMultiplierSquareRoot
import GaloisForLFunctions.HTGeometry.SmirnovToeplitzNPlusInnerCancellation
import GaloisForLFunctions.RHTower.KapustinGaugeSmirnovCollision
import GaloisForLFunctions.RHTower.KapustinOneSidedToeplitzPhase

/-!
# Oriented `N⁺` collision for a one-sided Kapustin gauge

The canonical inner--outer factorization retains the unsquared right-semicircle orientation.
Taking a bounded square root only of the zero-free outer factor cancels its boundary phase from the
measurable `p = 1` bounded-phase element.  The remaining canonical inner factor is then cancelled
inside `N⁺`, leaving the fixed one-sided reciprocal-Gamma symbol.
-/

open Complex MeasureTheory Metric

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem kapustinUniversalGammaCarrier_neg_div_norm (x : ℝ) :
    kapustinUniversalGammaCarrier (-x) /
        (‖kapustinUniversalGammaCarrier (-x)‖ : ℂ) =
      Complex.exp ((kapustinReciprocalGammaPhase x : ℂ) * I) := by
  rw [kapustinUniversalGammaCarrier_eq_normFactor_mul_exp_neg_phase,
    kapustinReciprocalGammaPhase_neg]
  let r : ℝ := Real.exp ((-3 / 2 : ℝ) * Real.log (2 * Real.pi)) /
    ‖gammaVerticalValue (1 / 2) (-x)‖
  have hr : 0 < r := by
    exact div_pos (Real.exp_pos _)
      (norm_pos_iff.mpr (gammaVerticalValue_ne_zero (by norm_num) (-x)))
  change (r : ℂ) *
      Complex.exp (-I * ((-kapustinReciprocalGammaPhase x : ℝ) : ℂ)) /
        ‖(r : ℂ) *
          Complex.exp (-I * ((-kapustinReciprocalGammaPhase x : ℝ) : ℂ))‖ = _
  have hphaseNorm :
      ‖Complex.exp (-I * ((-kapustinReciprocalGammaPhase x : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    hphaseNorm, mul_one]
  field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne']
  congr 1
  push_cast
  ring

private theorem diskMultiplierLineBoundary_squareRoot_sq_ae
    (O H : DiskMultiplier)
    (hHsq : ∀ z ∈ ball (0 : ℂ) 1, H.fn z ^ 2 = O.fn z) :
    (fun x => diskMultiplierLineBoundary H x ^ 2) =ᵐ[volume]
      diskMultiplierLineBoundary O := by
  have hmul := diskMultiplierLineBoundary_mul_ae H H
  have hcongr : diskMultiplierLineBoundary (H.mul H) =ᵐ[volume]
      diskMultiplierLineBoundary O := by
    apply diskMultiplierLineBoundary_congr_ae
    intro z hz
    change H.fn z * H.fn z = O.fn z
    simpa [pow_two] using hHsq z hz
  filter_upwards [hmul, hcongr] with x hxMul hxCongr
  rw [← hxCongr, hxMul, pow_two]

/-- A one-sided rotated Kapustin weight creates an exact local-`L¹` kernel element for the fixed
oriented reciprocal-Gamma symbol. -/
noncomputable def kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    SmirnovToeplitzNPlusElement kapustinOneSidedToeplitzSymbol := by
  let Iinner := diskMultiplierInnerFactor Phi hPhi
  let Oouter := diskMultiplierOuterFactor Phi hPhi
  have hOouter : IsOuterDiskMultiplier Oouter :=
    isOuterDiskMultiplier_diskMultiplierOuterFactor Phi hPhi
  have hOzero : ∀ z ∈ ball (0 : ℂ) 1, Oouter.fn z ≠ 0 := by
    intro z hz
    exact hOouter.ne_zero_on_disk
      (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  let hrootExists := Oouter.exists_squareRoot_of_zeroFree hOzero
  let Hroot : DiskMultiplier := Classical.choose hrootExists
  have hHsq : ∀ z ∈ ball (0 : ℂ) 1, Hroot.fn z ^ 2 = Oouter.fn z :=
    Classical.choose_spec hrootExists
  have hHnonzero : ∃ z ∈ ball (0 : ℂ) 1, Hroot.fn z ≠ 0 := by
    refine ⟨0, by simp [Metric.mem_ball], ?_⟩
    intro hzero
    have := hHsq 0 (by simp [Metric.mem_ball])
    rw [hzero] at this
    simp at this
    exact hOzero 0 (by simp [Metric.mem_ball]) this.symm
  let b := kapustinNonnegativePhaseCircle Phi
  let hb := measurable_kapustinNonnegativePhaseCircle Phi
  let hbound := abs_kapustinNonnegativePhaseCircle_le Phi
  let Kb := boundedPhaseSmirnovToeplitzNPlusOneElement b hb hbound
  let KH := Kb.mul_left_multiplier Hroot hHnonzero
  have hphase := kapustinNonnegativePhaseCircle_pullback_ae Phi hPhi hnonneg
  have hfactor := diskMultiplierLineBoundary_innerFactor_mul_outerFactor_ae Phi hPhi
  have hrootSq := diskMultiplierLineBoundary_squareRoot_sq_ae Oouter Hroot hHsq
  have hrootNe := diskMultiplierLineBoundary_ne_zero_ae Hroot hHnonzero
  have hinnerUnit :=
    ae_norm_diskMultiplierLineBoundary_innerFactor_eq_one Phi hPhi
  have hPhiNe := diskMultiplierLineBoundary_ne_zero_ae Phi hPhi
  have hsymbol :
      smirnovToeplitzSymbolMul (diskMultiplierPhaseReflectionSymbol Hroot)
          (boundedPhaseOneToeplitzSymbol b) =ᵐ[volume]
        smirnovToeplitzSymbolMul kapustinOneSidedToeplitzSymbol
          (diskMultiplierLineBoundary Iinner) := by
    filter_upwards [hphase, hfactor, hrootSq, hrootNe, hinnerUnit, hPhiNe]
      with x hxPhase hxFactor hxRootSq hxRootNe hxInnerUnit hxPhiNe
    let a := kapustinUniversalGammaCarrier (-x)
    let i := diskMultiplierLineBoundary Iinner x
    let o := diskMultiplierLineBoundary Oouter x
    let h := diskMultiplierLineBoundary Hroot x
    let phi := diskMultiplierLineBoundary Phi x
    let q := kapustinRotatedGaugeQ Phi x
    have ha : a ≠ 0 := kapustinUniversalGammaCarrier_ne_zero (-x)
    have hi : i ≠ 0 := by
      intro hz
      change ‖i‖ = 1 at hxInnerUnit
      rw [hz, norm_zero] at hxInnerUnit
      norm_num at hxInnerUnit
    have hphi : phi ≠ 0 := hxPhiNe
    have hq : q ≠ 0 := mul_ne_zero ha hphi
    have hfactor' : i * o = phi := hxFactor
    have hrootSq' : h ^ 2 = o := hxRootSq
    have hinnerNorm : ‖i‖ = 1 := hxInnerUnit
    have hqPhase : Complex.exp (I * (q.arg : ℂ)) = q / (‖q‖ : ℂ) := by
      have hp := Complex.norm_mul_exp_arg_mul_I q
      have hnorm : (‖q‖ : ℂ) ≠ 0 := by
        exact_mod_cast (norm_pos_iff.mpr hq).ne'
      calc
        Complex.exp (I * (q.arg : ℂ)) =
            Complex.exp ((q.arg : ℂ) * I) := by congr 1; ring
        _ = q / (‖q‖ : ℂ) := by
          field_simp [hnorm]
          simpa [mul_comm] using hp
    have hnormQ : ‖q‖ = ‖a‖ * ‖h‖ ^ 2 := by
      change ‖a * phi‖ = ‖a‖ * ‖h‖ ^ 2
      rw [← hfactor', norm_mul, norm_mul,
        hinnerNorm, one_mul, ← hrootSq', norm_pow]
    have hrootConjMul : (starRingEnd ℂ) h * h = (‖h‖ ^ 2 : ℂ) := by
      rw [Complex.conj_mul']
    rw [smirnovToeplitzSymbolMul, smirnovToeplitzSymbolMul,
      diskMultiplierPhaseReflectionSymbol, if_neg hxRootNe,
      boundedPhaseOneToeplitzSymbol]
    rw [show b (circleCayley x) = q.arg from hxPhase, hqPhase,
      kapustinOneSidedToeplitzSymbol, kapustinOneSidedToeplitzPhase]
    rw [show Complex.exp
          (((kapustinReciprocalGammaPhase x - 8 * Real.arctan x : ℝ) : ℂ) * I) =
        Complex.exp (((kapustinReciprocalGammaPhase x : ℝ) : ℂ) * I) *
          Complex.exp (((-8 * Real.arctan x : ℝ) : ℂ) * I) by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring]
    rw [← conj_realCayley_pow_four_eq_exp_neg_eight_arctan,
      ← kapustinUniversalGammaCarrier_neg_div_norm x]
    change ((starRingEnd ℂ) h / h) *
        ((starRingEnd ℂ) (realCayley x ^ 4) * (q / (‖q‖ : ℂ))) =
      (a / (‖a‖ : ℂ)) * (starRingEnd ℂ) (realCayley x ^ 4) * i
    have hqEq : q = a * phi := rfl
    rw [hnormQ, hqEq, ← hfactor', ← hrootSq']
    have hnormA : (‖a‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr ha).ne'
    have hnormH : (‖h‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr hxRootNe).ne'
    field_simp [ha, hi, hxRootNe, hnormA, hnormH]
    rw [hrootConjMul]
    push_cast
    ring
  let Kfixed : SmirnovToeplitzNPlusElement
      (smirnovToeplitzSymbolMul kapustinOneSidedToeplitzSymbol
        (diskMultiplierLineBoundary Iinner)) := KH.congr hsymbol
  exact Kfixed.cancel_right_unitBoundary Iinner hinnerUnit

/-- Negative one-sided weights give the same fixed oriented `N⁺` collision by applying the
positive branch to the literal analytic gauge `-Phi`. -/
noncomputable def kapustinSmirnovToeplitzNPlusElement_of_rotated_nonpositive
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonpos : ∀ᵐ x ∂volume, (kapustinRotatedGaugeQ Phi x).re ≤ 0) :
    SmirnovToeplitzNPlusElement kapustinOneSidedToeplitzSymbol := by
  have hPhiNeg : ∃ z ∈ ball (0 : ℂ) 1, Phi.neg.fn z ≠ 0 := by
    obtain ⟨z, hz, hne⟩ := hPhi
    exact ⟨z, hz, neg_ne_zero.mpr hne⟩
  have hnonnegNeg :
      ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi.neg x).re := by
    filter_upwards [kapustinRotatedGaugeQ_neg_ae Phi, hnonpos]
      with x hx hle
    rw [hx]
    simpa using neg_nonneg.mpr hle
  exact kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
    Phi.neg hPhiNeg hnonnegNeg

end


end RHTower
