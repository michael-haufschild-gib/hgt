import GaloisForLFunctions.HTGeometry.SmirnovToeplitzNPlus
import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiWeakPhaseBigO
import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiUpperDensity
import GaloisForLFunctions.RHTower.KapustinGaugeHardyHalfCollision

/-!
# Bounded regularization of the Kapustin half-power collision

The half-power bounded-phase witness is a quotient by the outer multiplier `1 + S`.  Clearing
that denominator turns the collision into a nonzero bounded analytic multiplier.  Its literal
phase reflection is the reciprocal-Gamma Toeplitz phase plus one uniformly bounded phase.  This
keeps the endpoint obstruction exact while avoiding the false implication `L^(1/2)loc ⊆ L¹loc`.
-/

open Complex Filter MeasureTheory Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The outer denominator in the bounded-phase construction attached to a Kapustin gauge. -/
def kapustinGaugeBoundedPhasePlus (Phi : DiskMultiplier) : DiskMultiplier :=
  boundedPhasePlus (kapustinNonnegativePhaseCircle Phi)
    (measurable_kapustinNonnegativePhaseCircle Phi)
    (abs_kapustinNonnegativePhaseCircle_le Phi)

/-- Bounded numerator obtained by clearing the outer denominator of the half-power collision. -/
def kapustinGaugeRegularizedMultiplier (Phi : DiskMultiplier) : DiskMultiplier :=
  Phi.mul (oneSubDiskMultiplierFourth.mul
    (boundedPhaseMinus (kapustinNonnegativePhaseCircle Phi)
      (measurable_kapustinNonnegativePhaseCircle Phi)
      (abs_kapustinNonnegativePhaseCircle_le Phi)))

/-- The cleared numerator remains nonzero whenever the original gauge is nonzero. -/
theorem kapustinGaugeRegularizedMultiplier_nonzero
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1,
      (kapustinGaugeRegularizedMultiplier Phi).fn z ≠ 0 := by
  let b := kapustinNonnegativePhaseCircle Phi
  let hb := measurable_kapustinNonnegativePhaseCircle Phi
  let hbound := abs_kapustinNonnegativePhaseCircle_le Phi
  let N := oneSubDiskMultiplierFourth.mul (boundedPhaseMinus b hb hbound)
  let G := boundedPhaseSmirnovToeplitzHalfElement b hb hbound
  have hN : ∃ z ∈ Metric.ball (0 : ℂ) 1, N.fn z ≠ 0 :=
    G.toSmirnovToeplitzKernelElement.forward_nonzero
  let K := (diskMultiplierSmirnovToeplitzElement Phi hPhi).mul
    (diskMultiplierSmirnovToeplitzElement N hN)
  exact K.forward_nonzero

/-- Uniformly bounded phase contributed by clearing `1 + S`. -/
def kapustinGaugeRegularizationPhase (Phi : DiskMultiplier) (x : ℝ) : ℝ :=
  2 * Complex.arg ((starRingEnd ℂ)
    (diskMultiplierLineBoundary (kapustinGaugeBoundedPhasePlus Phi) x))

theorem measurable_kapustinGaugeRegularizationPhase (Phi : DiskMultiplier) :
    Measurable (kapustinGaugeRegularizationPhase Phi) := by
  unfold kapustinGaugeRegularizationPhase
  exact measurable_const.mul (Complex.measurable_arg.comp
    (Complex.continuous_conj.measurable.comp
      (measurable_diskMultiplierLineBoundary (kapustinGaugeBoundedPhasePlus Phi))))

theorem abs_kapustinGaugeRegularizationPhase_le
    (Phi : DiskMultiplier) (x : ℝ) :
    |kapustinGaugeRegularizationPhase Phi x| ≤ 2 * Real.pi := by
  calc
    |kapustinGaugeRegularizationPhase Phi x| =
        2 * |Complex.arg ((starRingEnd ℂ)
          (diskMultiplierLineBoundary (kapustinGaugeBoundedPhasePlus Phi) x))| := by
            simp [kapustinGaugeRegularizationPhase]
    _ ≤ 2 * Real.pi :=
      mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi _) (by norm_num)

/-- The bounded regularization does not change reciprocal-Gamma superlinear phase growth. -/
theorem tendsto_kapustinToeplitzPhase_add_regularization_div_id_atTop
    (Phi : DiskMultiplier) :
    Tendsto (fun x =>
      (kapustinToeplitzPhase x + kapustinGaugeRegularizationPhase Phi x) / x)
        atTop atTop := by
  have hregularization : Tendsto (fun x =>
      kapustinGaugeRegularizationPhase Phi x / x) atTop (nhds 0) :=
    tendsto_div_atTop_zero_of_abs_le
      (fun x => abs_kapustinGaugeRegularizationPhase_le Phi x)
  have hregularization_lower : ∀ᶠ x in atTop,
      -1 < kapustinGaugeRegularizationPhase Phi x / x :=
    hregularization (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  have hmain_minus_one : Tendsto (fun x => kapustinToeplitzPhase x / x - 1)
      atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1)
        tendsto_kapustinToeplitzPhase_div_id_atTop
  refine tendsto_atTop_mono' atTop ?_ hmain_minus_one
  filter_upwards [hregularization_lower] with x hx
  rw [add_div]
  linarith

/-- No monotone-inner/weak-outer phase decomposition can absorb the bounded regularization of the
reciprocal-Gamma phase. -/
theorem noAESmirnovToeplitzWeakPhaseBigOWitness_kapustinToeplitzPhase_add_regularization
    (Phi : DiskMultiplier) :
    ¬ Nonempty (AESmirnovToeplitzWeakPhaseBigOWitness
      (fun x => kapustinToeplitzPhase x + kapustinGaugeRegularizationPhase Phi x)) :=
  not_aeSmirnovToeplitzWeakPhaseBigOWitness_of_ratio_tendsto_atTop
    (tendsto_kapustinToeplitzPhase_add_regularization_div_id_atTop Phi)

theorem kapustinGaugeBoundedPhasePlus_phaseReflection_eq_exp_ae
    (Phi : DiskMultiplier) :
    diskMultiplierPhaseReflectionSymbol (kapustinGaugeBoundedPhasePlus Phi) =ᵐ[volume]
      fun x => Complex.exp
        ((kapustinGaugeRegularizationPhase Phi x : ℂ) * I) := by
  let P := kapustinGaugeBoundedPhasePlus Phi
  have hP0 : ∃ z ∈ Metric.ball (0 : ℂ) 1, P.fn z ≠ 0 := by
    exact (isOuterDiskMultiplier_boundedPhasePlus
      (kapustinNonnegativePhaseCircle Phi)
      (measurable_kapustinNonnegativePhaseCircle Phi)
      (abs_kapustinNonnegativePhaseCircle_le Phi)).exists_nonzero
  have hP := diskMultiplierLineBoundary_ne_zero_ae P hP0
  filter_upwards [hP] with x hPx
  let p := diskMultiplierLineBoundary P x
  have hcp : (starRingEnd ℂ) p ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hPx
  rw [diskMultiplierPhaseReflectionSymbol, if_neg hPx]
  have hexp := exp_two_mul_I_mul_arg_eq_div_conj hcp
  have harg :
      ((kapustinGaugeRegularizationPhase Phi x : ℝ) : ℂ) * I =
        2 * I * (((starRingEnd ℂ) p).arg : ℂ) := by
    change (((2 * ((starRingEnd ℂ) p).arg : ℝ) : ℝ) : ℂ) * I = _
    push_cast
    ring
  rw [harg, hexp]
  simp only [starRingEnd_self_apply]
  rfl

private theorem diskMultiplierPhaseReflectionSymbol_mul_ae'
    (A B : DiskMultiplier)
    (hA : ∃ z ∈ Metric.ball (0 : ℂ) 1, A.fn z ≠ 0)
    (hB : ∃ z ∈ Metric.ball (0 : ℂ) 1, B.fn z ≠ 0) :
    diskMultiplierPhaseReflectionSymbol (A.mul B) =ᵐ[volume]
      fun x => diskMultiplierPhaseReflectionSymbol A x *
        diskMultiplierPhaseReflectionSymbol B x := by
  have hmul := diskMultiplierLineBoundary_mul_ae A B
  have hAne := diskMultiplierLineBoundary_ne_zero_ae A hA
  have hBne := diskMultiplierLineBoundary_ne_zero_ae B hB
  filter_upwards [hmul, hAne, hBne] with x hmulx hAx hBx
  have hABx : diskMultiplierLineBoundary (A.mul B) x ≠ 0 := by
    rw [hmulx]
    exact mul_ne_zero hAx hBx
  rw [diskMultiplierPhaseReflectionSymbol,
    diskMultiplierPhaseReflectionSymbol,
    diskMultiplierPhaseReflectionSymbol,
    if_neg hABx, if_neg hAx, if_neg hBx, hmulx, map_mul]
  field_simp

private theorem boundedPhaseNumerator_phaseReflection_ae
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    diskMultiplierPhaseReflectionSymbol
        (oneSubDiskMultiplierFourth.mul (boundedPhaseMinus b hb hbound)) =ᵐ[volume]
      fun x => boundedPhaseToeplitzSymbol b x *
        diskMultiplierPhaseReflectionSymbol (boundedPhasePlus b hb hbound) x := by
  let N := oneSubDiskMultiplierFourth.mul (boundedPhaseMinus b hb hbound)
  let P := boundedPhasePlus b hb hbound
  let K := boundedPhaseSmirnovToeplitzHalfElement b hb hbound
  have hN0 : ∃ z ∈ Metric.ball (0 : ℂ) 1, N.fn z ≠ 0 :=
    K.toSmirnovToeplitzKernelElement.forward_nonzero
  have hP0 : ∃ z ∈ Metric.ball (0 : ℂ) 1, P.fn z ≠ 0 :=
    (isOuterDiskMultiplier_boundedPhasePlus b hb hbound).exists_nonzero
  have hN := diskMultiplierLineBoundary_ne_zero_ae N hN0
  have hP := diskMultiplierLineBoundary_ne_zero_ae P hP0
  filter_upwards [K.toSmirnovToeplitzKernelElement.boundary_relation, hN, hP]
      with x hrel hNx hPx
  have hconjP : (starRingEnd ℂ) (diskMultiplierLineBoundary P x) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hPx
  rw [diskMultiplierPhaseReflectionSymbol,
    diskMultiplierPhaseReflectionSymbol, if_neg hNx, if_neg hPx]
  change diskMultiplierLineBoundary N x / diskMultiplierLineBoundary P x =
    (starRingEnd ℂ) (boundedPhaseToeplitzSymbol b x) *
      (starRingEnd ℂ)
        (diskMultiplierLineBoundary N x / diskMultiplierLineBoundary P x) at hrel
  have hc := congrArg (starRingEnd ℂ) hrel
  simp only [map_div₀, map_mul, starRingEnd_self_apply] at hc
  calc
    (starRingEnd ℂ) (diskMultiplierLineBoundary N x) /
        diskMultiplierLineBoundary N x =
      ((starRingEnd ℂ) (diskMultiplierLineBoundary N x) /
          (starRingEnd ℂ) (diskMultiplierLineBoundary P x)) *
        ((starRingEnd ℂ) (diskMultiplierLineBoundary P x) /
          diskMultiplierLineBoundary N x) := by
            field_simp
    _ = (boundedPhaseToeplitzSymbol b x *
          (diskMultiplierLineBoundary N x /
            diskMultiplierLineBoundary P x)) *
        ((starRingEnd ℂ) (diskMultiplierLineBoundary P x) /
          diskMultiplierLineBoundary N x) := by rw [hc]
    _ = boundedPhaseToeplitzSymbol b x *
        ((starRingEnd ℂ) (diskMultiplierLineBoundary P x) /
          diskMultiplierLineBoundary P x) := by
            field_simp

/-- Clearing the outer denominator converts the collision into the literal phase reflection of
one nonzero bounded analytic multiplier. -/
theorem kapustinGaugeRegularizedMultiplier_phaseReflection_ae
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    diskMultiplierPhaseReflectionSymbol (kapustinGaugeRegularizedMultiplier Phi) =ᵐ[volume]
      fun x => kapustinToeplitzSymbol x *
        diskMultiplierPhaseReflectionSymbol (kapustinGaugeBoundedPhasePlus Phi) x := by
  let b := kapustinNonnegativePhaseCircle Phi
  let hb := measurable_kapustinNonnegativePhaseCircle Phi
  let hbound := abs_kapustinNonnegativePhaseCircle_le Phi
  let N := oneSubDiskMultiplierFourth.mul (boundedPhaseMinus b hb hbound)
  have hN : ∃ z ∈ Metric.ball (0 : ℂ) 1, N.fn z ≠ 0 :=
    (boundedPhaseSmirnovToeplitzHalfElement b hb hbound).toSmirnovToeplitzKernelElement.forward_nonzero
  have hmul := diskMultiplierPhaseReflectionSymbol_mul_ae' Phi N hPhi hN
  have hNphase := boundedPhaseNumerator_phaseReflection_ae b hb hbound
  have hcollision := kapustinGauge_boundedPhase_symbol_eq_ae Phi hPhi hnonneg
  filter_upwards [hmul, hNphase, hcollision] with x hmulx hNphasex hcollisionx
  change diskMultiplierPhaseReflectionSymbol (Phi.mul N) x =
    kapustinToeplitzSymbol x *
      diskMultiplierPhaseReflectionSymbol (boundedPhasePlus b hb hbound) x
  rw [hmulx, hNphasex]
  change diskMultiplierPhaseReflectionSymbol Phi x * boundedPhaseToeplitzSymbol b x =
    kapustinToeplitzSymbol x at hcollisionx
  calc
    diskMultiplierPhaseReflectionSymbol Phi x *
        (boundedPhaseToeplitzSymbol b x *
          diskMultiplierPhaseReflectionSymbol (boundedPhasePlus b hb hbound) x) =
      (diskMultiplierPhaseReflectionSymbol Phi x * boundedPhaseToeplitzSymbol b x) *
        diskMultiplierPhaseReflectionSymbol (boundedPhasePlus b hb hbound) x := by ring
    _ = kapustinToeplitzSymbol x *
        diskMultiplierPhaseReflectionSymbol (boundedPhasePlus b hb hbound) x := by
          rw [hcollisionx]

/-- The regularized bounded multiplier has the reciprocal-Gamma phase plus a uniformly bounded
measurable phase, with no branch ambiguity left in the exponential identity. -/
theorem kapustinGaugeRegularizedMultiplier_phase_eq_exp_ae
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    diskMultiplierPhaseReflectionSymbol (kapustinGaugeRegularizedMultiplier Phi) =ᵐ[volume]
      fun x => Complex.exp
        (((kapustinToeplitzPhase x + kapustinGaugeRegularizationPhase Phi x : ℝ) : ℂ) * I) := by
  have hregularized :=
    kapustinGaugeRegularizedMultiplier_phaseReflection_ae Phi hPhi hnonneg
  have hplus := kapustinGaugeBoundedPhasePlus_phaseReflection_eq_exp_ae Phi
  filter_upwards [hregularized, hplus] with x hx hpx
  rw [hx, hpx, kapustinToeplitzSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact `N⁺` witness for the boundedly regularized reciprocal-Gamma phase. -/
noncomputable def kapustinGaugeRegularizedNPlusElement
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0) :
    SmirnovToeplitzNPlusElement
      (diskMultiplierPhaseReflectionSymbol (kapustinGaugeRegularizedMultiplier Phi)) :=
  diskMultiplierSmirnovToeplitzNPlusElement
    (kapustinGaugeRegularizedMultiplier Phi)
    (kapustinGaugeRegularizedMultiplier_nonzero Phi hPhi)

end

end RHTower
