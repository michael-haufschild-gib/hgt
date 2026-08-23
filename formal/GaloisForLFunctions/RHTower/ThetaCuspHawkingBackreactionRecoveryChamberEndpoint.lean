import GaloisForLFunctions.RHTower.ThetaCuspHawkingBackreactionCubicCompletionEndpoint

/-!
# Theta-Hawking passive-recovery chamber

The preceding cubic-completion endpoint identifies the conditional-independence edge

`r* = K_xy K_yz / K_yy`

and proves the exact repair identity

`D(r*) - D(r) = K_yy (r* - r)^2`.

Dempster covariance selection and Gaussian/Petz recovery explain `r*` as the unique
maximum-determinant (maximum-entropy) completion.  That literature does not prove a Hawking system
saturates strong subadditivity, so exact selection of \`r*\` cannot be assumed.

This endpoint extracts the stronger unconditional conclusion that does not require saturation.
Whenever the raw cubic is negative and any repaired edge is passive, the repaired edge has strictly
smaller squared distance to `r*` than the raw edge.  Its correction is positively oriented toward
`r*`.  Thus every passive backreaction—not only maximum-entropy completion—must create directed
remote-shell mixing.

The entire chamber is classified by one quadratic inequality.  An affine repair of strength
`s` has exact determinant gain

`K_yy s (2-s) (r* - r)^2`

and strengths compose by `s₁ + s₂ - s₁s₂`.  This supplies a canonical nonperturbative recovery
flow, while keeping the physical open core honest: actual nonlinear theta-mirror dynamics must
produce some chamber-entering contraction, but need not select the maximum-entropy center exactly.
The final theorems specialize this classification to the genuine selective modular gain and the
actual rank-one causal Hardy Hawking scattering dilation.
-/

namespace RHTower

noncomputable section

theorem symmetricThreePointLongEdgeDet_nonneg_iff_passiveDistance
    (K : ℝ → ℝ → ℝ) {x y z r : ℝ} (hy : 0 < K y y) :
    0 ≤ symmetricThreePointLongEdgeDet K x y z r ↔
      K y y * (threePointPassiveLongEdge K x y z - r) ^ 2 ≤
        symmetricThreePointLongEdgeDet K x y z
          (threePointPassiveLongEdge K x y z) := by
  have hrepair :=
    symmetricThreePointLongEdgeDet_passive_sub_eq_sq K
      (x := x) (y := y) (z := z) (r := r) hy.ne'
  constructor <;> intro h <;> linarith

theorem threePointPassiveLongEdge_maximizes_det
    (K : ℝ → ℝ → ℝ) {x y z r : ℝ} (hy : 0 < K y y) :
    symmetricThreePointLongEdgeDet K x y z r ≤
      symmetricThreePointLongEdgeDet K x y z
        (threePointPassiveLongEdge K x y z) := by
  have hrepair := symmetricThreePointLongEdgeDet_passive_sub_eq_sq K
    (x := x) (y := y) (z := z) (r := r) hy.ne'
  nlinarith [mul_nonneg hy.le (sq_nonneg (threePointPassiveLongEdge K x y z - r))]

theorem threePointPassiveLongEdge_unique_maximizer
    (K : ℝ → ℝ → ℝ) {x y z r : ℝ} (hy : 0 < K y y) :
    symmetricThreePointLongEdgeDet K x y z r =
        symmetricThreePointLongEdgeDet K x y z
          (threePointPassiveLongEdge K x y z) ↔
      r = threePointPassiveLongEdge K x y z := by
  have hrepair :=
    symmetricThreePointLongEdgeDet_passive_sub_eq_sq K
      (x := x) (y := y) (z := z) (r := r) hy.ne'
  constructor
  · intro heq
    have hzero : K y y * (threePointPassiveLongEdge K x y z - r) ^ 2 = 0 := by
      linarith
    have hsquare : (threePointPassiveLongEdge K x y z - r) ^ 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hy.ne'
    nlinarith
  · rintro rfl
    rfl

theorem negativeLongEdge_to_passive_squaredDistance_lt
    (K : ℝ → ℝ → ℝ) {x y z raw repaired : ℝ}
    (hy : 0 < K y y)
    (hraw : symmetricThreePointLongEdgeDet K x y z raw < 0)
    (hrepaired : 0 ≤ symmetricThreePointLongEdgeDet K x y z repaired) :
    (repaired - threePointPassiveLongEdge K x y z) ^ 2 <
      (raw - threePointPassiveLongEdge K x y z) ^ 2 := by
  have hrawRepair :=
    symmetricThreePointLongEdgeDet_passive_sub_eq_sq K
      (x := x) (y := y) (z := z) (r := raw) hy.ne'
  have hrepairedRepair :=
    symmetricThreePointLongEdgeDet_passive_sub_eq_sq K
      (x := x) (y := y) (z := z) (r := repaired) hy.ne'
  nlinarith

theorem negativeLongEdge_to_passive_correction_oriented
    (K : ℝ → ℝ → ℝ) {x y z raw repaired : ℝ}
    (hy : 0 < K y y)
    (hraw : symmetricThreePointLongEdgeDet K x y z raw < 0)
    (hrepaired : 0 ≤ symmetricThreePointLongEdgeDet K x y z repaired) :
    0 < (repaired - raw) *
      (threePointPassiveLongEdge K x y z - raw) := by
  have hsq := negativeLongEdge_to_passive_squaredDistance_lt K hy hraw hrepaired
  nlinarith [sq_nonneg
    ((raw - threePointPassiveLongEdge K x y z) -
      (repaired - threePointPassiveLongEdge K x y z))]

def threePointAffineBackreactionEdge
    (K : ℝ → ℝ → ℝ) (x y z strength raw : ℝ) : ℝ :=
  raw + strength * (threePointPassiveLongEdge K x y z - raw)

@[simp] theorem threePointAffineBackreactionEdge_zero
    (K : ℝ → ℝ → ℝ) (x y z raw : ℝ) :
    threePointAffineBackreactionEdge K x y z 0 raw = raw := by
  simp [threePointAffineBackreactionEdge]

@[simp] theorem threePointAffineBackreactionEdge_one
    (K : ℝ → ℝ → ℝ) (x y z raw : ℝ) :
    threePointAffineBackreactionEdge K x y z 1 raw =
      threePointPassiveLongEdge K x y z := by
  simp [threePointAffineBackreactionEdge]

theorem threePointAffineBackreactionEdge_comp
    (K : ℝ → ℝ → ℝ) (x y z strength₁ strength₂ raw : ℝ) :
    threePointAffineBackreactionEdge K x y z strength₂
        (threePointAffineBackreactionEdge K x y z strength₁ raw) =
      threePointAffineBackreactionEdge K x y z
        (strength₁ + strength₂ - strength₁ * strength₂) raw := by
  unfold threePointAffineBackreactionEdge
  ring

theorem symmetricThreePointLongEdgeDet_affineBackreaction_sub_eq
    (K : ℝ → ℝ → ℝ) {x y z strength raw : ℝ} (hy : K y y ≠ 0) :
    symmetricThreePointLongEdgeDet K x y z
        (threePointAffineBackreactionEdge K x y z strength raw) -
      symmetricThreePointLongEdgeDet K x y z raw =
    K y y * strength * (2 - strength) *
      (threePointPassiveLongEdge K x y z - raw) ^ 2 := by
  have hraw :=
    symmetricThreePointLongEdgeDet_passive_sub_eq_sq K
      (x := x) (y := y) (z := z) (r := raw) hy
  have hnew := symmetricThreePointLongEdgeDet_passive_sub_eq_sq K
    (x := x) (y := y) (z := z)
    (r := threePointAffineBackreactionEdge K x y z strength raw) hy
  calc
    symmetricThreePointLongEdgeDet K x y z
          (threePointAffineBackreactionEdge K x y z strength raw) -
        symmetricThreePointLongEdgeDet K x y z raw =
      (symmetricThreePointLongEdgeDet K x y z
          (threePointPassiveLongEdge K x y z) -
        symmetricThreePointLongEdgeDet K x y z raw) -
      (symmetricThreePointLongEdgeDet K x y z
          (threePointPassiveLongEdge K x y z) -
        symmetricThreePointLongEdgeDet K x y z
          (threePointAffineBackreactionEdge K x y z strength raw)) := by ring
    _ = K y y * (threePointPassiveLongEdge K x y z - raw) ^ 2 -
        K y y * (threePointPassiveLongEdge K x y z -
          threePointAffineBackreactionEdge K x y z strength raw) ^ 2 := by
      rw [hraw, hnew]
    _ = K y y * strength * (2 - strength) *
        (threePointPassiveLongEdge K x y z - raw) ^ 2 := by
      unfold threePointAffineBackreactionEdge
      ring

theorem symmetricThreePointLongEdgeDet_affineBackreaction_strictlyImproves
    (K : ℝ → ℝ → ℝ) {x y z strength raw : ℝ}
    (hy : 0 < K y y) (hstrength : 0 < strength) (hstrengthOne : strength ≤ 1)
    (hraw : raw ≠ threePointPassiveLongEdge K x y z) :
    symmetricThreePointLongEdgeDet K x y z raw <
      symmetricThreePointLongEdgeDet K x y z
        (threePointAffineBackreactionEdge K x y z strength raw) := by
  rw [← sub_pos, symmetricThreePointLongEdgeDet_affineBackreaction_sub_eq K hy.ne']
  have htwo : 0 < 2 - strength := by linarith
  exact mul_pos (mul_pos (mul_pos hy hstrength) htwo)
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hraw.symm))

def thetaCuspHawkingAffineBackreactionEdge
    (q : XiZeroCopy) (rapidity x y z strength : ℝ) : ℝ :=
  threePointAffineBackreactionEdge
    (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z strength
    (thetaCuspHawkingSelectiveModularGainKernel q rapidity x z)

theorem thetaCuspHawking_passiveRepair_squaredDistance_lt
    (q : XiZeroCopy) (rapidity : ℝ) {x y z repaired : ℝ}
    (hx : 0 < x) (hxy : x < y)
    (hraw : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0)
    (hrepaired : 0 ≤ symmetricThreePointLongEdgeDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z repaired) :
    (repaired - thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z) ^ 2 <
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity x z -
        thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z) ^ 2 := by
  apply negativeLongEdge_to_passive_squaredDistance_lt
  · exact xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) (hx.trans hxy)
  · rwa [← symmetricThreePointDet_eq_longEdgeDet]
  · exact hrepaired

theorem thetaCuspHawking_passiveRepair_correction_oriented
    (q : XiZeroCopy) (rapidity : ℝ) {x y z repaired : ℝ}
    (hx : 0 < x) (hxy : x < y)
    (hraw : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0)
    (hrepaired : 0 ≤ symmetricThreePointLongEdgeDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z repaired) :
    0 < (repaired -
        thetaCuspHawkingSelectiveModularGainKernel q rapidity x z) *
      (thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z -
        thetaCuspHawkingSelectiveModularGainKernel q rapidity x z) := by
  apply negativeLongEdge_to_passive_correction_oriented
  · exact xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) (hx.trans hxy)
  · rwa [← symmetricThreePointDet_eq_longEdgeDet]
  · exact hrepaired

theorem thetaCuspHawking_affineBackreaction_strictlyImproves
    (q : XiZeroCopy) (rapidity : ℝ) {x y z strength : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hstrength : 0 < strength) (hstrengthOne : strength ≤ 1)
    (hraw : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0) :
    symmetricThreePointDet
        (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z <
      symmetricThreePointLongEdgeDet
        (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z
        (thetaCuspHawkingAffineBackreactionEdge q rapidity x y z strength) := by
  rw [symmetricThreePointDet_eq_longEdgeDet]
  apply symmetricThreePointLongEdgeDet_affineBackreaction_strictlyImproves
  · exact xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) (hx.trans hxy)
  · exact hstrength
  · exact hstrengthOne
  · exact thetaCuspHawking_negativeCubic_forces_backreaction_mixing
      q rapidity hx hxy hyz hraw

theorem thetaCuspHawkingCausalHardy_passiveRepair_forces_contraction
    (q : XiZeroCopy)
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im)
    (horient : mode = thetaCuspHawkingXiOrbitResonantMode q ∨
      mode = thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q))
    (rapidity : ℝ) {x y z repaired : ℝ}
    (hx : 0 < x) (hxy : x < y)
    (hraw : symmetricThreePointDet
      (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity) x y z < 0)
    (hrepaired : 0 ≤ symmetricThreePointLongEdgeDet
      (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity)
        x y z repaired) :
    (repaired - thetaCuspHawkingCausalHardyPassiveBackreactionEdge
        mode hmode rapidity x y z) ^ 2 <
      (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity x z -
        thetaCuspHawkingCausalHardyPassiveBackreactionEdge
          mode hmode rapidity x y z) ^ 2 ∧
    0 < (repaired -
        thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity x z) *
      (thetaCuspHawkingCausalHardyPassiveBackreactionEdge
          mode hmode rapidity x y z -
        thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity x z) := by
  unfold thetaCuspHawkingCausalHardyPassiveBackreactionEdge
  rw [thetaCuspHawkingCausalHardyStimulatedKernel_eq_selectiveModularGainKernel
      q mode hmode horient rapidity] at hraw hrepaired ⊢
  exact ⟨thetaCuspHawking_passiveRepair_squaredDistance_lt
      q rapidity hx hxy hraw hrepaired,
    thetaCuspHawking_passiveRepair_correction_oriented
      q rapidity hx hxy hraw hrepaired⟩

theorem exists_thetaCuspHawking_eventually_everyPassiveRepair_contracts
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ R : ℝ, ∀ rapidity : ℝ, R ≤ rapidity → ∀ repaired : ℝ,
      0 ≤ symmetricThreePointLongEdgeDet
          (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z repaired →
        (repaired - thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z) ^ 2 <
          (thetaCuspHawkingSelectiveModularGainKernel q rapidity x z -
            thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z) ^ 2 ∧
        0 < (repaired -
            thetaCuspHawkingSelectiveModularGainKernel q rapidity x z) *
          (thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z -
            thetaCuspHawkingSelectiveModularGainKernel q rapidity x z) := by
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz
  refine ⟨R, fun rapidity hrapidity repaired hrepaired => ?_⟩
  have hraw := hR rapidity hrapidity
  exact ⟨thetaCuspHawking_passiveRepair_squaredDistance_lt
      q rapidity hx hxy hraw hrepaired,
    thetaCuspHawking_passiveRepair_correction_oriented
      q rapidity hx hxy hraw hrepaired⟩

end

end RHTower
