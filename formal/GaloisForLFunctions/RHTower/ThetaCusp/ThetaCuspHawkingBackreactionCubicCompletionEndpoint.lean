import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingCausalHardyDefectScatteringEndpoint

/-!
# Theta-Hawking backreaction cubic completion

This endpoint isolates the first passivity law that is both coefficient-faithful to the completed
theta/Xi divisor and attached to the actual causal Hardy Hawking scattering dilation.

A selective Hawking modular gain reweights one real Xi resonance response by
`lambda = cosh(r)^(2 : ℕ) >= 1`.  Complete and selected-orbit radial responses both decrease strictly,
while their radius-weighted responses increase strictly.  Hence every adjacent two-shell minor
remains strictly positive at every rapidity, even when an off-critical orbit eventually drives the
raw three-shell determinant negative.

For three shells, preserving diagonals and adjacent response edges leaves a canonical passive
long edge

`K_xz^* = K_xy K_yz / K_yy`.

Its quadratic energy is a sum of three nonnegative Schur squares, and its determinant factors as

`det K^* = det K_{xy} det K_{yz} / K_yy > 0`.

Thus a negative raw cubic cannot survive this completion.  More sharply, negative raw cubic forces
`K_xz != K_xz^*`: any passive backreaction preserving the local and adjacent theta responses must
create nonzero remote-sector mixing.  The determinant repair cost is exactly
`K_yy (K_xz^* - K_xz)^(2 : ℕ)`.

Generic KMS, CCR, group, inverse, and Krein identities enter only through the already-derived
scattering dilation and do not imply this cubic sign.  Theta-divisor chamber inequalities supply
the two strict adjacent minors.  This endpoint does not assert that nonlinear Hawking dynamics
selects the canonical completion.

`[PHYSICAL STATUS]` `ThetaCuspHawkingEKGNonlinearTailSignNoGo` now evaluates a genuine spherical
Einstein--Klein--Gordon cubic backreaction coefficient on the literal theta source and proves it
strictly negative.  That coefficient is not this three-shell determinant, so the algebra below
remains correct; however, positive stress energy/passivity cannot select this completion by sign
alone.  A coefficient-level incidence between Schwarzschild EKG/second-order Teukolsky dynamics
and this determinant would be required before the completion could become an RH-bearing producer.
-/

open Set

namespace RHTower

noncomputable section

def xiSquaredEulerReweightedFullResponse
    (q : XiZeroCopy) (lambda u : ℝ) : ℝ :=
  xiSquaredEulerFullResponse u +
    (lambda - 1) * xiSquaredEulerOrbitResponse q u

def xiSquaredEulerReweightedFullQ
    (q : XiZeroCopy) (lambda x : ℝ) : ℝ :=
  x * xiSquaredEulerReweightedFullResponse q lambda (x ^ (2 : ℕ))

theorem xiSquaredEulerReweightedFullKernel_eq_responseKernel
    (q : XiZeroCopy) (lambda : ℝ) :
    xiSquaredEulerReweightedFullKernel q lambda =
      eulerRayResponseKernel (xiSquaredEulerReweightedFullQ q lambda) := by
  funext x y
  rw [xiSquaredEulerReweightedFullKernel, xiSquaredEulerFullKernel,
    xiSquaredEulerOrbitKernel, squaredEulerOrbitKernel]
  simp only [eulerRayResponseKernel, xiSquaredEulerFullQ,
    xiSquaredEulerReweightedFullQ, xiSquaredEulerReweightedFullResponse,
    squaredEulerOrbitQ, xiSquaredEulerOrbitResponse]
  ring

theorem xiSquaredEulerReweightedFullResponse_pos
    (q : XiZeroCopy) {lambda u : ℝ} (hlambda : 1 ≤ lambda) (hu : 0 ≤ u) :
    0 < xiSquaredEulerReweightedFullResponse q lambda u := by
  have hfull := xiSquaredEulerFullResponse_pos hu
  have horbit := xiSquaredEulerOrbitResponse_pos q hu
  have hweight : 0 ≤ lambda - 1 := sub_nonneg.mpr hlambda
  rw [xiSquaredEulerReweightedFullResponse]
  positivity

theorem strictAntiOn_xiSquaredEulerReweightedFullResponse
    (q : XiZeroCopy) {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    StrictAntiOn (xiSquaredEulerReweightedFullResponse q lambda) (Ici 0) := by
  intro u hu v hv huv
  have hfull := strictAntiOn_xiSquaredEulerFullResponse hu hv huv
  have horbit := strictAntiOn_xiSquaredEulerOrbitResponse q hu hv huv
  have hweight : 0 ≤ lambda - 1 := sub_nonneg.mpr hlambda
  rw [xiSquaredEulerReweightedFullResponse,
    xiSquaredEulerReweightedFullResponse]
  nlinarith [mul_nonneg hweight (sub_nonneg.mpr horbit.le)]

theorem strictMonoOn_mul_xiSquaredEulerReweightedFullResponse
    (q : XiZeroCopy) {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    StrictMonoOn
      (fun u => u * xiSquaredEulerReweightedFullResponse q lambda u) (Ici 0) := by
  intro u hu v hv huv
  have hfull := strictMonoOn_mul_xiSquaredEulerFullResponse hu hv huv
  have horbit := strictMonoOn_mul_xiSquaredEulerOrbitResponse q hu hv huv
  have hweight : 0 ≤ lambda - 1 := sub_nonneg.mpr hlambda
  change u * (xiSquaredEulerFullResponse u +
      (lambda - 1) * xiSquaredEulerOrbitResponse q u) <
    v * (xiSquaredEulerFullResponse v +
      (lambda - 1) * xiSquaredEulerOrbitResponse q v)
  nlinarith [mul_nonneg hweight (sub_nonneg.mpr horbit.le)]

theorem xiSquaredEulerReweightedFullKernel_diag_pos
    (q : XiZeroCopy) {lambda x : ℝ} (hlambda : 1 ≤ lambda) (hx : 0 < x) :
    0 < xiSquaredEulerReweightedFullKernel q lambda x x := by
  rw [xiSquaredEulerReweightedFullKernel_eq_responseKernel,
    eulerRayResponseKernel, xiSquaredEulerReweightedFullQ]
  have hresponse := xiSquaredEulerReweightedFullResponse_pos q hlambda (sq_nonneg x)
  field_simp [hx.ne']
  nlinarith

theorem xiSquaredEulerReweightedFullKernel_twoPoint_det_pos
    (q : XiZeroCopy) {lambda x y : ℝ} (hlambda : 1 ≤ lambda)
    (hx : 0 < x) (hxy : x < y) :
    0 < xiSquaredEulerReweightedFullKernel q lambda x x *
        xiSquaredEulerReweightedFullKernel q lambda y y -
      xiSquaredEulerReweightedFullKernel q lambda x y ^ (2 : ℕ) := by
  have hy : 0 < y := hx.trans hxy
  have hsq : x ^ (2 : ℕ) < y ^ (2 : ℕ) := by nlinarith
  have hdecreaseProfile :=
    strictAntiOn_xiSquaredEulerReweightedFullResponse q hlambda
      (sq_nonneg x) (sq_nonneg y) hsq
  have hincreaseProfile :=
    strictMonoOn_mul_xiSquaredEulerReweightedFullResponse q hlambda
      (sq_nonneg x) (sq_nonneg y) hsq
  have hdecrease :
      xiSquaredEulerReweightedFullQ q lambda y / y <
        xiSquaredEulerReweightedFullQ q lambda x / x := by
    simpa [xiSquaredEulerReweightedFullQ, hx.ne', hy.ne'] using hdecreaseProfile
  have hincrease :
      x * xiSquaredEulerReweightedFullQ q lambda x <
        y * xiSquaredEulerReweightedFullQ q lambda y := by
    simpa [xiSquaredEulerReweightedFullQ, pow_two, mul_assoc] using hincreaseProfile
  rw [xiSquaredEulerReweightedFullKernel_eq_responseKernel]
  exact eulerRayResponseKernel_twoPoint_det_pos
    (xiSquaredEulerReweightedFullQ q lambda) hx hxy hdecrease hincrease

def threePointPassiveLongEdge
    (K : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  K x y * K y z / K y y

def symmetricThreePointLongEdgeDet
    (K : ℝ → ℝ → ℝ) (x y z r : ℝ) : ℝ :=
  K x x * K y y * K z z + 2 * K x y * r * K y z -
    K x x * K y z ^ (2 : ℕ) - K y y * r ^ (2 : ℕ) - K z z * K x y ^ (2 : ℕ)

theorem symmetricThreePointDet_eq_longEdgeDet
    (K : ℝ → ℝ → ℝ) (x y z : ℝ) :
    symmetricThreePointDet K x y z =
      symmetricThreePointLongEdgeDet K x y z (K x z) := by
  rfl

theorem symmetricThreePointLongEdgeDet_passive_factor
    (K : ℝ → ℝ → ℝ) {x y z : ℝ} (hy : K y y ≠ 0) :
    symmetricThreePointLongEdgeDet K x y z
        (threePointPassiveLongEdge K x y z) =
      ((K x x * K y y - K x y ^ (2 : ℕ)) *
        (K y y * K z z - K y z ^ (2 : ℕ))) / K y y := by
  rw [symmetricThreePointLongEdgeDet, threePointPassiveLongEdge]
  field_simp [hy]
  ring

theorem symmetricThreePointLongEdgeDet_passive_pos
    (K : ℝ → ℝ → ℝ) {x y z : ℝ}
    (hy : 0 < K y y)
    (hxy : 0 < K x x * K y y - K x y ^ (2 : ℕ))
    (hyz : 0 < K y y * K z z - K y z ^ (2 : ℕ)) :
    0 < symmetricThreePointLongEdgeDet K x y z
      (threePointPassiveLongEdge K x y z) := by
  rw [symmetricThreePointLongEdgeDet_passive_factor K hy.ne']
  exact div_pos (mul_pos hxy hyz) hy

def symmetricThreePointLongEdgeEnergy
    (K : ℝ → ℝ → ℝ) (x y z r a b c : ℝ) : ℝ :=
  K x x * a ^ (2 : ℕ) + K y y * b ^ (2 : ℕ) + K z z * c ^ (2 : ℕ) +
    2 * K x y * a * b + 2 * K y z * b * c + 2 * r * a * c

theorem symmetricThreePointLongEdgeEnergy_passive_factor
    (K : ℝ → ℝ → ℝ) {x y z a b c : ℝ} (hy : K y y ≠ 0) :
    symmetricThreePointLongEdgeEnergy K x y z
        (threePointPassiveLongEdge K x y z) a b c =
      K y y * (b + K x y * a / K y y + K y z * c / K y y) ^ (2 : ℕ) +
        (K x x - K x y ^ (2 : ℕ) / K y y) * a ^ (2 : ℕ) +
        (K z z - K y z ^ (2 : ℕ) / K y y) * c ^ (2 : ℕ) := by
  rw [symmetricThreePointLongEdgeEnergy, threePointPassiveLongEdge]
  field_simp [hy]
  ring

theorem symmetricThreePointLongEdgeEnergy_passive_nonneg
    (K : ℝ → ℝ → ℝ) {x y z a b c : ℝ}
    (hy : 0 < K y y)
    (hxy : 0 < K x x * K y y - K x y ^ (2 : ℕ))
    (hyz : 0 < K y y * K z z - K y z ^ (2 : ℕ)) :
    0 ≤ symmetricThreePointLongEdgeEnergy K x y z
      (threePointPassiveLongEdge K x y z) a b c := by
  rw [symmetricThreePointLongEdgeEnergy_passive_factor K hy.ne']
  have hleft : 0 < K x x - K x y ^ (2 : ℕ) / K y y := by
    rw [show K x x - K x y ^ (2 : ℕ) / K y y =
      (K x x * K y y - K x y ^ (2 : ℕ)) / K y y by field_simp]
    exact div_pos hxy hy
  have hright : 0 < K z z - K y z ^ (2 : ℕ) / K y y := by
    rw [show K z z - K y z ^ (2 : ℕ) / K y y =
      (K y y * K z z - K y z ^ (2 : ℕ)) / K y y by field_simp]
    exact div_pos hyz hy
  positivity

theorem symmetricThreePointLongEdgeDet_repair_identity
    (K : ℝ → ℝ → ℝ) (x y z r : ℝ) :
    symmetricThreePointLongEdgeDet K x y z
        (threePointPassiveLongEdge K x y z) -
      symmetricThreePointLongEdgeDet K x y z r =
    (threePointPassiveLongEdge K x y z - r) *
      (2 * K x y * K y z - 2 * K y y * r -
        K y y * (threePointPassiveLongEdge K x y z - r)) := by
  rw [symmetricThreePointLongEdgeDet, symmetricThreePointLongEdgeDet]
  ring

theorem symmetricThreePointLongEdgeDet_passive_sub_eq_sq
    (K : ℝ → ℝ → ℝ) {x y z r : ℝ} (hy : K y y ≠ 0) :
    symmetricThreePointLongEdgeDet K x y z
        (threePointPassiveLongEdge K x y z) -
      symmetricThreePointLongEdgeDet K x y z r =
    K y y * (threePointPassiveLongEdge K x y z - r) ^ (2 : ℕ) := by
  rw [symmetricThreePointLongEdgeDet, symmetricThreePointLongEdgeDet,
    threePointPassiveLongEdge]
  field_simp [hy]
  ring

def thetaCuspHawkingPassiveBackreactionEdge
    (q : XiZeroCopy) (r x y z : ℝ) : ℝ :=
  threePointPassiveLongEdge
    (thetaCuspHawkingSelectiveModularGainKernel q r) x y z

def thetaCuspHawkingCausalHardyPassiveBackreactionEdge
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r x y z : ℝ) : ℝ :=
  threePointPassiveLongEdge
    (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode r) x y z

theorem thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos
    (q : XiZeroCopy) (r : ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < thetaCuspHawkingSelectiveModularGainKernel q r x x *
        thetaCuspHawkingSelectiveModularGainKernel q r y y -
      thetaCuspHawkingSelectiveModularGainKernel q r x y ^ (2 : ℕ) := by
  exact xiSquaredEulerReweightedFullKernel_twoPoint_det_pos q
    (thetaCuspHawkingModularGain_one_le r) hx hxy

theorem thetaCuspHawkingPassiveBackreaction_cubic_pos
    (q : XiZeroCopy) (r : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    0 < symmetricThreePointLongEdgeDet
      (thetaCuspHawkingSelectiveModularGainKernel q r) x y z
      (thetaCuspHawkingPassiveBackreactionEdge q r x y z) := by
  apply symmetricThreePointLongEdgeDet_passive_pos
  · exact xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le r) (hx.trans hxy)
  · exact thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos q r hx hxy
  · exact thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos q r
      (hx.trans hxy) hyz

theorem thetaCuspHawkingPassiveBackreaction_energy_nonneg
    (q : XiZeroCopy) (r : ℝ) {x y z a b c : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    0 ≤ symmetricThreePointLongEdgeEnergy
      (thetaCuspHawkingSelectiveModularGainKernel q r) x y z
      (thetaCuspHawkingPassiveBackreactionEdge q r x y z) a b c := by
  apply symmetricThreePointLongEdgeEnergy_passive_nonneg
  · exact xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le r) (hx.trans hxy)
  · exact thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos q r hx hxy
  · exact thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos q r
      (hx.trans hxy) hyz

theorem thetaCuspHawking_negativeCubic_forces_backreaction_mixing
    (q : XiZeroCopy) (r : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hneg : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q r) x y z < 0) :
    thetaCuspHawkingSelectiveModularGainKernel q r x z ≠
      thetaCuspHawkingPassiveBackreactionEdge q r x y z := by
  intro heq
  have hpos := thetaCuspHawkingPassiveBackreaction_cubic_pos q r hx hxy hyz
  rw [← heq, ← symmetricThreePointDet_eq_longEdgeDet] at hpos
  linarith

theorem thetaCuspHawking_negativeCubic_backreactionCost_pos
    (q : XiZeroCopy) (r : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hneg : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q r) x y z < 0) :
    0 < thetaCuspHawkingSelectiveModularGainKernel q r y y *
      (thetaCuspHawkingPassiveBackreactionEdge q r x y z -
        thetaCuspHawkingSelectiveModularGainKernel q r x z) ^ (2 : ℕ) := by
  have hypos := xiSquaredEulerReweightedFullKernel_diag_pos q
    (thetaCuspHawkingModularGain_one_le r) (hx.trans hxy)
  have hne :=
    thetaCuspHawking_negativeCubic_forces_backreaction_mixing
      q r hx hxy hyz hneg
  exact mul_pos hypos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne.symm))

theorem thetaCuspHawkingCausalHardy_passiveBackreaction_cubic_pos
    (q : XiZeroCopy)
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im)
    (horient : mode = thetaCuspHawkingXiOrbitResonantMode q ∨
      mode = thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q))
    (r : ℝ) {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    0 < symmetricThreePointLongEdgeDet
      (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode r) x y z
      (thetaCuspHawkingCausalHardyPassiveBackreactionEdge mode hmode r x y z) := by
  rw [thetaCuspHawkingCausalHardyPassiveBackreactionEdge,
    thetaCuspHawkingCausalHardyStimulatedKernel_eq_selectiveModularGainKernel
      q mode hmode horient r]
  exact thetaCuspHawkingPassiveBackreaction_cubic_pos q r hx hxy hyz

theorem thetaCuspHawkingCausalHardy_negativeCubic_forces_backreaction_mixing
    (q : XiZeroCopy)
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im)
    (horient : mode = thetaCuspHawkingXiOrbitResonantMode q ∨
      mode = thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q))
    (r : ℝ) {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hneg : symmetricThreePointDet
      (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode r) x y z < 0) :
    thetaCuspHawkingCausalHardyStimulatedKernel mode hmode r x z ≠
      thetaCuspHawkingCausalHardyPassiveBackreactionEdge mode hmode r x y z := by
  unfold thetaCuspHawkingCausalHardyPassiveBackreactionEdge
  rw [thetaCuspHawkingCausalHardyStimulatedKernel_eq_selectiveModularGainKernel
      q mode hmode horient r] at hneg ⊢
  exact thetaCuspHawking_negativeCubic_forces_backreaction_mixing
    q r hx hxy hyz hneg

theorem exists_thetaCuspHawking_negativeCubic_forcedBackreaction
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      symmetricThreePointDet
          (thetaCuspHawkingSelectiveModularGainKernel q r) x y z < 0 ∧
        0 < symmetricThreePointLongEdgeDet
          (thetaCuspHawkingSelectiveModularGainKernel q r) x y z
          (thetaCuspHawkingPassiveBackreactionEdge q r x y z) ∧
        thetaCuspHawkingSelectiveModularGainKernel q r x z ≠
          thetaCuspHawkingPassiveBackreactionEdge q r x y z := by
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz
  refine ⟨R, fun r hr => ?_⟩
  have hneg := hR r hr
  exact ⟨hneg, thetaCuspHawkingPassiveBackreaction_cubic_pos q r hx hxy hyz,
    thetaCuspHawking_negativeCubic_forces_backreaction_mixing q r hx hxy hyz hneg⟩

end

end RHTower
