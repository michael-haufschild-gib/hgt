import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHorizonEdgeModeLoadEndpoint

/-!
# Theta-Hawking canonical horizon edge-mode load escape

This endpoint continues the source-specific Hawking backreaction cubic after positive gravitational
horizon edge modes are included.

**[LITERATURE]** Klinger--Kudler-Flam--Satishchandran, arXiv:2601.07910, derive
angle-dependent boost-supertranslation edge charges from second-order black-hole backreaction.
Their fully dressed black-hole algebra is Type II-infinity and has no maximum-entropy state.
Chandrasekaran--Flanagan, arXiv:2601.07915, construct gravitational half-sided modular inclusions
and prove perturbative quantum focusing. This supplies a positive null-translation generator and
entropy concavity, but not Markov/Petz saturation or a uniform edge-energy bound.

For an off-critical Xi orbit, write the stimulated Hawking kernel as
`K_lambda = B + lambda A`, where `lambda = cosh(r)^(2 : ℕ)`. Exact three-shell passivity asks for the
remote correction
`K_lambda(x,y) * K_lambda(y,z) / K_lambda(y,y) - K_lambda(x,z)`.
After division by `lambda`, this converges to the corresponding correction for `A`. Positive
adjacent two-point minors and the negative off-critical three-point determinant prove that limiting
correction is nonzero. Its absolute value therefore diverges with Hawking gain.

Any positive two-point horizon edge covariance realizing that correction obeys
`2 * |E(x,z)| <= E(x,x) + E(z,z)`. Consequently, canonical passive completion of an off-critical
theta sector costs unbounded endpoint edge load.

The final equivalence records a sharp RH endpoint: uniform finite endpoint load for every upper
theta-Hawking causal Hardy sector is equivalent to RH. Reverse direction is vacuous because RH
leaves no such upper tilted sector.

**[OPEN CORE]** A producer must prove a theta-specific load law stronger than perturbative
Type II-infinity permits--for example a nonperturbative normalized edge-flux bound--or prove strict
quantum focusing after quotienting exactly the gravitational edge zero modes. Generic KMS, CCR,
inverse, Krein, passivity, and QFC concavity do not supply either statement.
-/


open Set Filter Topology Real

namespace RHTower

noncomputable section

def threePointPassiveRemoteCorrection
    (K : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  threePointPassiveLongEdge K x y z - K x z

theorem tendsto_threePointPassiveRemoteCorrection_div_atTop
    (A B : ℝ → ℝ → ℝ) {x y z : ℝ} (hAyy : A y y ≠ 0) :
    Tendsto
      (fun lambda : ℝ =>
        threePointPassiveRemoteCorrection
            (fun u v => B u v + lambda * A u v) x y z / lambda)
      atTop (𝓝 (threePointPassiveRemoteCorrection A x y z)) := by
  have hinv : Tendsto (fun lambda : ℝ => lambda⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hxy : Tendsto (fun lambda : ℝ => lambda⁻¹ * B x y + A x y)
      atTop (𝓝 (A x y)) := by
    simpa using (hinv.mul tendsto_const_nhds).add tendsto_const_nhds
  have hyz : Tendsto (fun lambda : ℝ => lambda⁻¹ * B y z + A y z)
      atTop (𝓝 (A y z)) := by
    simpa using (hinv.mul tendsto_const_nhds).add tendsto_const_nhds
  have hyy : Tendsto (fun lambda : ℝ => lambda⁻¹ * B y y + A y y)
      atTop (𝓝 (A y y)) := by
    simpa using (hinv.mul tendsto_const_nhds).add tendsto_const_nhds
  have hxz : Tendsto (fun lambda : ℝ => lambda⁻¹ * B x z + A x z)
      atTop (𝓝 (A x z)) := by
    simpa using (hinv.mul tendsto_const_nhds).add tendsto_const_nhds
  have hlimit := (hxy.mul hyz).div hyy hAyy |>.sub hxz
  have heq : ∀ᶠ lambda : ℝ in atTop,
      threePointPassiveRemoteCorrection
          (fun u v => B u v + lambda * A u v) x y z / lambda =
        (lambda⁻¹ * B x y + A x y) *
            (lambda⁻¹ * B y z + A y z) /
              (lambda⁻¹ * B y y + A y y) -
          (lambda⁻¹ * B x z + A x z) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
    unfold threePointPassiveRemoteCorrection threePointPassiveLongEdge
    field_simp [hlambda.ne']
  exact hlimit.congr' (EventuallyEq.symm heq)

theorem xiSquaredEulerOrbitKernel_eq_responseKernel (q : XiZeroCopy) :
    xiSquaredEulerOrbitKernel q =
      eulerRayResponseKernel
        (fun x => x * xiSquaredEulerOrbitResponse q (x ^ (2 : ℕ))) := by
  rfl

theorem xiSquaredEulerOrbitKernel_diag_pos
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    0 < xiSquaredEulerOrbitKernel q x x := by
  rw [xiSquaredEulerOrbitKernel_eq_responseKernel, eulerRayResponseKernel]
  field_simp [hx.ne']
  exact xiSquaredEulerOrbitResponse_pos q (sq_nonneg x)

theorem xiSquaredEulerOrbitKernel_twoPoint_det_pos
    (q : XiZeroCopy) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < xiSquaredEulerOrbitKernel q x x *
        xiSquaredEulerOrbitKernel q y y -
      xiSquaredEulerOrbitKernel q x y ^ (2 : ℕ) := by
  have hy : 0 < y := hx.trans hxy
  have hsq : x ^ (2 : ℕ) < y ^ (2 : ℕ) := by nlinarith
  have hdecreaseProfile := strictAntiOn_xiSquaredEulerOrbitResponse q
    (sq_nonneg x) (sq_nonneg y) hsq
  have hincreaseProfile := strictMonoOn_mul_xiSquaredEulerOrbitResponse q
    (sq_nonneg x) (sq_nonneg y) hsq
  have hdecrease :
      (y * xiSquaredEulerOrbitResponse q (y ^ (2 : ℕ))) / y <
        (x * xiSquaredEulerOrbitResponse q (x ^ (2 : ℕ))) / x := by
    simpa [hx.ne', hy.ne'] using hdecreaseProfile
  have hincrease :
      x * (x * xiSquaredEulerOrbitResponse q (x ^ (2 : ℕ))) <
        y * (y * xiSquaredEulerOrbitResponse q (y ^ (2 : ℕ))) := by
    simpa [pow_two, mul_assoc] using hincreaseProfile
  rw [xiSquaredEulerOrbitKernel_eq_responseKernel]
  exact eulerRayResponseKernel_twoPoint_det_pos _ hx hxy hdecrease hincrease

theorem xiSquaredEulerOrbit_passiveRemoteCorrection_ne_zero
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    threePointPassiveRemoteCorrection
        (xiSquaredEulerOrbitKernel q) x y z ≠ 0 := by
  let A := xiSquaredEulerOrbitKernel q
  have hy : 0 < y := hx.trans hxy
  have hdiag : 0 < A y y := xiSquaredEulerOrbitKernel_diag_pos q hy
  have hleft : 0 < A x x * A y y - A x y ^ (2 : ℕ) :=
    xiSquaredEulerOrbitKernel_twoPoint_det_pos q hx hxy
  have hright : 0 < A y y * A z z - A y z ^ (2 : ℕ) :=
    xiSquaredEulerOrbitKernel_twoPoint_det_pos q hy hyz
  have hpass := symmetricThreePointLongEdgeDet_passive_pos A hdiag hleft hright
  have hraw := xiSquaredEulerOrbitKernel_threePointDet_neg q hoff hx hxy hyz
  intro hzero
  have hcenter : threePointPassiveLongEdge A x y z = A x z :=
    sub_eq_zero.mp hzero
  rw [hcenter] at hpass
  change 0 < symmetricThreePointDet A x y z at hpass
  linarith

theorem tendsto_thetaCuspHawkingPassiveRemoteCorrection_div_gain
    (q : XiZeroCopy) {x y z : ℝ} (hy : 0 < y) :
    Tendsto
      (fun r : ℝ =>
        threePointPassiveRemoteCorrection
            (thetaCuspHawkingSelectiveModularGainKernel q r) x y z /
          thetaCuspHawkingModularGain r)
      atTop
      (𝓝 (threePointPassiveRemoteCorrection
        (xiSquaredEulerOrbitKernel q) x y z)) := by
  let A : ℝ → ℝ → ℝ := xiSquaredEulerOrbitKernel q
  let B : ℝ → ℝ → ℝ := fun u v => xiSquaredEulerFullKernel u v - A u v
  have hAyy : A y y ≠ 0 :=
    (xiSquaredEulerOrbitKernel_diag_pos q hy).ne'
  have hbase :=
    (tendsto_threePointPassiveRemoteCorrection_div_atTop A B
      (x := x) (z := z) hAyy).comp
      tendsto_thetaCuspHawkingModularGain_atTop
  convert hbase using 1
  funext r
  congr 2
  funext u v
  simp only [thetaCuspHawkingSelectiveModularGainKernel,
    xiSquaredEulerReweightedFullKernel]
  dsimp only [A, B]
  ring

theorem tendsto_abs_thetaCuspHawkingPassiveRemoteCorrection_atTop
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    Tendsto
      (fun r : ℝ =>
        |threePointPassiveRemoteCorrection
          (thetaCuspHawkingSelectiveModularGainKernel q r) x y z|)
      atTop atTop := by
  let L := threePointPassiveRemoteCorrection
    (xiSquaredEulerOrbitKernel q) x y z
  have hL : L ≠ 0 :=
    xiSquaredEulerOrbit_passiveRemoteCorrection_ne_zero q hoff hx hxy hyz
  have hratio :=
    (tendsto_thetaCuspHawkingPassiveRemoteCorrection_div_gain q
      (x := x) (z := z) (hx.trans hxy)).abs
  have hhalf : 0 < |L| / 2 := by
    exact div_pos (abs_pos.mpr hL) (by norm_num)
  have hhalfL : |L| / 2 < |L| := by
    nlinarith [abs_pos.mpr hL]
  have hevent : ∀ᶠ r : ℝ in atTop,
      |L| / 2 <
        |threePointPassiveRemoteCorrection
            (thetaCuspHawkingSelectiveModularGainKernel q r) x y z /
          thetaCuspHawkingModularGain r| :=
    (tendsto_order.mp hratio).1 (|L| / 2) hhalfL
  have hscaled : Tendsto
      (fun r : ℝ => |L| / 2 * thetaCuspHawkingModularGain r)
      atTop atTop :=
    tendsto_thetaCuspHawkingModularGain_atTop.const_mul_atTop hhalf
  apply tendsto_atTop_mono' atTop _ hscaled
  filter_upwards [hevent] with r hr
  have hgain : 0 < thetaCuspHawkingModularGain r :=
    thetaCuspHawkingModularGain_pos r
  have hmul := mul_le_mul_of_nonneg_right hr.le hgain.le
  have habs :
      |threePointPassiveRemoteCorrection
          (thetaCuspHawkingSelectiveModularGainKernel q r) x y z /
        thetaCuspHawkingModularGain r| *
          thetaCuspHawkingModularGain r =
        |threePointPassiveRemoteCorrection
          (thetaCuspHawkingSelectiveModularGainKernel q r) x y z| := by
    rw [abs_div, abs_of_pos hgain]
    field_simp [hgain.ne']
  rwa [habs] at hmul

/-- Positive horizon covariance pays at least twice its remote load in endpoint self-energy. -/
theorem horizonEdgeMode_two_abs_remote_le_endpointLoad
    (E : ℝ → ℝ → ℝ) {x z : ℝ}
    (hE : HorizonEdgeModeTwoPointPositive E x z) :
    2 * |E x z| ≤ E x x + E z z := by
  rcases hE with ⟨hxx, hzz, hminor⟩
  have hsum : 0 ≤ E x x + E z z := add_nonneg hxx hzz
  have habs : 0 ≤ 2 * |E x z| := by positivity
  have hsquare : (2 * |E x z|) ^ (2 : ℕ) ≤ (E x x + E z z) ^ (2 : ℕ) := by
    calc
      (2 * |E x z|) ^ (2 : ℕ) = 4 * |E x z| ^ (2 : ℕ) := by ring
      _ = 4 * E x z ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ (E x x + E z z) ^ (2 : ℕ) := by
        nlinarith [sq_nonneg (E x x - E z z)]
  nlinarith

/-- Off-line theta response forces every positive gravitational realization of the canonical
remote completion above every prescribed endpoint-load budget at late Hawking rapidity. -/
theorem exists_eventually_thetaCuspHawkingCanonicalEdgeLoad_gt
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (budget : ℝ) :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      ∀ E : ℝ → ℝ → ℝ,
        HorizonEdgeModeTwoPointPositive E x z →
        thetaCuspHawkingSelectiveModularGainKernel q r x z + E x z =
          thetaCuspHawkingPassiveBackreactionEdge q r x y z →
        budget < E x x + E z z := by
  have hescape := tendsto_abs_thetaCuspHawkingPassiveRemoteCorrection_atTop
    q hoff hx hxy hyz
  have hevent : ∀ᶠ r : ℝ in atTop,
      |budget| + 1 ≤
        |threePointPassiveRemoteCorrection
          (thetaCuspHawkingSelectiveModularGainKernel q r) x y z| :=
    tendsto_atTop.mp hescape (|budget| + 1)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hevent
  refine ⟨R, fun r hr E hE hcompletion => ?_⟩
  have hremote : E x z =
      threePointPassiveRemoteCorrection
        (thetaCuspHawkingSelectiveModularGainKernel q r) x y z := by
    unfold thetaCuspHawkingPassiveBackreactionEdge at hcompletion
    unfold threePointPassiveRemoteCorrection
    linarith
  have hlower := horizonEdgeMode_two_abs_remote_le_endpointLoad E hE
  rw [hremote] at hlower
  have hlarge := hR r hr
  have hbudget : budget ≤ |budget| := le_abs_self budget
  nlinarith [abs_nonneg budget]

/-- A proposed finite-load law for full gravitational completion of every upper theta-Hawking
causal Hardy sector.  It asks for an actual positive edge covariance at every rapidity, with one
uniform endpoint self-energy budget for each ordered shell triple. -/
def ThetaCuspHawkingCausalHardyCanonicalEdgeLoadUniformlyBounded : Prop :=
  ∀ (mode : ThetaCuspHawkingBackreactionResonantMode)
      (hmode : 0 < mode.1.im) (x y z : ℝ),
    0 < x → x < y → y < z →
      ∃ budget : ℝ, ∀ r : ℝ,
        ∃ E : ℝ → ℝ → ℝ,
          HorizonEdgeModeTwoPointPositive E x z ∧
          thetaCuspHawkingCausalHardyStimulatedKernel mode hmode r x z + E x z =
            thetaCuspHawkingCausalHardyPassiveBackreactionEdge
              mode hmode r x y z ∧
          E x x + E z z ≤ budget

/-- Finite endpoint load under exact canonical completion is an RH endpoint.  The forward
direction uses the linear-in-Hawking-gain escape above; the reverse is vacuous because RH leaves
no upper tilted theta-Hawking resonance sector. -/
theorem thetaCuspHawkingCausalHardyCanonicalEdgeLoadUniformlyBounded_iff_riemannHypothesis :
    ThetaCuspHawkingCausalHardyCanonicalEdgeLoadUniformlyBounded ↔
      RiemannHypothesis := by
  constructor
  · intro hbounded
    apply xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.mp
    intro q
    apply (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).mpr
    by_contra hoff
    obtain ⟨mode, hmode, horient⟩ :=
      exists_upper_thetaCuspHawkingXiOrbitResonantMode q hoff
    obtain ⟨budget, hbudget⟩ :=
      hbounded mode hmode 1 2 3 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨R, hR⟩ :=
      exists_eventually_thetaCuspHawkingCanonicalEdgeLoad_gt
        q hoff (x := 1) (y := 2) (z := 3)
          (by norm_num) (by norm_num) (by norm_num) budget
    obtain ⟨E, hE, hcompletion, hload⟩ := hbudget R
    have hkernel :=
      thetaCuspHawkingCausalHardyStimulatedKernel_eq_selectiveModularGainKernel
        q mode hmode horient R
    have hcompletion' :
        thetaCuspHawkingSelectiveModularGainKernel q R 1 3 + E 1 3 =
          thetaCuspHawkingPassiveBackreactionEdge q R 1 2 3 := by
      simpa only [thetaCuspHawkingCausalHardyPassiveBackreactionEdge,
        thetaCuspHawkingPassiveBackreactionEdge, hkernel] using hcompletion
    have hlarge := hR R le_rfl E hE hcompletion'
    linarith
  · intro hRH mode hmode
    have hreal := (riemannHypothesis_iff_XiC_zeros_real.mp hRH) mode.1
      (thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero mode)
    exfalso
    linarith

end

end RHTower
