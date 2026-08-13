import GaloisForLFunctions.RHTower.RouteRHyperbolicGaugePolarReductionNoGo

/-!
# Universal positive-polar collapse under the Route R hyperbolic gauge

This strengthens the fixed-metric obstruction to arbitrary quadratic targets.
Every real quadratic form on the retained forward/reciprocal source plane
which is nonnegative and invariant under the full hyperbolic source gauge is
zero.  More generally, the energy of every real-linear landing into any
quadratic target vanishes on its entire image if its pullback is nonnegative
and gauge invariant.

The proof does not enumerate candidate constructions.  Hyperbolic invariance
first kills each retained axis.  The quadratic parallelogram law and
nonnegativity then kill the off-diagonal polarization.  Without
nonnegativity the split forward/reciprocal pairing survives, exactly matching
the sign-indefinite source form already present in Route R.

Consequently a nonzero positive polar handoff cannot be functorial for the
existing pre-polar source automorphisms, regardless of target dimension,
completion, or locality.  The only surviving polar handoff must visibly break
this gauge naturality using additional numerical source structure.
-/

open Complex Real

namespace RHTower

noncomputable section

/-! ## Axis collapse without positivity -/

/-- Hyperbolic invariance kills the complete forward axis of every quadratic
form, independently of any sign assumption. -/
theorem routeR_gaugeInvariantQuadraticForm_forwardAxis_eq_zero
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hinvariant : ∀ a z,
      Q (routeRHyperbolicSourceGauge a z) = Q z)
    (w : ℂ) :
    Q (w, 0) = 0 := by
  have h := hinvariant (Real.log 2) (w, 0)
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  have hgauge :
      routeRHyperbolicSourceGauge (Real.log 2) (w, 0) =
        (2 : ℝ) • (w, 0) := by
    ext <;> simp [routeRHyperbolicSourceGauge, htwo]
  rw [hgauge, Q.map_smul] at h
  norm_num at h
  linarith

/-- Hyperbolic invariance kills the complete reciprocal axis of every
quadratic form, independently of any sign assumption. -/
theorem routeR_gaugeInvariantQuadraticForm_reciprocalAxis_eq_zero
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hinvariant : ∀ a z,
      Q (routeRHyperbolicSourceGauge a z) = Q z)
    (w : ℂ) :
    Q (0, w) = 0 := by
  have h := hinvariant (-Real.log 2) (0, w)
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  have hgauge :
      routeRHyperbolicSourceGauge (-Real.log 2) (0, w) =
        (2 : ℝ) • (0, w) := by
    ext <;> simp [routeRHyperbolicSourceGauge, htwo]
  rw [hgauge, Q.map_smul] at h
  norm_num at h
  linarith

/-! ## Universal positive collapse -/

/-- A nonnegative quadratic form which vanishes separately on the retained
forward and reciprocal axes vanishes on their whole direct sum.  This is the
polarization step used below; it requires no gauge hypothesis. -/
theorem routeR_nonnegativeQuadraticForm_eq_zero_of_axes
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hnonnegative : ∀ z, 0 ≤ Q z)
    (hforward : ∀ w : ℂ, Q (w, 0) = 0)
    (hreciprocal : ∀ w : ℂ, Q (0, w) = 0) :
    Q = 0 := by
  apply QuadraticMap.ext
  intro z
  let x : RouteRHyperbolicSourcePlane := (z.1, 0)
  let y : RouteRHyperbolicSourcePlane := (0, z.2)
  have hx : Q x = 0 := hforward z.1
  have hy : Q y = 0 := hreciprocal z.2
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hplus := hB x y
  have hminus := hB x (-y)
  have hQneg : Q (-y) = Q y := by
    simpa only [neg_smul, one_smul, mul_neg, mul_one, neg_neg,
      one_smul] using Q.map_smul (-1 : ℝ) y
  have hBneg : B x (-y) = -B x y := by simp
  have hparallelogram : Q (x + y) + Q (x - y) = 0 := by
    rw [sub_eq_add_neg, hplus, hminus, hx, hQneg, hy, hBneg]
    ring
  have hplus_nonnegative := hnonnegative (x + y)
  have hminus_nonnegative := hnonnegative (x - y)
  have hxy : x + y = z := by
    ext <;> simp [x, y]
  change Q z = 0
  rw [← hxy]
  linarith

/-- **Universal positive-polar no-go.**  Every nonnegative quadratic form
natural for the Route R hyperbolic source gauge is identically zero. -/
theorem routeR_gaugeInvariant_nonnegativeQuadraticForm_eq_zero
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hnonnegative : ∀ z, 0 ≤ Q z)
    (hinvariant : ∀ a z,
      Q (routeRHyperbolicSourceGauge a z) = Q z) :
    Q = 0 := by
  exact routeR_nonnegativeQuadraticForm_eq_zero_of_axes Q hnonnegative
    (routeR_gaugeInvariantQuadraticForm_forwardAxis_eq_zero Q hinvariant)
    (routeR_gaugeInvariantQuadraticForm_reciprocalAxis_eq_zero Q hinvariant)

/-! ## Two-orientation contraction already collapses -/

/-- Exact quantitative alternative: every nonzero nonnegative quadratic
polar has a retained source axis whose energy is multiplied by four by one
of the two fixed Gamma-orientation boosts `±log 2`. -/
theorem routeR_nonzero_nonnegativeQuadraticForm_has_factorFourGaugeGain
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hnonnegative : ∀ z, 0 ≤ Q z) (hQ : Q ≠ 0) :
    (∃ z : RouteRHyperbolicSourcePlane,
        0 < Q z ∧
        Q (routeRHyperbolicSourceGauge (Real.log 2) z) = 4 * Q z) ∨
      (∃ z : RouteRHyperbolicSourcePlane,
        0 < Q z ∧
        Q (routeRHyperbolicSourceGauge (-Real.log 2) z) = 4 * Q z) := by
  have haxis :
      (∃ w : ℂ, Q (w, 0) ≠ 0) ∨ (∃ w : ℂ, Q (0, w) ≠ 0) := by
    by_contra h
    push Not at h
    exact hQ (routeR_nonnegativeQuadraticForm_eq_zero_of_axes
      Q hnonnegative h.1 h.2)
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  rcases haxis with ⟨w, hw⟩ | ⟨w, hw⟩
  · left
    refine ⟨(w, 0), lt_of_le_of_ne (hnonnegative (w, 0)) hw.symm, ?_⟩
    have hgauge :
        routeRHyperbolicSourceGauge (Real.log 2) (w, 0) =
          (2 : ℝ) • (w, 0) := by
      ext <;> simp [routeRHyperbolicSourceGauge, htwo]
    rw [hgauge, Q.map_smul]
    norm_num
  · right
    refine ⟨(0, w), lt_of_le_of_ne (hnonnegative (0, w)) hw.symm, ?_⟩
    have hgauge :
        routeRHyperbolicSourceGauge (-Real.log 2) (0, w) =
          (2 : ℝ) • (0, w) := by
      ext <;> simp [routeRHyperbolicSourceGauge, htwo]
    rw [hgauge, Q.map_smul]
    norm_num

/-- Full hyperbolic invariance is much stronger than necessary.  If one
fixed positive polar is non-amplifying for the two source orientations at
the single boosts `±log 2`, it is already zero. -/
theorem routeR_twoOrientationGaugeNonamplification_nonnegativeQuadraticForm_eq_zero
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hnonnegative : ∀ z, 0 ≤ Q z)
    (hforward : ∀ z,
      Q (routeRHyperbolicSourceGauge (Real.log 2) z) ≤ Q z)
    (hreciprocal : ∀ z,
      Q (routeRHyperbolicSourceGauge (-Real.log 2) z) ≤ Q z) :
    Q = 0 := by
  by_contra hQ
  rcases routeR_nonzero_nonnegativeQuadraticForm_has_factorFourGaugeGain
      Q hnonnegative hQ with ⟨z, hz, hgain⟩ | ⟨z, hz, hgain⟩
  · have hcontract := hforward z
    rw [hgain] at hcontract
    linarith
  · have hcontract := hreciprocal z
    rw [hgain] at hcontract
    linarith

/-- **Pointwise two-orientation collapse.**  Global gauge invariance and
non-amplification on every source vector are unnecessary.  For one fixed
carrier `z`, a nonnegative quadratic form cannot be non-amplifying under both
Gamma-orientation boosts `±log 2` unless its energy on `z` is already zero.

This is the exact local obstruction needed for a source-selected,
`rho`-dependent polar comparison: choosing the form nonfunctorially does not
create a positive fixed-carrier escape. -/
theorem routeR_pointwise_twoOrientationGaugeNonamplification_energy_eq_zero
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hnonnegative : ∀ z, 0 ≤ Q z)
    (z : RouteRHyperbolicSourcePlane)
    (hforward :
      Q (routeRHyperbolicSourceGauge (Real.log 2) z) ≤ Q z)
    (hreciprocal :
      Q (routeRHyperbolicSourceGauge (-Real.log 2) z) ≤ Q z) :
    Q z = 0 := by
  let x : RouteRHyperbolicSourcePlane := (z.1, 0)
  let y : RouteRHyperbolicSourcePlane := (0, z.2)
  have hxy : x + y = z := by
    ext <;> simp [x, y]
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  have hhalf : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg, htwo]
  have hgaugeForward :
      routeRHyperbolicSourceGauge (Real.log 2) z =
        (2 : ℝ) • x + (2 : ℝ)⁻¹ • y := by
    ext <;> simp [routeRHyperbolicSourceGauge, x, y, htwo, hhalf]
  have hgaugeReciprocal :
      routeRHyperbolicSourceGauge (-Real.log 2) z =
        (2 : ℝ)⁻¹ • x + (2 : ℝ) • y := by
    ext <;> simp [routeRHyperbolicSourceGauge, x, y, htwo, hhalf]
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hzExpand := hB x y
  have hQz : Q z = Q x + Q y + B x y := by
    rw [← hxy, hzExpand]
  have hforwardExpand := hB ((2 : ℝ) • x) ((2 : ℝ)⁻¹ • y)
  have hreciprocalExpand := hB ((2 : ℝ)⁻¹ • x) ((2 : ℝ) • y)
  rw [hQz] at hforward hreciprocal
  rw [hgaugeForward, hforwardExpand, Q.map_smul, Q.map_smul,
    map_smul, map_smul] at hforward
  rw [hgaugeReciprocal, hreciprocalExpand, Q.map_smul, Q.map_smul,
    map_smul, map_smul] at hreciprocal
  have hx : Q x = 0 := by
    have hxnonnegative := hnonnegative x
    have hynonnegative := hnonnegative y
    norm_num at hforward hreciprocal
    nlinarith
  have hy : Q y = 0 := by
    have hxnonnegative := hnonnegative x
    have hynonnegative := hnonnegative y
    norm_num at hforward hreciprocal
    nlinarith
  have hminus := hB x (-y)
  have hQneg : Q (-y) = Q y := by
    simpa only [neg_smul, one_smul, mul_neg, mul_one, neg_neg,
      one_smul] using Q.map_smul (-1 : ℝ) y
  have hBneg : B x (-y) = -B x y := by simp
  have hplusNonnegative := hnonnegative (x + y)
  have hminusNonnegative := hnonnegative (x - y)
  rw [sub_eq_add_neg, hminus, hx, hQneg, hy, hBneg] at hminusNonnegative
  rw [hzExpand, hx, hy] at hplusNonnegative
  have hBzero : B x y = 0 := by linarith
  rw [← hxy, hzExpand, hx, hy, hBzero]
  ring

/-! ## Strongest survivor: the split indefinite sector -/

/-- Sign reversal on the reciprocal source leg.  It fixes the forward leg
and reverses only the reciprocal orientation. -/
def routeRReciprocalLegSignFlip :
    RouteRHyperbolicSourcePlane →ₗ[ℝ] RouteRHyperbolicSourcePlane where
  toFun z := (z.1, -z.2)
  map_add' z w := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  map_smul' c z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring

@[simp] theorem routeRReciprocalLegSignFlip_apply
    (z : RouteRHyperbolicSourcePlane) :
    routeRReciprocalLegSignFlip z = (z.1, -z.2) := rfl

/-- Every hyperbolic-gauge-invariant quadratic form is odd under reversal of
one source leg.  This is the exact residual split/off-diagonal sector after
the two diagonal axes have been killed. -/
theorem routeR_gaugeInvariantQuadraticForm_reciprocalSignFlip
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hinvariant : ∀ a z,
      Q (routeRHyperbolicSourceGauge a z) = Q z)
    (z : RouteRHyperbolicSourcePlane) :
    Q (routeRReciprocalLegSignFlip z) = -Q z := by
  let x : RouteRHyperbolicSourcePlane := (z.1, 0)
  let y : RouteRHyperbolicSourcePlane := (0, z.2)
  have hx : Q x = 0 :=
    routeR_gaugeInvariantQuadraticForm_forwardAxis_eq_zero
      Q hinvariant z.1
  have hy : Q y = 0 :=
    routeR_gaugeInvariantQuadraticForm_reciprocalAxis_eq_zero
      Q hinvariant z.2
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hplus := hB x y
  have hminus := hB x (-y)
  have hQneg : Q (-y) = Q y := by
    simpa only [neg_smul, one_smul, mul_neg, mul_one, neg_neg,
      one_smul] using Q.map_smul (-1 : ℝ) y
  have hBneg : B x (-y) = -B x y := by simp
  have hplusValue : Q (x + y) = B x y := by
    rw [hplus, hx, hy]
    ring
  have hminusValue : Q (x - y) = -B x y := by
    rw [sub_eq_add_neg, hminus, hx, hQneg, hy, hBneg]
    ring
  have hplusXY : x + y = z := by
    ext <;> simp [x, y]
  have hminusXY : x - y = routeRReciprocalLegSignFlip z := by
    ext <;> simp [x, y, routeRReciprocalLegSignFlip]
  rw [← hminusXY, hminusValue, ← hplusValue, hplusXY]

/-- **Exact strongest positive survivor.**  A nonzero invariant quadratic
source form necessarily takes both signs.  Therefore the only invariant
quadratic information retained by Route R is sign-indefinite; positivity can
arise only after a non-natural polar reduction. -/
theorem routeR_gaugeInvariantQuadraticForm_nonzero_is_signIndefinite
    (Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane)
    (hinvariant : ∀ a z,
      Q (routeRHyperbolicSourceGauge a z) = Q z)
    (hQ : Q ≠ 0) :
    (∃ z, Q z < 0) ∧ (∃ z, 0 < Q z) := by
  have hexists : ∃ z, Q z ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ
    apply QuadraticMap.ext
    exact h
  obtain ⟨z, hz⟩ := hexists
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · refine ⟨⟨z, hzneg⟩,
      routeRReciprocalLegSignFlip z, ?_⟩
    rw [routeR_gaugeInvariantQuadraticForm_reciprocalSignFlip Q hinvariant]
    linarith
  · refine ⟨⟨routeRReciprocalLegSignFlip z, ?_⟩,
      z, hzpos⟩
    rw [routeR_gaugeInvariantQuadraticForm_reciprocalSignFlip Q hinvariant]
    linarith

/-- Target-independent form.  If a real-linear source landing has
nonnegative, hyperbolic-gauge-invariant target energy on its image, that
energy vanishes on every landed vector. -/
theorem routeR_gaugeNatural_nonnegativeQuadraticLanding_energy_eq_zero
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M)
    (landing : RouteRHyperbolicSourcePlane →ₗ[ℝ] M)
    (hnonnegative : ∀ z, 0 ≤ Q (landing z))
    (hinvariant : ∀ a z,
      Q (landing (routeRHyperbolicSourceGauge a z)) = Q (landing z)) :
    ∀ z, Q (landing z) = 0 := by
  have hzero : Q.comp landing = 0 :=
    routeR_gaugeInvariant_nonnegativeQuadraticForm_eq_zero
      (Q.comp landing) hnonnegative hinvariant
  intro z
  have hz := QuadraticMap.congr_fun hzero z
  simpa using hz

/-- Hence no gauge-natural nonnegative landing can retain even one vector
with nonzero positive energy. -/
theorem routeR_no_gaugeNatural_nonnegativeQuadraticLanding_with_retainedEnergy
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M)
    (landing : RouteRHyperbolicSourcePlane →ₗ[ℝ] M)
    (hnonnegative : ∀ z, 0 ≤ Q (landing z))
    (hinvariant : ∀ a z,
      Q (landing (routeRHyperbolicSourceGauge a z)) = Q (landing z)) :
    ¬ ∃ z, Q (landing z) ≠ 0 := by
  rintro ⟨z, hz⟩
  exact hz
    (routeR_gaugeNatural_nonnegativeQuadraticLanding_energy_eq_zero
      Q landing hnonnegative hinvariant z)

/-! ## Exclusion of the actual fixed physical excess -/

/-- The actual witness-edge physical excess is strictly positive at every
off-line Xi divisor. -/
theorem routeR_actualFixedPhysicalStokesExcess_pos_of_offLine
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    0 < primeDepthBVWoldSourcePolarizationStokesExcess
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) := by
  have hnonnegative :=
    primeDepthBVWoldSourcePolarizationStokesExcess_nonneg
      (primeDepthBVWoldXiCenteredRate rho)
      primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
      (iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho))
  have hne :
      primeDepthBVWoldSourcePolarizationStokesExcess
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)) ≠ 0 :=
    (primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff
      rho).not.mpr hoff
  exact lt_of_le_of_ne hnonnegative hne.symm

/-- **Actual-comparison no-go.**  At an off-line Xi divisor, no nonnegative
quadratic form natural for all pre-polar hyperbolic source automorphisms can
equal the fixed physical Stokes excess on even one chosen source vector.
This rules out the full functorial positive-polar category, not merely the
Euclidean metric used in earlier modules. -/
theorem routeR_no_gaugeNaturalPositivePolarComparison_to_actualExcess
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2)
    (carrier : RouteRHyperbolicSourcePlane) :
    ¬ ∃ Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane,
      (∀ z, 0 ≤ Q z) ∧
      (∀ a z, Q (routeRHyperbolicSourceGauge a z) = Q z) ∧
      Q carrier =
        primeDepthBVWoldSourcePolarizationStokesExcess
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)) := by
  rintro ⟨Q, hnonnegative, hinvariant, hcomparison⟩
  have hQzero := routeR_gaugeInvariant_nonnegativeQuadraticForm_eq_zero
    Q hnonnegative hinvariant
  have hzero :
      primeDepthBVWoldSourcePolarizationStokesExcess
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)) = 0 := by
    rw [hQzero, QuadraticMap.zero_apply] at hcomparison
    exact hcomparison.symm
  exact (ne_of_gt
    (routeR_actualFixedPhysicalStokesExcess_pos_of_offLine rho hoff)) hzero

/-! ## Global classification of the whole gauge-natural positive category -/

/-- For every choice of retained source carrier, the existence on every Xi
fibre of a nonnegative hyperbolic-gauge-natural quadratic comparison with the
actual physical Stokes excess is equivalent to RH.

The forward implication is target-free: gauge naturality and positivity make
each quadratic form zero before its value is compared with the Xi fibre.  The
reverse implication uses the zero quadratic form.  Thus neither a varying
quadratic form nor a rho-dependent choice of carrier creates an independent
producer inside the pre-polar gauge-natural category. -/
theorem routeR_forallXi_exists_gaugeNaturalPositiveComparison_iff_rh
    (carrier : XiDivisorSupport → RouteRHyperbolicSourcePlane) :
    (∀ rho : XiDivisorSupport,
        ∃ Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane,
          (∀ z, 0 ≤ Q z) ∧
          (∀ a z, Q (routeRHyperbolicSourceGauge a z) = Q z) ∧
          Q (carrier rho) =
            primeDepthBVWoldSourcePolarizationStokesExcess
              (primeDepthBVWoldXiCenteredRate rho)
              primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
              (iteratedDeriv (xiSupportMultiplicity rho) XiC
                (xiSpectralPointSupport rho))) ↔
      RiemannHypothesis := by
  constructor
  · intro hcomparison
    apply primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis.mp
    intro rho
    obtain ⟨Q, hnonnegative, hinvariant, hvalue⟩ := hcomparison rho
    have hQzero := routeR_gaugeInvariant_nonnegativeQuadraticForm_eq_zero
      Q hnonnegative hinvariant
    rw [hQzero, QuadraticMap.zero_apply] at hvalue
    exact hvalue.symm
  · intro hRH rho
    refine ⟨0, ?_, ?_, ?_⟩
    · intro z
      rw [QuadraticMap.zero_apply]
    · intro a z
      rw [QuadraticMap.zero_apply, QuadraticMap.zero_apply]
    · rw [QuadraticMap.zero_apply]
      exact
        (primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff
          rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho) |>.symm

/-- The same global RH classification holds after exact gauge invariance is
weakened to two one-step contraction inequalities.  Therefore a source law
valid in both Gamma orientations cannot produce the fixed physical excess
unless it has already supplied RH-strength information. -/
theorem
    routeR_forallXi_exists_twoOrientationNonamplifyingPositiveComparison_iff_rh
    (carrier : XiDivisorSupport → RouteRHyperbolicSourcePlane) :
    (∀ rho : XiDivisorSupport,
        ∃ Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane,
          (∀ z, 0 ≤ Q z) ∧
          (∀ z,
            Q (routeRHyperbolicSourceGauge (Real.log 2) z) ≤ Q z) ∧
          (∀ z,
            Q (routeRHyperbolicSourceGauge (-Real.log 2) z) ≤ Q z) ∧
          Q (carrier rho) =
            primeDepthBVWoldSourcePolarizationStokesExcess
              (primeDepthBVWoldXiCenteredRate rho)
              primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
              (iteratedDeriv (xiSupportMultiplicity rho) XiC
                (xiSpectralPointSupport rho))) ↔
      RiemannHypothesis := by
  constructor
  · intro hcomparison
    apply primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis.mp
    intro rho
    obtain ⟨Q, hnonnegative, hforward, hreciprocal, hvalue⟩ :=
      hcomparison rho
    have hQzero :=
      routeR_twoOrientationGaugeNonamplification_nonnegativeQuadraticForm_eq_zero
        Q hnonnegative hforward hreciprocal
    rw [hQzero, QuadraticMap.zero_apply] at hvalue
    exact hvalue.symm
  · intro hRH rho
    refine ⟨0, ?_, ?_, ?_, ?_⟩
    · intro z
      rw [QuadraticMap.zero_apply]
    · intro z
      rw [QuadraticMap.zero_apply, QuadraticMap.zero_apply]
    · intro z
      rw [QuadraticMap.zero_apply, QuadraticMap.zero_apply]
    · rw [QuadraticMap.zero_apply]
      exact
        (primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff
          rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho) |>.symm

/-- **Dependency-closed pointwise positive-polar classification.**  Even if
each Xi fibre chooses its own nonfunctorial positive quadratic form, only the
two inequalities on that fibre's one fixed carrier are needed: simultaneous
non-amplification in the two Gamma orientations is equivalent to RH once the
carrier energy is identified with the fixed physical Stokes excess.

Thus varying the metric, abandoning gauge naturality, and abandoning
whole-space contraction do not leave a positive-polar producer below the RH
endpoint. -/
theorem
    routeR_forallXi_exists_pointwiseTwoOrientationPositiveComparison_iff_rh
    (carrier : XiDivisorSupport → RouteRHyperbolicSourcePlane) :
    (∀ rho : XiDivisorSupport,
        ∃ Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane,
          (∀ z, 0 ≤ Q z) ∧
          Q (routeRHyperbolicSourceGauge (Real.log 2) (carrier rho)) ≤
            Q (carrier rho) ∧
          Q (routeRHyperbolicSourceGauge (-Real.log 2) (carrier rho)) ≤
            Q (carrier rho) ∧
          Q (carrier rho) =
            primeDepthBVWoldSourcePolarizationStokesExcess
              (primeDepthBVWoldXiCenteredRate rho)
              primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
              (iteratedDeriv (xiSupportMultiplicity rho) XiC
                (xiSpectralPointSupport rho))) ↔
      RiemannHypothesis := by
  constructor
  · intro hcomparison
    apply primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis.mp
    intro rho
    obtain ⟨Q, hnonnegative, hforward, hreciprocal, hvalue⟩ :=
      hcomparison rho
    have hzero :=
      routeR_pointwise_twoOrientationGaugeNonamplification_energy_eq_zero
        Q hnonnegative (carrier rho) hforward hreciprocal
    rw [hzero] at hvalue
    exact hvalue.symm
  · intro hRH rho
    refine ⟨0, ?_, ?_, ?_, ?_⟩
    · intro z
      rw [QuadraticMap.zero_apply]
    · rw [QuadraticMap.zero_apply, QuadraticMap.zero_apply]
    · rw [QuadraticMap.zero_apply, QuadraticMap.zero_apply]
    · rw [QuadraticMap.zero_apply]
      exact
        (primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff
          rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho) |>.symm

/-- Fully source-selected pointwise positive-polar handoff.  Both carrier and
quadratic form may vary with the arithmetic construction; only positivity,
the two fixed Gamma-orientation inequalities, and physical coefficient
fidelity remain. -/
def RouteRPointwiseTwoOrientationPositivePolarHandoff : Prop :=
  ∃ carrier : XiDivisorSupport → RouteRHyperbolicSourcePlane,
    ∀ rho : XiDivisorSupport,
      ∃ Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane,
        (∀ z, 0 ≤ Q z) ∧
        Q (routeRHyperbolicSourceGauge (Real.log 2) (carrier rho)) ≤
          Q (carrier rho) ∧
        Q (routeRHyperbolicSourceGauge (-Real.log 2) (carrier rho)) ≤
          Q (carrier rho) ∧
        Q (carrier rho) =
          primeDepthBVWoldSourcePolarizationStokesExcess
            (primeDepthBVWoldXiCenteredRate rho)
            primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            (iteratedDeriv (xiSupportMultiplicity rho) XiC
              (xiSpectralPointSupport rho))

/-- Allowing the source to select both carrier and metric leaves exactly the
RH-strength pointwise two-orientation obligation, with no hidden naturality
or global-contraction premise. -/
theorem
    routeRPointwiseTwoOrientationPositivePolarHandoff_iff_rh :
    RouteRPointwiseTwoOrientationPositivePolarHandoff ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨carrier, hcomparison⟩
    exact
      (routeR_forallXi_exists_pointwiseTwoOrientationPositiveComparison_iff_rh
        carrier).mp hcomparison
  · intro hRH
    refine ⟨fun _ ↦ 0, ?_⟩
    exact
      (routeR_forallXi_exists_pointwiseTwoOrientationPositiveComparison_iff_rh
        (fun _ ↦ 0)).mpr hRH

end

end RHTower
