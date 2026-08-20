import GaloisForLFunctions.HTGeometry.CalibrationSpectrumMechanics
import GaloisForLFunctions.HTGeometry.ConstantFieldQEDGammaClock
import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona
import GaloisForLFunctions.HTGeometry.HyperbolicModulus
import GaloisForLFunctions.HTGeometry.RegularLevelSetStratification
import GaloisForLFunctions.RHTower.CCMArchimedeanGeometricCompositeKernel
import GaloisForLFunctions.RHTower.FiniteWindowRecurrenceInstability
import GaloisForLFunctions.RHTower.LegStripSteepness
import GaloisForLFunctions.RHTower.ReversalPositivity
import GaloisForLFunctions.SelbergClass.MultipleStandardTwistDamping

/-!
# Mechanical quantum-oscillation interfaces

This module isolates unconditional closed consequences of four standard pieces of quantum-
oscillation mechanics:

* a free-electron Fermi surface is an energy level set;
* Landau crossings are equally spaced in inverse magnetic field and drive periodic dHvA/SdH
  oscillations;
* dHvA magnetization is the derivative of an oscillatory thermodynamic potential;
* the single-harmonic Lifshitz--Kosevich amplitude factors into thermal, Dingle, and spin terms.

Constants are unit-normalized. The purpose is exact structural reuse of existing corpus theorems,
not a material-specific model or numerical prediction.
-/

open Set Filter Topology
open scoped UnivMeroFieldInstances

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Free-electron Fermi surfaces -/

/-- Unit-normalized free-electron dispersion in arbitrary finite momentum dimension. -/
def freeElectronDispersion (d : ℕ) (k : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ‖k‖ ^ 2

/-- Unit-chemical-potential free-electron Fermi surface in arbitrary finite dimension. -/
def freeElectronFermiSurface (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {k | freeElectronDispersion d k = 1}

/-- Every unit free-electron Fermi surface is exactly a Euclidean unit sphere. -/
theorem freeElectronFermiSurface_eq_sphere :
    ∀ d : ℕ, freeElectronFermiSurface d = Metric.sphere 0 1 := by
  intro d
  ext k
  simp only [freeElectronFermiSurface, freeElectronDispersion, Set.mem_setOf_eq,
    Metric.mem_sphere, dist_zero_right]
  constructor
  · intro hk
    nlinarith [norm_nonneg k]
  · intro hk
    nlinarith

/-- Every finite-dimensional unit free-electron Fermi surface is compact. -/
theorem freeElectronFermiSurface_isCompact :
    ∀ d : ℕ, IsCompact (freeElectronFermiSurface d) := by
  intro d
  rw [freeElectronFermiSurface_eq_sphere]
  exact isCompact_sphere 0 1

/-- Free-electron Fermi surfaces are invariant under momentum reversal. -/
theorem freeElectronFermiSurface_neg_invariant :
    ∀ d : ℕ, MapsTo Neg.neg (freeElectronFermiSurface d)
      (freeElectronFermiSurface d) := by
  intro d k hk
  simpa [freeElectronFermiSurface, freeElectronDispersion] using hk

/-- Unit-normalized free-electron dispersion in one momentum dimension. -/
def oneDimensionalFreeElectronDispersion (k : ℝ) : ℝ := k ^ 2

/-- Fermi surface at unit chemical potential in one momentum dimension. -/
def oneDimensionalFreeElectronFermiSurface : Set ℝ :=
  {k | oneDimensionalFreeElectronDispersion k = 1}

/-- The one-dimensional unit Fermi surface consists of the two Fermi points. -/
theorem oneDimensionalFreeElectronFermiSurface_eq :
    oneDimensionalFreeElectronFermiSurface = {(-1 : ℝ), 1} := by
  ext k
  simp only [oneDimensionalFreeElectronFermiSurface,
    oneDimensionalFreeElectronDispersion, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro hk
    rcases sq_eq_one_iff.mp hk with hk | hk
    · exact Or.inr hk
    · exact Or.inl hk
  · rintro (rfl | rfl) <;> norm_num

/-- The one-dimensional unit Fermi surface is a regular codimension-one level set. -/
theorem oneDimensionalFreeElectronFermiSurface_regular :
    HTGeometry.IsLocalRegularLevelSetOfCodimAtLeast
      oneDimensionalFreeElectronFermiSurface 1 := by
  let g : ℝ → ℝ := fun k => k ^ 2 - 1
  have hg : ContDiff ℝ ⊤ g := by
    fun_prop
  have hsurj : ∀ k, g k = 0 → Function.Surjective (fderiv ℝ g k) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      dsimp [g] at hk
      nlinarith
    have hderiv : HasDerivAt g (2 * k) k := by
      simpa [g] using ((hasDerivAt_id k).pow 2).sub_const 1
    rw [hderiv.hasFDerivAt.fderiv]
    intro y
    refine ⟨y / (2 * k), ?_⟩
    simp [hk0]
  have hregular := HTGeometry.isLocalRegularLevelSetOfCodimAtLeast_zeroSet_finiteDimensional
    g (c := 1) (by norm_num) hg hsurj
  convert hregular using 1
  ext k
  simp only [oneDimensionalFreeElectronFermiSurface,
    oneDimensionalFreeElectronDispersion, Set.mem_setOf_eq, g]
  constructor <;> intro hk <;> nlinarith

/-- Unit-normalized free-electron dispersion in two momentum dimensions. -/
def twoDimensionalFreeElectronDispersion
    (k : EuclideanSpace ℝ (Fin 2)) : ℝ := ‖k‖ ^ 2

/-- Fermi surface at unit chemical potential in two momentum dimensions. -/
def twoDimensionalFreeElectronFermiSurface : Set (EuclideanSpace ℝ (Fin 2)) :=
  {k | twoDimensionalFreeElectronDispersion k = 1}

/-- The two-dimensional unit Fermi surface is exactly the unit momentum circle. -/
theorem twoDimensionalFreeElectronFermiSurface_eq_sphere :
    twoDimensionalFreeElectronFermiSurface = Metric.sphere 0 1 := by
  ext k
  simp only [twoDimensionalFreeElectronFermiSurface,
    twoDimensionalFreeElectronDispersion, Set.mem_setOf_eq, Metric.mem_sphere,
    dist_zero_right]
  constructor
  · intro hk
    nlinarith [norm_nonneg k]
  · intro hk
    nlinarith

/-! ## Reciprocal-field quantum oscillation mechanics -/

/-- Unit-frequency Onsager oscillation as a function of inverse magnetic field. -/
def unitOnsagerOscillation (inverseField : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * inverseField)

/-- The unit Onsager oscillation is periodic in inverse field. -/
theorem unitOnsagerOscillation_periodic :
    Function.Periodic unitOnsagerOscillation 1 := by
  intro inverseField
  unfold unitOnsagerOscillation
  rw [show 2 * Real.pi * (inverseField + 1) =
      2 * Real.pi * inverseField + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

/-- Unit-frequency Landau-level crossing coordinate in inverse field. -/
def unitLandauCrossing (n : ℕ) : ℝ := n + 1 / 2

/-- Consecutive Landau crossings are equally spaced in inverse field. -/
theorem unitLandauCrossing_spacing :
    ∀ n : ℕ, unitLandauCrossing (n + 1) - unitLandauCrossing n = 1 := by
  intro n
  simp only [unitLandauCrossing, Nat.cast_add, Nat.cast_one]
  ring

/-- Arbitrary Onsager phase offsets leave Landau-crossing spacing unchanged. -/
theorem landauCrossing_spacing :
    ∀ phaseOffset : ℝ, ∀ n : ℕ,
      ((n + 1 : ℕ) : ℝ) + phaseOffset - ((n : ℝ) + phaseOffset) = 1 := by
  intro phaseOffset n
  push_cast
  ring

/-- Scalar and spinor constant-field Landau ladders have an intrinsically HT comparison. -/
theorem constantMagneticLandauSpinSplit_hypertranscendental :
    HypertranscendentalOver (RatFunc ℂ)
      _root_.GaloisForLFunctions.constantMagneticQEDSpinStatisticsRatioMero :=
  _root_.GaloisForLFunctions.hypertranscendentalOver_constantMagneticQEDSpinStatisticsRatioMero

/-- No rational or finite-Laurent clock realizes the exact constant-field Landau spin split. -/
theorem constantMagneticLandauSpinSplit_ne_finiteClock :
    ∀ r : RatFunc ℂ,
      _root_.GaloisForLFunctions.constantMagneticQEDSpinStatisticsRatioMero ≠
        algebraMap (RatFunc ℂ) (_root_.Bottcher.meroField Set.univ) r :=
  _root_.GaloisForLFunctions.constantMagneticQEDSpinStatisticsRatioMero_ne_ratFuncModel

/-- Every unit Landau crossing is a trough of the Onsager oscillation. -/
theorem unitOnsagerOscillation_unitLandauCrossing :
    ∀ n : ℕ, unitOnsagerOscillation (unitLandauCrossing n) = -1 := by
  intro n
  induction n with
  | zero =>
      rw [show unitLandauCrossing 0 = 1 / 2 by
        norm_num [unitLandauCrossing]]
      unfold unitOnsagerOscillation
      rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring,
        Real.cos_pi]
  | succ n ih =>
      rw [show unitLandauCrossing (Nat.succ n) = unitLandauCrossing n + 1 by
        simp only [unitLandauCrossing, Nat.cast_succ]
        ring]
      exact unitOnsagerOscillation_periodic (unitLandauCrossing n) ▸ ih

/-- The corpus diagonal oscillation is the squared Onsager phase. -/
theorem ccmDiagonalOscillation_eq_unitOnsager_sq :
    ∀ inverseField : ℝ,
      _root_.RHTower.ccmArchimedeanGeometricCompositeDiagonalOscillation inverseField =
        unitOnsagerOscillation inverseField ^ 2 := by
  intro inverseField
  rfl

/-- Every unit Landau crossing is an intensity maximum of the corpus diagonal oscillation. -/
theorem ccmDiagonalOscillation_unitLandauCrossing :
    ∀ n : ℕ,
      _root_.RHTower.ccmArchimedeanGeometricCompositeDiagonalOscillation
        (unitLandauCrossing n) = 1 := by
  intro n
  rw [ccmDiagonalOscillation_eq_unitOnsager_sq,
    unitOnsagerOscillation_unitLandauCrossing]
  norm_num

/-- Unit-normalized Shubnikov--de Haas longitudinal response. -/
def shubnikovDeHaasResponse (inverseField : ℝ) : ℝ :=
  1 + _root_.RHTower.ccmArchimedeanGeometricCompositeDiagonalOscillation inverseField

/-- The Shubnikov--de Haas response is periodic in inverse field. -/
theorem shubnikovDeHaasResponse_periodic :
    Function.Periodic shubnikovDeHaasResponse 1 := by
  intro inverseField
  unfold shubnikovDeHaasResponse
  rw [_root_.RHTower.ccmArchimedeanGeometricCompositeDiagonalOscillation_periodic]

/-! ## Finite Onsager harmonic packets -/

/-- Entire finite Onsager packet from corpus period-one Fourier modes. -/
def finiteOnsagerPacket {k : ℕ} (amplitude : Fin k → ℂ) (z : ℂ) : ℂ :=
  HTGeometry.gammaPeriodicFourierPolynomial amplitude z

/-- Every finite Onsager packet is exactly period-one in inverse field. -/
theorem finiteOnsagerPacket_periodic :
    ∀ {k : ℕ} (amplitude : Fin k → ℂ),
      Function.Periodic (finiteOnsagerPacket amplitude) 1 := by
  intro k amplitude
  simpa [finiteOnsagerPacket] using
    HTGeometry.gammaPeriodicFourierPolynomial_periodic amplitude

/-- Arbitrary finite local response jets have a unique finite period-one Onsager packet. -/
theorem existsUnique_finiteOnsagerPacket_jet :
    ∀ {k : ℕ} (jet : Fin k → ℂ),
      ∃! amplitude : Fin k → ℂ,
        Function.Periodic (finiteOnsagerPacket amplitude) 1 ∧
          ∀ n : Fin k,
            iteratedDeriv (n : ℕ) (finiteOnsagerPacket amplitude) 0 = jet n := by
  intro k jet
  unfold finiteOnsagerPacket
  exact HTGeometry.existsUnique_gammaPeriodicFourierPolynomial_jet jet

/-- Real observable obtained from a complex finite Onsager packet. -/
def finiteOnsagerSignal {k : ℕ} (amplitude : Fin k → ℂ)
    (inverseField : ℝ) : ℝ :=
  (finiteOnsagerPacket amplitude inverseField).re

/-- Real finite Onsager signals inherit exact inverse-field period one. -/
theorem finiteOnsagerSignal_periodic :
    ∀ {k : ℕ} (amplitude : Fin k → ℂ),
      Function.Periodic (finiteOnsagerSignal amplitude) 1 := by
  intro k amplitude inverseField
  have h := finiteOnsagerPacket_periodic amplitude (inverseField : ℂ)
  simpa [finiteOnsagerSignal] using congrArg Complex.re h

/-! ## dHvA response as thermodynamic differentiation -/

/-- One-harmonic oscillatory grand potential in its phase coordinate. -/
def deHaasVanAlphenGrandPotential (phase : ℝ) : ℝ :=
  HTGeometry.phaseCosineResponse 0 1 0 phase

/-- Magnetization obtained from the one-harmonic grand potential. -/
def deHaasVanAlphenMagnetization (phase : ℝ) : ℝ :=
  HTGeometry.phaseCosineVelocity 1 0 phase

/-- The dHvA magnetization is the exact phase derivative of the oscillatory grand potential. -/
theorem deHaasVanAlphenGrandPotential_hasDerivAt :
    ∀ phase : ℝ,
      HasDerivAt deHaasVanAlphenGrandPotential
        (deHaasVanAlphenMagnetization phase) phase := by
  intro phase
  have hsub : HasDerivAt (fun theta : ℝ => theta - 0) 1 phase :=
    (hasDerivAt_id phase).sub_const 0
  have hcos := hsub.cos
  have hscaled := hcos.const_mul 1
  have hresponse := hscaled.const_sub 0
  unfold deHaasVanAlphenGrandPotential deHaasVanAlphenMagnetization
    HTGeometry.phaseCosineResponse HTGeometry.phaseCosineVelocity
  simpa using hresponse

/-! ## Lifshitz--Kosevich factors -/

/-- Continuous-value convention for the LK thermal factor `X / sinh X`. -/
def lifshitzKosevichThermalFactor (X : ℝ) : ℝ :=
  if X = 0 then 1 else X / Real.sinh X

@[simp]
theorem lifshitzKosevichThermalFactor_zero :
    lifshitzKosevichThermalFactor 0 = 1 := by
  simp [lifshitzKosevichThermalFactor]

/-- The LK thermal factor is even under reversal of its dimensionless temperature variable. -/
theorem lifshitzKosevichThermalFactor_even :
    Function.Even lifshitzKosevichThermalFactor := by
  intro X
  by_cases hX : X = 0
  · simp [hX]
  · have hneg : -X ≠ 0 := neg_ne_zero.mpr hX
    simp [lifshitzKosevichThermalFactor, hX, hneg, Real.sinh_neg]

/-- The LK factor tends to one in the zero-temperature limit. -/
theorem lifshitzKosevichThermalFactor_tendsto_zero :
    Tendsto lifshitzKosevichThermalFactor (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  refine _root_.RHTower.tendsto_self_div_sinh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with X hX
  have hX0 : X ≠ 0 := by simpa using hX
  simp [lifshitzKosevichThermalFactor, hX0]

/-- Thermal smearing strictly suppresses the LK amplitude for positive `X`. -/
theorem lifshitzKosevichThermalFactor_strictAntiOn :
    StrictAntiOn lifshitzKosevichThermalFactor (Ioi 0) := by
  intro X hX Y hY hXY
  have hXpos : 0 < X := hX
  have hYpos : 0 < Y := hY
  simpa [lifshitzKosevichThermalFactor, hXpos.ne', hYpos.ne'] using
    _root_.RHTower.div_sinh_strictAntiOn hX hY hXY

/-- On its physical half-line the LK thermal factor lies in `(0, 1]`. -/
theorem lifshitzKosevichThermalFactor_mapsTo_Ioc :
    MapsTo lifshitzKosevichThermalFactor (Ici 0) (Ioc 0 1) := by
  intro X hX
  have hXnonneg : 0 ≤ X := hX
  rcases hXnonneg.eq_or_lt with hXzero | hXpos
  · subst X
    simp
  · have hsinh : 0 < Real.sinh X := Real.sinh_pos_iff.mpr hXpos
    have hlt : X < Real.sinh X := _root_.RHTower.self_lt_sinh hXpos
    constructor
    · simp [lifshitzKosevichThermalFactor, hXpos.ne', div_pos hXpos hsinh]
    · simpa [lifshitzKosevichThermalFactor, hXpos.ne'] using
        ((div_lt_one hsinh).2 hlt).le

/-- The LK thermal factor vanishes in the high-temperature limit. -/
theorem lifshitzKosevichThermalFactor_tendsto_atTop :
    Tendsto lifshitzKosevichThermalFactor atTop (𝓝 0) := by
  refine HTGeometry.tendsto_freeDefectAngle_atTop.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  simp [lifshitzKosevichThermalFactor, ne_of_gt hX]

/-- Dingle attenuation as a function of its nonnegative scattering exponent. -/
def dingleFactor (scatteringExponent : ℝ) : ℝ :=
  Real.exp (-scatteringExponent)

/-- Independent scattering exponents multiply their Dingle attenuation. -/
theorem dingleFactor_add :
    ∀ x y : ℝ, dingleFactor (x + y) = dingleFactor x * dingleFactor y := by
  intro x y
  rw [dingleFactor, dingleFactor, dingleFactor,
    show -(x + y) = -x + -y by ring, Real.exp_add]

/-- On its physical half-line the Dingle factor lies in `(0, 1]`. -/
theorem dingleFactor_mapsTo_Ioc :
    MapsTo dingleFactor (Ici 0) (Ioc 0 1) := by
  intro scatteringExponent h
  exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr h)⟩

/-- Dingle attenuation vanishes at large scattering exponent. -/
theorem dingleFactor_tendsto_atTop :
    Tendsto dingleFactor atTop (𝓝 0) := by
  change Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0)
  exact Real.tendsto_exp_neg_atTop_nhds_zero

/-- Effective Dingle exponent carried by one damped multiple-standard-twist term. -/
def multipleTwistDingleExponent {N : ℕ} (kappa : Fin N → ℝ)
    (alpha X : ℝ) (n : Fin N → ℕ+) : ℝ :=
  (2 * Real.pi * alpha / X) *
    SelbergClass.multipleIndexPower kappa n

/-- Corpus multiple-twist damping is exactly a generalized Dingle factor. -/
theorem norm_multipleTwistDamping_eq_dingleFactor :
    ∀ {N : ℕ} (kappa : Fin N → ℝ) (alpha X : ℝ)
      (n : Fin N → ℕ+),
      ‖Complex.exp
          (-SelbergClass.multipleTwistDampingParameter alpha X *
            (SelbergClass.multipleIndexPower kappa n : ℂ))‖ =
        dingleFactor (multipleTwistDingleExponent kappa alpha X n) := by
  intro N kappa alpha X n
  simpa [dingleFactor, multipleTwistDingleExponent] using
    SelbergClass.norm_exp_multipleTwistDamping kappa alpha X n

/-- LK spin-splitting factor in a unit-normalized phase convention. -/
def lifshitzKosevichSpinFactor (spinPhase : ℝ) : ℝ :=
  Real.cos (Real.pi * spinPhase)

/-- The LK spin factor is exactly the real factor measured by a two-level survival probability. -/
theorem lifshitzKosevichSpinFactor_twoLevel_realization :
    ∀ spinPhase : ℝ,
      ‖_root_.RHTower.FiniteWindow.returningAmplitude 1 spinPhase‖ ^ 2 =
        lifshitzKosevichSpinFactor spinPhase ^ 2 := by
  intro spinPhase
  simpa [lifshitzKosevichSpinFactor] using
    _root_.RHTower.FiniteWindow.returningAmplitude_norm_sq 1 spinPhase

/-- Spin splitting is two-periodic. -/
theorem lifshitzKosevichSpinFactor_periodic :
    Function.Periodic lifshitzKosevichSpinFactor 2 := by
  intro spinPhase
  unfold lifshitzKosevichSpinFactor
  rw [show Real.pi * (spinPhase + 2) =
      Real.pi * spinPhase + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

/-- Translating spin phase by one reverses the LK spin factor. -/
theorem lifshitzKosevichSpinFactor_add_one :
    ∀ spinPhase : ℝ,
      lifshitzKosevichSpinFactor (spinPhase + 1) =
        -lifshitzKosevichSpinFactor spinPhase := by
  intro spinPhase
  unfold lifshitzKosevichSpinFactor
  rw [show Real.pi * (spinPhase + 1) =
      Real.pi * spinPhase + Real.pi by ring,
    Real.cos_add_pi]

/-- Every nonnegative half-integer spin phase is an exact LK spin-zero node. -/
theorem lifshitzKosevichSpinFactor_halfInteger_zero :
    ∀ n : ℕ,
      lifshitzKosevichSpinFactor ((n : ℝ) + 1 / 2) = 0 := by
  intro n
  induction n with
  | zero =>
      unfold lifshitzKosevichSpinFactor
      norm_num only [Nat.cast_zero, zero_add]
      rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
        Real.cos_pi_div_two]
  | succ n ih =>
      rw [show ((Nat.succ n : ℕ) : ℝ) + 1 / 2 =
          ((n : ℝ) + 1 / 2) + 1 by
        push_cast
        ring,
        lifshitzKosevichSpinFactor_add_one, ih, neg_zero]

/-- Single-harmonic Lifshitz--Kosevich amplitude. -/
def lifshitzKosevichAmplitude
    (X scatteringExponent spinPhase : ℝ) : ℝ :=
  lifshitzKosevichThermalFactor X *
    dingleFactor scatteringExponent *
      lifshitzKosevichSpinFactor spinPhase

/-- The complete single-harmonic LK amplitude retains spin-period two. -/
theorem lifshitzKosevichAmplitude_spinPeriodic :
    ∀ X scatteringExponent : ℝ,
      Function.Periodic
        (fun spinPhase =>
          lifshitzKosevichAmplitude X scatteringExponent spinPhase) 2 := by
  intro X scatteringExponent spinPhase
  change lifshitzKosevichThermalFactor X * dingleFactor scatteringExponent *
      lifshitzKosevichSpinFactor (spinPhase + 2) =
    lifshitzKosevichThermalFactor X * dingleFactor scatteringExponent *
      lifshitzKosevichSpinFactor spinPhase
  rw [lifshitzKosevichSpinFactor_periodic]

/-- High temperature kills every fixed Dingle/spin harmonic. -/
theorem lifshitzKosevichAmplitude_tendsto_temperature_atTop :
    ∀ scatteringExponent spinPhase : ℝ,
      Tendsto
        (fun X => lifshitzKosevichAmplitude X scatteringExponent spinPhase)
        atTop (𝓝 0) := by
  intro scatteringExponent spinPhase
  simpa [lifshitzKosevichAmplitude, mul_assoc] using
    lifshitzKosevichThermalFactor_tendsto_atTop.mul_const
      (dingleFactor scatteringExponent *
        lifshitzKosevichSpinFactor spinPhase)

/-- Physical thermal and scattering damping keep the complete LK harmonic in `[-1,1]`. -/
theorem abs_lifshitzKosevichAmplitude_le_one :
    ∀ X ∈ Ici (0 : ℝ), ∀ scatteringExponent ∈ Ici (0 : ℝ), ∀ spinPhase : ℝ,
      |lifshitzKosevichAmplitude X scatteringExponent spinPhase| ≤ 1 := by
  intro X hX scatteringExponent hscattering spinPhase
  have hthermal := lifshitzKosevichThermalFactor_mapsTo_Ioc hX
  have hdingle := dingleFactor_mapsTo_Ioc hscattering
  have hspin := Real.abs_cos_le_one (Real.pi * spinPhase)
  have hthermalDingle :
      lifshitzKosevichThermalFactor X * dingleFactor scatteringExponent ≤ 1 := by
    calc
      lifshitzKosevichThermalFactor X * dingleFactor scatteringExponent ≤
          1 * 1 := mul_le_mul hthermal.2 hdingle.2 hdingle.1.le (by norm_num)
      _ = 1 := by ring
  rw [lifshitzKosevichAmplitude, abs_mul, abs_mul,
    abs_of_pos hthermal.1, abs_of_pos hdingle.1]
  calc
    lifshitzKosevichThermalFactor X * dingleFactor scatteringExponent *
        |lifshitzKosevichSpinFactor spinPhase| ≤ 1 * 1 := by
      unfold lifshitzKosevichSpinFactor
      exact mul_le_mul hthermalDingle hspin (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

end GaloisForLFunctions.RHTower
