import GaloisForLFunctions.Bottcher.LoopGaugeApplications
import GaloisForLFunctions.HTGeometry.ClockPhaseEvolutionBridge
import GaloisForLFunctions.HTGeometry.ConstitutivePolarAmplitudeFisherPhase
import GaloisForLFunctions.HTGeometry.ContinuumChronometricGravity
import GaloisForLFunctions.HTGeometry.FoldedPhaseGenerator
import GaloisForLFunctions.HTGeometry.GaussianGoodCoefficientSet
import GaloisForLFunctions.HTGeometry.LoopGaugeApplications
import GaloisForLFunctions.HTGeometry.PageWoottersTopologicalClockAlgebra
import GaloisForLFunctions.HTGeometry.PhysicalFirstReturnHorizonInstabilityLaw
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw
import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier
import GaloisForLFunctions.RHTower.PrimeTorsionAutonomousCircuitPolygon
import GaloisForLFunctions.RHTower.PrimeAFXichargeNoNucleation
import GaloisForLFunctions.RHTower.RelationalClockLocalHorizonLaw
import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau
import GaloisForLFunctions.RHTower.TopologicalClockWindingReadout

/-!
# Corpus applications of topological Page--Wootters clock readout

This file mechanically instantiates the identities of arXiv:2608.27650 in existing corpus layers:

* a concrete Rice--Mele control loop and a gap-dominated harmonic perturbation;
* exact Page--Wootters evolution for the corpus's unit-gap two-level clock;
* common-phase blindness of both projective and full Choi density observers;
* doubling of the corpus Berry holonomy;
* an exact branch ledger for digitally wrapped phase increments.

Every statement is closed and unconditional.  Theorems quantify over data but introduce no axioms or
unproved physical assumptions.
-/

open Complex
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GaloisForLFunctions.TopologicalClockCorpusApplications

open HTGeometry
open PrimeQuasiLocalCharge

/-! ## A gapped Rice--Mele control loop in the scalar-circle winding layer -/

/-- Radius-`1/2` Rice--Mele control loop `delta + i Delta`. -/
def referenceRiceMeleControl (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

/-- The reference control is a bundled nonvanishing scalar loop. -/
def referenceRiceMeleControlLoop : ScalarCircleLoop where
  toFun := referenceRiceMeleControl
  isLoop := by
    refine ⟨by unfold referenceRiceMeleControl; fun_prop,
      fun _ => mul_ne_zero (by norm_num) (Complex.exp_ne_zero _), ?_⟩
    simp [referenceRiceMeleControl]

/-- The concrete Rice--Mele control cycle winds once around its gap-closing point. -/
theorem referenceRiceMeleControlLoop_winding :
    scalarCircleLoopWinding referenceRiceMeleControlLoop = 1 := by
  change RHTower.windingNumber referenceRiceMeleControl 0 (2 * Real.pi) = 1
  rw [show referenceRiceMeleControl =
      fun t : ℝ => ((1 / 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)) by
    funext t
    simp [referenceRiceMeleControl, mul_comm]]
  exact RHTower.windingNumber_scaled_circle (r := (1 / 2 : ℝ)) (by norm_num)

/-- Add a radius-`1/10` second harmonic to the reference control cycle. -/
def perturbedRiceMeleControl (t : ℝ) : ℂ :=
  referenceRiceMeleControl t +
    ((1 / 10 : ℝ) : ℂ) * Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I)

theorem perturbedRiceMeleControl_continuous : Continuous perturbedRiceMeleControl := by
  unfold perturbedRiceMeleControl referenceRiceMeleControl
  fun_prop

theorem perturbedRiceMeleControl_closed :
    perturbedRiceMeleControl 0 = perturbedRiceMeleControl (2 * Real.pi) := by
  unfold perturbedRiceMeleControl referenceRiceMeleControl
  simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one, ofReal_mul, ofReal_ofNat]
  rw [show (2 : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I =
      (2 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I) by norm_num; ring]
  rw [Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_two_pi_mul_I]
  norm_num

/-- The harmonic perturbation stays exactly `1/10` from the reference loop. -/
theorem perturbedRiceMeleControl_distance (t : ℝ) :
    ‖perturbedRiceMeleControl t - referenceRiceMeleControl t‖ = 1 / 10 := by
  rw [perturbedRiceMeleControl, add_sub_cancel_left]
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- The reference loop stays exactly `1/2` from the gap-closing point. -/
theorem referenceRiceMeleControl_norm (t : ℝ) :
    ‖referenceRiceMeleControl t‖ = 1 / 2 := by
  rw [referenceRiceMeleControl, norm_mul, Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- The perturbed loop remains nonzero, with the gap margin witnessed by its exact distance. -/
theorem perturbedRiceMeleControl_ne_zero (t : ℝ) : perturbedRiceMeleControl t ≠ 0 := by
  intro hzero
  have hdist := perturbedRiceMeleControl_distance t
  rw [hzero, zero_sub, norm_neg, referenceRiceMeleControl_norm] at hdist
  norm_num at hdist

/-- Quantitative gap protection: the second-harmonic deformation cannot change winding. -/
theorem perturbedRiceMeleControl_winding :
    RHTower.windingNumber perturbedRiceMeleControl 0 (2 * Real.pi) = 1 := by
  have hsame := RHTower.windingNumber_eq_of_close
    (γ := referenceRiceMeleControl) (δ := perturbedRiceMeleControl)
    (a := 0) (b := 2 * Real.pi) (m := (1 / 2 : ℝ))
    (by unfold referenceRiceMeleControl; fun_prop) perturbedRiceMeleControl_continuous
    (by simp [referenceRiceMeleControl]) perturbedRiceMeleControl_closed
    (fun t => by rw [referenceRiceMeleControl_norm])
    (fun t => by rw [perturbedRiceMeleControl_distance]; norm_num)
  rw [show RHTower.windingNumber referenceRiceMeleControl 0 (2 * Real.pi) = 1 by
    change scalarCircleLoopWinding referenceRiceMeleControlLoop = 1
    exact referenceRiceMeleControlLoop_winding] at hsame
  exact hsame

/-- The quantitatively protected harmonic perturbation as a bundled scalar loop. -/
def perturbedRiceMeleControlLoop : ScalarCircleLoop where
  toFun := perturbedRiceMeleControl
  isLoop := ⟨perturbedRiceMeleControl_continuous,
    perturbedRiceMeleControl_ne_zero, perturbedRiceMeleControl_closed⟩

theorem perturbedRiceMeleControlLoop_winding :
    scalarCircleLoopWinding perturbedRiceMeleControlLoop = 1 :=
  perturbedRiceMeleControl_winding

/-- Gap-protected perturbation produces the same doubled readout. -/
theorem perturbedRiceMeleFringe_winding :
    scalarCircleLoopWinding (scalarCircleLoopFringe perturbedRiceMeleControlLoop) = 2 := by
  rw [scalarCircleLoopFringe_winding, perturbedRiceMeleControlLoop_winding]
  norm_num

/-- The gapped control cycle produces the doubled forward/backward readout. -/
theorem referenceRiceMeleFringe_winding :
    scalarCircleLoopWinding (scalarCircleLoopFringe referenceRiceMeleControlLoop) = 2 := by
  rw [scalarCircleLoopFringe_winding, referenceRiceMeleControlLoop_winding]
  norm_num

/-- A topologically trivial second band leaves the unit-clock readout equal to two. -/
theorem referenceRiceMeleDifferentialFringe_winding :
    scalarCircleLoopWinding
        (scalarCircleLoopDifferentialFringe referenceRiceMeleControlLoop
          (scalarCircleLoopOfInt 0)) = 2 := by
  rw [scalarCircleLoopDifferentialFringe_winding,
    referenceRiceMeleControlLoop_winding, scalarCircleLoopOfInt_winding]
  norm_num

/-! ## Existing Page--Wootters clock orbit -/

/-- Diagonal Hamiltonian realizing the corpus's exact unit-gap two-level clock. -/
def unitGapTwoLevelHamiltonian : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => (unitGapTwoLevelSpectrum i : ℂ)

/-- The excited Page--Wootters coordinate carries exactly phase `exp (-it)`. -/
theorem unitGapPageWootters_excited_coordinate (c : Fin 2 → ℂ) (t : ℝ) :
    projectiveSpectralOrbit (0 : Fin 2) c
        (finiteClockPhasePoint
          (projectiveFrequency (fun i => -unitGapTwoLevelSpectrum i) 0) t) 1 =
      c 1 * Complex.exp (-(Complex.I * (t : ℂ))) := by
  simpa [unitGapTwoLevelSpectrum] using
    (projectiveSpectralOrbit_finiteClockPhasePoint
      (0 : Fin 2) c unitGapTwoLevelSpectrum t (1 : Fin 2))

/-- Physical unitary fidelity equals fidelity of the exact Page--Wootters phase orbit. -/
theorem unitGapPageWootters_fidelity (psi v : Fin 2 → ℂ) (t : ℝ) :
    finitePureStateFidelity (unitaryEvolution unitGapTwoLevelHamiltonian t *ᵥ psi) v =
      finitePureStateFidelity
        (projectiveSpectralOrbit (0 : Fin 2)
          (eigenCoords coordinateEigenBasis psi)
          (finiteClockPhasePoint
            (projectiveFrequency (fun i => -unitGapTwoLevelSpectrum i) 0) t))
        (eigenCoords coordinateEigenBasis v) := by
  exact finitePureStateFidelity_unitaryEvolution_eq_orbit
    (isOrthoEigenBasis_diagonal_real unitGapTwoLevelSpectrum)
    (0 : Fin 2) psi v t

/-- Corpus fixed-endpoint clock obeys exact Page--Wootters covariance on a unit time interval. -/
theorem unitIntervalPageWootters_covariant
    {n : ℕ} {theta : ℝ}
    (model : RHTower.ParityForecast.FixedEndpointPathModel 1 n theta) (s t : ℝ) :
    model.timeEvolution (by norm_num) s (model.stateAt t) = model.stateAt (s + t) :=
  model.timeEvolution_stateAt (by norm_num) s t

/-! ## Why interference is necessary: density observers erase each common phase -/

/-- Projective Choi density cannot distinguish forward and backward common phase shifts. -/
theorem uniformPhaseDensity_forward_eq_backward
    (d : ℕ) (x : Fin d → UnitAddCircle)
    (dynamic geometric common : UnitAddCircle) :
    RHTower.uniformPhaseDensity d
        (fun i => x i + (dynamic + geometric + common)) =
      RHTower.uniformPhaseDensity d
        (fun i => x i + (dynamic - geometric + common)) := by
  rw [RHTower.uniformPhaseDensity_add_common,
    RHTower.uniformPhaseDensity_add_common]

/-- Full Choi density has the same blindness; cross-arm coherence is the missing observable. -/
theorem fullUniformPhaseChoiDensity_forward_eq_backward
    (d : ℕ) (x : Fin d → UnitAddCircle)
    (dynamic geometric common : UnitAddCircle) :
    RHTower.fullUniformPhaseChoiDensity d
        (fun i => x i + (dynamic + geometric + common)) =
      RHTower.fullUniformPhaseChoiDensity d
        (fun i => x i + (dynamic - geometric + common)) := by
  rw [RHTower.fullUniformPhaseChoiDensity_add_common,
    RHTower.fullUniformPhaseChoiDensity_add_common]

/-- Ramsey X/Y tomography reads the cosine and sine of the doubled geometric phase. -/
theorem ramseyDoubledPhase_quadratures (geometric : ℝ) :
    chronometricRamseyQuadratures
        (Complex.exp (((2 * geometric : ℝ) : ℂ) * Complex.I)) =
      ((Real.cos (2 * geometric) : ℂ), (Real.sin (2 * geometric) : ℂ)) := by
  rw [chronometricRamseyQuadratures,
    trace_chronometricRamseyClockState_mul_pauliX,
    trace_chronometricRamseyClockState_mul_pauliY,
    Complex.exp_ofReal_mul_I]
  apply Prod.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
  · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, zero_add, add_zero]

/-! ## Berry holonomy and digital branch ledger -/

/-- Forward/backward composition squares and therefore doubles the corpus Berry holonomy phase. -/
theorem berryHolonomy_fringe {N : ℕ} (p : Fin N → ℝ) (k : Fin N → ℤ) :
    berryHolonomy p k ^ 2 =
      Complex.exp (Complex.I * ((4 * Real.pi * velMean p k : ℝ) : ℂ)) := by
  rw [berryHolonomy, pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A sampled phase increment inside the exact half-open Nyquist window. -/
structure NyquistSafePhaseIncrement where
  value : ℝ
  lower : -Real.pi < value
  upper : value ≤ Real.pi

instance : Coe NyquistSafePhaseIncrement ℝ := ⟨NyquistSafePhaseIncrement.value⟩

/-- The corpus phase wrapper is the identity on every bundled Nyquist-safe increment. -/
theorem NyquistSafePhaseIncrement.phaseWrap_eq (delta : NyquistSafePhaseIncrement) :
    phaseWrap delta.value = delta.value := by
  obtain ⟨hwrapLower, hwrapUpper⟩ := phaseWrap_mem delta.value
  have hledger := sub_phaseWrap_eq delta.value
  have hlower : -2 * Real.pi <
      2 * Real.pi * (branchIndex delta.value : ℝ) := by
    linarith [delta.lower, hwrapUpper]
  have hupper : 2 * Real.pi * (branchIndex delta.value : ℝ) <
      2 * Real.pi := by
    linarith [delta.upper, hwrapLower]
  have hcastLower : (-1 : ℝ) < (branchIndex delta.value : ℝ) := by
    nlinarith [Real.pi_pos]
  have hcastUpper : (branchIndex delta.value : ℝ) < (1 : ℝ) := by
    nlinarith [Real.pi_pos]
  have hintLower : (-1 : ℤ) < branchIndex delta.value := by exact_mod_cast hcastLower
  have hintUpper : branchIndex delta.value < (1 : ℤ) := by exact_mod_cast hcastUpper
  have hbranch : branchIndex delta.value = 0 := by omega
  rw [hbranch] at hledger
  norm_num at hledger ⊢
  linarith

/-- Finite Nyquist-safe packet whose true total phase is an integral number of turns. -/
structure NyquistSafeWindingPacket (n : ℕ) where
  increment : Fin n → NyquistSafePhaseIncrement
  winding : ℤ
  total : (∑ j, (increment j : ℝ)) = 2 * Real.pi * (winding : ℝ)

/-- Phase wrapping recovers exact winding on every Nyquist-safe packet. -/
theorem NyquistSafeWindingPacket.wrappedReadout_eq {n : ℕ}
    (packet : NyquistSafeWindingPacket n) :
    (∑ j, phaseWrap (packet.increment j).value) / (2 * Real.pi) = packet.winding := by
  simp_rw [NyquistSafePhaseIncrement.phaseWrap_eq]
  rw [packet.total]
  field_simp [Real.pi_ne_zero]

/-- Eight uniform `-π/2` increments realize the paper's unit-charge doubled readout `-2`. -/
def unitClockEightSamplePacket : NyquistSafeWindingPacket 8 where
  increment := fun _ =>
    { value := -(Real.pi / 2)
      lower := by linarith [Real.pi_pos]
      upper := by linarith [Real.pi_pos] }
  winding := -2
  total := by
    simp
    ring

theorem unitClockEightSample_wrappedReadout :
    (∑ j, phaseWrap (unitClockEightSamplePacket.increment j).value) /
        (2 * Real.pi) = -2 :=
  by simpa [unitClockEightSamplePacket] using
    unitClockEightSamplePacket.wrappedReadout_eq

/-- Eight standardized increment errors all stay below four standard deviations. -/
def unitClockEightSampleGaussianNoSlipSet : Set (Fin 8 → ℝ) :=
  {noise | ∀ j, |noise j| < 4}

/-- Four-sigma Gaussian union bound for the eight-step readout; no independence is used here. -/
theorem unitClockEightSample_gaussianSlipProbability_le :
    (centredProductGaussian (Fin 8) 1).real
        unitClockEightSampleGaussianNoSlipSetᶜ ≤ 16 * Real.exp (-8) := by
  classical
  have hcompl : unitClockEightSampleGaussianNoSlipSetᶜ ⊆
      ⋃ j : Fin 8, {noise : Fin 8 → ℝ | 4 ≤ |noise j|} := by
    intro noise hnoise
    rw [unitClockEightSampleGaussianNoSlipSet, Set.mem_compl_iff,
      Set.mem_setOf_eq] at hnoise
    push Not at hnoise
    obtain ⟨j, hj⟩ := hnoise
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  calc
    (centredProductGaussian (Fin 8) 1).real unitClockEightSampleGaussianNoSlipSetᶜ
        ≤ (centredProductGaussian (Fin 8) 1).real
            (⋃ j : Fin 8, {noise : Fin 8 → ℝ | 4 ≤ |noise j|}) :=
      measureReal_mono hcompl (measure_ne_top _ _)
    _ ≤ ∑ j : Fin 8,
          (centredProductGaussian (Fin 8) 1).real
            {noise : Fin 8 → ℝ | 4 ≤ |noise j|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin 8, 2 * Real.exp (-(4 : ℝ) ^ 2 / 2) :=
      Finset.sum_le_sum fun j _ =>
        measureReal_abs_ge_le_of_standardGaussian
          (p := centredProductGaussian (Fin 8) 1)
          (measurable_pi_apply j).aemeasurable
          (map_coordinate_centredProductGaussian j) (by norm_num)
    _ = 16 * Real.exp (-8) := by
      norm_num
      ring

/-- Exact aliasing ledger for any finite packet of digitally wrapped phase increments. -/
theorem sum_phaseWrap_eq_sub_branchLedger {n : ℕ} (delta : Fin n → ℝ) :
    (∑ j, phaseWrap (delta j)) =
      (∑ j, delta j) - 2 * Real.pi * (∑ j, (branchIndex (delta j) : ℝ)) := by
  have hpoint : ∀ j, phaseWrap (delta j) =
      delta j - 2 * Real.pi * (branchIndex (delta j) : ℝ) := by
    intro j
    linarith [sub_phaseWrap_eq (delta j)]
  simp_rw [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Wrapping every sampled increment preserves its unit-circle phase exactly. -/
theorem exp_phaseWrap_packet {n : ℕ} (delta : Fin n → ℝ) (j : Fin n) :
    Complex.exp (-((phaseWrap (delta j) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((delta j : ℝ) : ℂ) * Complex.I) :=
  exp_phaseWrap (delta j)

/-! ## A pre-existing Wilson-loop squaring law acquires the same even-sector diagnostic -/

/-- Quadratic Böttcher evolution is another literal forward/backward squaring readout. -/
theorem quadraticBottcherWilsonReadout_even
    (c : ℂ) {x0 : Bottcher.escapeOpen c} (path : Path x0 x0) :
    Even
      (Bottcher.wind (fun x : Bottcher.escapeOpen c => Bottcher.quadratic c (x : ℂ))
        ((Bottcher.continuous_quadratic c).comp continuous_subtype_val)
        (fun x => by
          have hx : Bottcher.quadratic c (x : ℂ) ∈ Bottcher.escapeOpen c := by
            have h := Bottcher.escapeOpen_iterate (c := c) (z := (x : ℂ)) x.2 1
            simpa [Function.iterate_one] using h
          exact Bottcher.escapeOpen_coe_ne_zero c ⟨Bottcher.quadratic c (x : ℂ), hx⟩)
        path) := by
  rw [Bottcher.LoopGaugeApplications.quadraticWilsonLoop_doubles]
  exact even_two_mul _

/-! ## Determinant Wilson histories and an unconditional Xi boundary signal -/

/-- Doubling determinant charge is pointwise squaring of its Wilson history. -/
theorem loopHistory_two_mul (charge : ℤ) (t : ℝ) :
    loopHistory (2 * charge) t = loopHistory charge t ^ 2 := by
  rw [loopHistory, loopHistory, pow_two, ← Complex.exp_add]
  congr 1
  simp only [loopSpeed]
  push_cast
  ring

/-- Logarithmic-derivative Wilson readout doubles the exact determinant charge. -/
theorem determinantWilson_fringe_winding_exact (charge : ℤ) :
    (2 * Real.pi * Complex.I)⁻¹ *
        ∫ t in (0 : ℝ)..1,
          (loopHistory (2 * charge) t)⁻¹ * deriv (loopHistory (2 * charge)) t =
      (2 * charge : ℤ) := by
  simpa using HTGeometry.LoopGaugeApplications.determinantWilson_winding_exact (2 * charge)

/-- Hardy's unconditional Xi boundary charge yields an actual nonzero even clock readout. -/
theorem exists_xiBoundaryClockFringe_nonzero_even :
    ∃ gamma : ScalarCircleLoop,
      scalarCircleLoopWinding (scalarCircleLoopFringe gamma) ≠ 0 ∧
      Even (scalarCircleLoopWinding (scalarCircleLoopFringe gamma)) := by
  obtain ⟨gamma, hcontinuous, hnonzero, hperiodic, hwinding⟩ :=
    PrimeQuasiLocalCharge.exists_xiBoundaryLoop_nonzero_winding
  let loop : ScalarCircleLoop :=
    { toFun := gamma
      isLoop := ⟨hcontinuous, hnonzero, by simpa using (hperiodic 0).symm⟩ }
  refine ⟨loop, ?_, scalarCircleLoopFringe_winding_even loop⟩
  rw [scalarCircleLoopFringe_winding]
  exact mul_ne_zero (by norm_num) hwinding

end GaloisForLFunctions.TopologicalClockCorpusApplications

end
