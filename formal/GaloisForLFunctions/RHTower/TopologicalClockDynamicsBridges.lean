import GaloisForLFunctions.RHTower.TopologicalClockCorpusBridges
import GaloisForLFunctions.Bottcher.LoopGaugeApplications
import GaloisForLFunctions.HTGeometry.FormationClockTransmutation
import GaloisForLFunctions.HTGeometry.PauliBoundedWeightSpan

open scoped BigOperators Matrix
open Complex Topology unitInterval

noncomputable section

namespace GaloisForLFunctions.RHTower.TopologicalClockApplications

def iteratedPaperReadoutLoop (C : ℤ) (n : ℕ) :
    PrimeQuasiLocalCharge.ScalarCircleLoop where
  toFun := fun t => paperGeometricLoop C t ^ (2 ^ n)
  isLoop := by
    refine ⟨(paperGeometricLoop C).isLoop.continuous.pow (2 ^ n),
      fun t => pow_ne_zero _ ((paperGeometricLoop C).isLoop.nonzero t), ?_⟩
    rw [(paperGeometricLoop C).isLoop.closed]

theorem iteratedPaperReadoutLoop_winding (C : ℤ) (n : ℕ) :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (iteratedPaperReadoutLoop C n) =
      -((2 : ℤ) ^ n) * C := by
  change RHTower.windingNumber (fun t => paperGeometricLoop C t ^ (2 ^ n))
      0 (2 * Real.pi) = _
  rw [RHTower.windingNumber_pow (paperGeometricLoop C).isLoop (2 ^ n)]
  change ((2 ^ n : ℕ) : ℤ) *
      PrimeQuasiLocalCharge.scalarCircleLoopWinding (paperGeometricLoop C) = _
  rw [paperGeometricLoop_winding]
  push_cast
  ring

theorem quadraticWilsonLoop_is_singleClockReadout
    (c : ℂ) {x0 : Bottcher.escapeOpen c} (p : Path x0 x0) :
    Bottcher.wind (fun x : Bottcher.escapeOpen c => Bottcher.quadratic c (x : ℂ))
        ((Bottcher.continuous_quadratic c).comp continuous_subtype_val)
        (fun x => by
          have hx : Bottcher.quadratic c (x : ℂ) ∈ Bottcher.escapeOpen c := by
            have h := Bottcher.escapeOpen_iterate (c := c) (z := (x : ℂ)) x.2 1
            simpa [Function.iterate_one] using h
          exact Bottcher.escapeOpen_coe_ne_zero c
            ⟨Bottcher.quadratic c (x : ℂ), hx⟩) p =
      PrimeQuasiLocalCharge.scalarCircleLoopWinding
        (iteratedPaperReadoutLoop
          (-Bottcher.LoopGaugeApplications.farFieldWilsonWinding c p) 1) := by
  rw [Bottcher.LoopGaugeApplications.quadraticWilsonLoop_doubles,
    iteratedPaperReadoutLoop_winding]
  ring

theorem iteratedQuadraticWilsonLoop_is_iteratedClockReadout
    (c : ℂ) (n : ℕ) {x0 : Bottcher.escapeOpen c} (p : Path x0 x0) :
    Bottcher.wind (fun x : Bottcher.escapeOpen c => (Bottcher.quadratic c)^[n] (x : ℂ))
        (((Bottcher.continuous_quadratic c).iterate n).comp continuous_subtype_val)
        (fun x => Bottcher.escapeOpen_coe_ne_zero c
          ⟨(Bottcher.quadratic c)^[n] (x : ℂ),
            Bottcher.escapeOpen_iterate x.2 n⟩) p =
      PrimeQuasiLocalCharge.scalarCircleLoopWinding
        (iteratedPaperReadoutLoop
          (-Bottcher.LoopGaugeApplications.farFieldWilsonWinding c p) n) := by
  rw [Bottcher.LoopGaugeApplications.iteratedQuadraticWilsonLoop_degree,
    iteratedPaperReadoutLoop_winding]
  ring

theorem bottcherWilsonLoop_is_iteratedClockReadout
    (c : ℂ) (n : ℕ) {x0 : Bottcher.escapeOpen c} (p : Path x0 x0) :
    Bottcher.wind (fun x : Bottcher.escapeOpen c =>
          Bottcher.bottcherCoord c ((Bottcher.quadratic c)^[n] (x : ℂ)))
        (Bottcher.continuous_bottcherCoord_iterate_escapeOpen c n)
        (fun _ => Bottcher.bottcherCoord_ne_zero c _) p =
      PrimeQuasiLocalCharge.scalarCircleLoopWinding
        (iteratedPaperReadoutLoop
          (-Bottcher.LoopGaugeApplications.farFieldWilsonWinding c p) n) := by
  rw [Bottcher.LoopGaugeApplications.bottcherWilsonLoop_degree,
    iteratedPaperReadoutLoop_winding]
  ring

def unitFormationClock (k : ℕ) : ℝ := k

def doubleFormationClock (k : ℕ) : ℝ := 2 * k

theorem unitFormationClock_edge (k : ℕ) :
    HTGeometry.formationClockEdge unitFormationClock k = 1 := by
  simp [HTGeometry.formationClockEdge, unitFormationClock]

theorem doubleFormationClock_edge (k : ℕ) :
    HTGeometry.formationClockEdge doubleFormationClock k = 2 := by
  simp [HTGeometry.formationClockEdge, doubleFormationClock]
  ring

theorem explicitFormationClock_forwardRate (k : ℕ) :
    HTGeometry.relativeFormationClockRate unitFormationClock doubleFormationClock k = 2 := by
  rw [HTGeometry.relativeFormationClockRate, unitFormationClock_edge,
    doubleFormationClock_edge]
  norm_num

theorem explicitFormationClock_reverseRate (k : ℕ) :
    HTGeometry.relativeFormationClockRate doubleFormationClock unitFormationClock k = 1 / 2 := by
  rw [HTGeometry.relativeFormationClockRate, unitFormationClock_edge,
    doubleFormationClock_edge]

theorem explicitFormationClock_forward_reverse_cancel (k : ℕ) :
    HTGeometry.relativeFormationClockRate unitFormationClock doubleFormationClock k *
      HTGeometry.relativeFormationClockRate doubleFormationClock unitFormationClock k = 1 := by
  exact HTGeometry.relativeFormationClockRate_mul_reverse
    unitFormationClock doubleFormationClock
    (by rw [unitFormationClock_edge]; norm_num)
    (by rw [doubleFormationClock_edge]; norm_num)

def periodicDynamicalPhase (a b k : ℝ) : ℝ :=
  a * Real.cos k + b * Real.sin k

theorem hasDerivAt_periodicDynamicalPhase (a b k : ℝ) :
    HasDerivAt (periodicDynamicalPhase a b)
      (-a * Real.sin k + b * Real.cos k) k := by
  unfold periodicDynamicalPhase
  have h := (Real.hasDerivAt_cos k).const_mul a |>.add
    ((Real.hasDerivAt_sin k).const_mul b)
  have hfun : ((fun y : ℝ => a * Real.cos y) + fun y => b * Real.sin y) =
      fun y => a * Real.cos y + b * Real.sin y := by
    funext y
    rfl
  rw [hfun] at h
  simpa only [mul_neg, neg_mul] using h

theorem periodicDynamicalPhase_derivative_integral_zero (a b : ℝ) :
    ∫ k in (-Real.pi)..Real.pi, deriv (periodicDynamicalPhase a b) k = 0 := by
  have hdiff : ∀ k ∈ Set.uIcc (-Real.pi) Real.pi,
      DifferentiableAt ℝ (periodicDynamicalPhase a b) k := by
    intro k _
    exact (hasDerivAt_periodicDynamicalPhase a b k).differentiableAt
  have hderiv : deriv (periodicDynamicalPhase a b) =
      fun k => -a * Real.sin k + b * Real.cos k := by
    funext k
    exact (hasDerivAt_periodicDynamicalPhase a b k).deriv
  have hint : IntervalIntegrable (deriv (periodicDynamicalPhase a b))
      MeasureTheory.volume (-Real.pi) Real.pi := by
    rw [hderiv]
    exact (by fun_prop : Continuous (fun k : ℝ => -a * Real.sin k + b * Real.cos k))
      |>.intervalIntegrable (-Real.pi) Real.pi
  rw [intervalIntegral.integral_deriv_eq_sub hdiff hint]
  simp [periodicDynamicalPhase, Real.cos_neg, Real.sin_neg]

theorem uniformPacket_periodicDisplacement_zero (a b : ℝ) :
    (1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi, deriv (periodicDynamicalPhase a b) k = 0 := by
  rw [periodicDynamicalPhase_derivative_integral_zero, mul_zero]

def oneQubitPauliLabel (a : Fin 3) : Fin 1 → Option (Fin 3) :=
  fun _ => some a

def riceMelePauliHamiltonian (J delta Delta k : ℝ) :
    selfAdjoint (Matrix (HTGeometry.FiniteQubitConfiguration (Fin 1))
      (HTGeometry.FiniteQubitConfiguration (Fin 1)) ℂ) :=
  riceMeleDx J delta k • HTGeometry.finitePauliSelfAdjoint (oneQubitPauliLabel 0) +
    riceMeleDy J delta k • HTGeometry.finitePauliSelfAdjoint (oneQubitPauliLabel 1) +
      Delta • HTGeometry.finitePauliSelfAdjoint (oneQubitPauliLabel 2)

def riceMelePauliHamiltonianMatrix (J delta Delta k : ℝ) :
    Matrix (HTGeometry.FiniteQubitConfiguration (Fin 1))
      (HTGeometry.FiniteQubitConfiguration (Fin 1)) ℂ :=
  riceMelePauliHamiltonian J delta Delta k

theorem riceMelePauliHamiltonian_isHermitian (J delta Delta k : ℝ) :
    (riceMelePauliHamiltonianMatrix J delta Delta k).IsHermitian := by
  exact (riceMelePauliHamiltonian J delta Delta k).property

theorem oneQubitPauli_mem_weightOneSpan (a : Fin 3) :
    HTGeometry.finitePauliMatrix (oneQubitPauliLabel a) ∈ HTGeometry.pauliSpan 1 1 := by
  apply HTGeometry.finitePauliMatrix_mem_pauliSpan
  · simp [HTGeometry.pauliWeight, oneQubitPauliLabel]
  · intro h
    have h0 := congrFun h (0 : Fin 1)
    simp [oneQubitPauliLabel, HTGeometry.pauliIdentityLabel] at h0

theorem riceMelePauliHamiltonian_mem_weightOneSpan (J delta Delta k : ℝ) :
    riceMelePauliHamiltonianMatrix J delta Delta k ∈ HTGeometry.pauliSpan 1 1 := by
  change (((riceMeleDx J delta k : ℝ) : ℂ) •
        HTGeometry.finitePauliMatrix (oneQubitPauliLabel 0) +
      ((riceMeleDy J delta k : ℝ) : ℂ) •
        HTGeometry.finitePauliMatrix (oneQubitPauliLabel 1) +
      ((Delta : ℝ) : ℂ) • HTGeometry.finitePauliMatrix (oneQubitPauliLabel 2)) ∈
    HTGeometry.pauliSpan 1 1
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ _ (oneQubitPauli_mem_weightOneSpan 0))
      (Submodule.smul_mem _ _ (oneQubitPauli_mem_weightOneSpan 1)))
    (Submodule.smul_mem _ _ (oneQubitPauli_mem_weightOneSpan 2))

end GaloisForLFunctions.RHTower.TopologicalClockApplications

end
