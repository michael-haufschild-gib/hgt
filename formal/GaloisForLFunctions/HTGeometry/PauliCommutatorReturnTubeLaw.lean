import GaloisForLFunctions.HTGeometry.PauliCommutatorGramStableRankFloor
import GaloisForLFunctions.HTGeometry.ObserverProfileStability

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem unitaryEvolution_commutes_generator
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (t : ℝ) :
    H * unitaryEvolution H t = unitaryEvolution H t * H := by
  exact (((Commute.refl H).smul_right (-Complex.I)).smul_right t).exp_right.eq

theorem hsNorm_sub_comm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    hsNorm (A - B) = hsNorm (B - A) := by
  have hmatrix : A - B = -(B - A) := by abel
  rw [hmatrix]
  change ‖-(matVec (B - A))‖ = ‖matVec (B - A)‖
  rw [norm_neg]

theorem hsNorm_commutator_le_of_near_commutingTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H U V : Matrix ι ι ℂ) (hcomm : H * V = V * H) :
    hsNorm (H * U - U * H) ≤
      2 * ‖H‖ * hsNorm (V - U) := by
  have hmatrix : H * U - U * H =
      H * (U - V) - (U - V) * H := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hcomm]
    abel
  rw [hmatrix]
  calc
    hsNorm (H * (U - V) - (U - V) * H) =
        ‖matVec (H * (U - V)) - matVec ((U - V) * H)‖ := rfl
    _ ≤ ‖matVec (H * (U - V))‖ + ‖matVec ((U - V) * H)‖ :=
      norm_sub_le _ _
    _ = hsNorm (H * (U - V)) + hsNorm ((U - V) * H) := rfl
    _ ≤ ‖H‖ * hsNorm (U - V) + hsNorm (U - V) * ‖H‖ :=
      add_le_add (hsNorm_mul_le H (U - V)) (hsNorm_mul_le' (U - V) H)
    _ = 2 * ‖H‖ * hsNorm (V - U) := by
      rw [hsNorm_sub_comm U V]
      ring

theorem hsNorm_commutator_le_of_unitaryEvolution_near
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H U : Matrix ι ι ℂ) (t : ℝ) :
    hsNorm (H * U - U * H) ≤
      2 * ‖H‖ * hsNorm (unitaryEvolution H t - U) := by
  exact hsNorm_commutator_le_of_near_commutingTarget H U
    (unitaryEvolution H t) (unitaryEvolution_commutes_generator H t)

theorem norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : TwoLocalPauliCoefficientSpace n) (t : ℝ) :
    ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ (2 : ℕ) ≤
      (2 * ‖realActivePauliHamiltonian x‖ *
        hsNorm
          (unitaryEvolution (realActivePauliHamiltonian x) t -
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) := by
  rw [norm_twoLocalPauliUnitaryCommutatorMap_sq, frobSq_eq_hsNorm_sq]
  exact pow_le_pow_left₀ (hsNorm_nonneg _)
    (hsNorm_commutator_le_of_unitaryEvolution_near
      (realActivePauliHamiltonian x)
      (U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) t) 2

/-- Energy-normalized fixed-time return law.  At every laboratory time, a
near return to any member of a finite circuit family is no likelier than the
explicit centralizer tube.  Same Hamiltonian draw appears in evolution,
energy scale, and commutator observer. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_energyNormalizedReturnTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          (2 * ‖realActivePauliHamiltonian x‖ *
            hsNorm
              (unitaryEvolution (realActivePauliHamiltonian x) t -
                (U c : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ n *
                (1 - ‖Matrix.trace
                  (U c : Matrix (FiniteQubitConfiguration (Fin n))
                    (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
                  ((2 : ℝ) ^ n) ^ (2 : ℕ)))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((n - 1 : ℕ) : ℝ) *
            (1 - ‖Matrix.trace
              (U c : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
              ((2 : ℝ) ^ n) ^ (2 : ℕ)))) := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_iUnion_explicitCommutatorTube_le U)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
    (U c) x t).trans hc⟩

/-- Target-adaptive dynamical return law.  Exact Pauli incidence, rather than
worst-target trace deficit, controls both fixed-time return radius and
anti-concentration exponent for the same static Hamiltonian draw. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_incidenceReturnTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          (2 * ‖realActivePauliHamiltonian x‖ *
            hsNorm
              (unitaryEvolution (realActivePauliHamiltonian x) t -
                (U c : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_iUnion_incidenceCommutatorTube_le U)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
    (U c) x t).trans hc⟩

/-- Support-isoperimetric dynamical return law.  A target whose Pauli mass
occupies extensive weights pays a quadratic anti-return exponent at every
fixed laboratory time for the same static two-local Hamiltonian draw. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_boundaryReturnTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          (2 * ‖realActivePauliHamiltonian x‖ *
            hsNorm
              (unitaryEvolution (realActivePauliHamiltonian x) t -
                (U c : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryBoundaryMoment (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryBoundaryMoment (U c)) := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_iUnion_boundaryCommutatorTube_le U)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
    (U c) x t).trans hc⟩

/-- Active-support dynamical return law.  At every fixed laboratory time,
Pauli mass of weight `w` pays the `w(n-1)` same-draw anti-return exponent;
full-support targets retain a quadratic penalty. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_activeWeightReturnTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          (2 * ‖realActivePauliHamiltonian x‖ *
            hsNorm
              (unitaryEvolution (realActivePauliHamiltonian x) t -
                (U c : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryActiveWeightMoment (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryActiveWeightMoment (U c)) := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_iUnion_activeWeightCommutatorTube_le U)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
    (U c) x t).trans hc⟩

/-- Enhanced active-support dynamical return law.  At every fixed laboratory
time, weight-`w` target mass pays the explicit `2wn` same-draw anti-return
exponent for one ordinary static two-local Gaussian Hamiltonian. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_enhancedActiveWeightReturnTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          (2 * ‖realActivePauliHamiltonian x‖ *
            hsNorm
              (unitaryEvolution (realActivePauliHamiltonian x) t -
                (U c : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryEnhancedActiveWeightMoment (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryEnhancedActiveWeightMoment (U c)) := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_iUnion_enhancedActiveWeightCommutatorTube_le U)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
    (U c) x t).trans hc⟩

/-- Full Pauli-weight same-draw return law.  At every fixed laboratory time,
each target pays its `2w(3n-2w)`-weighted Pauli mass in the anti-return
exponent for one ordinary static two-local Gaussian Hamiltonian. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_fullWeightPolynomialReturnTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          (2 * ‖realActivePauliHamiltonian x‖ *
            hsNorm
              (unitaryEvolution (realActivePauliHamiltonian x) t -
                (U c : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryFullWeightPolynomialMoment (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryFullWeightPolynomialMoment (U c)) := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_iUnion_fullWeightPolynomialCommutatorTube_le U)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
    (U c) x t).trans hc⟩

/-- Sharp worst-target same-draw return law.  Every nonprojective target pays
`6n-4` times normalized trace deficit at every fixed laboratory time. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_sixNSubFourReturnTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          (2 * ‖realActivePauliHamiltonian x‖ *
            hsNorm
              (unitaryEvolution (realActivePauliHamiltonian x) t -
                (U c : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                (((6 * n - 4 : ℕ) : ℝ) *
                  (1 - ‖Matrix.trace
                    (U c : Matrix (FiniteQubitConfiguration (Fin n))
                      (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
                    ((2 : ℝ) ^ n) ^ (2 : ℕ))))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((6 * n - 4 : ℕ) : ℝ) *
            (1 - ‖Matrix.trace
              (U c : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
              ((2 : ℝ) ^ n) ^ (2 : ℕ)))) := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_iUnion_sixNSubFourCommutatorTube_le U)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
    (U c) x t).trans hc⟩

end

end GaloisForLFunctions.HTGeometry
