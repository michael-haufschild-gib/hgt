import GaloisForLFunctions.RHTower.StaticChoiComplexityAlternationLaw
import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau
import GaloisForLFunctions.RHTower.StaticChoiTraceDistanceLaw
import GaloisForLFunctions.HTGeometry.PauliBoundedHamiltonianLocalityLaw
import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity

/-!
# Static Choi complexity plateau for bounded-weight Pauli Hamiltonians

The abstract static Choi plateau, syndetic hardness and alternation laws are specialized here to
the traceless fixed-weight Pauli ensemble on `n` qubits.  The eigenvalue family of a real
combination of nonidentity Pauli strings of weight at most `q` is relabelled from computational
configurations to `Fin (2 ^ n)`, where the projective genericity already proved for that ensemble
supplies the maximal projective rank hypothesis verbatim.

Consequently, for `q ≥ 2`, the completed-time occupation bound, the syndetic circuit-hardness law
and the ordered recurrence–hardness–recurrence alternation hold on a dense residual
full-Lebesgue-measure set of Pauli coefficient vectors, hence almost surely for every ensemble
with a density — in particular for a Gaussian ensemble.
-/

open Set MeasureTheory Filter
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Relabelling of the computational register by `Fin (d + 1)` when `d + 1 = 2 ^ n`. -/
def pauliRegisterEquiv {n d : ℕ} (hd : d + 1 = 2 ^ n) :
    Fin (d + 1) ≃ FiniteQubitConfiguration (Fin n) :=
  (finCongr hd).trans
    (Fintype.equivFinOfCardEq
      (α := FiniteQubitConfiguration (Fin n)) (n := 2 ^ n) (by simp)).symm

/-- Eigenvalue family of a traceless bounded-weight Pauli Hamiltonian, indexed by
`Fin (d + 1)`. -/
def pauliTracelessChoiEnergy {n d q : ℕ} (hd : d + 1 = 2 ^ n)
    (p : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ) : Fin (d + 1) → ℝ :=
  fun i => (isHermitian_pauliTracelessFinEval p).eigenvalues (pauliRegisterEquiv hd i)

theorem maximallyProjective_pauliTracelessChoiEnergy {n d q : ℕ} (hd : d + 1 = 2 ^ n)
    (p : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)
    (hmax : MaximallyProjectiveEnergy (isHermitian_pauliTracelessFinEval p).eigenvalues) :
    MaximallyProjectiveEnergy (pauliTracelessChoiEnergy hd p) :=
  MaximallyProjectiveEnergy.comp_equiv hmax (pauliRegisterEquiv hd)

/-- Maximal projective rank of a generic traceless fixed-weight Pauli Hamiltonian. -/
theorem maximallyProjective_of_mem_pauliTracelessGenericSet {n q : ℕ} (hq : 2 ≤ q)
    (p : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q)) :
    MaximallyProjectiveEnergy (isHermitian_pauliTracelessFinEval p).eigenvalues :=
  ((pauliTraceless_simple_and_projectivelyIndependent_generically n hq).2.2.2 p hp).2

/-- **Completed-time occupation plateau for the traceless fixed-weight Pauli ensemble.** At every
generic Pauli coefficient vector the completed-time occupation of the padded-circuit target is at
most its Haar volume, which is bounded by the explicit circuit-entropy factor. -/
theorem pauliTraceless_completedTime_paddedCircuitTargets
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) {d : ℕ} (hd : d + 1 = 2 ^ n)
    (p : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q))
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ) :
    let A := zeroAnchoredPaddedCircuitTarget d s target δ
    atTop.limsup (fun T ↦
        (finiteTorusPhaseProbabilityMeasure
          (zeroProjectiveFrequency (pauliTracelessChoiEnergy hd p)) T :
            Measure (UnitAddTorus (Fin d))) A) ≤ volume A ∧
      volume.real A ≤
        (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) :=
  completedTime_zeroAnchoredPaddedCircuitTargets (pauliTracelessChoiEnergy hd p)
    (maximallyProjective_pauliTracelessChoiEnergy hd p
      (maximallyProjective_of_mem_pauliTracelessGenericSet hq p hp))
    s target hδ

/-- **Syndetic circuit hardness for the traceless fixed-weight Pauli ensemble.** Below the
entropy threshold, hard endpoints of the Choi trajectory occur in every interval of one finite
length. -/
theorem pauliTraceless_pureChoiTraceHardTimes_syndetic
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) {d : ℕ} (hd : d + 1 = 2 ^ n)
    (p : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q))
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    {ε : ℝ} (hε : 0 < ε)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt
              (Real.pi * (2 * (Real.sqrt 2 * ε) ^ 2) / 2) ^
                ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      ∀ w : PaddedCircuitWord gate s,
        ε < pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d
              (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) t)))
          (target w) :=
  maximallyProjective_pureChoiTraceHardTimes_syndetic (pauliTracelessChoiEnergy hd p)
    (maximallyProjective_pauliTracelessChoiEnergy hd p
      (maximallyProjective_of_mem_pauliTracelessGenericSet hq p hp))
    s target htarget hε hentropy

/-- **Ordered operational alternation for the traceless fixed-weight Pauli ensemble.** Every
generic Pauli Hamiltonian alternates forever between operational recurrence and bounded-circuit
hardness, with one finite bound on every leg. -/
theorem pauliTraceless_pureChoiComplexity_alternates_syndetically
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) {d : ℕ} (hd : d + 1 = 2 ^ n)
    (p : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q))
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identityWord : PaddedCircuitWord gate s)
    (hidentity : target identityWord =
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {ε : ℝ} (hε : 0 < ε)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt
              (Real.pi * (2 * (Real.sqrt 2 * ε) ^ 2) / 2) ^
                ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ tLow ∈ Set.Icc a (a + L),
      ∃ tHigh ∈ Set.Ioc tLow (tLow + L),
      ∃ tLow' ∈ Set.Ioc tHigh (tHigh + L),
        pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tLow)))
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε ∧
        (∀ w : PaddedCircuitWord gate s,
          ε < pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tHigh)))
            (target w)) ∧
        pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tLow')))
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε :=
  maximallyProjective_pureChoiComplexity_alternates_syndetically
    (pauliTracelessChoiEnergy hd p)
    (maximallyProjective_pauliTracelessChoiEnergy hd p
      (maximallyProjective_of_mem_pauliTracelessGenericSet hq p hp))
    s target htarget identityWord hidentity hε hentropy

/-- **Almost-sure ordered alternation for every full-density fixed-weight Pauli ensemble.** For
`q ≥ 2` and any coefficient law absolutely continuous with respect to Lebesgue measure — in
particular a Gaussian ensemble — the ordered recurrence–hardness–recurrence law holds with
probability one. -/
theorem pauliTraceless_pureChoiComplexity_alternates_syndetically_ae
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) {d : ℕ} (hd : d + 1 = 2 ^ n)
    {μ : Measure (Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)} (hμ : μ ≪ volume)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identityWord : PaddedCircuitWord gate s)
    (hidentity : target identityWord =
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {ε : ℝ} (hε : 0 < ε)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt
              (Real.pi * (2 * (Real.sqrt 2 * ε) ^ 2) / 2) ^
                ((d + 1 : ℕ) - 1)) < 1) :
    ∀ᵐ p ∂μ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
        ∃ tLow ∈ Set.Icc a (a + L),
        ∃ tHigh ∈ Set.Ioc tLow (tLow + L),
        ∃ tLow' ∈ Set.Ioc tHigh (tHigh + L),
          pureStateTraceDistance
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d
                  (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tLow)))
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε ∧
          (∀ w : PaddedCircuitWord gate s,
            ε < pureStateTraceDistance
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d
                  (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tHigh)))
              (target w)) ∧
          pureStateTraceDistance
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d
                  (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tLow')))
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε := by
  filter_upwards [pauliTraceless_projectivelyIndependent_ae n hq hμ] with p hp
  exact maximallyProjective_pureChoiComplexity_alternates_syndetically
    (pauliTracelessChoiEnergy hd p)
    (maximallyProjective_pauliTracelessChoiEnergy hd p hp.2)
    s target htarget identityWord hidentity hε hentropy

/-- **Almost-sure completed-time occupation plateau for every full-density fixed-weight Pauli
ensemble.** -/
theorem pauliTraceless_completedTime_paddedCircuitTargets_ae
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) {d : ℕ} (hd : d + 1 = 2 ^ n)
    {μ : Measure (Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)} (hμ : μ ≪ volume)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ p ∂μ,
      atTop.limsup (fun T ↦
          (finiteTorusPhaseProbabilityMeasure
            (zeroProjectiveFrequency (pauliTracelessChoiEnergy hd p)) T :
              Measure (UnitAddTorus (Fin d)))
            (zeroAnchoredPaddedCircuitTarget d s target δ)) ≤
        volume (zeroAnchoredPaddedCircuitTarget d s target δ) ∧
      volume.real (zeroAnchoredPaddedCircuitTarget d s target δ) ≤
        (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) := by
  filter_upwards [pauliTraceless_projectivelyIndependent_ae n hq hμ] with p hp
  exact completedTime_zeroAnchoredPaddedCircuitTargets (pauliTracelessChoiEnergy hd p)
    (maximallyProjective_pauliTracelessChoiEnergy hd p hp.2) s target hδ

/-- **Ordered operational alternation for the fixed-weight Pauli Gaussian ensemble.** For `q ≥ 2`
and a nondegenerate product Gaussian law on the nonidentity Pauli coefficients, the ordered
recurrence--hardness--recurrence law holds with probability one. -/
theorem pauliTracelessGaussian_pureChoiComplexity_alternates_syndetically_ae
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) {d : ℕ} (hd : d + 1 = 2 ^ n)
    {v : NNReal} (hv : v ≠ 0)
    (mean : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identityWord : PaddedCircuitWord gate s)
    (hidentity : target identityWord =
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {ε : ℝ} (hε : 0 < ε)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt
              (Real.pi * (2 * (Real.sqrt 2 * ε) ^ 2) / 2) ^
                ((d + 1 : ℕ) - 1)) < 1) :
    ∀ᵐ p ∂(Measure.pi fun i => ProbabilityTheory.gaussianReal (mean i) v),
      ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
        ∃ tLow ∈ Set.Icc a (a + L),
        ∃ tHigh ∈ Set.Ioc tLow (tLow + L),
        ∃ tLow' ∈ Set.Ioc tHigh (tHigh + L),
          pureStateTraceDistance
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d
                  (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tLow)))
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε ∧
          (∀ w : PaddedCircuitWord gate s,
            ε < pureStateTraceDistance
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d
                  (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tHigh)))
              (target w)) ∧
          pureStateTraceDistance
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d
                  (projectivePhysicalPhaseFlow (pauliTracelessChoiEnergy hd p) tLow')))
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε :=
  pauliTraceless_pureChoiComplexity_alternates_syndetically_ae n hq hd
    (productGaussian_absolutelyContinuous _ hv mean)
    s target htarget identityWord hidentity hε hentropy

/-- **Completed-time occupation plateau for the fixed-weight Pauli Gaussian ensemble.** -/
theorem pauliTracelessGaussian_completedTime_paddedCircuitTargets_ae
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) {d : ℕ} (hd : d + 1 = 2 ^ n)
    {v : NNReal} (hv : v ≠ 0)
    (mean : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ p ∂(Measure.pi fun i => ProbabilityTheory.gaussianReal (mean i) v),
      atTop.limsup (fun T ↦
          (finiteTorusPhaseProbabilityMeasure
            (zeroProjectiveFrequency (pauliTracelessChoiEnergy hd p)) T :
              Measure (UnitAddTorus (Fin d)))
            (zeroAnchoredPaddedCircuitTarget d s target δ)) ≤
        volume (zeroAnchoredPaddedCircuitTarget d s target δ) ∧
      volume.real (zeroAnchoredPaddedCircuitTarget d s target δ) ≤
        (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) :=
  pauliTraceless_completedTime_paddedCircuitTargets_ae n hq hd
    (productGaussian_absolutelyContinuous _ hv mean) s target hδ

end RHTower
