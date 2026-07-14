import GaloisForLFunctions.RHTower.PrimeArchThermalKrylovEquivalence
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaPolarSourceLaw

/-!
# Local finite KMS moment closure for the prime--archimedean source

The thermodynamic KMS capstone does not require a finite system realizing every source moment.
Even a preassembled convergent family is unnecessary: arbitrary approximation of each finite
initial moment block by some canonical finite KMS/Wightman system produces a diagonal
product-topology limit.  Closedness of the trace-Hankel cone then supplies the source positivity
used by the RH consumer.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Every finite initial block of `target` lies in the coordinatewise closure of canonical finite
KMS/Wightman moment systems.  The witnessing system may depend independently on the cutoff and
tolerance. -/
def FiniteKMSWightmanLocalMomentClosure (target : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ m : ℕ → ℝ,
      FiniteKMSWightmanMomentSequence m ∧
        ∀ n : ℕ, n < N → dist (m n) (target n) < ε

/-- A scalar sequence represented by finitely many nonnegative masses at nonnegative nodes. -/
def FinitePositiveAtomicMomentSequence (m : ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ mass node : Fin d → ℝ,
    (∀ i, 0 ≤ mass i) ∧ (∀ i, 0 ≤ node i) ∧
      m = fun n => ∑ i, mass i * node i ^ n

/-- Every finite positive atomic Stieltjes moment sequence is a canonical finite KMS/Wightman
moment sequence. -/
theorem finitePositiveAtomicMomentSequence_finiteKMSWightman
    {m : ℕ → ℝ} (hm : FinitePositiveAtomicMomentSequence m) :
    FiniteKMSWightmanMomentSequence m := by
  obtain ⟨d, mass, node, hmass, hnode, rfl⟩ := hm
  refine ⟨d, 0, HTGeometry.finiteAtomicThermalEnergy node,
    HTGeometry.finiteAtomicKMSAmplitude mass, ?_⟩
  funext n
  exact (HTGeometry.thermalEvenGapMoment_finiteAtomicKMS
    mass node hmass hnode n).symm

/-- The explicit Xi thermal truncations are finite positive atomic Stieltjes moment sequences. -/
theorem finitePositiveAtomicMomentSequence_xiThermalTruncation (N : ℕ) :
    FinitePositiveAtomicMomentSequence (xiThermalTruncation N) := by
  let node : Fin N → ℝ := fun i => xiThermalNode (xiThermalEnumeration i)
  refine ⟨N, node, node, fun i => (xiThermalNode_pos _).le,
    fun i => (xiThermalNode_pos _).le, ?_⟩
  funext n
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => xiThermalNode (xiThermalEnumeration j) *
      xiThermalNode (xiThermalEnumeration j) ^ n) N).symm

/-- Every finite initial block of `target` is arbitrarily approximable by scalar finite positive
atomic Stieltjes moments. -/
def FinitePositiveAtomicLocalMomentClosure (target : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ m : ℕ → ℝ,
      FinitePositiveAtomicMomentSequence m ∧
        ∀ n : ℕ, n < N → dist (m n) (target n) < ε

/-- One canonical countable schedule of independent finite positive-atomic certificates: at level
`j`, approximate the first `j+1` coordinates within `1/(j+1)`. -/
def FinitePositiveAtomicDiagonalApproximation (target : ℕ → ℝ) : Prop :=
  ∀ j : ℕ,
    ∃ m : ℕ → ℝ,
      FinitePositiveAtomicMomentSequence m ∧
        ∀ n : ℕ, n < j + 1 →
          dist (m n) (target n) < 1 / ((j : ℝ) + 1)

/-- Scalar positive-atomic local closure implies canonical finite-KMS local closure. -/
theorem finiteKMSWightmanLocalMomentClosure_of_finitePositiveAtomicLocalMomentClosure
    {target : ℕ → ℝ}
    (h : FinitePositiveAtomicLocalMomentClosure target) :
    FiniteKMSWightmanLocalMomentClosure target := by
  intro N ε hε
  obtain ⟨m, hm, happrox⟩ := h N ε hε
  exact ⟨m, finitePositiveAtomicMomentSequence_finiteKMSWightman hm, happrox⟩

/-- Local finite-block closure automatically assembles into one sequence of canonical finite KMS
systems converging pointwise to the entire target moment sequence. -/
theorem exists_finiteKMSWightmanMomentSequence_tendsto_of_localMomentClosure
    {target : ℕ → ℝ}
    (h : FiniteKMSWightmanLocalMomentClosure target) :
    ∃ m : ℕ → ℕ → ℝ,
      (∀ j, FiniteKMSWightmanMomentSequence (m j)) ∧
        Tendsto m atTop (nhds target) := by
  have happ : ∀ j : ℕ, ∃ mj : ℕ → ℝ,
      FiniteKMSWightmanMomentSequence mj ∧
        ∀ n : ℕ, n < j + 1 →
          dist (mj n) (target n) < 1 / ((j : ℝ) + 1) := by
    intro j
    exact h (j + 1) (1 / ((j : ℝ) + 1)) (by positivity)
  choose m hm happrox using happ
  refine ⟨m, hm, ?_⟩
  apply tendsto_pi_nhds.mpr
  intro n
  rw [Metric.tendsto_atTop]
  intro ε hε
  have herr : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp herr
  refine ⟨max J n, fun j hj => ?_⟩
  exact (happrox j n (by omega)).trans
    (hJ j (le_trans (le_max_left _ _) hj))

/-- Conversely, a pointwise convergent family of canonical finite KMS systems gives local
finite-block closure.  Only finitely many coordinatewise convergence estimates have to be
simultaneous for each requested block. -/
theorem finiteKMSWightmanLocalMomentClosure_of_tendsto
    {target : ℕ → ℝ} {m : ℕ → ℕ → ℝ}
    (hm : ∀ j, FiniteKMSWightmanMomentSequence (m j))
    (hconv : Tendsto m atTop (nhds target)) :
    FiniteKMSWightmanLocalMomentClosure target := by
  intro N ε hε
  have hev : ∀ᶠ j : ℕ in atTop,
      ∀ n ∈ Finset.range N, dist (m j n) (target n) < ε := by
    rw [Finset.eventually_all]
    intro n hn
    exact eventually_atTop.mpr
      ((Metric.tendsto_atTop.mp ((tendsto_pi_nhds.mp hconv) n)) ε hε)
  obtain ⟨j, hj⟩ := hev.exists
  exact ⟨m j, hm j, fun n hn => hj n (Finset.mem_range.mpr hn)⟩

/-- A pointwise limit of scalar finite positive atomic moment sequences lies in their local
finite-block closure. -/
theorem finitePositiveAtomicLocalMomentClosure_of_tendsto
    {target : ℕ → ℝ} {m : ℕ → ℕ → ℝ}
    (hm : ∀ j, FinitePositiveAtomicMomentSequence (m j))
    (hconv : Tendsto m atTop (nhds target)) :
    FinitePositiveAtomicLocalMomentClosure target := by
  intro N ε hε
  have hev : ∀ᶠ j : ℕ in atTop,
      ∀ n ∈ Finset.range N, dist (m j n) (target n) < ε := by
    rw [Finset.eventually_all]
    intro n hn
    exact eventually_atTop.mpr
      ((Metric.tendsto_atTop.mp ((tendsto_pi_nhds.mp hconv) n)) ε hε)
  obtain ⟨j, hj⟩ := hev.exists
  exact ⟨m j, hm j, fun n hn => hj n (Finset.mem_range.mpr hn)⟩

/-- The canonical diagonal certificate schedule assembles into a pointwise convergent sequence of
finite positive-atomic moment systems. -/
theorem exists_finitePositiveAtomicMomentSequence_tendsto_of_diagonalApproximation
    {target : ℕ → ℝ}
    (h : FinitePositiveAtomicDiagonalApproximation target) :
    ∃ m : ℕ → ℕ → ℝ,
      (∀ j, FinitePositiveAtomicMomentSequence (m j)) ∧
        Tendsto m atTop (nhds target) := by
  choose m hm happrox using h
  refine ⟨m, hm, ?_⟩
  apply tendsto_pi_nhds.mpr
  intro n
  rw [Metric.tendsto_atTop]
  intro ε hε
  have herr : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp herr
  refine ⟨max J n, fun j hj => ?_⟩
  exact (happrox j n (by omega)).trans
    (hJ j (le_trans (le_max_left _ _) hj))

/-- Local finite-block closure is equivalent to the single countable diagonal error schedule. -/
theorem finitePositiveAtomicLocalMomentClosure_iff_diagonalApproximation
    {target : ℕ → ℝ} :
    FinitePositiveAtomicLocalMomentClosure target ↔
      FinitePositiveAtomicDiagonalApproximation target := by
  constructor
  · intro h j
    exact h (j + 1) (1 / ((j : ℝ) + 1)) (by positivity)
  · intro h
    obtain ⟨m, hm, hconv⟩ :=
      exists_finitePositiveAtomicMomentSequence_tendsto_of_diagonalApproximation h
    exact finitePositiveAtomicLocalMomentClosure_of_tendsto hm hconv

/-- Local canonical finite-KMS closure places the target in the complete trace-Hankel cone. -/
theorem sequenceTraceHankelNonnegative_of_finiteKMSWightmanLocalMomentClosure
    {target : ℕ → ℝ}
    (h : FiniteKMSWightmanLocalMomentClosure target) :
    SequenceTraceHankelNonnegative target := by
  obtain ⟨m, hm, hconv⟩ :=
    exists_finiteKMSWightmanMomentSequence_tendsto_of_localMomentClosure h
  exact sequenceTraceHankelNonnegative_of_finiteThermalKrylov_tendsto m target
    (fun j => finiteKMSWightmanMomentSequence_finiteThermalKrylov (hm j)) hconv

/-- The normalized prime--Gamma source has local canonical finite-KMS moment closure. -/
def PrimeArchFiniteKMSWightmanLocalMomentClosure : Prop :=
  FiniteKMSWightmanLocalMomentClosure normalizedPrimeArchMoment

/-- The normalized prime--Gamma source lies in the local closure of scalar finite positive
atomic Stieltjes moment sequences. -/
def PrimeArchFinitePositiveAtomicLocalMomentClosure : Prop :=
  FinitePositiveAtomicLocalMomentClosure normalizedPrimeArchMoment

/-- The canonical diagonal finite positive-atomic approximation schedule for the normalized
prime--Gamma source. -/
def PrimeArchFinitePositiveAtomicDiagonalApproximation : Prop :=
  FinitePositiveAtomicDiagonalApproximation normalizedPrimeArchMoment

/-- Local canonical finite-KMS closure discharges the complete prime--Gamma trace-Hankel
positivity hypothesis. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_finiteKMSWightmanLocalMomentClosure
    (h : PrimeArchFiniteKMSWightmanLocalMomentClosure) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  have hseq : SequenceTraceHankelNonnegative normalizedPrimeArchMoment :=
    sequenceTraceHankelNonnegative_of_finiteKMSWightmanLocalMomentClosure h
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  rw [← sequenceTraceHankel_eq_momentFunctional]
  exact hseq (p.map (Int.castRingHom ℝ))

/-- **Local finite-KMS value-closure RH capstone.**  Different finite moment cutoffs may use
unrelated finite Hamiltonians; arbitrary local approximation of the source values is sufficient. -/
theorem riemannHypothesis_of_primeArchFiniteKMSWightmanLocalMomentClosure
    (h : PrimeArchFiniteKMSWightmanLocalMomentClosure) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_finiteKMSWightmanLocalMomentClosure h)

/-- RH supplies local finite-KMS approximation through the explicit multiplicity-exact Xi
thermal truncations. -/
theorem primeArchFiniteKMSWightmanLocalMomentClosure_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchFiniteKMSWightmanLocalMomentClosure := by
  exact finiteKMSWightmanLocalMomentClosure_of_tendsto
    finiteKMSWightmanMomentSequence_xiThermalTruncation
    (tendsto_xiThermalTruncation_of_rh hRH)

/-- **Local finite-system value law for RH.**  RH is equivalent to the following closure
property: for every finite initial block of prime--Gamma source moments and every positive
tolerance, some canonical finite KMS/Wightman system approximates that block.  The systems for
different blocks need not be related or form a prescribed thermodynamic family. -/
theorem primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis :
    PrimeArchFiniteKMSWightmanLocalMomentClosure ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_primeArchFiniteKMSWightmanLocalMomentClosure,
    primeArchFiniteKMSWightmanLocalMomentClosure_of_riemannHypothesis⟩

/-- RH supplies scalar finite positive-atomic approximation of every finite source block through
the explicit reciprocal-square Xi truncations. -/
theorem primeArchFinitePositiveAtomicLocalMomentClosure_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchFinitePositiveAtomicLocalMomentClosure := by
  exact finitePositiveAtomicLocalMomentClosure_of_tendsto
    finitePositiveAtomicMomentSequence_xiThermalTruncation
    (tendsto_xiThermalTruncation_of_rh hRH)

/-- Scalar positive-atomic local source closure implies RH. -/
theorem riemannHypothesis_of_primeArchFinitePositiveAtomicLocalMomentClosure
    (h : PrimeArchFinitePositiveAtomicLocalMomentClosure) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primeArchFiniteKMSWightmanLocalMomentClosure
    (finiteKMSWightmanLocalMomentClosure_of_finitePositiveAtomicLocalMomentClosure h)

/-- **Finite positive-atomic value law for RH.**  RH is equivalent to approximating every finite
prime--Gamma source moment block, to arbitrary accuracy, by finitely many nonnegative scalar
masses at nonnegative scalar nodes. -/
theorem primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis :
    PrimeArchFinitePositiveAtomicLocalMomentClosure ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_primeArchFinitePositiveAtomicLocalMomentClosure,
    primeArchFinitePositiveAtomicLocalMomentClosure_of_riemannHypothesis⟩

/-- **Countable finite-certificate RH law.**  One finite positive-atomic approximation with the
canonical error `1/(j+1)` at each level `j` is equivalent to RH. -/
theorem primeArchFinitePositiveAtomicDiagonalApproximation_iff_riemannHypothesis :
    PrimeArchFinitePositiveAtomicDiagonalApproximation ↔ RiemannHypothesis := by
  exact
    finitePositiveAtomicLocalMomentClosure_iff_diagonalApproximation.symm.trans
      primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis

/-- At the prime--Gamma source, finite positive-atomic local closure and canonical finite-KMS
local closure are equivalent. -/
theorem primeArchFinitePositiveAtomicLocalMomentClosure_iff_finiteKMSLocalMomentClosure :
    PrimeArchFinitePositiveAtomicLocalMomentClosure ↔
      PrimeArchFiniteKMSWightmanLocalMomentClosure :=
  primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis.trans
    primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis.symm

/-- The exact prime--polar abscissa target is equivalent to local finite-system KMS realization
of arbitrary finite prime--Gamma moment blocks. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFiniteKMSLocalClosure
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      PrimeArchFiniteKMSWightmanLocalMomentClosure := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans
    primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis.symm

/-- The exact prime--polar abscissa target is equivalent to arbitrary finite-block approximation
of the prime--Gamma source by scalar finite positive atomic moments. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFinitePositiveAtomicLocalClosure
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      PrimeArchFinitePositiveAtomicLocalMomentClosure := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans
    primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis.symm

/-- The exact prime--polar abscissa target is equivalent to the canonical countable schedule of
independent finite positive-atomic source certificates. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFinitePositiveAtomicDiagonalApproximation
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      PrimeArchFinitePositiveAtomicDiagonalApproximation := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans
    primeArchFinitePositiveAtomicDiagonalApproximation_iff_riemannHypothesis.symm

end

end RHTower
