import GaloisForLFunctions.RHTower.XiContinuedCauchyPacketDensity
import GaloisForLFunctions.RHTower.XiHurwitzOrientationSourceSequenceGate

/-!
# Explicit separated source-packet reconstruction of Hurwitz orientation

The abstract continued-Cauchy closure of the canonical Xi--Hurwitz orientation vector can be
realized by actual finite packets on which every pairwise prime--Gamma divided difference is
defined.  Pairwise-separated packets are dense in each algebraic packet, hence their evaluations
have the same Hilbert closure as the continued Cauchy algebraic core.

There is therefore an unconditional sequence of finite, pairwise-separated continued-source
packets whose evaluation vectors converge to the orientation vector and whose explicit
prime--Gamma energies converge to `-xiHurwitzOrientationEnergy`.

This closes the analytic packet-representation and collision layer.  It does not close RH: the
sequence is extracted through the target orientation closure, so the remaining theorem must either
select it from source values alone or prove its eventual source sign independently.
-/

open Complex Metric Function Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- A finite continued-source Cauchy packet with every pairwise conjugate denominator separated. -/
structure XiSeparatedContinuedCauchyPacket where
  index : Type
  fintypeIndex : Fintype index
  coeff : index → ℂ
  pole : index → XiContinuedCauchyPoint
  separated : ∀ i j, (pole i : ℂ) ≠ (starRingEnd ℂ) (pole j : ℂ)

def XiSeparatedContinuedCauchyPacket.evaluation
    (P : XiSeparatedContinuedCauchyPacket) :
    lp (fun _ : XiZeroCopy => ℂ) 2 := by
  letI := P.fintypeIndex
  exact xiWeilContinuedCauchyPacketLp P.coeff P.pole

def XiSeparatedContinuedCauchyPacket.sourceEnergy
    (P : XiSeparatedContinuedCauchyPacket) : ℝ := by
  letI := P.fintypeIndex
  exact continuedCauchyPacketSourceEnergy P.coeff P.pole

/-- A separated packet's explicit source energy equals its unconditional Xi Weil Hilbert value. -/
theorem XiSeparatedContinuedCauchyPacket.sourceEnergy_eq_hilbertQuadratic
    (P : XiSeparatedContinuedCauchyPacket) :
    P.sourceEnergy = xiWeilHilbertQuadratic P.evaluation := by
  letI := P.fintypeIndex
  exact (xiWeilHilbertQuadratic_indexedCauchyPacket_eq_continuedSource_re
    P.coeff P.pole P.separated).symm

def xiSeparatedContinuedCauchyPacketEvaluationSet :
    Set (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Set.range XiSeparatedContinuedCauchyPacket.evaluation

/-- Every algebraic continued Cauchy vector lies in the Hilbert closure of actual separated
packet evaluations. -/
theorem continuedCauchyAlgebraicSubspace_le_closure_separatedPacketEvaluations :
    (xiWeilContinuedCauchyAlgebraicSubspace :
      Set (lp (fun _ : XiZeroCopy => ℂ) 2)) ⊆
      closure xiSeparatedContinuedCauchyPacketEvaluationSet := by
  intro v hv
  obtain ⟨c, hc⟩ := exists_finsupp_indexedCauchyPacket_eq_of_mem v hv
  let ι := {x // x ∈ c.support}
  let coeff : ι → ℂ := fun i => c i.1
  let pole : ι → XiContinuedCauchyPoint := fun i => i.1
  obtain ⟨w, hwsep, hw, _henergy⟩ :=
    exists_pairwiseConjSeparatedContinuedSourceEnergy_tendsto coeff pole
  let P : ℕ → XiSeparatedContinuedCauchyPacket := fun n =>
    { index := ι
      fintypeIndex := inferInstance
      coeff := coeff
      pole := w n
      separated := hwsep n }
  have hP : Tendsto (fun n => (P n).evaluation) atTop (nhds v) := by
    change Tendsto (fun n => xiWeilContinuedCauchyPacketLp coeff (w n))
      atTop (nhds v)
    rw [← hc]
    exact hw
  exact mem_closure_of_tendsto hP
    (Eventually.of_forall fun n => ⟨P n, rfl⟩)

/-- The canonical orientation vector belongs to the closure of evaluations of explicit finite
pairwise-separated continued-source packets. -/
theorem xiHurwitzOrientationVector_mem_closure_separatedPacketEvaluations :
    xiHurwitzOrientationVector ∈
      closure xiSeparatedContinuedCauchyPacketEvaluationSet := by
  have hclosure : closure
      (xiWeilContinuedCauchyAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2)) ⊆
      closure xiSeparatedContinuedCauchyPacketEvaluationSet :=
    closure_minimal
      continuedCauchyAlgebraicSubspace_le_closure_separatedPacketEvaluations
      isClosed_closure
  exact hclosure xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace

/-- An unconditional sequence of explicit separated packets converges to the canonical
orientation vector. -/
theorem exists_separatedContinuedCauchyPackets_tendsto_orientationVector :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop
        (nhds xiHurwitzOrientationVector) := by
  have hclosure :=
    xiHurwitzOrientationVector_mem_closure_separatedPacketEvaluations
  have happ : ∀ n : ℕ, ∃ v,
      v ∈ xiSeparatedContinuedCauchyPacketEvaluationSet ∧
      dist xiHurwitzOrientationVector v < 1 / ((n : ℝ) + 1) := by
    intro n
    exact Metric.mem_closure_iff.mp hclosure _ (by positivity)
  choose v hv hdist using happ
  choose P hP using hv
  refine ⟨P, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  have hden : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hn 1
  rw [show (P n).evaluation = v n by exact hP n]
  rw [dist_comm]
  exact (hdist n).trans
    ((one_div_le_one_div_of_le (by positivity) hden).trans_lt hN)

/-- **Explicit separated-source reconstruction law.**  The packet evaluations converge to the
canonical orientation vector and their exact finite prime--Gamma divided-difference energies
converge to minus the global orientation defect. -/
theorem xiHurwitzOrientationEnergy_separatedContinuedSource_reconstruction :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop
        (nhds xiHurwitzOrientationVector) ∧
      Tendsto (fun n => (P n).sourceEnergy) atTop
        (nhds (-xiHurwitzOrientationEnergy)) := by
  obtain ⟨P, hP⟩ :=
    exists_separatedContinuedCauchyPackets_tendsto_orientationVector
  refine ⟨P, hP, ?_⟩
  have hQ := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hP
  rw [xiWeilHilbertQuadratic_xiHurwitzOrientationVector] at hQ
  apply hQ.congr'
  exact Eventually.of_forall fun n =>
    (P n).sourceEnergy_eq_hilbertQuadratic.symm

/-- **One explicit finite-source-sequence criterion.**  There is an unconditional sequence of
pairwise-separated finite continued prime--Gamma packets for which eventual nonnegativity of the
displayed divided-difference energies is equivalent to RH. -/
theorem exists_separatedContinuedSource_sequence_eventually_nonnegative_iff_riemannHypothesis :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop
        (nhds xiHurwitzOrientationVector) ∧
      Tendsto (fun n => (P n).sourceEnergy) atTop
        (nhds (-xiHurwitzOrientationEnergy)) ∧
      (RiemannHypothesis ↔ ∀ᶠ n in atTop, 0 ≤ (P n).sourceEnergy) := by
  obtain ⟨P, hP, hE⟩ :=
    xiHurwitzOrientationEnergy_separatedContinuedSource_reconstruction
  refine ⟨P, hP, hE, ?_⟩
  constructor
  · intro hRH
    exact Eventually.of_forall fun n => by
      rw [(P n).sourceEnergy_eq_hilbertQuadratic]
      exact xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH (P n).evaluation
  · intro hnonneg
    have hlimit : 0 ≤ -xiHurwitzOrientationEnergy :=
      ge_of_tendsto hE hnonneg
    apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr
    linarith [xiHurwitzOrientationEnergy_nonneg]

end

end RHTower
