import Mathlib.LinearAlgebra.Matrix.Stochastic
import GaloisForLFunctions.RHTower.CCMFirstClockHalfWaveReflection

/-!
# CCM first-clock barycentric orientation completeness

This file classifies the strongest finite positive source-faithful transport left open by the
physical-phase naturality obstruction.  For a nonnegative source vector of positive total mass,
a column-stochastic matrix can fix the source and orient every coordinate of the transported dual
phase exactly when the original source--phase dot product is nonnegative.

The reverse direction is constructive: the rank-one matrix whose every column is the normalized
source vector is a canonical witness.  Applied to the completed CCM packet, with the positive
continuous half-wave budget as an anchor coordinate, universal transport existence is exactly the
published first-clock source condition and hence exactly the Riemann hypothesis.

All results are unconditional equivalences.  In particular, the final theorem does not assert
that the transports exist; it proves that their existence cannot be an independent positivity
mechanism.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-- Rank-one transport whose every column is the source vector normalized by its total mass. -/
def ccmBarycentricSourceTransport (w : ι → ℝ) : Matrix ι ι ℝ :=
  fun i _j => w i / ∑ k, w k

/-- The barycentric transport fixes its defining source vector whenever its total mass is
nonzero. -/
theorem ccmBarycentricSourceTransport_mulVec
    {w : ι → ℝ} (hW : 0 < ∑ i, w i) :
    Matrix.mulVec (ccmBarycentricSourceTransport w) w = w := by
  funext i
  simp only [ccmBarycentricSourceTransport, Matrix.mulVec, dotProduct]
  rw [← Finset.mul_sum]
  exact div_mul_cancel₀ (w i) hW.ne'

/-- The dual barycentric transport collapses every phase vector to its normalized source
scalar. -/
theorem ccmBarycentricSourceTransport_transpose_mulVec
    {w s : ι → ℝ} :
    Matrix.mulVec (ccmBarycentricSourceTransport w).transpose s =
      fun _ => (w ⬝ᵥ s) / ∑ i, w i := by
  funext j
  simp only [ccmBarycentricSourceTransport, Matrix.mulVec,
    Matrix.transpose_apply, dotProduct]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

variable [DecidableEq ι]

/-- A positive Markov transport that fixes the source and makes every dual phase coordinate
nonnegative. -/
def CCMOrientedSourceFaithfulMarkovTransport (w s : ι → ℝ) : Prop :=
  ∃ M : Matrix ι ι ℝ,
    M ∈ Matrix.colStochastic ℝ ι ∧
    Matrix.mulVec M w = w ∧
    ∀ j, 0 ≤ Matrix.mulVec M.transpose s j

/-- A nonnegative source of positive total mass gives a column-stochastic barycentric
transport. -/
theorem ccmBarycentricSourceTransport_mem_colStochastic
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) :
    ccmBarycentricSourceTransport w ∈ Matrix.colStochastic ℝ ι := by
  rw [Matrix.mem_colStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    exact div_nonneg (hw i) hW.le
  · intro j
    simp only [ccmBarycentricSourceTransport]
    rw [← Finset.sum_div]
    exact div_self hW.ne'

/-- **Positive source-faithful transport completeness.**  Coordinatewise dual orientation by
an arbitrary positive Markov transport is possible exactly when the original source scalar is
nonnegative. -/
theorem ccm_orientedSourceFaithfulMarkovTransport_iff_dotProduct_nonnegative
    {w s : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hW : 0 < ∑ i, w i) :
    CCMOrientedSourceFaithfulMarkovTransport w s ↔ 0 ≤ w ⬝ᵥ s := by
  constructor
  · rintro ⟨M, _hM, hfix, horiented⟩
    have hweighted : 0 ≤ w ⬝ᵥ Matrix.mulVec M.transpose s := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _hi => mul_nonneg (hw i) (horiented i)
    calc
      0 ≤ w ⬝ᵥ Matrix.mulVec M.transpose s := hweighted
      _ = s ⬝ᵥ Matrix.mulVec M w := Matrix.dotProduct_transpose_mulVec M w s
      _ = s ⬝ᵥ w := by rw [hfix]
      _ = w ⬝ᵥ s := dotProduct_comm _ _
  · intro hscalar
    refine ⟨ccmBarycentricSourceTransport w,
      ccmBarycentricSourceTransport_mem_colStochastic hw hW,
      ccmBarycentricSourceTransport_mulVec hW, ?_⟩
    intro j
    rw [ccmBarycentricSourceTransport_transpose_mulVec]
    exact div_nonneg hscalar hW.le

/-- Finite completed first-clock packet: one continuous anchor plus every integer in the sharp
prime window.  Composite non-prime-power coordinates have zero von Mangoldt weight. -/
abbrev CCMFirstClockCompletedPacketIndex (L : ℝ) :=
  Option {k : ℕ // k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊}

/-- Completed packet source weights.  The `none` coordinate is the continuous half-wave budget. -/
def ccmFirstClockCompletedPacketWeight (L ξ : ℝ) :
    CCMFirstClockCompletedPacketIndex L → ℝ
  | none => ccmFirstClockContinuousHalfWaveBudget L ξ
  | some k => criticalMellinAtomWeight k

/-- Completed packet phases.  The anchor has phase one; arithmetic coordinates carry the literal
first-clock sine phase. -/
def ccmFirstClockCompletedPacketPhase (L ξ : ℝ) :
    CCMFirstClockCompletedPacketIndex L → ℝ
  | none => 1
  | some k => Real.sin (ξ * Real.log k)

/-- The completed packet dot product is exactly the continuous half-wave budget plus the signed
prime sine mass. -/
theorem ccmFirstClockCompletedPacket_dotProduct (L ξ : ℝ) :
    ccmFirstClockCompletedPacketWeight L ξ ⬝ᵥ
        ccmFirstClockCompletedPacketPhase L ξ =
      ccmFirstClockContinuousHalfWaveBudget L ξ +
        ccmFirstClockPrimeSineMass L ξ := by
  rw [dotProduct, Fintype.sum_option]
  simp only [ccmFirstClockCompletedPacketWeight,
    ccmFirstClockCompletedPacketPhase, mul_one]
  rw [ccmFirstClockPrimeSineMass]
  congr 1
  exact (Finset.sum_subtype
    (p := fun k : ℕ => k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊)
    (Finset.Icc 2 ⌊Real.exp L⌋₊) (fun _ => Iff.rfl)
    (fun k => criticalMellinAtomWeight k * Real.sin (ξ * Real.log k))).symm

/-- Every completed source coordinate is nonnegative at a physical full-period clock. -/
theorem ccmFirstClockCompletedPacketWeight_nonneg
    {L ξ : ℝ} (hL : 0 < L) (hperiod : ξ * L = 2 * Real.pi) :
    ∀ j, 0 ≤ ccmFirstClockCompletedPacketWeight L ξ j
  | none => (ccmFirstClockContinuousHalfWaveBudget_pos hL hperiod).le
  | some k => criticalMellinAtomWeight_nonneg k

/-- The completed source has positive total mass because its continuous anchor is strictly
positive. -/
theorem ccmFirstClockCompletedPacketWeight_sum_pos
    {L ξ : ℝ} (hL : 0 < L) (hperiod : ξ * L = 2 * Real.pi) :
    0 < ∑ j, ccmFirstClockCompletedPacketWeight L ξ j := by
  rw [Fintype.sum_option]
  exact add_pos_of_pos_of_nonneg
    (ccmFirstClockContinuousHalfWaveBudget_pos hL hperiod)
    (Finset.sum_nonneg fun k _hk => criticalMellinAtomWeight_nonneg k)

/-- Existence of an oriented source-faithful positive Markov transport for the completed packet
at an arbitrary full-period frequency. -/
def CCMFirstClockCompletedMarkovOrientationAtFrequency (L ξ : ℝ) : Prop :=
  CCMOrientedSourceFaithfulMarkovTransport
    (ccmFirstClockCompletedPacketWeight L ξ)
    (ccmFirstClockCompletedPacketPhase L ξ)

/-- Completed transport feasibility is exactly the sign of the literal published source at the
same aperture and full-period frequency. -/
theorem ccmFirstClockCompletedMarkovOrientationAtFrequency_iff_source_nonnegative
    {L ξ : ℝ} (hL : 0 < L) (hperiod : ξ * L = 2 * Real.pi) :
    CCMFirstClockCompletedMarkovOrientationAtFrequency L ξ ↔
      0 ≤ ccmPublishedSourceSineCoefficient (L / 2) ξ := by
  rw [CCMFirstClockCompletedMarkovOrientationAtFrequency,
    ccm_orientedSourceFaithfulMarkovTransport_iff_dotProduct_nonnegative
      (ccmFirstClockCompletedPacketWeight_nonneg hL hperiod)
      (ccmFirstClockCompletedPacketWeight_sum_pos hL hperiod),
    ccmFirstClockCompletedPacket_dotProduct,
    ← pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime hL hperiod]
  exact mul_nonneg_iff_of_pos_left Real.pi_pos

/-- Completed positive transport feasibility at the physical first-clock frequency. -/
def CCMFirstClockCompletedMarkovOrientationAt (L : ℝ) : Prop :=
  CCMFirstClockCompletedMarkovOrientationAtFrequency L (2 * Real.pi / L)

/-- Aperturewise physical transport feasibility is exactly aperturewise published-source
nonnegativity. -/
theorem ccmFirstClockCompletedMarkovOrientationAt_iff_source_nonnegative
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    CCMFirstClockCompletedMarkovOrientationAt L ↔
      0 ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) := by
  have hLpos : 0 < L := lt_of_lt_of_le (half_pos Real.pi_pos) hL
  have hperiod : (2 * Real.pi / L) * L = 2 * Real.pi := by
    field_simp
  exact
    ccmFirstClockCompletedMarkovOrientationAtFrequency_iff_source_nonnegative
      hLpos hperiod

/-- Universal existence of completed positive Markov orientations over all physical first-clock
apertures. -/
def CCMFirstClockAllCompletedMarkovOrientations : Prop :=
  ∀ L : ℝ, Real.pi / 2 ≤ L → CCMFirstClockCompletedMarkovOrientationAt L

/-- Universal completed transport existence is exactly the published first-clock source floor. -/
theorem ccmFirstClockAllCompletedMarkovOrientations_iff_publishedSourceNonnegative :
    CCMFirstClockAllCompletedMarkovOrientations ↔
      CCMFirstClockPublishedSourceNonnegative := by
  constructor
  · intro hall L hL
    exact
      (ccmFirstClockCompletedMarkovOrientationAt_iff_source_nonnegative hL).1
        (hall L hL)
  · intro hsource L hL
    exact
      (ccmFirstClockCompletedMarkovOrientationAt_iff_source_nonnegative hL).2
        (hsource L hL)

/-- **CCM barycentric transport completeness.**  Universal positive source-faithful Markov
orientation is exactly RH.  This is an unconditional equivalence and therefore a terminal
classification, not a proof that the transports exist. -/
theorem ccmFirstClockAllCompletedMarkovOrientations_iff_rh :
    CCMFirstClockAllCompletedMarkovOrientations ↔ RiemannHypothesis := by
  rw [ccmFirstClockAllCompletedMarkovOrientations_iff_publishedSourceNonnegative,
    ccmFirstClockPublishedSourceNonnegative_iff_rh]

end RHTower
