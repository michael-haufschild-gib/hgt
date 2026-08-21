import GaloisForLFunctions.HTGeometry.StaticLocalExactReturnReflectionLaw
import GaloisForLFunctions.HTGeometry.ObserverProfileStability

/-!
# Robust laboratory-time complexity growth for one static Hamiltonian

The inverse-square-chain ramp is not isolated.  Its operator two-gate lower bound persists for
every self-adjoint Hamiltonian in an explicit operator-norm tube.  More strongly, one fixed
Hamiltonian obeys the lower bound simultaneously throughout a complete laboratory-time interval
whenever its distance from the reference is controlled at the interval endpoint.

The proof combines the exact inverse-square-chain circuit lower bound with the dimension-free
C⋆ Duhamel estimate.  No randomness, asymptotics, or unproved dynamical hypothesis enters.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- The real diagonal inverse-square-chain Hamiltonian is self-adjoint. -/
theorem inverseSquareChainHamiltonian_isSelfAdjoint (L : ℕ) :
    IsSelfAdjoint (inverseSquareChainHamiltonian L) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, inverseSquareChainHamiltonian,
    Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  simp

/-- A support-certified local circuit approximates an arbitrary matrix target. -/
def OperatorApproximatesTarget {L : ℕ}
    (W : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)
    (ε : ℝ) (c : List (LocalGate (PairQubit L))) : Prop :=
  ‖circuitMatrix c - W‖ ≤ ε

/-- Operator-norm two-qubit-gate complexity of an arbitrary matrix target. -/
noncomputable def operatorTwoGateComplexityTo (L : ℕ)
    (ε : ℝ) (W : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) : ℕ∞ :=
  ⨅ c ∈ {c : List (LocalGate (PairQubit L)) | OperatorApproximatesTarget W ε c},
    (twoGateCount c : ℕ∞)

theorem le_operatorTwoGateComplexityTo_iff {L : ℕ}
    (ε : ℝ) (W : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) (G : ℕ∞) :
    G ≤ operatorTwoGateComplexityTo L ε W ↔
      ∀ c : List (LocalGate (PairQubit L)),
        OperatorApproximatesTarget W ε c → G ≤ (twoGateCount c : ℕ∞) := by
  rw [operatorTwoGateComplexityTo, le_iInf_iff]
  constructor
  · intro h c hc
    exact le_iInf_iff.mp (h c) hc
  · intro h c
    exact le_iInf fun hc => h c hc

/-- Target-stability transfer: a target within `δ` of the reference inherits the reference lower
bound with error enlarged from `ε` to `ε + δ`. -/
theorem operatorTwoGateComplexityTo_inverseSquareChain_floor_of_close
    {L : ℕ} {t ε δ : ℝ}
    {W : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hε : 0 < ε + δ) (hεmax : ε + δ ≤ 1 / 100)
    (htMin : 1024 * Real.pi * (ε + δ) ≤ t)
    (htLab : t ≤ (ε + δ) * L / 2)
    (hclose : ‖W - inverseSquareChainEvolution L t‖ ≤ δ) :
    ((⌊t / (128 * Real.pi * (ε + δ))⌋₊ : ℕ) : ℕ∞) ≤
      operatorTwoGateComplexityTo L ε W := by
  rw [le_operatorTwoGateComplexityTo_iff]
  intro c hc
  have href : OperatorApproximates t (ε + δ) c := by
    unfold OperatorApproximatesTarget at hc
    unfold OperatorApproximates
    calc
      ‖circuitMatrix c - inverseSquareChainEvolution L t‖ =
          ‖(circuitMatrix c - W) + (W - inverseSquareChainEvolution L t)‖ := by
        congr 1
        abel
      _ ≤ ‖circuitMatrix c - W‖ + ‖W - inverseSquareChainEvolution L t‖ :=
        norm_add_le _ _
      _ ≤ ε + δ := add_le_add hc hclose
  exact_mod_cast
    (inverseSquareChain_floor_ceil_growth hε hεmax htMin htLab).1 c href

/-- **Robust pointwise static-local ramp.** Every self-adjoint Hamiltonian in the explicit
time-scaled tube around the inverse-square chain has linear operator two-gate complexity. -/
theorem perturbed_inverseSquareChain_floor_growth
    {L : ℕ} {t ε : ℝ}
    {H : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hH : IsSelfAdjoint H)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (htMin : 2048 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L)
    (hclose : |t| * ‖H - inverseSquareChainHamiltonian L‖ ≤ ε) :
    ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
      operatorTwoGateComplexityTo L ε (unitaryEvolution H t) := by
  have hreference := inverseSquareChainHamiltonian_isSelfAdjoint L
  have hevolution :
      ‖unitaryEvolution H t - inverseSquareChainEvolution L t‖ ≤ ε := by
    exact (norm_unitaryEvolution_sub_le H (inverseSquareChainHamiltonian L)
      hH hreference t).trans hclose
  have hraw := operatorTwoGateComplexityTo_inverseSquareChain_floor_of_close
    (L := L) (t := t) (ε := ε) (δ := ε)
    (W := unitaryEvolution H t)
    (by linarith) (by linarith) (by linarith) (by linarith) hevolution
  have hden : 128 * Real.pi * (ε + ε) = 256 * Real.pi * ε := by ring
  simpa [hden] using hraw

/-- **One-draw robust laboratory-time growth law.** One fixed self-adjoint Hamiltonian in the
endpoint tube obeys the linear lower bound at every time in the stated laboratory interval. -/
theorem perturbed_inverseSquareChain_uniform_laboratory_growth
    {L : ℕ} {T ε : ℝ}
    {H : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hH : IsSelfAdjoint H)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (htube : T * ‖H - inverseSquareChainHamiltonian L‖ ≤ ε) :
    ∀ t : ℝ,
      2048 * Real.pi * ε ≤ t →
      t ≤ ε * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L ε (unitaryEvolution H t) := by
  intro t htMin htLab htT
  have hmin0 : 0 < 2048 * Real.pi * ε := by positivity
  have ht0 : 0 ≤ t := by linarith
  have hclose : |t| * ‖H - inverseSquareChainHamiltonian L‖ ≤ ε := by
    rw [abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_right htT (norm_nonneg _)).trans htube
  exact perturbed_inverseSquareChain_floor_growth
    hH hε hεmax htMin htLab hclose

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
