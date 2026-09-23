import GaloisForLFunctions.HTGeometry.NormalizedCasimirLeakage
import GaloisForLFunctions.HTGeometry.FullPauliCasimirGap
import GaloisForLFunctions.HTGeometry.UnitMassWordLeakage

/-!
# The all-replica incidence-normalized local-word leakage law

The collective full-Pauli commutator family has central quadratic Casimir and a spectral gap `2D²`
off its sitewise singlet sector, at every finite replica order.  Feeding that gap into the
normalized leakage budget gives the unscaled estimate: routing a source subspace of the complement
of the singlet sector into a smaller target leaks at least `2D²` per lost dimension, uniformly in
the replica order.

Expanding each label in a unit-mass word synthesis and normalizing by the label count `D²-1` turns
that estimate into the incidence-normalized local-word bound, whose right-hand side is strictly
larger than twice the dimension drop and independent of replica order.
-/

open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable (R : Type*) [Fintype R] [DecidableEq R] (n : ℕ)

/-- **The unscaled all-replica leakage estimate.**  Every dimension a collective-Pauli incidence
cut loses off the singlet sector costs `2D²` of Hilbert--Schmidt leakage. -/
theorem finiteAllReplicaFullPauli_leak_ge_dim_sub
    {PU PV : Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ}
    (hUherm : PUᴴ = PU) (hUidem : PU * PU = PU) (hVidem : PV * PV = PV)
    (hUQ : hermitianMatrixFamilyCommonKernelProjection
      (finiteReplicaFullPauliCommutatorMatrix R n) * PU = 0) :
    2 * ((2 : ℝ) ^ n) ^ (2 : ℕ) * ((PU.trace).re - (PV.trace).re)
      ≤ ∑ q : NonidentityPauliLabel n,
          hsSqRe ((1 - PV) * finiteReplicaFullPauliCommutatorMatrix R n q * PU) := by
  refine hermitianCentralFamily_leak_ge_gap_mul_dim_sub _
    (finiteReplicaFullPauliCommutatorMatrix_conjTranspose R n)
    (finiteReplicaFullPauliCommutator_quadraticCasimir_commutes R n)
    (by positivity) ?_ hUherm hUidem hVidem hUQ
  intro z hz
  exact commonKernelProjection_form_ge_of_eigenvalue_gap _
    (finiteReplicaFullPauliCommutatorMatrix_conjTranspose R n)
    (fun _ _ hY heig => fullPauliCasimir_eigenvalue_gap hY heig) z hz

/-- **The incidence-normalized local-word estimate.**  A unit-mass word synthesis of every label
transports the leakage budget to the word level, normalized by any positive label count. -/
theorem finiteAllReplicaFullPauli_incidenceNormalized_leakage_ge
    {ι : Type*} [Fintype ι]
    {PU PV : Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ}
    (hUherm : PUᴴ = PU) (hUidem : PU * PU = PU) (hVidem : PV * PV = PV)
    (hUQ : hermitianMatrixFamilyCommonKernelProjection
      (finiteReplicaFullPauliCommutatorMatrix R n) * PU = 0)
    (c : NonidentityPauliLabel n → ι → ℂ)
    (W : NonidentityPauliLabel n → ι → Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ)
    (hc : ∀ q, ∑ w, ‖c q w‖ = 1)
    (hsynth : ∀ q, finiteReplicaFullPauliCommutatorMatrix R n q = ∑ w, c q w • W q w)
    {N : ℝ} (hN : 0 < N) :
    2 * ((2 : ℝ) ^ n) ^ (2 : ℕ) * ((PU.trace).re - (PV.trace).re) / N
      ≤ (∑ q : NonidentityPauliLabel n, ∑ w, ‖c q w‖ * hsSqRe ((1 - PV) * W q w * PU)) / N := by
  refine incidenceNormalized_leakage_ge PU PV c W hc hN ?_
  refine le_trans (finiteAllReplicaFullPauli_leak_ge_dim_sub R n hUherm hUidem hVidem hUQ)
    (le_of_eq ?_)
  exact Finset.sum_congr rfl fun q _ => by rw [hsynth q]

/-- **The incidence-normalized budget at the label count `D²-1`.**  The right-hand side is a
replica-independent multiple of the dimension drop strictly larger than two. -/
theorem finiteAllReplicaFullPauli_leakage_budget
    {ι : Type*} [Fintype ι] (hn : 1 ≤ n)
    {PU PV : Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ}
    (hUherm : PUᴴ = PU) (hUidem : PU * PU = PU) (hVidem : PV * PV = PV)
    (hUQ : hermitianMatrixFamilyCommonKernelProjection
      (finiteReplicaFullPauliCommutatorMatrix R n) * PU = 0)
    (c : NonidentityPauliLabel n → ι → ℂ)
    (W : NonidentityPauliLabel n → ι → Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ)
    (hc : ∀ q, ∑ w, ‖c q w‖ = 1)
    (hsynth : ∀ q, finiteReplicaFullPauliCommutatorMatrix R n q = ∑ w, c q w • W q w) :
    2 * ((2 : ℝ) ^ n) ^ (2 : ℕ) * ((PU.trace).re - (PV.trace).re) / (((2 : ℝ) ^ n) ^ (2 : ℕ) - 1)
      ≤ (∑ q : NonidentityPauliLabel n, ∑ w, ‖c q w‖ * hsSqRe ((1 - PV) * W q w * PU))
          / (((2 : ℝ) ^ n) ^ (2 : ℕ) - 1) := by
  have hD : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ n := by
          exact pow_le_pow_right₀ (by norm_num) hn
  have hN : (0 : ℝ) < ((2 : ℝ) ^ n) ^ (2 : ℕ) - 1 := by nlinarith
  exact finiteAllReplicaFullPauli_incidenceNormalized_leakage_ge R n hUherm hUidem hVidem hUQ
    c W hc hsynth hN

end

end GaloisForLFunctions.HTGeometry
