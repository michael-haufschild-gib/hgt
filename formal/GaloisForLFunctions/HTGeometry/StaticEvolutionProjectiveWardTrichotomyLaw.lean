import GaloisForLFunctions.HTGeometry.PauliCommutatorReturnTubeLaw
import GaloisForLFunctions.HTGeometry.PauliContinuousLaboratoryReturnLaw
import GaloisForLFunctions.HTGeometry.TwoReplicaPositiveGraphEdgeCasimir
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap
import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
import GaloisForLFunctions.RHTower.AffineTwoLocalPauliSpectralActionLaw

/-!
# Projective Ward trichotomy for one static local Hamiltonian

The usual transfer from return error to commutator error loses the global
factor `2 * ‖H‖`.  Static evolution permits a sharper Ward identity.  Since
`exp (-itH)` commutes with `H` and commutation by a Hermitian matrix is
self-adjoint in Hilbert--Schmidt geometry, the squared target commutator is
controlled by return error times the target's double commutator.

For the ordinary two-local Pauli family this gives an unconditional trichotomy
at every time and against every unitary target: miss the target, return close
to the projective scalar sector, or enter a target-sensitive transverse
approximate-centralizer tube.  No spectral-gap or minimum-gap input occurs.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
open Matrix Set
open GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

/-- **Target-sensitive static Ward law.**  For one ordinary two-local Pauli
Hamiltonian drawn once, the squared observer response to any unitary target is
bounded by its double-commutator scale times the exact same-draw return error.

Unlike the elementary commutator Lipschitz bound, this statement has no global
`‖H‖` prefactor.  Hermiticity and commutation of the static evolution are
discharged internally, so the theorem has no physical side conditions. -/
theorem norm_twoLocalPauliUnitaryCommutatorMap_sq_le_doubleCommutator_mul_returnDefect
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : TwoLocalPauliCoefficientSpace n) (t : ℝ) :
    ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ 2 ≤
      hsNorm
          (ringCommutator (realActivePauliHamiltonian x)
            (ringCommutator (realActivePauliHamiltonian x)
              (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ))) *
        hsNorm
          (unitaryEvolution (realActivePauliHamiltonian x) t -
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) := by
  rw [norm_twoLocalPauliUnitaryCommutatorMap_sq, frobSq_eq_hsNorm_sq]
  let H := realActivePauliHamiltonian x
  let U0 := (U : Matrix (FiniteQubitConfiguration (Fin n))
    (FiniteQubitConfiguration (Fin n)) ℂ)
  let V := unitaryEvolution H t
  let A := ringCommutator H U0
  let E := U0 - V
  let D := ringCommutator H A
  change hsNorm A ^ 2 ≤ hsNorm D * hsNorm (V - U0)
  have hH : Hᴴ = H := (isSelfAdjoint_realActivePauliHamiltonian x).star_eq
  have hcomm : H * V = V * H := unitaryEvolution_commutes_generator H t
  have hAE : A = ringCommutator H E := by
    simp only [A, E, ringCommutator, Matrix.mul_sub, Matrix.sub_mul]
    rw [hcomm]
    abel
  have henergy : (hsNorm A ^ 2 : ℂ) = hsInner E D := by
    calc
      (hsNorm A ^ 2 : ℂ) = hsInner A A := by
        rw [← inner_finiteMatrixHilbertEquiv_eq_hsInner,
          inner_self_eq_norm_sq_to_K]
        rfl
      _ = hsInner (ringCommutator H E) A := by rw [← hAE]
      _ = hsInner E (ringCommutator H A) :=
        hsInner_ringCommutator_selfAdjoint H E A hH
      _ = hsInner E D := rfl
  have hcs := norm_inner_le_norm (𝕜 := ℂ)
    (finiteMatrixHilbertEquiv E) (finiteMatrixHilbertEquiv D)
  rw [inner_finiteMatrixHilbertEquiv_eq_hsInner] at hcs
  have hnormE : ‖finiteMatrixHilbertEquiv E‖ = hsNorm E := by rfl
  have hnormD : ‖finiteMatrixHilbertEquiv D‖ = hsNorm D := by rfl
  rw [hnormE, hnormD] at hcs
  have hnorm : hsNorm A ^ 2 = ‖hsInner E D‖ := by
    rw [← henergy, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hsNorm_nonneg A)]
  have hward : hsNorm A ^ 2 ≤ hsNorm D * hsNorm E := by
    rw [hnorm]
    simpa only [mul_comm] using hcs
  rw [hsNorm_sub_comm U0 V] at hward
  exact hward

/-- **Projective Ward trichotomy.**  Every operator-norm circuit hit by one
static ordinary two-local evolution is either a projective Choi return or a
transverse approximate-centralizer hit.  The transverse branch retains the
target-specific double commutator instead of paying the extensive global
Hamiltonian norm. -/
theorem unitaryEvolution_near_unitary_projectiveReturn_or_transverseWardObserver
    {n : ℕ}
    (x : TwoLocalPauliCoefficientSpace n) (t : ℝ)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (ε β : ℝ) :
    ε < ‖unitaryEvolution (realActivePauliHamiltonian x) t -
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ ∨
      choiDist
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) 1 ≤ Real.sqrt β ∨
      (((6 * n - 4 : ℕ) : ℝ) * β ≤
          twoLocalPauliUnitaryCommutatorGramStableRatio U ∧
        ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ 2 ≤
          hsNorm
              (ringCommutator (realActivePauliHamiltonian x)
                (ringCommutator (realActivePauliHamiltonian x)
                  (U : Matrix (FiniteQubitConfiguration (Fin n))
                    (FiniteQubitConfiguration (Fin n)) ℂ))) *
            (Real.sqrt ((2 : ℝ) ^ n) * ε)) := by
  let V := unitaryEvolution (realActivePauliHamiltonian x) t
  let deficit := RHTower.unitaryProjectiveTraceDeficit U
  by_cases hnear : ‖V - (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤ ε
  · right
    by_cases hdeficit : deficit ≤ β
    · left
      show choiDist
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) 1 ≤ Real.sqrt β
      rw [choiDist_comm, choiDist_eq Fintype.card_pos]
      simpa [deficit, RHTower.unitaryProjectiveTraceDeficit, div_pow] using
        Real.sqrt_le_sqrt hdeficit
    · right
      have hdeficit' : β ≤ deficit := (lt_of_not_ge hdeficit).le
      constructor
      · exact (mul_le_mul_of_nonneg_left hdeficit' (Nat.cast_nonneg _)).trans
          (by simpa [deficit, RHTower.unitaryProjectiveTraceDeficit] using
            twoLocalPauliUnitaryCommutatorGramStableRatio_ge_sixNSubFour_normalizedTraceDeficit U)
      · have hbase :=
          norm_twoLocalPauliUnitaryCommutatorMap_sq_le_doubleCommutator_mul_returnDefect U x t
        have hhs := hsNorm_le_sqrt_card_mul_opNorm
          (V - (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ))
        have hcard :
            (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) =
              (2 : ℝ) ^ n := by simp
        rw [hcard] at hhs
        have hhsε : hsNorm
            (V - (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) ≤
            Real.sqrt ((2 : ℝ) ^ n) * ε :=
          hhs.trans (mul_le_mul_of_nonneg_left hnear (Real.sqrt_nonneg _))
        exact hbase.trans (mul_le_mul_of_nonneg_left hhsε (hsNorm_nonneg _))
  · left
    exact lt_of_not_ge hnear

/-- **All-time Ward reduction.**  Return to a projectively excised member of
an arbitrary target family at any real time forces membership in a static,
same-draw Ward tube.  The conclusion contains no time variable: continuous
time, unbounded horizons, repeated fibre sheets, and target-family cardinality
are all eliminated before any probabilistic estimate is applied. -/
theorem allTime_returnExcisedCircuitHit_subset_staticWardObserverTube
    {n : ℕ} {C : Type*}
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (ε β : ℝ) :
    {x : TwoLocalPauliCoefficientSpace n |
        ∃ t : ℝ, ∃ c : C,
          ‖unitaryEvolution (realActivePauliHamiltonian x) t -
              (U c : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖ ≤ ε ∧
            Real.sqrt β <
              choiDist
                (U c : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ) 1} ⊆
      {x : TwoLocalPauliCoefficientSpace n |
        ∃ c : C,
          ((6 * n - 4 : ℕ) : ℝ) * β ≤
              twoLocalPauliUnitaryCommutatorGramStableRatio (U c) ∧
            ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ 2 ≤
              hsNorm
                  (ringCommutator (realActivePauliHamiltonian x)
                    (ringCommutator (realActivePauliHamiltonian x)
                      (U c : Matrix (FiniteQubitConfiguration (Fin n))
                        (FiniteQubitConfiguration (Fin n)) ℂ))) *
                (Real.sqrt ((2 : ℝ) ^ n) * ε)} := by
  intro x hx
  rcases hx with ⟨t, c, hnear, hreturnExcised⟩
  rcases unitaryEvolution_near_unitary_projectiveReturn_or_transverseWardObserver
      x t (U c) ε β with hmiss | hprojective | hward
  · exact False.elim ((not_lt_of_ge hnear) hmiss)
  · exact False.elim ((not_lt_of_ge hprojective) hreturnExcised)
  · exact ⟨c, hward⟩

end

end GaloisForLFunctions.HTGeometry
