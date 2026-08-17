import GaloisForLFunctions.RHTower.RoutePPrimitiveJointDepthGammaJuliaScalarIntertwinerNoGo
import GaloisForLFunctions.RHTower.FiniteMixedSpikeRealization
import GaloisForLFunctions.RHTower.MixedSpikeQuantumFisher

/-!
# Literal two-prime source-state Ward budget obstruction

The exact Route P Gamma--Julia transport is diagonal in prime labels, so resolved-channel
off-diagonal Ward energy cannot see it.  This module instead couples the prime-log Hamiltonian to
the normalized rank-one state carried by the literal reciprocal-promotion co-source on depth-zero
primes two and three.

Its Hilbert--Schmidt commutator energy is exactly twice the weighted two-point variance.  It stays
strictly positive at the critical boundary `u = 0`, whereas the completed Möbius eight-unit budget
`8 * (1 - exp (-u))` tends to zero.  Thus the completed budget cannot dominate this literal source
compression for every positive `u`.  Any viable Ward completion must use a nonlocal cancellation
before this two-cell compression; a compression-monotone comparison is impossible.
-/

open scoped BigOperators InnerProductSpace Topology
open Filter ContinuousLinearMap

namespace RHTower

noncomputable section

def routePTwoPrimeWardCellTwo : Nat.Primes × ℕ :=
  (⟨2, Nat.prime_two⟩, 0)

def routePTwoPrimeWardCellThree : Nat.Primes × ℕ :=
  (⟨3, Nat.prime_three⟩, 0)

def routePTwoPrimeWardCell (i : Fin 2) : Nat.Primes × ℕ :=
  if i = 0 then routePTwoPrimeWardCellTwo else routePTwoPrimeWardCellThree

def routePTwoPrimeWardRawWeight (u : ℝ) (i : Fin 2) : ℝ :=
  xiGammaEulerPrimitiveDescentTestAmplitude u (routePTwoPrimeWardCell i) ^ 2

def routePTwoPrimeWardMass (u : ℝ) : ℝ :=
  ∑ i : Fin 2, routePTwoPrimeWardRawWeight u i

def routePTwoPrimeWardWeight (u : ℝ) (i : Fin 2) : ℝ :=
  routePTwoPrimeWardRawWeight u i / routePTwoPrimeWardMass u

def routePTwoPrimeWardEnergyLevel (i : Fin 2) : ℝ :=
  routePPrimitiveJointDepthGammaJuliaLogMultiplier (routePTwoPrimeWardCell i)

def routePTwoPrimeWardKet (u : ℝ) : FiniteIndexClockSpace (Fin 2) :=
  finiteIndexWeightKet (routePTwoPrimeWardWeight u)

def routePTwoPrimeWardHamiltonian :
    FiniteIndexClockSpace (Fin 2) →L[ℂ] FiniteIndexClockSpace (Fin 2) :=
  finiteIndexDiagonalHamiltonian routePTwoPrimeWardEnergyLevel

def routePTwoPrimeSourceStateWardEnergy (u : ℝ) : ℝ :=
  hsNormSq
    (rankOneHamiltonianCommutator routePTwoPrimeWardHamiltonian
      (routePTwoPrimeWardKet u))

def routePCompletedEightUnitBudget (u : ℝ) : ℝ :=
  8 * (1 - Real.exp (-u))

theorem routePTwoPrimeWardRawWeight_pos (u : ℝ) (i : Fin 2) :
    0 < routePTwoPrimeWardRawWeight u i := by
  exact sq_pos_of_pos
    (xiGammaEulerPrimitiveDescentTestAmplitude_pos u (routePTwoPrimeWardCell i))

theorem routePTwoPrimeWardRawWeight_eq (u : ℝ) (i : Fin 2) :
    routePTwoPrimeWardRawWeight u i =
      Real.exp
          (-u * Real.log
            (xiGammaEulerValuationNat (routePTwoPrimeWardCell i))) /
        (xiGammaEulerValuationNat (routePTwoPrimeWardCell i) : ℝ) := by
  rw [routePTwoPrimeWardRawWeight,
    xiGammaEulerPrimitiveDescentTestAmplitude_sq,
    xiGammaEulerBoundaryRealAmplitude_sq]
  have hlog : Real.log ((routePTwoPrimeWardCell i).1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by
      exact_mod_cast (routePTwoPrimeWardCell i).1.property.one_lt))
  field_simp

theorem continuous_routePTwoPrimeWardRawWeight (i : Fin 2) :
    Continuous (fun u : ℝ => routePTwoPrimeWardRawWeight u i) := by
  rw [show (fun u : ℝ => routePTwoPrimeWardRawWeight u i) =
      fun u =>
        Real.exp
            (-u * Real.log
              (xiGammaEulerValuationNat (routePTwoPrimeWardCell i))) /
          (xiGammaEulerValuationNat (routePTwoPrimeWardCell i) : ℝ) by
    funext u
    exact routePTwoPrimeWardRawWeight_eq u i]
  fun_prop

theorem routePTwoPrimeWardMass_pos (u : ℝ) :
    0 < routePTwoPrimeWardMass u := by
  rw [routePTwoPrimeWardMass, Fin.sum_univ_two]
  exact add_pos (routePTwoPrimeWardRawWeight_pos u 0)
    (routePTwoPrimeWardRawWeight_pos u 1)

theorem continuous_routePTwoPrimeWardMass :
    Continuous routePTwoPrimeWardMass := by
  rw [show routePTwoPrimeWardMass =
      fun u : ℝ => routePTwoPrimeWardRawWeight u 0 +
        routePTwoPrimeWardRawWeight u 1 by
    funext u
    rw [routePTwoPrimeWardMass, Fin.sum_univ_two]]
  exact (continuous_routePTwoPrimeWardRawWeight 0).add
    (continuous_routePTwoPrimeWardRawWeight 1)

theorem routePTwoPrimeWardWeight_nonneg (u : ℝ) (i : Fin 2) :
    0 ≤ routePTwoPrimeWardWeight u i := by
  exact (div_pos (routePTwoPrimeWardRawWeight_pos u i)
    (routePTwoPrimeWardMass_pos u)).le

theorem routePTwoPrimeWardWeight_pos (u : ℝ) (i : Fin 2) :
    0 < routePTwoPrimeWardWeight u i := by
  exact div_pos (routePTwoPrimeWardRawWeight_pos u i)
    (routePTwoPrimeWardMass_pos u)

theorem continuous_routePTwoPrimeWardWeight (i : Fin 2) :
    Continuous (fun u : ℝ => routePTwoPrimeWardWeight u i) := by
  exact (continuous_routePTwoPrimeWardRawWeight i).div
    continuous_routePTwoPrimeWardMass
    (fun u => ne_of_gt (routePTwoPrimeWardMass_pos u))

theorem routePTwoPrimeWardWeight_sum (u : ℝ) :
    ∑ i : Fin 2, routePTwoPrimeWardWeight u i = 1 := by
  simp only [routePTwoPrimeWardWeight]
  rw [← Finset.sum_div, routePTwoPrimeWardMass]
  exact div_self (ne_of_gt (routePTwoPrimeWardMass_pos u))

theorem routePTwoPrimeWardKet_norm_eq_one (u : ℝ) :
    ‖routePTwoPrimeWardKet u‖ = 1 := by
  exact finiteIndexWeightKet_norm_eq_one _
    (routePTwoPrimeWardWeight_nonneg u) (routePTwoPrimeWardWeight_sum u)

theorem routePTwoPrimeWardHamiltonian_selfAdjoint :
    adjoint routePTwoPrimeWardHamiltonian = routePTwoPrimeWardHamiltonian := by
  exact finiteIndexDiagonalHamiltonian_selfAdjoint _

theorem routePTwoPrimeSourceStateWardEnergy_eq_variance (u : ℝ) :
    routePTwoPrimeSourceStateWardEnergy u =
      2 * ((∑ i : Fin 2,
          routePTwoPrimeWardWeight u i * routePTwoPrimeWardEnergyLevel i ^ 2) -
        (∑ i : Fin 2,
          routePTwoPrimeWardWeight u i * routePTwoPrimeWardEnergyLevel i) ^ 2) := by
  rw [routePTwoPrimeSourceStateWardEnergy,
    hsNormSq_rankOneHamiltonianCommutator routePTwoPrimeWardHamiltonian
      routePTwoPrimeWardHamiltonian_selfAdjoint (routePTwoPrimeWardKet u)
      (routePTwoPrimeWardKet_norm_eq_one u)]
  congr 1
  simpa [routePTwoPrimeWardHamiltonian, routePTwoPrimeWardKet] using
    finiteIndexWeightKet_diagonal_variance
      (routePTwoPrimeWardWeight u) routePTwoPrimeWardEnergyLevel
      (routePTwoPrimeWardWeight_nonneg u)

theorem routePTwoPrimeSourceStateWardEnergy_eq_pair (u : ℝ) :
    routePTwoPrimeSourceStateWardEnergy u =
      2 * routePTwoPrimeWardWeight u 0 * routePTwoPrimeWardWeight u 1 *
        (routePTwoPrimeWardEnergyLevel 0 - routePTwoPrimeWardEnergyLevel 1) ^ 2 := by
  rw [routePTwoPrimeSourceStateWardEnergy_eq_variance]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have hsum := routePTwoPrimeWardWeight_sum u
  rw [Fin.sum_univ_two] at hsum
  have hw1 : routePTwoPrimeWardWeight u 1 =
      1 - routePTwoPrimeWardWeight u 0 := by
    linarith
  rw [hw1]
  ring

theorem routePTwoPrimeWardEnergyLevel_ne :
    routePTwoPrimeWardEnergyLevel 0 ≠ routePTwoPrimeWardEnergyLevel 1 := by
  have hc : routePPrimitiveFourthDepthGammaCyclicAmplitude ≠ 0 := by
    intro hc
    have hsq := routePPrimitiveFourthDepthGammaCyclicAmplitude_sq
    rw [hc] at hsq
    norm_num at hsq
  have hlog : Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by
    exact ne_of_lt
      (Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num))
  intro h
  apply hlog
  apply mul_left_cancel₀ hc
  simpa [routePTwoPrimeWardEnergyLevel,
    routePPrimitiveJointDepthGammaJuliaLogMultiplier,
    routePTwoPrimeWardCell, routePTwoPrimeWardCellTwo,
    routePTwoPrimeWardCellThree] using h

theorem routePTwoPrimeSourceStateWardEnergy_pos (u : ℝ) :
    0 < routePTwoPrimeSourceStateWardEnergy u := by
  rw [routePTwoPrimeSourceStateWardEnergy_eq_pair]
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num) (routePTwoPrimeWardWeight_pos u 0))
      (routePTwoPrimeWardWeight_pos u 1))
    (sq_pos_of_ne_zero (sub_ne_zero.mpr routePTwoPrimeWardEnergyLevel_ne))

theorem continuous_routePTwoPrimeSourceStateWardEnergy :
    Continuous routePTwoPrimeSourceStateWardEnergy := by
  rw [show routePTwoPrimeSourceStateWardEnergy =
      fun u : ℝ =>
        2 * routePTwoPrimeWardWeight u 0 * routePTwoPrimeWardWeight u 1 *
          (routePTwoPrimeWardEnergyLevel 0 -
            routePTwoPrimeWardEnergyLevel 1) ^ 2 by
    funext u
    exact routePTwoPrimeSourceStateWardEnergy_eq_pair u]
  exact (((continuous_const.mul
      (continuous_routePTwoPrimeWardWeight 0)).mul
      (continuous_routePTwoPrimeWardWeight 1)).mul continuous_const)

theorem tendsto_routePCompletedEightUnitBudget_zero :
    Tendsto routePCompletedEightUnitBudget (nhds 0) (nhds 0) := by
  have hcont : Continuous routePCompletedEightUnitBudget := by
    unfold routePCompletedEightUnitBudget
    fun_prop
  have ht : Tendsto routePCompletedEightUnitBudget (nhds 0)
      (nhds (routePCompletedEightUnitBudget 0)) := hcont.continuousAt
  simpa [routePCompletedEightUnitBudget] using ht

theorem eventually_routePCompletedEightUnitBudget_lt_sourceStateWardEnergy :
    ∀ᶠ u in 𝓝[>] (0 : ℝ),
      routePCompletedEightUnitBudget u <
        routePTwoPrimeSourceStateWardEnergy u := by
  have hward0 : 0 < routePTwoPrimeSourceStateWardEnergy 0 :=
    routePTwoPrimeSourceStateWardEnergy_pos 0
  have hward : Tendsto routePTwoPrimeSourceStateWardEnergy
      (nhds 0) (nhds (routePTwoPrimeSourceStateWardEnergy 0)) :=
    continuous_routePTwoPrimeSourceStateWardEnergy.continuousAt
  have hwardLower : ∀ᶠ u in nhds (0 : ℝ),
      routePTwoPrimeSourceStateWardEnergy 0 / 2 <
        routePTwoPrimeSourceStateWardEnergy u :=
    hward.eventually (eventually_gt_nhds (by linarith))
  have hbudgetUpper : ∀ᶠ u in nhds (0 : ℝ),
      routePCompletedEightUnitBudget u <
        routePTwoPrimeSourceStateWardEnergy 0 / 2 :=
    tendsto_routePCompletedEightUnitBudget_zero.eventually
      (eventually_lt_nhds (half_pos hward0))
  exact ((hbudgetUpper.and hwardLower).mono fun u hu => lt_trans hu.1 hu.2).filter_mono
    inf_le_left

theorem not_forall_routePTwoPrimeSourceStateWardEnergy_le_completedEightUnitBudget :
    ¬ ∀ u : ℝ, 0 < u →
      routePTwoPrimeSourceStateWardEnergy u ≤
        routePCompletedEightUnitBudget u := by
  intro hbound
  obtain ⟨u, hlt, hu⟩ :=
    (eventually_routePCompletedEightUnitBudget_lt_sourceStateWardEnergy.and
      self_mem_nhdsWithin).exists
  exact (not_lt_of_ge (hbound u hu)) hlt

end

end RHTower
