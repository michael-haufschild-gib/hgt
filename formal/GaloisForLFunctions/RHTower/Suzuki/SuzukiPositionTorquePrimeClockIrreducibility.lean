import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilPositionTorqueCurvature
import GaloisForLFunctions.RHTower.XiShiftResidueValuationFusionBarrier

/-!
# Prime-clock irreducibility of Suzuki's position torque

The prime term in Suzuki's exact position-torque transform is the half-shifted logarithmic
filtered von Mangoldt source.  Its coefficient is nonzero on every positive prime power.
Consequently every valuation layer remains private, and the exact prime-source boundary proves
that its analytic carrier is hypertranscendental even after adjoining:

* the genuine upper-end coordinate;
* every finite-prime Euler germ;
* every depth of every finite residue--valuation fusion carrier;
* all differential jets of those carriers.

This is a faithful-source theorem.  It proves that Suzuki's literal torque contains irreducibly
global prime-clock data; it does not by itself supply parity interlacing, transition-scale
selection, a meromorphic limit, or the Hermite--Biehler conclusion.
-/

namespace RHTower

open ArithmeticFunction Set
open scoped Differential LSeries.notation

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

universe u

local instance suzukiTorquePrimeUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance suzukiTorquePrimeUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance suzukiTorquePrimeUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- Finite-abscissa arithmetic carrier of the prime term in Suzuki's position torque. -/
def suzukiPositionTorquePrimeFiniteAbscissaSource :
    finiteAbscissaArithmeticSubalgebra :=
  finiteAbscissaDirichletShift (-(1 / 2 : ℂ))
    (finiteAbscissaLogWeight filteredVonMangoldtFiniteAbscissaSource)

@[simp]
theorem suzukiPositionTorquePrimeFiniteAbscissaSource_apply (n : ℕ) :
    suzukiPositionTorquePrimeFiniteAbscissaSource.1 n =
      cpowWeight (-(1 / 2 : ℂ)) n * (Real.log n : ℂ) *
        filteredVonMangoldtCoeff n := by
  rw [suzukiPositionTorquePrimeFiniteAbscissaSource,
    finiteAbscissaDirichletShift_apply]
  change cpowWeight (-(1 / 2 : ℂ)) n *
      logWeight filteredVonMangoldtArithmetic n = _
  rw [logWeight_apply, filteredVonMangoldtArithmetic_apply]
  ring

/-- The Suzuki torque source remains supported on positive prime powers. -/
theorem suzukiPositionTorquePrimeSource_supportedOnPositivePrimePowers :
    PrimeProfileSupportedOnPositivePrimePowers
      suzukiPositionTorquePrimeFiniteAbscissaSource.1 := by
  intro n hn
  apply filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers
  intro hzero
  apply hn
  rw [suzukiPositionTorquePrimeFiniteAbscissaSource_apply]
  rw [show filteredVonMangoldtCoeff n = 0 from hzero]
  simp

/-- Every valuation layer of the Suzuki torque source is nowhere zero. -/
theorem suzukiPositionTorquePrimeSource_primePow_ne_zero
    (p : Nat.Primes) (e : ℕ) :
    suzukiPositionTorquePrimeFiniteAbscissaSource.1
      ((p : ℕ) ^ (e + 1)) ≠ 0 := by
  rw [suzukiPositionTorquePrimeFiniteAbscissaSource_apply]
  apply mul_ne_zero
  · apply mul_ne_zero
    · rw [cpowWeight]
      exact Complex.cpow_ne_zero_iff.mpr <| Or.inl <| by
        exact_mod_cast (pow_ne_zero (e + 1) p.2.ne_zero)
    · have hp1 : (1 : ℝ) < (p : ℕ) := by
        exact_mod_cast p.2.one_lt
      have hN1 : (1 : ℝ) < (((p : ℕ) ^ (e + 1) : ℕ) : ℝ) := by
        push_cast
        exact one_lt_pow₀ hp1 (Nat.succ_ne_zero e)
      exact_mod_cast (Real.log_pos hN1).ne'
  · exact filteredVonMangoldtCoeff_primePow_ne_zero p e

/-- All valuation depths are usable by the Suzuki torque source. -/
theorem suzukiPositionTorquePrimeSource_nonvanishing_layers_infinite :
    ¬ {e : ℕ | ∀ p : Nat.Primes,
        suzukiPositionTorquePrimeFiniteAbscissaSource.1
          ((p : ℕ) ^ (e + 1)) ≠ 0}.Finite := by
  have hset : {e : ℕ | ∀ p : Nat.Primes,
      suzukiPositionTorquePrimeFiniteAbscissaSource.1
        ((p : ℕ) ^ (e + 1)) ≠ 0} = (Set.univ : Set ℕ) := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro p
    exact suzukiPositionTorquePrimeSource_primePow_ne_zero p e
  rw [hset]
  exact Set.infinite_univ

/-- Exact Dirichlet-series identification with the prime numerator in Suzuki's torque. -/
theorem LSeries_suzukiPositionTorquePrimeFiniteAbscissaSource (s : ℂ) :
    LSeries suzukiPositionTorquePrimeFiniteAbscissaSource.1 s =
      LSeries (LSeries.logMul filteredVonMangoldtCoeff) (s - 1 / 2) := by
  rw [show LSeries suzukiPositionTorquePrimeFiniteAbscissaSource.1 s =
      LSeries
        (dirichletShift (-(1 / 2 : ℂ))
          (logWeight filteredVonMangoldtArithmetic)) s by rfl,
    LSeries_dirichletShift]
  rw [show s + -(1 / 2 : ℂ) = s - 1 / 2 by ring]
  congr 1
  funext n
  have h :=
    congrFun (lSeries_logMul_eq_logWeight filteredVonMangoldtArithmetic) n
  exact h.symm

/-- Actual upper-end meromorphic carrier of Suzuki's prime position-torque source. -/
def suzukiPositionTorquePrimeUpperEndCarrier : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    suzukiPositionTorquePrimeFiniteAbscissaSource

/-- Suzuki's prime torque carrier is differentially independent over every local-Euler
residue--valuation fusion completion. -/
theorem suzukiPositionTorquePrimeUpperEndCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    DifferentialIndependent
      (primeResidueValuationLocalEulerFusionCompletionField A y)
      (fun _ : Unit => suzukiPositionTorquePrimeUpperEndCarrier) := by
  exact
    analyticPrimeProfileCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
      A y hy suzukiPositionTorquePrimeFiniteAbscissaSource
      suzukiPositionTorquePrimeSource_supportedOnPositivePrimePowers
      suzukiPositionTorquePrimeSource_nonvanishing_layers_infinite

/-- The exact prime carrier inside Suzuki's position torque is hypertranscendental over every
local-Euler residue--valuation fusion completion. -/
theorem suzukiPositionTorquePrimeUpperEndCarrier_hypertranscendentalOver_localEulerResidueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    HypertranscendentalOver
      (primeResidueValuationLocalEulerFusionCompletionField A y)
      suzukiPositionTorquePrimeUpperEndCarrier := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact
    suzukiPositionTorquePrimeUpperEndCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
      A y hy

/-- The arithmetic term displayed in Suzuki's Euler-half-plane torque is exactly the L-series
of the shifted logarithmic filtered-von-Mangoldt source. -/
theorem suzukiPositionTorqueEulerSource_eq_primeSource (s : ℂ) :
    suzukiPositionTorqueEulerSource s =
      (LSeries suzukiPositionTorquePrimeFiniteAbscissaSource.1 s +
        (1 / (s + 3 / 2) ^ (2 : ℕ) + 1 / (s + 1 / 2) ^ (2 : ℕ) -
          1 / (s - 3 / 2) ^ (2 : ℕ))) / (2 * s ^ (2 : ℕ)) := by
  rw [suzukiPositionTorqueEulerSource,
    LSeries_suzukiPositionTorquePrimeFiniteAbscissaSource]

end

end RHTower
