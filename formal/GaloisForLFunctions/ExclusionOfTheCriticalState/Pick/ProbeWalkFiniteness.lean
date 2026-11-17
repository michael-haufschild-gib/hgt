import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeHullRanks
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheProbeSamplesHaveNoFiniteRecurrence
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Finite probe-walk recurrences and critical samples

The reflection hull carries the actual probe walk. Cayley–Hamilton gives
every linear observation a recurrence whose degree is the sum of the two
sector Gram ranks. The critical-state sample sequence has no such recurrence,
so no finite-dimensional linear orbit can reproduce it.

This dynamical consequence uses the finite character decomposition obtained
from the averaging mechanism of Aoki, arXiv:2611.20592, Lemma 3.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticHodgeTheoryOfDegenerations

private theorem charpoly_readout_recurrence {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : Module.End K V) (ℓ : V →ₗ[K] K)
    (x : V) (n : ℕ) :
    ∑ j ∈ T.charpoly.support, T.charpoly.coeff j * ℓ ((T ^ (n + j)) x) = 0 := by
  have h := congrArg (fun A : Module.End K V => ℓ ((T^n) (A x))) (LinearMap.aeval_self_charpoly T)
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum,
    pow_add, Module.End.mul_apply] using h

variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

/-- Reflection closure also contains every step of the actual probe walk. -/
theorem walk_mem_reflectionHull {x : ZeroSpace} (hx : x ∈ reflectionHull p) :
    walk p x ∈ reflectionHull p := by
  apply zeroReflection_mem_reflectionHull p
  change probeProjection p x + probeProjection p x - x ∈ reflectionHull p
  have hq := probeSpace_le_reflectionHull p ((probeSpace p).starProjection_apply_mem x)
  exact (reflectionHull p).sub_mem ((reflectionHull p).add_mem hq hq) hx

/-- The finite active state space carries the genuine walk, with no invariance premise. -/
def hullWalk : Module.End ℂ (reflectionHull p) :=
  (walk p).toLinearMap.restrict (fun _ hx => walk_mem_reflectionHull p hx)

@[simp] theorem hullWalk_apply (x : reflectionHull p) :
    (hullWalk p x : ZeroSpace) = walk p x := rfl

/-- Iteration in the finite active space agrees with iteration in the full zero space. -/
theorem hullWalk_pow_apply (x : reflectionHull p) (n : ℕ) :
    ((hullWalk p ^ n) x : ZeroSpace) = (walk p ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ']
    change walk p (((hullWalk p ^ n) x : reflectionHull p) : ZeroSpace) =
      walk p ((walk p ^ n) x)
    rw [ih]

/-- The exact finite recurrence has degree equal to the sum of the two sector Gram ranks. -/
theorem hullWalk_charpoly_degree :
    (hullWalk p).charpoly.natDegree =
      (positiveProbeGram p).rank + (negativeProbeGram p).rank := by
  rw [LinearMap.charpoly_natDegree, reflectionHull_finrank_eq_sector_ranks]

/-- Every complex linear observation of the finite probe walk obeys its characteristic recurrence. -/
theorem probeWalk_readout_recurrence (ℓ : ZeroSpace →ₗ[ℂ] ℂ) (x : reflectionHull p) (n : ℕ) :
    ∑ j ∈ (hullWalk p).charpoly.support,
      (hullWalk p).charpoly.coeff j * ℓ ((walk p ^ (n + j)) x) = 0 := by
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, hullWalk_pow_apply] using
    charpoly_readout_recurrence (hullWalk p) (ℓ.comp (reflectionHull p).subtype) x n

/-- No finite-dimensional real linear orbit can represent all critical-state probe samples. -/
theorem finite_linear_orbit_cannot_realize_criticalSamples {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (T : Module.End ℝ V) (ℓ : V →ₗ[ℝ] ℝ) (x : V)
    {W₀ : ℝ} {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ¬ ∀ n : ℕ, ℓ ((T ^ n) x) = criticalProbeSample F n := by
  intro h
  obtain ⟨n, hn⟩ := criticalProbeSample_no_recurrence hF (LinearMap.charpoly_monic T).ne_zero
  apply hn
  simpa only [h] using charpoly_readout_recurrence T ℓ x n

/-- Every finite probe walk fails to reproduce the normalized critical state's complete sample sequence. -/
theorem probeWalk_cannot_realize_criticalSamples (ℓ : ZeroSpace →ₗ[ℝ] ℝ) (x : reflectionHull p)
    {W₀ : ℝ} {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ¬ ∀ n : ℕ, ℓ ((walk p ^ n) x) = criticalProbeSample F n := by
  intro h
  letI : FiniteDimensional ℝ (reflectionHull p) :=
    FiniteDimensional.trans ℝ ℂ (reflectionHull p)
  apply finite_linear_orbit_cannot_realize_criticalSamples
    ((hullWalk p).restrictScalars ℝ) (ℓ.comp ((reflectionHull p).subtype.restrictScalars ℝ)) x hF
  intro n
  have he : (((hullWalk p).restrictScalars ℝ ^ n) x : ZeroSpace) = (walk p ^ n) x := by
    have hr : (((hullWalk p).restrictScalars ℝ ^ n) x : reflectionHull p) =
        (hullWalk p ^ n) x := by
      induction n with
      | zero => rfl
      | succ n ih =>
        simp only [pow_succ', Module.End.mul_apply]
        change (hullWalk p) ((((hullWalk p).restrictScalars ℝ ^ n) x)) =
          (hullWalk p) ((hullWalk p ^ n) x)
        rw [ih]
    rw [hr, hullWalk_pow_apply]
  change ℓ ((((hullWalk p).restrictScalars ℝ ^ n) x : reflectionHull p) : ZeroSpace) = _
  rw [he]
  exact h n

#print axioms hullWalk_charpoly_degree
#print axioms probeWalk_readout_recurrence
#print axioms finite_linear_orbit_cannot_realize_criticalSamples
#print axioms probeWalk_cannot_realize_criticalSamples
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
