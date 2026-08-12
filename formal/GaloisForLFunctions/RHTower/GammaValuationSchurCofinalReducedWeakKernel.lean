import GaloisForLFunctions.RHTower.GammaValuationSchurAdjacentPrimePrimitiveRecovery

/-!
# Cofinal physical reduction after cumulative prime incidence

P-G87/P-G88 determine the order in which P-G84's physical cofinal Schur fraction can act on
P-G78's weak Köthe kernel.  Multiplying the local adjacent edge Gram by the physical residual
factor still misses every nonadjacent covariance.  Thus scalar depletion cannot repair locality.

Applying cumulative inverse incidence first is different.  Scaling P-G86's recovered global weak
kernel by the same physical residual factor produces an absolutely summable positive weak kernel,
bounded by strictly less than one half of the original seminorm product.  It retains nonadjacent
covariance with exact value equal to the physical residual factor.

This constructs the canonical operator-level survivor.  It does not assert that an independently
constructed completed Gamma/polar Feshbach operator equals this reduced kernel.
-/

open Real Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace RHTower.HedenmalmThetaSource

noncomputable section

def gammaSewnCriticalCofinalResidualFactor : ℝ :=
  1 - gammaSewnCriticalAdjacentPrime_CofinalFraction

theorem gammaSewnCriticalCofinalResidualFactor_mem :
    gammaSewnCriticalCofinalResidualFactor ∈ Set.Ioo 0 (1 / 2 : ℝ) := by
  rcases gammaSewnCriticalAdjacentPrime_CofinalFraction_mem with ⟨hlower, hupper⟩
  constructor <;> unfold gammaSewnCriticalCofinalResidualFactor <;> linarith

def gammaSewnCriticalCofinalReducedLocalEdgeKernel
    (a b : RHTower.DeningerHeightKothe) : ℂ :=
  (gammaSewnCriticalCofinalResidualFactor : ℂ) *
    RHTower.gammaValuationAdjacentEdgeKernel a b

def gammaSewnCriticalCofinalReducedWeakKernel
    (a b : RHTower.DeningerHeightKothe) : ℂ :=
  (gammaSewnCriticalCofinalResidualFactor : ℂ) *
    RHTower.gammaValuationAdjacentPrimitiveKernel a b

theorem gammaSewnCriticalCofinalReducedWeakKernel_eq
    (a b : RHTower.DeningerHeightKothe) :
    gammaSewnCriticalCofinalReducedWeakKernel a b =
      (gammaSewnCriticalCofinalResidualFactor : ℂ) *
        RHTower.gammaValuationWeakKernel a b := by
  rw [gammaSewnCriticalCofinalReducedWeakKernel,
    RHTower.gammaValuationAdjacentPrimitiveKernel_eq_weakKernel]

theorem summable_gammaSewnCriticalCofinalReducedWeakKernelLayer
    (a b : RHTower.DeningerHeightKothe) :
    Summable (fun e : ℕ =>
      (gammaSewnCriticalCofinalResidualFactor : ℂ) *
        (conj (RHTower.gammaValuationAdjacentPrimitive e a) *
          RHTower.gammaValuationAdjacentPrimitive e b)) := by
  have h := (RHTower.summable_gammaValuationWeakKernel a b).mul_left
    (gammaSewnCriticalCofinalResidualFactor : ℂ)
  exact h.congr fun e => by
    rw [RHTower.gammaValuationAdjacentPrimitive_eq_layerSum,
      RHTower.gammaValuationAdjacentPrimitive_eq_layerSum]

theorem norm_gammaSewnCriticalCofinalReducedWeakKernel_lt_half_bound
    (a b : RHTower.DeningerHeightKothe) :
    ‖gammaSewnCriticalCofinalReducedWeakKernel a b‖ ≤
      (1 / 2 : ℝ) *
        (RHTower.deningerHeightSeminorm 0 a *
          RHTower.deningerHeightSeminorm 0 b) := by
  rw [gammaSewnCriticalCofinalReducedWeakKernel_eq, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos gammaSewnCriticalCofinalResidualFactor_mem.1]
  exact mul_le_mul gammaSewnCriticalCofinalResidualFactor_mem.2.le
    (RHTower.norm_gammaValuationWeakKernel_le a b)
    (norm_nonneg _) (by norm_num)

theorem gammaSewnCriticalCofinalReducedWeakKernel_self_eq_energy
    (a : RHTower.DeningerHeightKothe) :
    gammaSewnCriticalCofinalReducedWeakKernel a a =
      ((gammaSewnCriticalCofinalResidualFactor *
        RHTower.gammaValuationWeakEnergy a : ℝ) : ℂ) := by
  rw [gammaSewnCriticalCofinalReducedWeakKernel_eq,
    RHTower.gammaValuationWeakKernel_self_eq_energy]
  norm_cast

theorem gammaSewnCriticalCofinalReducedWeakEnergy_nonneg
    (a : RHTower.DeningerHeightKothe) :
    0 ≤ gammaSewnCriticalCofinalResidualFactor *
      RHTower.gammaValuationWeakEnergy a := by
  exact mul_nonneg gammaSewnCriticalCofinalResidualFactor_mem.1.le
    (RHTower.gammaValuationWeakEnergy_nonneg a)

theorem gammaSewnCriticalCofinalReducedLocalEdgeKernel_indexZero_indexTwo_eq_zero :
    gammaSewnCriticalCofinalReducedLocalEdgeKernel
        (RHTower.gammaValuationAxisDelta (RHTower.nthPrimeSubtype 0) 0)
        (RHTower.gammaValuationAxisDelta (RHTower.nthPrimeSubtype 2) 0) = 0 := by
  rw [gammaSewnCriticalCofinalReducedLocalEdgeKernel,
    RHTower.gammaValuationAdjacentEdgeKernel_indexZero_indexTwo_eq_zero, mul_zero]

theorem gammaSewnCriticalCofinalReducedWeakKernel_indexZero_indexTwo_eq_factor :
    gammaSewnCriticalCofinalReducedWeakKernel
        (RHTower.gammaValuationAxisDelta (RHTower.nthPrimeSubtype 0) 0)
        (RHTower.gammaValuationAxisDelta (RHTower.nthPrimeSubtype 2) 0) =
      (gammaSewnCriticalCofinalResidualFactor : ℂ) := by
  rw [gammaSewnCriticalCofinalReducedWeakKernel,
    RHTower.gammaValuationAdjacentPrimitiveKernel_indexZero_indexTwo_eq_one, mul_one]

/-- **P-G87 order no-go.** Physical scalar depletion cannot turn local edges into global kernel. -/
theorem gammaSewnCriticalCofinalReducedLocalEdgeKernel_ne_reducedWeakKernel :
    gammaSewnCriticalCofinalReducedLocalEdgeKernel ≠
      gammaSewnCriticalCofinalReducedWeakKernel := by
  intro h
  have hpair := congrFun (congrFun h
    (RHTower.gammaValuationAxisDelta (RHTower.nthPrimeSubtype 0) 0))
    (RHTower.gammaValuationAxisDelta (RHTower.nthPrimeSubtype 2) 0)
  rw [gammaSewnCriticalCofinalReducedLocalEdgeKernel_indexZero_indexTwo_eq_zero,
    gammaSewnCriticalCofinalReducedWeakKernel_indexZero_indexTwo_eq_factor] at hpair
  have hre := congrArg Complex.re hpair
  simp at hre
  linarith [gammaSewnCriticalCofinalResidualFactor_mem.1]

/-- **P-G88 nonlocal covariance.** Physical reduced response survives every common-depth pair. -/
theorem gammaSewnCriticalCofinalReducedWeakKernel_axisDelta_sameDepth
    (p q : Nat.Primes) (e : ℕ) :
    gammaSewnCriticalCofinalReducedWeakKernel
        (RHTower.gammaValuationAxisDelta p e)
        (RHTower.gammaValuationAxisDelta q e) =
      (gammaSewnCriticalCofinalResidualFactor : ℂ) := by
  rw [gammaSewnCriticalCofinalReducedWeakKernel_eq,
    RHTower.gammaValuationWeakKernel_axisDelta_sameDepth, mul_one]

end

end RHTower.HedenmalmThetaSource
