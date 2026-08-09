import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Core

/-!
# Abelian zeta gas: finite-group realization and Gibbs factorization

This file proves the exact finite-group realization in the chamber `sigma + tau > 1`, the atom
formula of the countable product measure, and the equality between independent mode weight and
the two intrinsic group observables (order and socle order).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Independent mode weight and intrinsic order/socle weight agree exactly. -/
theorem abelianZetaModeWeight_eq_twoObservableWeight
    (θ : AbelianZetaParameters) (A : AbelianZetaGroupClass) :
    abelianZetaModeWeight θ A = abelianZetaTwoObservableWeight θ A := by
  classical
  simp only [abelianZetaModeWeight, abelianZetaTwoObservableWeight,
    AbelianZetaGroupClass.order, AbelianZetaGroupClass.socleOrder, Finsupp.prod,
    Nat.cast_prod, Nat.cast_pow]
  rw [← Real.finsetProd_rpow A.support
    (fun m => ((m.1 : ℝ) ^ (AbelianZetaMode.depth m * A m)))
    (fun m _ => pow_nonneg (by positivity) _) (-θ.sigma)]
  rw [← Real.finsetProd_rpow A.support
    (fun m => ((m.1 : ℝ) ^ (A m)))
    (fun m _ => pow_nonneg (by positivity) _) (-θ.tau)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent]
  have hp : 0 < (m.1 : ℝ) := by exact_mod_cast m.1.prop.pos
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  rw [show (-((AbelianZetaMode.depth m : ℝ) * θ.sigma + θ.tau)) * (A m : ℝ) =
      (AbelianZetaMode.depth m * A m : ℕ) * (-θ.sigma) +
        (A m : ℕ) * (-θ.tau) by push_cast; ring]
  rw [Real.rpow_add hp]
  congr 1 <;> rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]

/-- Product-measure atom carried by a canonical finite abelian group class. -/
def abelianZetaClassMass (θ : AbelianZetaParameters) (A : AbelianZetaGroupClass) : ℝ≥0∞ :=
  θ.gasMeasure {A.configuration}

/-- Exact countable product formula for every canonical group class atom. -/
theorem abelianZetaClassMass_eq_tprod
    (θ : AbelianZetaParameters) (A : AbelianZetaGroupClass) :
    abelianZetaClassMass θ A =
      ∏' m : AbelianZetaMode,
        ENNReal.ofReal ((θ.ratio m) ^ (A m) * (1 - θ.ratio m)) := by
  rw [abelianZetaClassMass, AbelianZetaParameters.gasMeasure,
    Measure.infinitePi_singleton]
  apply tprod_congr
  intro m
  exact θ.modeLaw_singleton m (A m)

/-- In the exact first-depth chamber, all modes are active only finitely often almost surely. -/
theorem AbelianZetaConvergentParameters.measure_finite_occupancy_eq_one
    (θ : AbelianZetaConvergentParameters) :
    θ.toAbelianZetaParameters.gasMeasure
      {k : AbelianZetaMode → ℕ | (occupiedSet k).Finite} = 1 := by
  have htail := θ.toAbelianZetaParameters.measure_finite_depthTail_eq_one
    (g := 1) (by omega) (by simpa using θ.firstDepth)
  have hevent : {k : AbelianZetaMode → ℕ | (occupiedSet k).Finite} =
      {k | (localHitSet (θ.toAbelianZetaParameters.depthTailEvent 1) k).Finite} := by
    ext k
    simp only [mem_setOf_eq]
    rw [show occupiedSet k =
        localHitSet (θ.toAbelianZetaParameters.depthTailEvent 1) k by
      ext m
      have hd : 1 ≤ AbelianZetaMode.depth m := AbelianZetaMode.depth_pos m
      simp [localHitSet, AbelianZetaParameters.depthTailEvent, hd, occupiedSet]]
  rw [hevent]
  exact htail

/-- In the convergence chamber, almost every full occupation configuration is represented by one
and only one canonical finite abelian group class. -/
theorem AbelianZetaConvergentParameters.measure_existsUnique_groupClass_eq_one
    (θ : AbelianZetaConvergentParameters) :
    θ.toAbelianZetaParameters.gasMeasure
      {k : AbelianZetaMode → ℕ | ∃! A : AbelianZetaGroupClass, A.configuration = k} = 1 := by
  have hevent :
      {k : AbelianZetaMode → ℕ | ∃! A : AbelianZetaGroupClass, A.configuration = k} =
        {k | (occupiedSet k).Finite} := by
    ext k
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨A, hA, _⟩
      rw [← hA]
      exact A.finite_occupiedSet
    · intro hk
      exact existsUnique_groupClass_of_finite_occupiedSet k hk
  rw [hevent]
  exact θ.measure_finite_occupancy_eq_one

/-- Every finite group-class atom has the exact intrinsic Gibbs factor in its mode component. -/
theorem abelianZetaClassMass_intrinsic_factor
    (θ : AbelianZetaParameters) (A : AbelianZetaGroupClass) :
    abelianZetaModeWeight θ A =
      (A.order : ℝ) ^ (-θ.sigma) * (A.socleOrder : ℝ) ^ (-θ.tau) :=
  abelianZetaModeWeight_eq_twoObservableWeight θ A

end GaloisForLFunctions.HTGeometry
