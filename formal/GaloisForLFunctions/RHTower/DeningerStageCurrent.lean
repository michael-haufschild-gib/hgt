import GaloisForLFunctions.RHTower.DeningerCohomologyFunctor
import GaloisForLFunctions.RHTower.DeningerArchimedeanCurrentLift

/-!
# The archimedean current on the first cohomology of a character stage

The first holomorphic de Rham cohomology of a character stage is free on the classes of the
logarithmic differentials of the coordinates.  Dividing those by `2πi` gives the basis in which a
lattice element `a` has class `d log χ^a / (2πi)`, so a functional on the cohomology is freely and
uniquely prescribed by its values on lattice elements.  That functional is the archimedean homology
current, and a transition of stages transports it by the exponent matrix.

* `RHTower.deningerNormalizedBasis` : the basis `d log χ^{e_i} / (2πi)` of the first cohomology.
* `RHTower.deningerKummerClass` : the Kummer class `a ↦ [d log χ^a / (2πi)]`, a linear equivalence.
* `RHTower.deningerStageCurrent`, `_exists_unique` : the current and its characterisation.
* `RHTower.deningerStageCurrent_natural` : compatibility with a transition of stages.
* `RHTower.deningerStageLift` : the square-zero derived algebra map on the stage cohomology.
-/

set_option maxSynthPendingDepth 3

namespace RHTower

open Complex Finset Module

section Singleton

variable {r : ℕ}

/-- The one-element sets of coordinates are the coordinates. -/
noncomputable def deningerSingletonEquiv (r : ℕ) : Fin r ≃ {S : Finset (Fin r) // S.card = 1} where
  toFun i := ⟨{i}, Finset.card_singleton i⟩
  invFun S := deningerSubsetTuple S 0
  left_inv i := by
    show ({i} : Finset (Fin r)).orderEmbOfFin (Finset.card_singleton i) 0 = i
    exact Finset.orderEmbOfFin_singleton i 0
  right_inv S := by
    refine Subtype.ext ?_
    refine Finset.coe_injective ?_
    rw [Finset.coe_singleton, ← deningerSubsetTuple_range S]
    exact (Set.range_unique (f := deningerSubsetTuple S)).symm

@[simp] theorem deningerSubsetTuple_singleton (i : Fin r) (a : Fin 1) :
    deningerSubsetTuple (deningerSingletonEquiv r i) a = i :=
  Finset.orderEmbOfFin_singleton i a

end Singleton

section Basis

variable {r : ℕ}

/-- The invertible normalisation `(2πi)⁻¹`. -/
noncomputable def deningerTwoPiIUnit : ℂˣ :=
  Units.mk0 (2 * (Real.pi : ℂ) * I)⁻¹ (by
    refine inv_ne_zero ?_
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
    exact_mod_cast Real.pi_ne_zero)

theorem deningerTwoPiIUnit_val : (deningerTwoPiIUnit : ℂ) = (2 * (Real.pi : ℂ) * I)⁻¹ := rfl

/-- **The basis of the first cohomology of a character stage given by the normalised logarithmic
differentials** `d log χ^{e_i} / (2πi)`. -/
noncomputable def deningerNormalizedBasis (r : ℕ) :
    Module.Basis (Fin r) ℂ (deningerCohomology r 0) :=
  ((deningerCohomologyBasis r 0).reindex (deningerSingletonEquiv r).symm).unitsSMul
    fun _ => deningerTwoPiIUnit

theorem deningerNormalizedBasis_apply (i : Fin r) :
    deningerNormalizedBasis r i
      = (2 * (Real.pi : ℂ) * I)⁻¹ • deningerCohomologyBasis r 0 (deningerSingletonEquiv r i) := by
  rw [deningerNormalizedBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm]
  rfl

/-- The normalised basis vector is the class of the logarithmic differential of a coordinate,
divided by `2πi`. -/
theorem deningerNormalizedBasis_eq_class (i : Fin r) :
    deningerNormalizedBasis r i = (2 * (Real.pi : ℂ) * I)⁻¹ •
      deningerConstantClass r 0 (deningerDetForm (fun _ : Fin 1 => i)) := by
  rw [deningerNormalizedBasis_apply]
  refine congrArg (fun z => (2 * (Real.pi : ℂ) * I)⁻¹ • z) ?_
  show deningerCohomologyEquiv r 0 (deningerDetFormBasis r 1 (deningerSingletonEquiv r i)) = _
  rw [deningerDetFormBasis_apply]
  refine congrArg (deningerConstantClass r 0) ?_
  refine congrArg deningerDetForm ?_
  funext a
  exact deningerSubsetTuple_singleton i a

end Basis

section Current

variable {r : ℕ}

/-- **The Kummer class map** `a ↦ [d log χ^a / (2πi)]`, a linear equivalence of the complexified
lattice with the first cohomology of the stage. -/
noncomputable def deningerKummerClass (r : ℕ) : (Fin r → ℂ) ≃ₗ[ℂ] deningerCohomology r 0 :=
  (Pi.basisFun ℂ (Fin r)).equiv (deningerNormalizedBasis r) (Equiv.refl _)

theorem deningerKummerClass_single (i : Fin r) :
    deningerKummerClass r (Pi.single i (1 : ℂ)) = deningerNormalizedBasis r i := by
  have h := Module.Basis.equiv_apply (Pi.basisFun ℂ (Fin r)) i (deningerNormalizedBasis r)
    (Equiv.refl _)
  rwa [Pi.basisFun_apply] at h

theorem deningerKummerClass_apply (a : Fin r → ℂ) :
    deningerKummerClass r a = ∑ i, a i • deningerNormalizedBasis r i := by
  conv_lhs => rw [← (Pi.basisFun ℂ (Fin r)).sum_repr a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.basisFun_repr]
  refine congrArg (fun z => a i • z) ?_
  exact Module.Basis.equiv_apply (Pi.basisFun ℂ (Fin r)) i (deningerNormalizedBasis r)
    (Equiv.refl _)

/-- **`(3)`: the archimedean current of a character stage**, the functional on the first cohomology
prescribed by the archimedean place average on a lattice basis. -/
noncomputable def deningerStageCurrent (r : ℕ) (ell : Fin r → ℂ) :
    deningerCohomology r 0 →ₗ[ℂ] ℂ :=
  (deningerNormalizedBasis r).constr ℂ ell

@[simp] theorem deningerStageCurrent_basis (ell : Fin r → ℂ) (i : Fin r) :
    deningerStageCurrent r ell (deningerNormalizedBasis r i) = ell i :=
  Module.Basis.constr_basis _ ℂ ell i

/-- **The defining property of the current**: its value on the class of `d log χ^a / (2πi)` is the
archimedean place average of `a`. -/
theorem deningerStageCurrent_kummer (ell a : Fin r → ℂ) :
    deningerStageCurrent r ell (deningerKummerClass r a) = ∑ i, a i * ell i := by
  rw [deningerKummerClass_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, deningerStageCurrent_basis, smul_eq_mul]

/-- **`(3)`: existence and uniqueness of the archimedean current.**  The Kummer classes exhaust the
first cohomology, so a functional prescribed on them is unique; they are free, so it exists. -/
theorem deningerStageCurrent_exists_unique (r : ℕ) (ell : Fin r → ℂ) :
    ∃! c : deningerCohomology r 0 →ₗ[ℂ] ℂ,
      ∀ a : Fin r → ℂ, c (deningerKummerClass r a) = ∑ i, a i * ell i := by
  refine ⟨deningerStageCurrent r ell, fun a => deningerStageCurrent_kummer ell a, ?_⟩
  intro c hc
  refine (deningerNormalizedBasis r).ext fun i => ?_
  have hsingle := hc (Pi.single i (1 : ℂ))
  rw [deningerKummerClass_single] at hsingle
  rw [hsingle, deningerStageCurrent_basis]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_mul]

end Current

section Naturality

variable {r s : ℕ}

/-- The pullback of the logarithmic differential of a coordinate along a transition is the
combination of the logarithmic differentials given by the exponent matrix. -/
theorem deningerDetForm_one_comp (m : Fin r → Fin s → ℤ) (i : Fin r) :
    (deningerDetForm (fun _ : Fin 1 => i)).compContinuousLinearMap (deningerMatrixCLM m)
      = ∑ j, (m i j : ℂ) • deningerDetForm (fun _ : Fin 1 => j) := by
  ext v
  show deningerDetForm (fun _ : Fin 1 => i) (fun a => deningerMatrixCLM m (v a)) = _
  rw [deningerDetForm_apply, Matrix.det_fin_one]
  show deningerMatrixCLM m (v 0) i = _
  rw [deningerMatrixCLM_apply, ContinuousAlternatingMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (m i j : ℂ) * v 0 j = (m i j : ℂ) • deningerDetForm (fun _ : Fin 1 => j) v
  rw [deningerDetForm_apply, Matrix.det_fin_one, smul_eq_mul]
  rfl

/-- **The transition acts on the normalised basis by the exponent matrix.** -/
theorem deningerCohomologyMap_normalizedBasis (m : Fin r → Fin s → ℤ) (i : Fin r) :
    deningerCohomologyMap m 0 (deningerNormalizedBasis r i)
      = ∑ j, (m i j : ℂ) • deningerNormalizedBasis s j := by
  rw [deningerNormalizedBasis_eq_class, map_smul, deningerCohomologyMap_constantClass,
    deningerDetForm_one_comp, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, deningerNormalizedBasis_eq_class, smul_comm]

/-- **The transition acts on Kummer classes by the exponent matrix**, that is, by the lattice
inclusion itself. -/
theorem deningerCohomologyMap_kummerClass (m : Fin r → Fin s → ℤ) (a : Fin r → ℂ) :
    deningerCohomologyMap m 0 (deningerKummerClass r a)
      = deningerKummerClass s (fun j => ∑ i, a i * (m i j : ℂ)) := by
  rw [deningerKummerClass_apply, map_sum, deningerKummerClass_apply]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
    rw [map_smul, deningerCohomologyMap_normalizedBasis, Finset.smul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

/-- **Transition compatibility of the archimedean current.**  Restricting the current of a larger
stage along a transition is the current of the smaller stage for the restricted place average. -/
theorem deningerStageCurrent_natural (m : Fin r → Fin s → ℤ) (ell : Fin s → ℂ) :
    (deningerStageCurrent s ell).comp (deningerCohomologyMap m 0)
      = deningerStageCurrent r (fun i => ∑ j, (m i j : ℂ) * ell j) := by
  refine (deningerNormalizedBasis r).ext fun i => ?_
  rw [LinearMap.comp_apply, deningerCohomologyMap_normalizedBasis, map_sum,
    deningerStageCurrent_basis]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, deningerStageCurrent_basis, smul_eq_mul]

end Naturality

section SquareZero

variable {r : ℕ}

/-- **The square-zero derived algebra map of a character stage.**  The archimedean current on the
first cohomology extends, by the universal property of the exterior algebra, to a unital algebra map
of the exterior algebra of the cohomology into `ℂ[ε]/(ε²)`. -/
noncomputable def deningerStageLift (r : ℕ) (ell : Fin r → ℂ) :
    ExteriorAlgebra ℂ (deningerCohomology r 0) →ₐ[ℂ] TrivSqZeroExt ℂ ℂ :=
  deningerArchimedeanLift (deningerStageCurrent r ell)

/-- The value of the lift on a Kummer generator is the archimedean place average. -/
theorem deningerStageLift_kummer (ell a : Fin r → ℂ) :
    deningerStageLift r ell (ExteriorAlgebra.ι ℂ (deningerKummerClass r a))
      = TrivSqZeroExt.inr (∑ i, a i * ell i) := by
  rw [deningerStageLift, deningerArchimedeanLift_ι, deningerStageCurrent_kummer]

/-- Products of two Kummer generators are killed by the lift. -/
theorem deningerStageLift_mul_eq_zero (ell : Fin r → ℂ) (x y : deningerCohomology r 0) :
    deningerStageLift r ell (ExteriorAlgebra.ι ℂ x * ExteriorAlgebra.ι ℂ y) = 0 :=
  deningerArchimedeanLift_mul_eq_zero (deningerStageCurrent r ell) x y

end SquareZero

end RHTower
