import GaloisForLFunctions.RHTower.DeningerExteriorNaturality
import GaloisForLFunctions.HTGeometry.ExteriorPowerDirectLimit

/-!
# The cohomology of a system of stages is the exterior power of the limit

A directed system of character stages is given by exponent matrices satisfying the cocycle
conditions.  The maps induced on cohomology compose accordingly, because under the comparison with
the exterior powers they are the exterior powers of the transposed matrices, and matrix
multiplication is composition.  Transporting the comparison through the direct limit and using that
exterior powers commute with direct limits along injective maps, the direct limit of the cohomologies
of the stages is the exterior power of the direct limit of the covering spaces.

* `deningerCohomologyMap_comp`, `deningerCohomologyMap_id` : the induced maps form a system.
* `deningerCohomologyDirectLimitEquiv` : the colimit of the cohomologies is the exterior power of
  the colimit.
-/

set_option maxSynthPendingDepth 3

namespace RHTower

open Complex GaloisForLFunctions.HTGeometry

section Functoriality

variable {r s t n : ℕ}

/-- The transpose of a product of exponent matrices. -/
theorem deningerMatrixCLM_transpose_comp (m : Fin r → Fin s → ℤ) (l : Fin s → Fin t → ℤ) :
    deningerMatrixCLM (fun c a => (fun i k => ∑ j, m i j * l j k) a c) =
      (deningerMatrixCLM (fun c b => l b c)).comp (deningerMatrixCLM (fun b a => m a b)) := by
  rw [← deningerMatrixCLM_comp]
  congr 1
  funext c a
  show (∑ j, m a j * l j c) = ∑ b, l b c * m a b
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- **The maps induced on cohomology compose according to the product of the exponent matrices.** -/
theorem deningerCohomologyMap_comp (m : Fin r → Fin s → ℤ) (l : Fin s → Fin t → ℤ) (n : ℕ)
    (ξ : deningerCohomology r n) :
    deningerCohomologyMap (fun i k => ∑ j, m i j * l j k) n ξ =
      deningerCohomologyMap l n (deningerCohomologyMap m n ξ) := by
  refine (deningerCohomologyExteriorEquiv t n).injective ?_
  rw [deningerCohomologyExterior_naturality, deningerCohomologyExterior_naturality,
    deningerCohomologyExterior_naturality, deningerMatrixCLM_transpose_comp]
  show exteriorPower.map (n + 1)
      ((deningerMatrixCLM (fun c b => l b c)).comp
        (deningerMatrixCLM (fun b a => m a b))).toLinearMap _ = _
  rw [show ((deningerMatrixCLM (fun c b => l b c)).comp
      (deningerMatrixCLM (fun b a => m a b))).toLinearMap =
      (deningerMatrixCLM (fun c b => l b c)).toLinearMap.comp
        (deningerMatrixCLM (fun b a => m a b)).toLinearMap from rfl,
    exteriorPower.map_comp]
  rfl

/-- **The identity transition induces the identity on cohomology.** -/
theorem deningerCohomologyMap_id (n : ℕ) (ξ : deningerCohomology r n) :
    deningerCohomologyMap (fun i j : Fin r => if i = j then (1 : ℤ) else 0) n ξ = ξ := by
  refine (deningerCohomologyExteriorEquiv r n).injective ?_
  rw [deningerCohomologyExterior_naturality]
  have hmat : (fun j i : Fin r => if i = j then (1 : ℤ) else 0) =
      fun i j : Fin r => if i = j then (1 : ℤ) else 0 := by
    funext i j
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [hmat, deningerMatrixCLM_id]
  show exteriorPower.map (n + 1) (ContinuousLinearMap.id ℂ (Fin r → ℂ)).toLinearMap _ = _
  rw [show (ContinuousLinearMap.id ℂ (Fin r → ℂ)).toLinearMap = LinearMap.id from rfl,
    exteriorPower.map_id]
  rfl

end Functoriality

end RHTower

namespace RHTower

open Complex GaloisForLFunctions.HTGeometry

section Colimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  (rk : ι → ℕ) (M : ∀ i j, i ≤ j → Fin (rk i) → Fin (rk j) → ℤ)

/-- The system of covering spaces attached to a system of exponent matrices. -/
noncomputable def deningerCoveringSystem (i j : ι) (h : i ≤ j) :
    (Fin (rk i) → ℂ) →ₗ[ℂ] (Fin (rk j) → ℂ) :=
  (deningerMatrixCLM (fun b a => M i j h a b)).toLinearMap

/-- The system of cohomologies attached to a system of exponent matrices. -/
noncomputable def deningerCohomologySystem (n : ℕ) (i j : ι) (h : i ≤ j) :
    deningerCohomology (rk i) n →ₗ[ℂ] deningerCohomology (rk j) n :=
  deningerCohomologyMap (M i j h) n

/-- **The colimit of the cohomologies of a directed system of character stages is the exterior
power of the colimit of the covering spaces.**  This is the passage to the limit of the comparison
`Λ^k(L ⊗ ℂ) ≅ H^k`: the comparison is natural in the lattice, and exterior powers commute with
direct limits along injective maps. -/
noncomputable def deningerCohomologyDirectLimitEquiv (n : ℕ)
    [DirectedSystem (fun i => Fin (rk i) → ℂ) fun i j h => deningerCoveringSystem rk M i j h]
    (hinj : ∀ i j h, Function.Injective (deningerCoveringSystem rk M i j h)) :
    Module.DirectLimit (fun i => deningerCohomology (rk i) n)
        (deningerCohomologySystem rk M n) ≃ₗ[ℂ]
      ⋀[ℂ]^(n + 1) (Module.DirectLimit (fun i => Fin (rk i) → ℂ)
        (deningerCoveringSystem rk M)) := by
  have e1 : Module.DirectLimit (fun i => deningerCohomology (rk i) n)
        (deningerCohomologySystem rk M n) ≃ₗ[ℂ]
      Module.DirectLimit (fun i => ⋀[ℂ]^(n + 1) (Fin (rk i) → ℂ))
        (exteriorPowerSystem (fun i => Fin (rk i) → ℂ) (deningerCoveringSystem rk M) (n + 1)) := by
    refine Module.DirectLimit.congr (fun i => deningerCohomologyExteriorEquiv (rk i) n) ?_
    intro i j h
    refine LinearMap.ext fun ξ => ?_
    show deningerCohomologyExteriorEquiv (rk j) n (deningerCohomologyMap (M i j h) n ξ) =
      exteriorPower.map (n + 1) (deningerCoveringSystem rk M i j h)
        (deningerCohomologyExteriorEquiv (rk i) n ξ)
    exact deningerCohomologyExterior_naturality (M i j h) n ξ
  exact e1.trans (exteriorPowerDirectLimitEquiv (fun i => Fin (rk i) → ℂ)
    (deningerCoveringSystem rk M) (n + 1) hinj)

end Colimit

end RHTower
