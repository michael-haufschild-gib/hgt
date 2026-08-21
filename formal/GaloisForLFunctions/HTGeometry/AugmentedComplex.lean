import GaloisForLFunctions.HTGeometry.HomologyZeroExplicit
import GaloisForLFunctions.HTGeometry.PairSequence

/-!
# The augmented singular chain complex

Appending the coefficient ring below degree zero, with the augmentation as the new differential,
gives the augmented complex whose homology is the reduced homology: in degrees at least two it
agrees with the ordinary homology one degree lower, and in degree one it is the chains of total
coefficient zero modulo the boundaries, which vanishes exactly when the space is path-connected.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] (X : Type v) [TopologicalSpace X]

/-- The objects of the augmented complex: the ring in degree zero, the chains above. -/
noncomputable def augObj : ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R (ULift.{v} R)
  | (n + 1) => ModuleCat.of R (C(topSimplex n, X) →₀ R)

/-- The differentials of the augmented complex. -/
noncomputable def augD : ∀ n, augObj R X (n + 1) ⟶ augObj R X n
  | 0 => ModuleCat.ofHom
      ((ULift.moduleEquiv (R := R) (M := R)).symm.toLinearMap ∘ₗ singAug R (X := X))
  | (n + 1) => ModuleCat.ofHom (singBd R X n)

/-- The augmented singular chain complex. -/
noncomputable def augChain : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (augObj R X) (augD R X) (by
    intro n
    cases n with
    | zero =>
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      show (ULift.moduleEquiv (R := R) (M := R)).symm (singAug R (singBd R X 0 c)) = 0
      rw [singAug_singBd, map_zero]
    | succ n =>
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      exact singBd_singBd R X c)

theorem augChain_d (n : ℕ) : (augChain R X).d (n + 1) n = augD R X n :=
  ChainComplex.of_d (augObj R X) (augD R X) n

theorem augChain_d_succ (n : ℕ) :
    (augChain R X).d (n + 2) (n + 1) = ModuleCat.ofHom (singBd R X n) :=
  augChain_d R X (n + 1)

/-- The chains supported in a subspace, as a subcomplex of the augmented complex. -/
noncomputable def augSub (S : Set X) : ModuleSubcomplex R (augChain R X) where
  carrier
    | 0 => ⊤
    | (n + 1) => subChains R S n
  bd_mem := by
    intro k x hx
    cases k with
    | zero => exact Submodule.mem_top
    | succ n =>
      rw [augChain_d_succ]
      exact singBd_mem_subChains R hx

end GaloisForLFunctions.HTGeometry
