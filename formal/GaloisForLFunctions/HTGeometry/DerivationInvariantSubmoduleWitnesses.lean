import GaloisForLFunctions.HTGeometry.FiniteLinearStateDifferentialEscape

/-!
# Realizations of the derivation-invariant state interface

The trivial and full submodules are derivation invariant, and invariance is stable under
intersections, sums and arbitrary infima, so the interface is a complete sublattice of the submodule
lattice rather than an unrealized side condition.

Taking the full submodule removes the interface from the linear escape law: over a finite-dimensional
differential field extension every element is differentially algebraic, hence no element is
hypertranscendental.
-/

open scoped Differential
open Module

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-! ## Realizations -/

theorem derivationInvariantSubmodule_bot :
    DerivationInvariantSubmodule (⊥ : Submodule F E) := by
  intro x hx
  rw [Submodule.mem_bot] at hx
  subst hx
  simp

theorem derivationInvariantSubmodule_top :
    DerivationInvariantSubmodule (⊤ : Submodule F E) := fun _ _ => Submodule.mem_top

theorem DerivationInvariantSubmodule.inf {V W : Submodule F E}
    (hV : DerivationInvariantSubmodule V) (hW : DerivationInvariantSubmodule W) :
    DerivationInvariantSubmodule (V ⊓ W) := by
  intro x hx
  exact ⟨hV hx.1, hW hx.2⟩

theorem DerivationInvariantSubmodule.sup {V W : Submodule F E}
    (hV : DerivationInvariantSubmodule V) (hW : DerivationInvariantSubmodule W) :
    DerivationInvariantSubmodule (V ⊔ W) := by
  intro x hx
  rw [Submodule.mem_sup] at hx
  obtain ⟨v, hv, w, hw, rfl⟩ := hx
  rw [Submodule.mem_sup]
  refine ⟨v′, hV hv, w′, hW hw, ?_⟩
  simp

theorem DerivationInvariantSubmodule.iInf {ι : Type*} {V : ι → Submodule F E}
    (hV : ∀ i, DerivationInvariantSubmodule (V i)) :
    DerivationInvariantSubmodule (⨅ i, V i) := by
  intro x hx
  rw [Submodule.mem_iInf] at hx ⊢
  exact fun i => hV i (hx i)

/-! ## The interface disappears in finite dimension -/

/-- **Finite-dimensional differential algebraicity.**  Over a finite-dimensional extension every
element satisfies a nonzero scalar linear differential relation. -/
theorem differentialAlgebraicOver_of_finiteDimensional [FiniteDimensional F E] (x : E) :
    DifferentialAlgebraicOver F x :=
  differentialAlgebraicOver_of_mem_derivationInvariantSubmodule
    (⊤ : Submodule F E) Submodule.mem_top derivationInvariantSubmodule_top

/-- **No hypertranscendence in finite dimension.**  A finite-dimensional differential extension
contains no element hypertranscendental over the coefficient field. -/
theorem not_hypertranscendentalOver_of_finiteDimensional [FiniteDimensional F E] (x : E) :
    ¬ HypertranscendentalOver F x := fun hx =>
  not_mem_derivationInvariantSubmodule_of_hypertranscendentalOver
    (⊤ : Submodule F E) hx derivationInvariantSubmodule_top Submodule.mem_top

end

end GaloisForLFunctions.HTGeometry
