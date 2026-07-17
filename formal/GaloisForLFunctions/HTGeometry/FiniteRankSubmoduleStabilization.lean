import GaloisForLFunctions.HTGeometry.HolonomicityLimit
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Stabilization of bounded finite-rank submodule chains

Strict compatibility is not a stabilization hypothesis.  The exact elementary linear replacement
is a monotone chain of finite-dimensional submodules whose dimensions have a uniform total bound:
its dimension sequence stabilizes, after which inclusion plus equality of finite rank forces the
submodules themselves to stabilize.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A monotone chain of finite-dimensional submodules with uniformly bounded finite rank is
eventually constant. -/
theorem monotoneSubmodule_eventually_constant_of_finrank_bddAbove
    {F E : Type*} [DivisionRing F] [AddCommGroup E] [Module F E]
    (V : ℕ → Submodule F E) [hfinite : ∀ n, FiniteDimensional F (V n)]
    (hmono : Monotone V)
    (hbdd : ∃ B, ∀ n, Module.finrank F (V n) ≤ B) :
    ∃ N, ∀ n, N ≤ n → V n = V N := by
  have hrankMono : Monotone (fun n => Module.finrank F (V n)) := by
    intro m n hmn
    exact Submodule.finrank_mono (hmono hmn)
  obtain ⟨N, hN⟩ := monotoneNat_eventually_constant_of_bddAbove
    (fun n => Module.finrank F (V n)) hrankMono hbdd
  refine ⟨N, ?_⟩
  intro n hn
  exact (Submodule.eq_of_le_of_finrank_eq (hmono hn) (hN n hn).symm).symm

/-- A monotone chain contained in one finite-dimensional ambient submodule is eventually
constant. -/
theorem monotoneSubmodule_eventually_constant_of_le_finiteDimensional
    {F E : Type*} [DivisionRing F] [AddCommGroup E] [Module F E]
    (V : ℕ → Submodule F E) (W : Submodule F E)
    [FiniteDimensional F W]
    (hmono : Monotone V) (hVW : ∀ n, V n ≤ W) :
    ∃ N, ∀ n, N ≤ n → V n = V N := by
  letI (n : ℕ) : FiniteDimensional F (V n) :=
    FiniteDimensional.of_injective
      (Submodule.inclusion (hVW n)) (Submodule.inclusion_injective (hVW n))
  apply monotoneSubmodule_eventually_constant_of_finrank_bddAbove V hmono
  exact ⟨Module.finrank F W, fun n => Submodule.finrank_mono (hVW n)⟩

end GaloisForLFunctions.HTGeometry
