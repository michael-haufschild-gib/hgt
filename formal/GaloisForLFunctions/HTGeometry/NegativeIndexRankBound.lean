import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Negative index of a positive form minus a degenerate one

A quadratic functional written as `P - R` with `P` nonnegative can be negative only where `R` is
nonzero.  Consequently any subspace on which `P - R` is negative definite meets the radical of `R`
trivially, and its dimension is bounded by the corank of that radical.

This is the finiteness engine behind an index formula for the Weil functional: on test functions of
bounded exponential type the prime side involves only finitely many prime powers, so it is
degenerate on a subspace of finite corank, and the negative index of the whole functional is bounded
by the number of prime powers that appear.  The bound is structural -- no estimate is involved, only
the observation that a nonnegative form cannot be negative.
-/

namespace HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **A negative subspace avoids the radical.**  If `P` is nonnegative and `P - R` is negative on
every nonzero vector of `W`, then `W` meets any subspace annihilated by `R` only at zero. -/
theorem negativeSubspace_inf_radical_eq_bot
    (P R : V → ℝ) (hP : ∀ v, 0 ≤ P v)
    (K : Submodule ℝ V) (hK : ∀ v ∈ K, R v = 0)
    (W : Submodule ℝ V) (hW : ∀ v ∈ W, v ≠ 0 → P v - R v < 0) :
    W ⊓ K = ⊥ := by
  refine Submodule.eq_bot_iff _ |>.mpr fun v hv => ?_
  by_contra hne
  have hneg := hW v hv.1 hne
  rw [hK v hv.2, sub_zero] at hneg
  exact absurd (hP v) (not_le.mpr hneg)

/-- The same statement in the form used for an index bound: a negative-definite subspace injects
into the quotient by the radical of the degenerate part. -/
theorem negativeSubspace_disjoint_radical
    (P R : V → ℝ) (hP : ∀ v, 0 ≤ P v)
    (K : Submodule ℝ V) (hK : ∀ v ∈ K, R v = 0)
    (W : Submodule ℝ V) (hW : ∀ v ∈ W, v ≠ 0 → P v - R v < 0) :
    Disjoint W K :=
  disjoint_iff.mpr (negativeSubspace_inf_radical_eq_bot P R hP K hK W hW)

/-- **The negative index is bounded by the corank of the radical.**  In finite dimension a
negative-definite subspace of `P - R` has dimension at most the corank of any subspace on which `R`
vanishes: the negative directions all have to fit into the finitely many directions the degenerate
part can see. -/
theorem finrank_negativeSubspace_add_finrank_le
    [FiniteDimensional ℝ V]
    (P R : V → ℝ) (hP : ∀ v, 0 ≤ P v)
    (K : Submodule ℝ V) (hK : ∀ v ∈ K, R v = 0)
    (W : Submodule ℝ V) (hW : ∀ v ∈ W, v ≠ 0 → P v - R v < 0) :
    Module.finrank ℝ W + Module.finrank ℝ K ≤ Module.finrank ℝ V := by
  have hdisj := negativeSubspace_disjoint_radical P R hP K hK W hW
  have hsup : Module.finrank ℝ (W ⊔ K : Submodule ℝ V) ≤ Module.finrank ℝ V :=
    Submodule.finrank_le _
  have hadd : Module.finrank ℝ W + Module.finrank ℝ K
      = Module.finrank ℝ (W ⊔ K : Submodule ℝ V) := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq W K,
      (disjoint_iff.mp hdisj)]
    simp
  rw [hadd]
  exact hsup

end HTGeometry
