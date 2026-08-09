import Mathlib

/-!
# A linear map that drops dimension has a nonzero kernel vector

The counting step of every "too many coefficients for too few conditions" argument: a linear map
from a finite-dimensional space into one of strictly smaller dimension kills a nonzero vector.
This is the abstract core of the Siegel dimension count, where the source is the coefficient space
of polynomials of degree at most `m` in `n + 1` variables and the target is the space of Taylor
jets of order below `N` at the centres of a finite polydisc cover.

* **`exists_ne_zero_apply_eq_zero_of_finrank_lt`**;
* **`exists_ne_zero_forall_apply_eq_zero_of_finrank_lt`** — the form used in practice, where the
  conditions are a finite family of linear functionals.
-/

open Module

namespace GaloisForLFunctions.HTGeometry

/-- **Dimension drop forces a kernel vector.** -/
theorem exists_ne_zero_apply_eq_zero_of_finrank_lt
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W] (f : V →ₗ[K] W)
    (h : finrank K W < finrank K V) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  have hrange : finrank K (LinearMap.range f) ≤ finrank K W := Submodule.finrank_le _
  have hsum : finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker f
  have hpos : 0 < finrank K (LinearMap.ker f) := by omega
  have hnt : Nontrivial (LinearMap.ker f) := (finrank_pos_iff).mp hpos
  obtain ⟨w, hw⟩ := exists_ne (0 : LinearMap.ker f)
  refine ⟨(w : V), ?_, w.2⟩
  intro hzero
  exact hw (Subtype.ext hzero)

/-- **Dimension drop against a finite family of conditions.**  If the number of linear conditions
is smaller than the dimension of the coefficient space, some nonzero coefficient vector satisfies
all of them. -/
theorem exists_ne_zero_forall_apply_eq_zero_of_finrank_lt
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} [Fintype ι] (c : ι → (V →ₗ[K] K))
    (h : Fintype.card ι < finrank K V) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, c i v = 0 := by
  set f : V →ₗ[K] (ι → K) := LinearMap.pi c with hf
  have hdim : finrank K (ι → K) = Fintype.card ι := by
    simp
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_apply_eq_zero_of_finrank_lt f (by rw [hdim]; exact h)
  refine ⟨v, hv0, fun i => ?_⟩
  have := congrFun hv i
  simpa [hf, LinearMap.pi_apply] using this

end GaloisForLFunctions.HTGeometry
