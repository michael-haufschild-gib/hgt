/-
# Room beside a greedy truncation

The greedy truncation at order `n` reads its argument only through the first `n` greedy vectors and
writes only into their images, so it is carried by one finite-dimensional subspace.  A vector in the
orthogonal complement of that subspace is therefore killed by the truncation and is orthogonal to
its whole range.  In an infinite-dimensional space this leaves an orthonormal family of any size
beside the truncation -- the room the vanishing micro-spectrum block needs.

Main results:
* `greedySupport` — the finite-dimensional subspace carrying the greedy truncation.
* `greedyTrunc_apply_eq_zero_of_mem_orthogonal`, `inner_greedyTrunc_eq_zero_of_mem_orthogonal` —
  the complement is annihilated on both sides.
* `exists_orthonormal_beside_greedyTrunc` — **an orthonormal family of any size beside the
  truncation**.
-/
import GaloisForLFunctions.HTGeometry.OrthonormalComplementFamily
import GaloisForLFunctions.RHTower.SchattenTwoIdentity

open ContinuousLinearMap
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem greedyTrunc_apply (T : H →L[ℂ] H) (n : ℕ) (x : H) :
    greedyTrunc T n x
      = ∑ k ∈ Finset.range n, ⟪svVec (energyOp T) k, x⟫_ℂ • T (svVec (energyOp T) k) := by
  rw [greedyTrunc, sum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [smulRight_apply, innerSL_apply_apply]

/-- The finite-dimensional subspace carrying the greedy truncation at order `n`: the span of the
first `n` greedy vectors together with their images. -/
def greedySupport (T : H →L[ℂ] H) (n : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ
    (((fun k => svVec (energyOp T) k) '' ((Finset.range n : Finset ℕ) : Set ℕ)) ∪
      ((fun k => T (svVec (energyOp T) k)) '' ((Finset.range n : Finset ℕ) : Set ℕ)))

instance finiteDimensional_greedySupport (T : H →L[ℂ] H) (n : ℕ) :
    FiniteDimensional ℂ (greedySupport T n) :=
  FiniteDimensional.span_of_finite ℂ
    (((Finset.range n).finite_toSet.image _).union ((Finset.range n).finite_toSet.image _))

theorem svVec_mem_greedySupport (T : H →L[ℂ] H) {n k : ℕ} (hk : k < n) :
    svVec (energyOp T) k ∈ greedySupport T n :=
  Submodule.subset_span (Or.inl ⟨k, by simpa using hk, rfl⟩)

theorem apply_svVec_mem_greedySupport (T : H →L[ℂ] H) {n k : ℕ} (hk : k < n) :
    T (svVec (energyOp T) k) ∈ greedySupport T n :=
  Submodule.subset_span (Or.inr ⟨k, by simpa using hk, rfl⟩)

theorem greedyTrunc_apply_mem_greedySupport (T : H →L[ℂ] H) (n : ℕ) (x : H) :
    greedyTrunc T n x ∈ greedySupport T n := by
  rw [greedyTrunc_apply]
  exact Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (apply_svVec_mem_greedySupport T (Finset.mem_range.mp hk))

/-- The orthogonal complement of the carrier is killed by the truncation. -/
theorem greedyTrunc_apply_eq_zero_of_mem_orthogonal (T : H →L[ℂ] H) (n : ℕ) {y : H}
    (hy : y ∈ (greedySupport T n)ᗮ) : greedyTrunc T n y = 0 := by
  rw [greedyTrunc_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hzero : ⟪svVec (energyOp T) k, y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hy _ (svVec_mem_greedySupport T (Finset.mem_range.mp hk))
  rw [hzero, zero_smul]

/-- The orthogonal complement of the carrier is orthogonal to the range of the truncation. -/
theorem inner_greedyTrunc_eq_zero_of_mem_orthogonal (T : H →L[ℂ] H) (n : ℕ) {y : H}
    (hy : y ∈ (greedySupport T n)ᗮ) (x : H) : ⟪y, greedyTrunc T n x⟫_ℂ = 0 :=
  (Submodule.mem_orthogonal' _ _).mp hy _ (greedyTrunc_apply_mem_greedySupport T n x)

/-- **An orthonormal family of any size beside the greedy truncation.** -/
theorem exists_orthonormal_beside_greedyTrunc (hH : ¬ FiniteDimensional ℂ H) (T : H →L[ℂ] H)
    (n mm : ℕ) :
    ∃ e : Fin mm → H, Orthonormal ℂ e ∧ (∀ i, greedyTrunc T n (e i) = 0) ∧
      (∀ i x, ⟪e i, greedyTrunc T n x⟫_ℂ = 0) := by
  obtain ⟨e, he, hmem⟩ :=
    exists_orthonormal_mem_orthogonal hH mm (greedySupport T n)
      (finiteDimensional_greedySupport T n)
  exact ⟨e, he, fun i => greedyTrunc_apply_eq_zero_of_mem_orthogonal T n (hmem i),
    fun i x => inner_greedyTrunc_eq_zero_of_mem_orthogonal T n (hmem i) x⟩

end

end GaloisForLFunctions.HTGeometry
