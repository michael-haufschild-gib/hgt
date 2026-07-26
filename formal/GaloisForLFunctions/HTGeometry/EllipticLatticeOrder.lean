import GaloisForLFunctions.HTGeometry.EllipticRegularPoint

/-!
# Orders are lattice invariants

For a function periodic under two steps, the meromorphic order is constant along the lattice they
generate.  Combined with the covering of `ℂ` by translates of the fundamental parallelogram, every
point has a congruent point *inside the parallelogram* with the same order — so the poles of a
lattice-periodic function are exactly the lattice translates of the finitely many poles in the
parallelogram.

* **`meromorphicOrderAt_sub_latticeCombination`** — the order is invariant under the lattice;
* **`exists_mem_parallelogram_orderEq`** — a congruent point in the parallelogram;
* **`exists_mem_poleFinset_orderEq`** — for a pole, that point lies in the finite pole set.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The meromorphic order is a lattice invariant.** -/
theorem meromorphicOrderAt_sub_latticeCombination {g : ℂ → ℂ} {w₁ w₂ : ℂ}
    (h₁ : Function.Periodic g w₁) (h₂ : Function.Periodic g w₂) (m n : ℤ) (z : ℂ) :
    meromorphicOrderAt g (z - (m • w₁ + n • w₂)) = meromorphicOrderAt g z := by
  have hm : Function.Periodic g ((m : ℂ) * w₁) := h₁.int_mul m
  have hn : Function.Periodic g ((n : ℂ) * w₂) := h₂.int_mul n
  have hper : Function.Periodic g (m • w₁ + n • w₂) := by
    have hsm : m • w₁ + n • w₂ = (m : ℂ) * w₁ + (n : ℂ) * w₂ := by
      simp [zsmul_eq_mul]
    rw [hsm]
    exact hm.add_period hn
  have hshift := meromorphicOrderAt_add_period g (m • w₁ + n • w₂)
    (z - (m • w₁ + n • w₂)) hper
  rw [sub_add_cancel] at hshift
  exact hshift.symm

/-- **Every point has a congruent point in the fundamental parallelogram with the same order.** -/
theorem exists_mem_parallelogram_orderEq {g : ℂ → ℂ} {w₁ w₂ : ℂ}
    (hindep : LinearIndependent ℝ ![w₁, w₂])
    (h₁ : Function.Periodic g w₁) (h₂ : Function.Periodic g w₂) (z : ℂ) :
    ∃ p ∈ fundamentalParallelogram w₁ w₂, meromorphicOrderAt g p = meromorphicOrderAt g z := by
  obtain ⟨_, _, hcov⟩ := exists_bounded_intCombination hindep
  obtain ⟨m, n, hmem, _, _⟩ := hcov z
  exact ⟨z - (m • w₁ + n • w₂), hmem, meromorphicOrderAt_sub_latticeCombination h₁ h₂ m n z⟩

/-- **A pole of a lattice-periodic function is congruent to one of the finitely many poles in the
parallelogram.** -/
theorem exists_mem_poleFinset_orderEq {f : ℂ → ℂ} (hmer : MeromorphicOn f Set.univ) {w₁ w₂ : ℂ}
    (hindep : LinearIndependent ℝ ![w₁, w₂])
    (h₁ : Function.Periodic f w₁) (h₂ : Function.Periodic f w₂) {z : ℂ}
    (hz : meromorphicOrderAt f z < 0) :
    ∃ p ∈ (finite_poles_fundamentalParallelogram hmer w₁ w₂).toFinset,
      meromorphicOrderAt f p = meromorphicOrderAt f z := by
  obtain ⟨p, hp, hord⟩ := exists_mem_parallelogram_orderEq hindep h₁ h₂ z
  refine ⟨p, ?_, hord⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨hp, by rw [hord]; exact hz⟩

end GaloisForLFunctions.HTGeometry
