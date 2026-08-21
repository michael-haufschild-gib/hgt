import GaloisForLFunctions.HTGeometry.BorelWeil.PairBaseCoordinate

/-!
# Local triviality of the `ℙ¹` fibration

Every chart function is the fibre coordinate times a chart function plus a function regular on both
cells of the coset pair.  Since that property is stable under sums and products and holds for the
coordinates, it holds throughout the chart ring — which is exactly local triviality of the
fibration `G/B → G/P_i` over the base cell.

## Main results

* `exists_fibre_decomposition` — the decomposition, for a chart function.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- The chart functions admitting a fibre decomposition. -/
def HasFibreDecomposition {i : Fin N} (hi : (i : ℕ) + 1 < N) (x : FlagLoc N k) : Prop :=
  ∃ a : FlagLoc N k, a ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))} ∧
    ∃ b : FlagLoc N k, b ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))} ∧
      b ∈ cellSubalg N k {swapNext i hi} ∧
      x = cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i * a + b

theorem hasFibreDecomposition_add {i : Fin N} (hi : (i : ℕ) + 1 < N) {x y : FlagLoc N k}
    (hx : HasFibreDecomposition (k := k) hi x) (hy : HasFibreDecomposition (k := k) hi y) :
    HasFibreDecomposition (k := k) hi (x + y) := by
  obtain ⟨a₁, ha₁, b₁, hb₁, hb₁', hx⟩ := hx
  obtain ⟨a₂, ha₂, b₂, hb₂, hb₂', hy⟩ := hy
  refine ⟨a₁ + a₂, Subalgebra.add_mem _ ha₁ ha₂, b₁ + b₂, Subalgebra.add_mem _ hb₁ hb₂,
    Subalgebra.add_mem _ hb₁' hb₂', ?_⟩
  rw [hx, hy]
  ring

theorem hasFibreDecomposition_mul {i : Fin N} (hi : (i : ℕ) + 1 < N) {x y : FlagLoc N k}
    (hx : HasFibreDecomposition (k := k) hi x) (hy : HasFibreDecomposition (k := k) hi y) :
    HasFibreDecomposition (k := k) hi (x * y) := by
  obtain ⟨a₁, ha₁, b₁, hb₁, hb₁', hx⟩ := hx
  obtain ⟨a₂, ha₂, b₂, hb₂, hb₂', hy⟩ := hy
  have hT : cellCoord (k := k) (⟨(i : ℕ) + 1, hi⟩ : Fin N) i
      ∈ cellSubalg N k {(1 : Equiv.Perm (Fin N))} := cellCoord_mem_cellSections _ _
  refine ⟨cellCoord (⟨(i : ℕ) + 1, hi⟩ : Fin N) i * a₁ * a₂ + a₁ * b₂ + b₁ * a₂, ?_,
    b₁ * b₂, Subalgebra.mul_mem _ hb₁ hb₂, Subalgebra.mul_mem _ hb₁' hb₂', ?_⟩
  · exact Subalgebra.add_mem _ (Subalgebra.add_mem _
      (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hT ha₁) ha₂)
      (Subalgebra.mul_mem _ ha₁ hb₂)) (Subalgebra.mul_mem _ hb₁ ha₂)
  · rw [hx, hy]
    ring

theorem hasFibreDecomposition_algebraMap {i : Fin N} (hi : (i : ℕ) + 1 < N) (r : k) :
    HasFibreDecomposition (k := k) hi (algebraMap k (FlagLoc N k) r) := by
  refine ⟨0, Subalgebra.zero_mem _, algebraMap k (FlagLoc N k) r, Subalgebra.algebraMap_mem _ r,
    Subalgebra.algebraMap_mem _ r, ?_⟩
  rw [mul_zero, zero_add]

theorem hasFibreDecomposition_cellCoord {i : Fin N} (hi : (i : ℕ) + 1 < N) (r j : Fin N) :
    HasFibreDecomposition (k := k) hi (cellCoord r j) := by
  obtain ⟨y, hy1, hys, w, hw, heq⟩ := cellCoord_eq_fibre_mul_add (k := k) hi r j
  exact ⟨w, hw, y, hy1, hys, heq⟩

theorem hasFibreDecomposition_cellCoordAlg {i : Fin N} (hi : (i : ℕ) + 1 < N)
    (p : MvPolynomial (Fin N × Fin N) k) :
    HasFibreDecomposition (k := k) hi (cellCoordAlg p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [cellCoordAlg, MvPolynomial.aeval_C]
      exact hasFibreDecomposition_algebraMap hi r
  | add q r hq hr =>
      rw [map_add]
      exact hasFibreDecomposition_add hi hq hr
  | mul_X q ij hq =>
      rw [map_mul, cellCoordAlg, MvPolynomial.aeval_X]
      exact hasFibreDecomposition_mul hi hq (hasFibreDecomposition_cellCoord hi ij.1 ij.2)

/-- **Local triviality.**  Every function regular on the big cell is the fibre coordinate times
such a function, plus a function regular on both cells of the coset pair. -/
theorem exists_fibre_decomposition {i : Fin N} (hi : (i : ℕ) + 1 < N) {x : FlagLoc N k}
    (hx : x ∈ cellSections N k {(1 : Equiv.Perm (Fin N))} (fun _ => 0)) :
    HasFibreDecomposition (k := k) hi x := by
  obtain ⟨p, hp⟩ := exists_cellCoordAlg_eq hx
  rw [hp]
  exact hasFibreDecomposition_cellCoordAlg hi p

end GaloisForLFunctions.HTGeometry.BorelWeil
