import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreChartError
import GaloisForLFunctions.HTGeometry.CellMaxSetDiscretisation

/-!
# Exact finite chart-grid tiling

The product grid covers its half-open coordinate rectangle exactly.  At the
special core parameters `a = -1/2`, `hx = 1/M`, `hy = 1/M`, this gives the
interior fundamental-domain partition needed to splice the finite core to the
cuspidal tail.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A finite product grid covers exactly its half-open coordinate rectangle. -/
theorem upperChartGridCore_eq_coordinateRect {M K : ℕ} (a c hx hy : ℝ)
    (hhx : 0 ≤ hx) (hhy : 0 ≤ hy) :
    upperChartGridCore (M := M) (K := K) a c hx hy =
      {z : ℍ | z.re ∈ Set.Ioc a (a + (M : ℝ) * hx) ∧
        z.im ∈ Set.Ioc c (c + (K : ℝ) * hy)} := by
  ext z
  change (z ∈ ⋃ i : Fin K × Fin M, upperChartGridCell a c hx hy i) ↔
    (z.re ∈ Set.Ioc a (a + (M : ℝ) * hx) ∧
      z.im ∈ Set.Ioc c (c + (K : ℝ) * hy))
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
    change z.re ∈ Set.Ioc (a + (i.2 : ℝ) * hx)
      (a + ((i.2 : ℕ) + 1 : ℝ) * hx) ∧
      z.im ∈ Set.Ioc (c + (i.1 : ℝ) * hy)
        (c + ((i.1 : ℕ) + 1 : ℝ) * hy) at hzi
    constructor
    · constructor
      · have hi0 : 0 ≤ (i.2 : ℝ) := Nat.cast_nonneg _
        have hstart : a ≤ a + (i.2 : ℝ) * hx := by
          nlinarith [mul_nonneg hi0 hhx]
        exact hstart.trans_lt hzi.1.1
      · have hi : ((i.2 : ℕ) + 1 : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast Nat.succ_le_iff.mpr i.2.isLt
        have hmul := mul_le_mul_of_nonneg_right hi hhx
        have hend : a + ((i.2 : ℕ) + 1 : ℝ) * hx ≤ a + (M : ℝ) * hx := by
          linarith
        exact hzi.1.2.trans hend
    · constructor
      · have hi0 : 0 ≤ (i.1 : ℝ) := Nat.cast_nonneg _
        have hstart : c ≤ c + (i.1 : ℝ) * hy := by
          nlinarith [mul_nonneg hi0 hhy]
        exact hstart.trans_lt hzi.2.1
      · have hi : ((i.1 : ℕ) + 1 : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast Nat.succ_le_iff.mpr i.1.isLt
        have hmul := mul_le_mul_of_nonneg_right hi hhy
        have hend : c + ((i.1 : ℕ) + 1 : ℝ) * hy ≤ c + (K : ℝ) * hy := by
          linarith
        exact hzi.2.2.trans hend
  · rintro ⟨hxz, hyz⟩
    have hxcover : z.re ∈ ⋃ k ∈ Finset.range M,
        Set.Ioc (a + (k : ℝ) * hx) (a + ((k : ℝ) + 1) * hx) := by
      rw [GaloisForLFunctions.HTGeometry.iUnion_Ioc_cells a hx hhx M]
      exact hxz
    have hycover : z.im ∈ ⋃ k ∈ Finset.range K,
        Set.Ioc (c + (k : ℝ) * hy) (c + ((k : ℝ) + 1) * hy) := by
      rw [GaloisForLFunctions.HTGeometry.iUnion_Ioc_cells c hy hhy K]
      exact hyz
    simp only [Set.mem_iUnion, Finset.mem_range] at hxcover hycover
    obtain ⟨m, hm, hxm⟩ := hxcover
    obtain ⟨k, hk, hyk⟩ := hycover
    apply Set.mem_iUnion.mpr
    refine ⟨(⟨k, hk⟩, ⟨m, hm⟩), ?_⟩
    change z.re ∈ Set.Ioc (a + (m : ℝ) * hx)
      (a + ((m : ℕ) + 1 : ℝ) * hx) ∧
      z.im ∈ Set.Ioc (c + (k : ℝ) * hy)
        (c + ((k : ℕ) + 1 : ℝ) * hy)
    exact ⟨by simpa using hxm, by simpa using hyk⟩

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
