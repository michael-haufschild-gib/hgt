import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.PathGaps
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.IntervalPacking
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw
import GaloisForLFunctions.HTGeometry.Quantum.SparsePathCircuitCompiler

/-! # Thickening every inward entry by one physical product step -/
open Matrix MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section
open SharpOccupation EmptyVisitFlux

/-- Each entry at physical error δ supplies a disjoint interval of length
h at error δ+M²h², provided that width fits in the entry separation. -/
theorem path_entry_intervals {n : ℕ} (u : PathShell n) {δ h : ℝ}
    (hδ : 0<δ) (hs : δ<sqrt 2) (hh : 0≤h) (T : ℝ) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let E := fun j => -H.2.isHermitian.eigenvalues j
    let M := ∑ l : PathLabel n, |u l|
    let J := Fintype.card (PathLabel n)
    let x := physicalArc δ
    h*(M/π) ≤ 1-2*x →
      ((entryDates E x T).card:ℝ)*h ≤ volume.real (visitSet H J (δ+M^2*h^2) ∩ Icc 0 (T+h)) := by
  intro H E M J x hsep
  let w := fun i => E i/(2*π)
  let F := entryDates E x T
  have hx := (physicalArc_spec hδ hs).1
  have hmark (t) (ht : t∈F) := (mem_entryDates E hx.1.le hx.2 t T).mp ht
  apply interval_packing H J F hh
  · intro t ht
    obtain ⟨h0,hT,he⟩ := hmark t ht
    exact ⟨⟨h0.le,hT⟩,(physical_visit H hδ hs t).mp he.1⟩
  · intro t ht v hv htv
    have hg := entries_separated w hx.1.le hx.2 htv (hmark t ht).2.2 (hmark v hv).2.2
    have hw := path_velocity_width u
    have hle := hg.trans (mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr htv.le))
    have hp : 0 < M/π := by
      by_contra! hn
      have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htv.le) hn
      linarith only [hle,h,hx.2]
    have hlag := le_of_mul_le_mul_right (hsep.trans hle) hp
    linarith only [hlag]
  · intro v hv
    obtain ⟨z,hz,C,hC,he⟩ := exists_sparse_path_circuit u v 1 (by decide)
    simp only [one_mul,Nat.cast_one,div_one,abs_of_nonneg hv.1] at hC he
    exact ⟨z,hz,C,hC.le,he.trans (mul_le_mul_of_nonneg_left
      (sq_le_sq' (by linarith only [hv.1,hh]) hv.2) (sq_nonneg _))⟩

#print axioms path_entry_intervals
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
