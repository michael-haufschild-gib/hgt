import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.DisjointBoxes

/-! # A positive density of calibrated triples with bounded neighboring rows -/
open Filter MeasureTheory Finset Set Real
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

private def guardedCoordinate (p : ℕ × (Fin 3 × TripleBoxIndex)) :=
  blockCoordinate (3*p.1+p.2.1.val,p.2.2)

private theorem guardedCoordinate_injective : Function.Injective guardedCoordinate := by
  rintro ⟨k,a,i⟩ ⟨k',b,j⟩ h
  obtain ⟨hl,hij⟩ := Prod.mk.inj (blockCoordinate_injective h)
  have ha := a.isLt
  have hb := b.isLt
  exact Prod.ext (by omega) (Prod.ext (Fin.ext (by omega)) hij)

open scoped Classical in
/-- Three successive four-row boxes. The middle one carries the
reporter, and the two adjacent boxes control its local error. -/
def guardedBoxes (δ : ℝ) (ω : PathPauliDisorder) (m : ℕ) :=
  (range m).filter fun k => ∀ a : Fin 3, goodBox (1/sqrt 2) δ ω (3*k+a.val)

theorem gaussian_guarded_box_density {δ : ℝ} (hδ : 0<δ) :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop,
      c*m≤((guardedBoxes δ ω m).card:ℝ) := by
  classical
  let lo (p : Fin 3 × TripleBoxIndex) := boxField (1/sqrt 2) p.2-δ
  let hi (p : Fin 3 × TripleBoxIndex) := boxField (1/sqrt 2) p.2+δ
  obtain ⟨hp,h⟩ := gaussian_disjoint_box_half_mass guardedCoordinate guardedCoordinate_injective lo hi
    (fun i => by dsimp only [lo,hi]; linarith only [hδ])
  refine ⟨_,hp,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with m hm
  have he : guardedBoxes δ ω m=(range m).filter
      (fun k => ∀ j, ω (guardedCoordinate (k,j))∈Icc (lo j) (hi j)) := by
    ext k
    simp only [guardedBoxes,mem_filter]
    apply and_congr_right
    intro _
    exact ⟨fun h p => h p.1 p.2,fun h i j => h (i,j)⟩
  rwa [he]

#print axioms gaussian_guarded_box_density
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
