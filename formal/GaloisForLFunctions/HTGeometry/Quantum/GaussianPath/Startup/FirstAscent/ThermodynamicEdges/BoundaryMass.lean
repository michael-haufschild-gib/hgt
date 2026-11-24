import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.IntervalLabels
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.BlockLaw

/-! # Mass of omitted bonds and the last incomplete block -/

open Finset
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
open SpectralGapMass.Bulk.PeriodicCuts
noncomputable section
variable {n : ℕ}

def seamMass (m : ℕ) (u : RowBlock (m+2)→ℝ) := ∑ p : Fin 3 × Fin 3, |u (Fin.last (m+1),.inr p)|

def rowMass (L : ℕ) (u : RowBlock L→ℝ) := ∑ p, |u p|

private theorem source_inj : Function.Injective (pathPauliSourceCoordinate (n:=n)) := by
  rintro (⟨i,a⟩|⟨i,a⟩) (⟨j,b⟩|⟨j,b⟩) h <;>
    simp [pathPauliSourceCoordinate,Fin.ext_iff] at h ⊢ <;> exact h

private theorem mass_cover {β : Type*} [Fintype β] (ω : PathPauliDisorder) (s : Finset (PathLabel n))
    (g : β→ℕ × PathPauliDirections) (hg : Function.Injective g)
    (hc : ∀ l ∈ s, ∃ j, g j=pathPauliSourceCoordinate l) :
    ∑ l ∈ s, |pathPauliDisorderShell ω n l| ≤ ∑ j, |ω (g j)| := by
  classical
  simp only [pathPauliDisorderShell_apply_source]
  rw [←sum_image (f:=fun c => |ω c|) (source_inj (n:=n)).injOn,←sum_image (f:=fun c => |ω c|) hg.injOn]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
  intro c h
  obtain ⟨l,hl,rfl⟩ := mem_image.mp h
  obtain ⟨j,hj⟩ := hc l hl
  exact mem_image.mpr ⟨j,mem_univ _,hj⟩

/-- Each seam is the final outgoing bond of a different full block. -/
theorem seam_bound (m : ℕ) (ω : PathPauliDisorder) :
    ∑ l ∈ labels (n:=n) (m+2) none, |pathPauliDisorderShell ω n l| ≤
      ∑ j ∈ range ((n+2)/(m+2)), seamMass m (readRows (m+2) ω j) := by
  let L := m+2
  let q := (n+2)/L
  let g (j : Fin q × (Fin 3 × Fin 3)) : ℕ × PathPauliDirections := (j.1.val*L+(m+1),.inr j.2)
  have hL : 0<L := by dsimp [L]; omega
  have hg : Function.Injective g := by
    rintro ⟨i,p⟩ ⟨j,s⟩ h
    obtain ⟨hi,hp⟩ := Prod.mk.inj h
    apply Prod.ext _ (Sum.inr.inj hp)
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hL (Nat.add_right_cancel hi))
  have h := mass_cover ω (labels (n:=n) L none) g hg (by
    intro l hl
    have ho := (mem_filter.mp hl).2
    rcases l with ⟨i,a⟩|⟨e,p⟩
    · change owner L (.inl (i,a))=none at ho
      simp [owner] at ho
      exact (ho rfl).elim
    · let k := e.val/L
      let b : Fin (n+2) := ⟨k,(Nat.div_le_self ..).trans_lt e.castSucc.isLt⟩
      have hd : k*L≤e.val ∧ e.val≤k*L+L-1 := (Nat.div_eq_iff hL).mp rfl
      have hb : ¬(k*L≤e.val ∧ e.val+1<k*L+L) := by
        intro hc
        have hh := (owner_iff_interval hL b (.inr (e,p))).2 hc
        rw [ho] at hh
        contradiction
      have hedge : e.val+1=k*L+L := by omega
      have hk : k<q := by
        apply (Nat.le_div_iff_mul_le hL).2
        rw [Nat.succ_mul,←hedge]
        exact e.succ.isLt.le
      refine ⟨(⟨k,hk⟩,p),Prod.ext ?_ rfl⟩
      change k*L+(m+1)=e.val
      dsimp [L] at hedge ⊢
      omega)
  apply h.trans_eq
  rw [Fintype.sum_prod_type]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => seamMass m (readRows L ω j)) q

/-- All terms in the final block fit in a single row block, including a partial bond row. -/
theorem last_block_mass (m : ℕ) (ω : PathPauliDisorder) (b : Fin (n+2)) :
    ∑ l ∈ labels (m+2) (some b), |pathPauliDisorderShell ω n l| ≤
      rowMass (m+2) (readRows (m+2) ω b.val) := by
  let L := m+2
  let g (j : RowBlock L) : ℕ × PathPauliDirections := (b.val*L+j.1.val,j.2)
  apply mass_cover ω _ g
  · rintro ⟨i,p⟩ ⟨j,s⟩ h
    obtain ⟨hi,hp⟩ := Prod.mk.inj h
    exact Prod.ext (Fin.ext (Nat.add_left_cancel hi)) hp
  · intro l hl
    obtain ⟨h₁,h₂⟩ := (owner_iff_interval (by dsimp [L]; omega : 0<L) b l).mp (mem_filter.mp hl).2
    have he : (pathPauliSourceCoordinate l).1≤lastRow l := by cases l <;> simp [pathPauliSourceCoordinate,lastRow]
    refine ⟨(⟨(pathPauliSourceCoordinate l).1-b.val*L,by omega⟩,(pathPauliSourceCoordinate l).2),?_⟩
    exact Prod.ext (by change b.val*L+(_-b.val*L)=_; omega) rfl

#print axioms seam_bound
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
