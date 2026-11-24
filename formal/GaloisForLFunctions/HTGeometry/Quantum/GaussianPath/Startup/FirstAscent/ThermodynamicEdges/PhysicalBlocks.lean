import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Intervals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.BoundaryMass

/-! # An extensive block approximation to the physical energy width -/

open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
open SpectralGapMass.Bulk.PeriodicCuts
noncomputable section
variable {n : ℕ}

def physicalWidth (ω : PathPauliDisorder) (n : ℕ) :=
  circuitHamiltonianSpectralWidth (shellOperator (pathPauliDisorderShell ω n))

private theorem piece_le (m : ℕ) (ω : PathPauliDisorder) (b : Fin (n+2)) :
    circuitHamiltonianSpectralWidth (shellOperator (piece (m+2) (pathPauliDisorderShell ω n) b)) ≤
    2*∑ l ∈ labels (m+2) (some b), |pathPauliDisorderShell ω n l| := by
  have h := width_le_mass n (fun l => piece (m+2) (pathPauliDisorderShell ω n) b l)
  apply h.trans_eq
  congr 1
  rw [labels,sum_filter]
  apply sum_congr rfl
  intro l _
  by_cases ho : owner (m+2) l=some b <;> simp [piece,ho]

private theorem empty_piece {m : ℕ} (ω : PathPauliDisorder) (b : Fin (n+2))
    (hb : (n+2)/(m+2)<b.val) :
    circuitHamiltonianSpectralWidth (shellOperator (piece (m+2) (pathPauliDisorderShell ω n) b))=0 := by
  have hs : labels (m+2) (some b)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro l hl
    have h := ((owner_iff_interval (by omega) b l).mp (mem_filter.mp hl).2).1
    have ht : (pathPauliSourceCoordinate l).1<n+2 := by
      rcases l with ⟨i,a⟩|⟨e,p⟩
      · exact i.isLt
      · exact e.castSucc.isLt
    exact hb.not_ge ((Nat.le_div_iff_mul_le (by omega)).2 (h.trans ht.le))
  have h := piece_le m ω b
  rw [hs,sum_empty,mul_zero] at h
  exact le_antisymm h (circuitHamiltonianSpectralWidth_nonneg _)

/-- All complete physical pieces have the ordinary row-block widths. -/
theorem full_width_sum (ω : PathPauliDisorder) (n m : ℕ) :
    let L := m+2
    let q := (n+2)/L
    ∑ b ∈ univ.filter (fun b : Fin (n+2) => b.val<q),
        circuitHamiltonianSpectralWidth (shellOperator (piece L (pathPauliDisorderShell ω n) b)) =
      ∑ j ∈ range q, blockWidth m (readBlock m ω j) := by
  intro L q
  have hL : 0<L := by dsimp [L]; omega
  have hq : q<n+2 := Nat.div_lt_self (by omega) (by dsimp [L]; omega)
  apply sum_bij (fun b _ => b.val)
  · exact fun _ hb => mem_range.mpr (mem_filter.mp hb).2
  · exact fun _ _ _ _ h => Fin.ext h
  · exact fun j hj => ⟨⟨j,(mem_range.mp hj).trans hq⟩,mem_filter.mpr ⟨mem_univ _,mem_range.mp hj⟩,rfl⟩
  · intro b hb
    have h := (Nat.le_div_iff_mul_le hL).mp (Nat.succ_le_of_lt (mem_filter.mp hb).2)
    rw [Nat.succ_mul] at h
    exact width_full_piece ω b h

/-- Comparing with the sum over full length-L blocks costs exactly one
row-block remainder and at most twice the absolute seam mass. -/
theorem block_approximation (ω : PathPauliDisorder) (n m : ℕ) :
    let L := m+2
    let q := (n+2)/L
    |physicalWidth ω n-∑ j ∈ range q, blockWidth m (readBlock m ω j)| ≤
      2*((∑ j ∈ range q, seamMass m (readRows L ω j))+rowMass L (readRows L ω q)) := by
  intro L q
  let F (b : Fin (n+2)) :=
    circuitHamiltonianSpectralWidth (shellOperator (piece L (pathPauliDisorderShell ω n) b))
  have hq : q<n+2 := Nat.div_lt_self (by omega) (by dsimp [L]; omega)
  let last : Fin (n+2) := ⟨q,hq⟩
  have ha : ∑ b ∈ univ.filter (fun b : Fin (n+2) => b.val<q), F b =
      ∑ j ∈ range q, blockWidth m (readBlock m ω j) := full_width_sum ω n m
  have hb : ∑ b ∈ univ.filter (fun b : Fin (n+2) => ¬b.val<q), F b=F last := by
    apply sum_eq_single last
    · intro b hb hn
      apply empty_piece
      have hge : q ≤ b.val := Nat.le_of_not_gt (mem_filter.mp hb).2
      exact lt_of_le_of_ne hge (fun h => hn (Fin.ext h.symm))
    · intro hn
      exact (hn (mem_filter.mpr ⟨mem_univ _,lt_irrefl q⟩)).elim
  have he := sum_filter_add_sum_filter_not univ (fun b : Fin (n+2) => b.val<q) F
  rw [ha,hb] at he
  have hs := (cut_width_error L (pathPauliDisorderShell ω n)).trans
    (mul_le_mul_of_nonneg_left (seam_bound m ω (n:=n)) (by norm_num : (0:ℝ)≤2))
  have ht := (piece_le m ω last).trans
    (mul_le_mul_of_nonneg_left (last_block_mass m ω last) (by norm_num : (0:ℝ)≤2))
  change |physicalWidth ω n-∑ b,F b|≤_ at hs
  rw [←he] at hs
  change F last≤2*rowMass L (readRows L ω q) at ht
  have hpos : 0≤F last := circuitHamiltonianSpectralWidth_nonneg _
  obtain ⟨h₁,h₂⟩ := abs_le.mp hs
  exact abs_le.mpr ⟨by linarith only [h₁,hpos,ht],by linarith only [h₂,ht]⟩

#print axioms block_approximation
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
