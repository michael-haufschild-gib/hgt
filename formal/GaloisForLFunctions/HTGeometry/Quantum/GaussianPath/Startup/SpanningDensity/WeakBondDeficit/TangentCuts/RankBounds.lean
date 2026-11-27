import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.TangentCuts.PhaseContrast
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.MissingMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.MatchedAxes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrecisionProfile.RemovableRank

/-! # Deterministic error bounds from ranks of the weakest physical bonds -/

open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

private theorem dominant_frame (u : PathShell n) (F : Finset (Fin (n+1))) (b : Fin (n+1)→Fin 3×Fin 3) :
    ∃ a : Fin (n+2)→Fin 3, (∑ e∈F, |u (.inr (e,b e))|)≤2*(∑ e∈F, |u (.inr (e,a e.castSucc,a e.succ))|) := by
  classical
  let E := F.filter (fun e => e.val%2=0)
  let O := F \ E
  let w (e : Fin (n+1)) := |u (.inr (e,b e))|
  have extend (G : Finset (Fin (n+1))) (hG : G⊆F) (p : ℕ) (hp : ∀ e∈G, e.val%2=p) :
      ∃ a : Fin (n+2)→Fin 3, (∑ e∈G, w e)≤∑ e∈F, |u (.inr (e,a e.castSucc,a e.succ))| := by
    obtain ⟨a,ha⟩ := axis_frame_on_matching G b (by
      intro e he f hf hef
      have hv : e.val=f.val+1 := congrArg Fin.val hef
      have h₁ := hp e he
      have h₂ := hp f hf
      omega)
    refine ⟨a,?_⟩
    calc
      _ = ∑ e∈G, |u (.inr (e,a e.castSucc,a e.succ))| := sum_congr rfl fun e he => by rw [ha e he]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hG (fun _ _ _ => abs_nonneg _)
  have hsplit : (∑ e∈O, w e)+(∑ e∈E, w e)=∑ e∈F, w e := sum_sdiff (filter_subset _ _)
  rcases le_total (∑ e∈O, w e) (∑ e∈E, w e) with h|h
  · obtain ⟨a,ha⟩ := extend E (filter_subset ..) 0 (fun _ he => (mem_filter.mp he).2)
    exact ⟨a,by change (∑ e∈F,w e)≤_; linarith only [ha,h,hsplit]⟩
  · obtain ⟨a,ha⟩ := extend O sdiff_subset 1 (by
      intro e he
      obtain ⟨hf,hne⟩ := mem_sdiff.mp he
      have hp : e.val%2≠0 := fun h => hne (mem_filter.mpr ⟨hf,h⟩)
      omega)
    exact ⟨a,by change (∑ e∈F,w e)≤_; linarith only [ha,h,hsplit]⟩

/-- If at most d/4 physical bonds fit in the nine-coordinate h-box,
the entire circuit set with d missing gates has initial slope at least
dh/8. The quadratic correction is uniform over physical architectures. -/
theorem rank_distance_lower (u : PathShell n) (d : ℕ) {h : ℝ} (hh : 0≤h)
    (hd : d≤n+1) (hw : 4*(weakEdges u h).card≤d) (t : ℝ) :
    let δ := Metric.infDist (unitaryEvolution (pathHamiltonian u) t) (phaseCircuitMatrixImageAtMost (n+2) (n+1-d))
    |t| * ((d:ℝ)*h/8)≤δ+t^2*(21*‖u‖^2+4*(((n+1:ℕ):ℝ)*‖u‖)^2) := by
  intro δ
  obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist
    (unitaryEvolution (pathHamiltonian u) t) (n+1-d) δ).mpr le_rfl
  obtain ⟨c,b,hb⟩ := missing_bond_mass u C d hh (by omega) hw
  obtain ⟨a,ha⟩ := dominant_frame u (crossed c) b
  let S := ∑ e∈crossed c, |u (.inr (e,a e.castSucc,a e.succ))|
  have hlow : (d:ℝ)*h/8≤S := by linarith only [hb,ha]
  have hhigh : S≤((n+1:ℕ):ℝ)*‖u‖ := calc
    _ ≤ ∑ _e∈crossed c, ‖u‖ := sum_le_sum fun _ _ => abs_coord_le_norm u _
    _ = ((crossed c).card:ℝ)*‖u‖ := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr ((card_le_univ _).trans_eq (Fintype.card_fin _))) (norm_nonneg u)
  have hs := TangentCuts.frame_cut_speed u C c z hz t a
  have hsq := pow_le_pow_left₀ (show 0≤S from sum_nonneg fun _ _ => abs_nonneg _) hhigh 2
  apply (mul_le_mul_of_nonneg_left hlow (abs_nonneg _)).trans (hs.trans _)
  exact add_le_add hfit (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (by norm_num))) (sq_nonneg _))

#print axioms rank_distance_lower
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
