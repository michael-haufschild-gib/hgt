import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PathCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.BondSets

/-! # A gate deficit forces a cut with large selected interaction mass -/

open Finset
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- When at most d/4 bonds are weak, every circuit missing at least
d gates has one cut carrying at least dh/4 in chosen Pauli couplings. -/
theorem missing_bond_mass (u : PathShell n) (C : TwoQubitCircuit (n+2)) (d : ℕ) {h : ℝ}
    (hh : 0≤h) (hd : C.gateCount+d≤n+1) (hw : 4*(weakEdges u h).card≤d) :
    ∃ c : Cut C, ∃ b : Fin (n+1)→Fin 3×Fin 3,
      (d:ℝ)*h/4≤∑ e∈crossed c, |u (.inr (e,b e))| := by
  classical
  obtain ⟨c,hc⟩ := many_crossed C
  let F := crossed c
  let W := weakEdges u h
  have witness (e : Fin (n+1)) (he : e∉W) : ∃ b : Fin 3×Fin 3, h < |u (.inr (e,b))| := by
    by_contra! hn
    exact he (mem_filter.mpr ⟨mem_univ _,hn⟩)
  let b (e : Fin (n+1)) := if he : e∉W then (witness e he).choose else (0,0)
  refine ⟨c,b,?_⟩
  have hcard : F.card≤(F\W).card+W.card := by
    rw [←card_sdiff_add_card_inter F W]
    exact Nat.add_le_add_left (card_le_card inter_subset_right) _
  have hn : d≤4*(F\W).card := by
    change n+1≤C.gateCount+2*F.card at hc
    change 4*W.card≤d at hw
    omega
  calc
    (d:ℝ)*h/4 ≤ ((F\W).card:ℝ)*h := by
      have he : (d:ℝ)≤4*((F\W).card:ℝ) := by exact_mod_cast hn
      linarith only [mul_le_mul_of_nonneg_right he hh]
    _ = ∑ _e∈F\W, h := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ ∑ e∈F\W, |u (.inr (e,b e))| := by
      apply sum_le_sum
      intro e he
      have hn := (mem_sdiff.mp he).2
      simpa only [b,dif_pos hn] using (witness e hn).choose_spec.le
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => abs_nonneg _)

#print axioms missing_bond_mass
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
