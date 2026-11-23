import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.EnergyCount
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance

/-! # Twenty-one disjoint interaction layers partition the Pauli path -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section
variable {n : ℕ}
abbrev Layer := Fin 3 ⊕ (Fin 2 × (Fin 3 × Fin 3))
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

def color : PathLabel n → Layer
  | .inl (_,a) => .inl a
  | .inr (e,p) => .inr (⟨e.val%2,Nat.mod_lt _ (by decide)⟩,p)

private def sites : PathLabel n → Finset (Fin (n+2))
  | .inl (i,_) => {i}
  | .inr (e,_) => {e.castSucc,e.succ}

private theorem color_disjoint {i j : PathLabel n} (hc : color i=color j) (hne : i≠j) :
    Disjoint (sites i) (sites j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  apply hne
  rcases i with ⟨i,a⟩|⟨i,a⟩ <;> rcases j with ⟨j,b⟩|⟨j,b⟩
  · simp only [color,Sum.inl.injEq] at hc
    simp only [sites,mem_singleton] at hi hj
    rw [←hi,←hj,hc]
  · cases hc
  · cases hc
  · simp only [color,Sum.inr.injEq,Prod.mk.injEq,Fin.mk.injEq] at hc
    obtain ⟨hmod,rfl⟩ := hc
    simp only [sites,mem_insert,mem_singleton] at hi hj
    have he : i=j := by
      apply Fin.ext
      rcases hi with rfl|rfl <;> rcases hj with h|h <;>
        have hv := congrArg Fin.val h <;> simp only [Fin.val_castSucc,Fin.val_succ] at hv <;> omega
    rw [he]

private theorem term_supported (l : PathLabel n) :
    IsSiteSupported (sites l) (finitePauliMatrix (pathWord l)) := by
  apply finitePauliMatrix_isSiteSupported_of_eq_none
  intro v hv
  rcases l with ⟨i,a⟩|⟨e,p⟩
  · simp only [pathWord,onsiteWord,if_neg (show v≠i from fun h => hv (mem_singleton.mpr h))]
  · have h₁ : v≠e.castSucc := fun h => hv (mem_insert.mpr (Or.inl h))
    have h₂ : v≠e.succ := fun h => hv (mem_insert.mpr (Or.inr (mem_singleton.mpr h)))
    simp only [pathWord,couplingWord,if_neg h₁,if_neg h₂]

def layer (u : PathShell n) (a : Layer) : Reg (n+2) :=
  ∑ l ∈ univ.filter (fun l : PathLabel n => color l=a), (u l:ℂ) • finitePauliMatrix (pathWord l)

theorem sum_layer (u : PathShell n) : ∑ a, layer u a = pathHamiltonian u := by
  rw [pathHamiltonian_eq_sum]
  simp only [layer,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem hermitian_layer (u : PathShell n) (a : Layer) : (layer u a).IsHermitian := by
  apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
  unfold layer
  rw [IsSelfAdjoint,star_sum]
  apply sum_congr rfl
  intro i _
  rw [star_smul,(finitePauliMatrix_isHermitian (pathWord i)).isSelfAdjoint.star_eq]
  simp only [Complex.star_def,Complex.conj_ofReal]

theorem layer_energy_count (u : PathShell n) (a : Layer) {B r : ℝ}
    (hB : 0 < B) (hmass : ‖u‖^2 ≤ B) (hr : 0 ≤ r) :
    ((univ.filter fun j => r < |(hermitian_layer u a).eigenvalues j|).card:ℝ) ≤
      2*(2:ℝ)^(n+2)*Real.exp (-(r^2)/(2*B)) := by
  let s := univ.filter fun l : PathLabel n => color l=a
  have hsub : ∑ i ∈ s, (u i)^2 ≤ ‖u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [Real.norm_eq_abs,sq_abs] using
      (sum_le_sum_of_subset_of_nonneg (f:=fun i : PathLabel n => (u i)^2) (subset_univ s)
        (fun _ _ _ => sq_nonneg _))
  have h := disjoint_energy_count s sites (fun l => finitePauliMatrix (pathWord l)) (fun l => u l)
    (fun i hi j hj => color_disjoint ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm))
    (fun i _ => term_supported i) (fun i _ => finitePauliMatrix_mul_self _)
    (fun i _ => finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity i))
    (hermitian_layer u a) hB (hsub.trans hmass) hr
  change ((univ.filter fun j => r < |(hermitian_layer u a).eigenvalues j|).card:ℝ) ≤
    2*(Fintype.card (Fin (n+2) → Bool):ℝ)*Real.exp (-(r^2)/(2*B)) at h
  simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

#print axioms layer_energy_count
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
