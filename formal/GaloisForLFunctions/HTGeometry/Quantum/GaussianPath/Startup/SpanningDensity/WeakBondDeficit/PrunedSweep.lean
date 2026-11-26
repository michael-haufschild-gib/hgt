import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.AssignedSweep

/-! # Removing weak bonds from a single circuit sweep -/

open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- Removing edges leaves all onsite fields intact. -/
private def retained (S : Finset (Fin (n+1))) : PathLabel n → Bool
  | .inl _ => true
  | .inr (e,_) => decide (e∈S)

/-- A covering family of physical bonds implements one sweep with one
gate per retained edge. The discarded couplings cost at most their
total absolute mass times elapsed time. -/
theorem pruned_sweep (u : PathShell n) (S : Finset (Fin (n+1)))
    (hS : ∀ v : Fin (n+2), ∃ e∈S, v=e.castSucc ∨ v=e.succ) (t : ℝ) (ht : 0≤t) :
    HasProjectiveCircuitApproximation (n+2)
      (t*(∑ e ∈ Sᶜ, ∑ ab : Fin 3×Fin 3, |u (.inr (e,ab))|)+t^2*(84*‖u‖^2)) S.card
      (unitaryEvolution (pathHamiltonian u) t) := by
  classical
  let v : PathShell n := WithLp.toLp 2 (fun l => if retained S l then u l else 0)
  let σ : ↥S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe _)
  let edge (j : Fin S.card) := (σ.symm j).val
  choose incident hin hsite using hS
  let owner : PathLabel n→Fin S.card
    | .inl (i,_) => σ ⟨incident i,hin i⟩
    | .inr (e,_) => if h : e∈S then σ ⟨e,h⟩ else σ ⟨incident 0,hin 0⟩
  have support (l : PathLabel n) (hn : v l≠0) (i : Fin (n+2))
      (h₁ : i≠(edge (owner l)).castSucc) (h₂ : i≠(edge (owner l)).succ) : pathWord l i=none := by
    rcases l with ⟨k,a⟩ | ⟨e,ab⟩
    · have he : edge (owner (.inl (k,a)))=incident k := by simp [owner,edge]
      rw [he] at h₁ h₂
      have hik : i≠k := fun h => (hsite k).elim (fun hk => h₁ (h.trans hk)) (fun hk => h₂ (h.trans hk))
      simp [pathWord,onsiteWord,hik]
    · have heS : e∈S := by
        by_contra h
        exact hn (by simp [v,retained,h])
      have he : edge (owner (.inr (e,ab)))=e := by simp [owner,edge,heS]
      rw [he] at h₁ h₂
      simp [pathWord,couplingWord,h₁,h₂]
  obtain ⟨z,hz,C,hC,hfit⟩ := assigned_sweep v owner edge support t ht
  have henergy : ‖v‖^2≤‖u‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    apply sum_le_sum
    intro l _
    change (if retained S l then u l else 0)^2≤(u l)^2
    split <;> simp [sq_nonneg]
  have hmass : ‖pathHamiltonian u-pathHamiltonian v‖ ≤
      ∑ e ∈ Sᶜ, ∑ ab : Fin 3×Fin 3, |u (.inr (e,ab))| := by
    rw [pathHamiltonian_eq_sum,pathHamiltonian_eq_sum,←sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    have hn (l : PathLabel n) : ‖((u l:ℝ):ℂ) • finitePauliMatrix (pathWord l)-
        ((v l:ℝ):ℂ) • finitePauliMatrix (pathWord l)‖ = if retained S l then 0 else |u l| := by
      by_cases h : retained S l
      · simp [v,h]
      · simp [v,h,norm_smul,norm_finitePauliMatrix]
    simp_rw [hn]
    rw [Fintype.sum_sum_type]
    have hzero : (∑ l : Fin (n+2)×Fin 3, if retained S (.inl l) then (0:ℝ) else |u (.inl l)|)=0 :=
      sum_eq_zero fun _ _ => rfl
    rw [hzero,zero_add,Fintype.sum_prod_type]
    have hc : Sᶜ=univ.filter fun e => e∉S := by ext; simp
    rw [hc,sum_filter]
    apply sum_le_sum
    intro e _
    by_cases he : e∈S <;> simp [retained,he]
  have hdiff := norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u) (isSelfAdjoint_pathHamiltonian v) t
  rw [abs_of_nonneg ht] at hdiff
  refine ⟨z,hz,C,hC,(norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution (pathHamiltonian v) t) _).trans ?_⟩
  exact add_le_add (hdiff.trans (mul_le_mul_of_nonneg_left hmass ht))
    (hfit.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy (by norm_num)) (sq_nonneg t)))

#print axioms pruned_sweep
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
