import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.MinimumGateCount
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # Minimum gate counts on leaving accurate circuit returns -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem compose_at_times {N s r : ℕ} (H : selfAdjoint (Reg N)) {x y e f g : ℝ}
    (hx : HasProjectiveCircuitApproximation N e s (unitaryEvolution H.val x))
    (hy : HasProjectiveCircuitApproximation N f r (unitaryEvolution H.val y)) (hε : e+f ≤ g) :
    HasProjectiveCircuitApproximation N g (s+r) (unitaryEvolution H.val (x+y)) := by
  by_contra hno
  have hfar : ProjectiveCircuitSeparated N g (s+r) (unitaryEvolution H.val (x+y)) :=
    fun z hz C hC => lt_of_not_ge fun h => hno ⟨z,hz,C,hC,h⟩
  have h := projectiveCircuitSeparated_unitaryEvolution_backward_cone H (Nat.le_add_left _ _) hfar hy hε
  rw [add_sub_cancel_right,Nat.add_sub_cancel] at h
  obtain ⟨z,hz,C,hC,he⟩ := hx
  exact (not_lt_of_ge he) (h z hz C hC)

/-- The increment uses error 1/20 and the inverse comparison uses error
1/4. Every admissible allocation gives the same post-return cost bounds. -/
theorem gaussian_path_minimum_after_accurate_return :
    ∃ A c : ℝ, ∃ J : ℕ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ (v : ℝ) (s : ℕ) (α ε : ℝ), α+1/20 ≤ ε → α+ε ≤ 1/4 →
        HasProjectiveCircuitApproximation N α s (unitaryEvolution H v) →
        ∀ t ∈ Icc (A/(N:ℝ)) (1/Real.sqrt N), ∃ r : ℕ,
          IsLeast {k | HasProjectiveCircuitApproximation N ε k (unitaryEvolution H (v+t))} r ∧
            c*(N:ℝ) ≤ (s:ℝ)+r ∧ r ≤ s+J*N := by
  classical
  obtain ⟨A,c,J,hA,hc,hw⟩ := gaussian_path_startup_minimum_gate_count
  refine ⟨A,c,J,hA,hc,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  let N := n+2
  let H : selfAdjoint (Reg N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  intro _ _ v s α ε hupper hlower hv t ht
  obtain ⟨a,ha,_,hcount⟩ := hn t ht (1/20) (by constructor <;> norm_num)
  obtain ⟨b,hb,hfloor,_⟩ := hn t ht (1/4) (by constructor <;> norm_num)
  let affordable (k : ℕ) := HasProjectiveCircuitApproximation N ε k
    (unitaryEvolution H.val (v+t))
  have hfit : affordable (s+a) := compose_at_times H hv ha.1 hupper
  have hex : ∃ k, affordable k := ⟨_,hfit⟩
  let r := Nat.find hex
  have hr : affordable r := Nat.find_spec hex
  have hinc := compose_at_times H (hv.neg_time H) hr hlower
  rw [neg_add_cancel_left] at hinc
  have hbr : b ≤ s+r := hb.2 hinc
  exact ⟨r,⟨hr,fun _ hk => Nat.find_min' hex hk⟩,hfloor.trans (by exact_mod_cast hbr),
    (Nat.find_min' hex hfit).trans (Nat.add_le_add_left hcount _)⟩

/-- Arbitrarily late returns to the identity have an entire following
interval of extensive minimum cost. The same interval works after every
such return at error 1/20. -/
theorem gaussian_path_startup_after_identity_returns :
    ∃ A c : ℝ, ∃ J : ℕ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ a : ℝ, ∃ v ∈ Icc (|a|+1) ((|a|+1)*(160:ℝ)^(2^N-1)),
        HasProjectiveCircuitApproximation N (1/20:ℝ) 0 (unitaryEvolution H v) ∧
        ∀ t ∈ Icc (A/(N:ℝ)) (1/Real.sqrt N), ∃ r : ℕ,
          IsLeast {k | HasProjectiveCircuitApproximation N (1/10:ℝ) k (unitaryEvolution H (v+t))} r ∧
            c*(N:ℝ) ≤ r ∧ r ≤ J*N := by
  obtain ⟨A,c,J,hA,hc,hw⟩ := gaussian_path_minimum_after_accurate_return
  refine ⟨A,c,J,hA,hc,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  let N := n+2
  let H : selfAdjoint (Reg N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  let d := 2^N-1
  let e : (Fin N → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    have : 0 < (2:ℕ)^N := by positivity
    dsimp [d]; omega))
  intro _ _ a
  obtain ⟨v,hv,z,hz,C,hC,he⟩ := projective_operator_zero_gate_return_after e H a 159
  have hcheap : HasProjectiveCircuitApproximation N (1/20:ℝ) 0 (unitaryEvolution H.val v) :=
    ⟨z,hz,C,hC,he.trans (by norm_num; linarith only [Real.pi_lt_four])⟩
  refine ⟨v,by norm_num at hv; exact hv,hcheap,?_⟩
  simpa only [Nat.cast_zero,zero_add,Nat.zero_add] using hn v 0 (1/20) (1/10) (by norm_num) (by norm_num) hcheap

#print axioms gaussian_path_minimum_after_accurate_return
#print axioms gaussian_path_startup_after_identity_returns
end
end GaloisForLFunctions.HTGeometry

