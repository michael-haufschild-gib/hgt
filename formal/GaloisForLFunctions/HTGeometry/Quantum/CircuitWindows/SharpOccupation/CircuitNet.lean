import GaloisForLFunctions.HTGeometry.UniformFixedErrorSpectralTorusCircuitHardnessLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # A unitary net for all circuits below a gate budget at arbitrary mesh -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- The mesh loss is paid once per gate. Every net point is unitary. -/
theorem exists_budget_net (n s : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ),
      (∀ C : TwoQubitCircuit n, C.gateCount ≤ s → ∃ W ∈ F,
        ‖(C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤ δ) ∧
      (F.card:ℝ) ≤ ((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s := by
  classical
  let L := ((n:ℝ)+1)^2*(1+4*(s:ℝ)/δ)^32
  have hn : 1 ≤ ((n:ℝ)+1)^2 := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg n) : 1 ≤ (n:ℝ)+1)
  have hs : 1 ≤ 1+4*(s:ℝ)/δ := le_add_of_nonneg_right (by positivity)
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hn (one_le_pow₀ hs)
  have each (j : ℕ) : ∃ F : Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ),
      (∀ C : TwoQubitCircuit n, C.gateCount = j → ∃ W ∈ F, ‖(C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)-(W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤ δ) ∧
      (j ≤ s → (F.card:ℝ) ≤ L^s) := by
    rcases eq_or_ne j 0 with rfl|hj
    · refine ⟨{1},?_,fun _ => ?_⟩
      · intro C hC
        exact ⟨1,mem_singleton_self _,by simp [zeroGateCircuit_eval C hC.le,hδ.le]⟩
      · simpa using one_le_pow₀ hL (n := s)
    · obtain ⟨F,hF,hcard⟩ := exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
        (n := n) (Nat.pos_of_ne_zero hj) hδ
      refine ⟨F,?_,?_⟩
      · rintro C rfl
        obtain ⟨W,hW,hd⟩ := hF C.architecture C.gates
        rw [dist_eq_norm] at hd
        exact ⟨W,hW,hd⟩
      · intro hjs
        have hj' : (j:ℝ) ≤ s := by exact_mod_cast hjs
        apply hcard.trans
        rw [Nat.cast_mul,pow_mul,←mul_pow]
        apply (pow_le_pow_left₀ (by positivity) _ j).trans (pow_le_pow_right₀ hL hjs)
        apply mul_le_mul (by nlinarith only [Nat.cast_nonneg (α := ℝ) n]) _ (by positivity) (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        gcongr
  choose F hF hcard using each
  refine ⟨(range (s+1)).biUnion F,?_,?_⟩
  · intro C hC
    obtain ⟨W,hW,hh⟩ := hF C.gateCount C rfl
    exact ⟨W,mem_biUnion.mpr ⟨_,mem_range.mpr (by omega),hW⟩,hh⟩
  · have bound : (((range (s+1)).biUnion F).card:ℝ) ≤ ∑ j ∈ range (s+1), ((F j).card:ℝ) := by
      exact_mod_cast (card_biUnion_le : ((range (s+1)).biUnion F).card ≤ ∑ j ∈ range (s+1), (F j).card)
    apply bound.trans
    simpa [nsmul_eq_mul,L] using sum_le_sum (s := range (s+1)) (fun j hj => hcard j (by
      have := mem_range.mp hj; omega))

#print axioms exists_budget_net
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
