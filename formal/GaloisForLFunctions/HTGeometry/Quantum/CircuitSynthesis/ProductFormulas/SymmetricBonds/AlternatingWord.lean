import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.Layer
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.PhaseCircuit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.RepeatedSteps

/-! # Merging consecutive half layers of a symmetric bond sweep -/
open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
open DiagonalSynthesis (Realizes)
local instance (N : ℕ) : CStarAlgebra (Register N) where
local instance (N : ℕ) : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _

private theorem realizes_power {N k : ℕ} {X : Register N} (h : Realizes k X) (r : ℕ) : Realizes (r*k) (X^r) := by
  obtain ⟨z,hz,C,hC,he⟩ := h
  refine ⟨z^r,by simp [norm_pow,hz],C.pow r,?_,?_⟩
  · rw [TwoQubitCircuit.pow_gateCount]; exact Nat.mul_le_mul_left _ hC
  · rw [he,smul_pow,TwoQubitCircuit.pow_eval_coe]

private theorem merge_word {R : Type*} [Monoid R] (A B : R) (r : ℕ) :
    (A*B*A)^(r+1)=A*(B*(A*A))^r*B*A := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ (A*B*A) (r+1),ih,pow_succ (B*(A*A)) r]
    simp only [mul_assoc]

private theorem exact_layer {n : ℕ} (B : Fin (n+1)→selfAdjoint BondCoordinates.LocalMatrix)
    (S : Finset (Fin (n+1))) (hs : ∀ i∈S, ∀ j∈S, i.val%2=j.val%2) (t : ℝ) :
    Realizes S.card (exp (t • ∑ e∈S,generator e (B e))) := by
  obtain ⟨z,hz,C,hC,he⟩ := compile_layer B S hs t
  exact ⟨z,hz,C,hC,sub_eq_zero.mp (norm_le_zero_iff.mp he)⟩

/-- Repeating the step r+1 times costs r+1 full bond layers and one
additional copy of its outer parity, for arbitrary signed step size. -/
theorem realizes_alternating_powers {n : ℕ} (B : Fin (n+1)→selfAdjoint BondCoordinates.LocalMatrix)
    (S : Finset (Fin (n+1))) (hs : ∀ i∈S, ∀ j∈S, i.val%2=j.val%2)
    (hc : ∀ i∈Sᶜ, ∀ j∈Sᶜ, i.val%2=j.val%2) (t : ℝ) (r : ℕ) :
    let X := ∑ e∈S,generator e (B e)
    let Y := ∑ e∈Sᶜ,generator e (B e)
    Realizes ((r+1)*(n+1)+S.card) ((exp ((t/2) • X)*exp (t • Y)*exp ((t/2) • X))^(r+1)) := by
  intro X Y
  let A := exp ((t/2) • X)
  let D := exp (t • Y)
  have hh : A*A=exp (t • X) := by
    change exp ((t/2) • X)*exp ((t/2) • X)=_
    rw [←exp_add_of_commute (Commute.refl ((t/2) • X)),←add_smul,add_halves]
  have hA : Realizes S.card A := exact_layer B S hs _
  have hD : Realizes Sᶜ.card D := exact_layer B Sᶜ hc _
  have hfull : Realizes S.card (A*A) := by rw [hh]; exact exact_layer B S hs t
  have hword := ((hA.mul (realizes_power (hD.mul hfull) r)).mul hD).mul hA
  change Realizes _ ((A*D*A)^(r+1))
  rw [merge_word]
  have hn : Sᶜ.card+S.card=n+1 := by simpa only [Nat.add_comm S.card,Fintype.card_fin] using Finset.card_add_card_compl S
  obtain ⟨z,hz,C,hsize,he⟩ := hword
  refine ⟨z,hz,C,?_,he⟩
  rw [hn] at hsize
  rw [Nat.add_mul,one_mul]; omega

end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
