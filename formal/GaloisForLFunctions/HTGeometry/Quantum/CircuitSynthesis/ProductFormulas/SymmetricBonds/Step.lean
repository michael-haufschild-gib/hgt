import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.Layer
import GaloisForLFunctions.HTGeometry.QuantitativeStrangProductFormula

/-! # A second-order physical sweep with the smaller parity layer repeated -/
open Filter Matrix NormedSpace Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
local instance (N : ℕ) : CStarAlgebra (Register N) where
local instance (N : ℕ) : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _

private theorem shorter_parity (m : ℕ) : ∃ S : Finset (Fin m), 2*S.card ≤ m ∧
    (∀ i∈S, ∀ j∈S, i.val%2=j.val%2) ∧ (∀ i∈Sᶜ, ∀ j∈Sᶜ, i.val%2=j.val%2) := by
  classical
  let E := Finset.univ.filter (fun i : Fin m => i.val%2=0)
  have he (i : Fin m) : i ∈ E ↔ i.val%2=0 := by simp [E]
  have ev : ∀ i∈E, ∀ j∈E, i.val%2=j.val%2 := fun i hi j hj =>
    ((he i).mp hi).trans ((he j).mp hj).symm
  have od : ∀ i∈Eᶜ, ∀ j∈Eᶜ, i.val%2=j.val%2 := by
    intro i hi j hj
    have hi' := (he i).not.mp (Finset.mem_compl.mp hi)
    have hj' := (he j).not.mp (Finset.mem_compl.mp hj)
    omega
  have hcard : E.card+Eᶜ.card=m := by simpa only [Fintype.card_fin] using Finset.card_add_card_compl E
  by_cases h : 2*E.card ≤ m
  · exact ⟨E,h,ev,od⟩
  · exact ⟨Eᶜ,by omega,od,by simpa only [compl_compl] using ev⟩

/-- At sufficiently short signed times, a symmetric sweep achieves cubic
operator error with N−1+floor((N−1)/2) gates and no ancillas. -/
theorem cubic_bond_step {n : ℕ} (u : PathShell n) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in 𝓝 0,
      HasProjectiveCircuitApproximation (n+2) (K*|t|^3) ((n+1)+(n+1)/2)
        (unitaryEvolution (pathHamiltonian u) t) := by
  classical
  obtain ⟨B,hB⟩ := exists_bond_hamiltonians u
  obtain ⟨S,hcard,hs,hc⟩ := shorter_parity (n+1)
  let X := ∑ e∈S, generator e (B e)
  let Y := ∑ e∈Sᶜ, generator e (B e)
  have hsum : X+Y=(-Complex.I) • pathHamiltonian u := by
    dsimp only [X,Y]
    rw [Finset.sum_add_sum_compl,hB,Finset.smul_sum]; rfl
  have hx : X ∈ skewAdjoint _ := (skewAdjoint _).sum_mem fun e _ => generator_skew e (B e)
  have hy : Y ∈ skewAdjoint _ := (skewAdjoint _).sum_mem fun e _ => generator_skew e (B e)
  let L := ‖X‖+‖Y‖
  have hL : 0 ≤ L := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨8*L^3+1,by positivity,?_⟩
  have hlim : Tendsto (fun t : ℝ => |t| *L) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_abs.mul_const L).continuousAt (x:=0)).tendsto
  filter_upwards [hlim.eventually_lt_const zero_lt_one] with t ht
  have ha := compile_layer B S hs (t/2)
  have hb := compile_layer B Sᶜ hc t
  have hword := LocalPatches.approx_product (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem (t/2) hx))
    (LocalPatches.approx_product (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hy)) ha hb) ha
  obtain ⟨z,hz,C,hsize,he⟩ := hword
  have hw : exp ((t/2) • X)*exp (t • Y)*exp ((t/2) • X)=z • C.eval.val :=
    sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_add] using he))
  have herror := norm_exp_half_mul_exp_mul_exp_half_sub_exp_add_le X Y hx hy t ht.le
  rw [hw,hsum,norm_sub_rev] at herror
  refine ⟨z,hz,C,?_,herror.trans ?_⟩
  · rw [Finset.card_compl,Fintype.card_fin] at hsize
    omega
  · change 8*L^3*|t|^3 ≤ (8*L^3+1)*|t|^3
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

#print axioms cubic_bond_step
end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
