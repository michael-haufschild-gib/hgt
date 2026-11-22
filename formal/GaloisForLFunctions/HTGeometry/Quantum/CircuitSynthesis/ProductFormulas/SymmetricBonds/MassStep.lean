import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.SubsetBracket
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.PairError
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.AlternatingWord
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.ParityPartition
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Uniform symmetric-sweep simulation from the cubic coefficient mass -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
open LocalPatches
local instance (N : ℕ) : CStarAlgebra (Register N) where
local instance (N : ℕ) : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _

private theorem half_pair_error {R : Type*} [CStarAlgebra R] (X Y : R) (hx : X∈skewAdjoint R)
    (hy : Y∈skewAdjoint R) (t : ℝ) (ht : 0≤t) :
    ‖exp ((t/2) • X)*exp (t • Y)*exp ((t/2) • X)-exp (t • (X+Y))‖ ≤
      t^3*(‖bracketStep X (bracketStep X Y)‖+‖bracketStep Y (bracketStep Y X)‖) := by
  let a := (1/2:ℝ) • X
  have ha : a∈skewAdjoint R := skewAdjoint.smul_mem _ hx
  have he : a+Y+a=X+Y := by
    rw [add_right_comm,←add_smul,show (1/2:ℝ)+1/2=1 by norm_num,one_smul]
  have hs : t • a=(t/2) • X := by rw [smul_smul]; congr 1; ring
  have hh := symmetric_pair_error a Y ha hy t ht
  rw [hs,he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hL (r : ℝ) (x y : R) : bracketStep (r • x) y=r • bracketStep x y := by
    simp only [bracketStep,mul_smul_comm,smul_mul_assoc,smul_sub]
  have hR (r : ℝ) (x y : R) : bracketStep x (r • y)=r • bracketStep x y := by
    simp only [bracketStep,mul_smul_comm,smul_mul_assoc,smul_sub]
  simp only [a,show -Y=(-1:ℝ) • Y by simp,hL,hR,norm_smul,Real.norm_eq_abs,abs_neg,abs_one,one_mul]
  rw [abs_of_pos (by norm_num : 0<(1/2:ℝ))]
  linarith only [norm_nonneg (bracketStep X (bracketStep X Y)),norm_nonneg (bracketStep Y (bracketStep Y X))]

private theorem positive_sweeps {n : ℕ} (u : PathShell n) (t : ℝ) (ht : 0≤t) (r : ℕ) :
    HasProjectiveCircuitApproximation (n+2) ((48*42^2)*t^3*(∑ l, |u l|^3)/(r+1:ℕ)^2)
      ((r+1)*(n+1)+(n+1)/2) (unitaryEvolution (pathHamiltonian u) t) := by
  classical
  obtain ⟨B,hB⟩ := BondCoordinates.exists_local_blocks u
  obtain ⟨S,hs,hsame,hcomp⟩ := shorter_parity (n+1)
  let V (T : Finset (Fin (n+1))) := ∑ e∈T,generator e (B e)
  let terms (T : Finset (Fin (n+1))) := Finset.univ.filter (fun l : PathLabel n => BondCoordinates.termBond l∈T)
  have hblock (e : Fin (n+1)) : generator e (B e)=∑ l∈Finset.univ.filter (fun l => BondCoordinates.termBond l=e), pathTermGenerator u l := by
    unfold generator; rw [hB,← Finset.sum_filter,Finset.smul_sum]; rfl
  have hT (T) : V T=∑ l∈terms T,pathTermGenerator u l := by
    simp only [V,hblock,terms,Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have htogether : V S+V Sᶜ=(-Complex.I) • pathHamiltonian u := by
    simp only [V,Finset.sum_add_sum_compl,hblock,Finset.sum_filter]
    rw [Finset.sum_comm,pathHamiltonian_eq_sum,Finset.smul_sum]
    simp [pathTermGenerator]
  have hsk (T) : V T∈skewAdjoint _ := (skewAdjoint _).sum_mem fun e _ => generator_skew e (B e)
  let K := (24*42^2)*∑ l,|u l|^3
  have bound (T P) : ‖bracketStep (V T) (bracketStep (V T) (V P))‖≤K := by
    rw [hT T,hT P]
    exact subset_nested_mass u _ _ _
  let h := t/(r+1:ℕ)
  have hr : 0<((r+1:ℕ):ℝ) := by positivity
  have hh : 0≤h := div_nonneg ht hr.le
  let W := exp ((h/2) • V S)*exp (h • V Sᶜ)*exp ((h/2) • V S)
  let E := exp (h • (V S+V Sᶜ))
  have hp : ‖W-E‖≤h^3*(K+K) := (half_pair_error _ _ (hsk S) (hsk Sᶜ) h hh).trans
    (mul_le_mul_of_nonneg_left (add_le_add (bound S Sᶜ) (bound Sᶜ S)) (by positivity))
  have hU (s : ℝ) (T) := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s (hsk T))
  have hw : W ∈ unitary (Register (n+2)) := mul_mem (mul_mem (hU _ _) (hU _ _)) (hU _ _)
  have hv : E ∈ unitary (Register (n+2)) := exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem h ((skewAdjoint _).add_mem (hsk S) (hsk Sᶜ)))
  have hpow : E^(r+1)=unitaryEvolution (pathHamiltonian u) t := by
    dsimp only [E]
    rw [exp_real_smul_pow,htogether,show ((r+1:ℕ):ℝ)*h=t by dsimp only [h]; field_simp]
    rfl
  obtain ⟨z,hz,C,hsize,he⟩ := realizes_alternating_powers B S hsame hcomp h r
  change W^(r+1)=z • C.eval.val at he
  have htel := (unitary_pow_norm_sub_pow_le W E hw hv (r+1)).trans (mul_le_mul_of_nonneg_left hp hr.le)
  rw [hpow,he,norm_sub_rev] at htel
  refine ⟨z,hz,C,by omega,htel.trans_eq ?_⟩
  dsimp only [h,K]; field_simp; ring

/-- Each repetition costs a full bond sweep; the two ends together cost
one extra short parity. The error constant is independent of chain length. -/
theorem cubic_mass_sweeps {n : ℕ} (u : PathShell n) (t : ℝ) (r : ℕ) :
    HasProjectiveCircuitApproximation (n+2) ((48*42^2)*|t|^3*(∑ l, |u l|^3)/(r+1:ℕ)^2)
      ((r+1)*(n+1)+(n+1)/2) (unitaryEvolution (pathHamiltonian u) t) := by
  let H : selfAdjoint (Register (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
  have h := positive_sweeps u |t| (abs_nonneg _) r
  rcases le_or_gt 0 t with hp|hn
  · simpa only [abs_of_nonneg hp] using h
  · have hh := h.neg_time H
    rwa [abs_of_neg hn,neg_neg] at hh ⊢

#print axioms cubic_mass_sweeps
end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
