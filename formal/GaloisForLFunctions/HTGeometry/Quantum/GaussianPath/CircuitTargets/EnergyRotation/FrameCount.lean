import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitTargets.EnergyRotation.PauliFrames

/-! # How many Pauli corrections of one circuit the orbit can visit -/
open Finset Real MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section
private abbrev Word (K : ℕ) := Fin K → Option (Fin 3)
private def distance {K : ℕ} (P Q : Word K) := (univ.filter fun i => P i ≠ Q i).card

private theorem partition {K : ℕ} (P : Word K) (θ : ℝ) :
    (∑ Q : Word K, exp (-θ*(distance P Q:ℝ)))=(1+3*exp (-θ))^K := by
  classical
  let w (i : Fin K) (a : Option (Fin 3)) := if P i ≠ a then exp (-θ) else 1
  have hcol (i : Fin K) : ∑ a, w i a=1+3*exp (-θ) := by
    have h (a) : w i a=(if P i=a then 1-exp (-θ) else 0)+exp (-θ) := by
      by_cases he : P i=a <;> simp [w,he]
    simp only [h,sum_add_distrib,sum_ite_eq,mem_univ,if_true,sum_const,card_univ,Fintype.card_option,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
    ring
  have hrow (Q : Word K) : (∏ i, w i (Q i))=exp (-θ*(distance P Q:ℝ)) := by
    dsimp only [w]
    rw [←prod_filter,prod_const,←Real.exp_nat_mul]
    congr 1
    exact mul_comm _ _
  have h := Fintype.prod_sum w
  simpa only [hcol,prod_const,card_univ,Fintype.card_fin,hrow] using h.symm

/-- Exponential tilt for a four-letter Hamming ball. -/
private theorem count_in_ball {K : ℕ} (F : Finset (Word K)) (P : Word K)
    {θ η : ℝ} (hθ : 0 ≤ θ) (hF : ∀ Q ∈ F, (distance P Q:ℝ) ≤ η*K) :
    (F.card:ℝ) ≤ exp ((3*exp (-θ)+θ*η)*K) := by
  have he (Q) (hQ : Q∈F) : exp (-θ*(η*K))≤exp (-θ*(distance P Q:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hF Q hQ) (neg_nonpos.mpr hθ))
  have h := (sum_le_sum he).trans (sum_le_sum_of_subset_of_nonneg (subset_univ F)
    (fun q _ _ => (Real.exp_pos _).le))
  rw [sum_const,nsmul_eq_mul,partition] at h
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1+3*exp (-θ))
    ((add_comm 1 (3*exp (-θ))).le.trans (Real.add_one_le_exp _)) K
  rw [←Real.exp_nat_mul] at hs
  have hh := (le_div_iff₀ (Real.exp_pos _)).mpr (h.trans hs)
  rw [←Real.exp_sub] at hh
  exact hh.trans_eq (by congr 1; ring)

/-- Candidate left Pauli corrections of a fixed circuit reached within one tenth. -/
open scoped Classical in
def visitedFrame {K : ℕ} (H X : Matrix (Fin K → Bool) (Fin K → Bool) ℂ) : Finset (Word K) :=
  univ.filter fun Q => ∃ t : ℝ, ∃ z : ℂ, ‖z‖=1 ∧
    ‖unitaryEvolution H t-z • (finitePauliMatrix Q*X)‖≤1/10

/-- Among all 4^K Pauli corrections of any common unitary, at most
exp(o(K)) are ever visited. The base unitary may vary with the frozen draw. -/
theorem gaussian_frame_count :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
      let K := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ X : Matrix.unitaryGroup (Fin K → Bool) ℂ, ((visitedFrame H X.val).card:ℝ)≤exp (c*K) := by
  classical
  filter_upwards [gaussian_pauli_frame_diameter] with ω hw
  intro c hc
  let θ := 6/c
  have hθ : 0 < θ := div_pos (by norm_num) hc
  let η := c/(2*θ)
  have hη : 0 < η := div_pos hc (mul_pos (by norm_num) hθ)
  filter_upwards [hw η hη] with n hn
  intro K H X
  let F := visitedFrame H X.val
  rcases F.eq_empty_or_nonempty with h0|h0
  · change (F.card:ℝ)≤_
    rw [h0,card_empty,Nat.cast_zero]
    exact (exp_pos _).le
  obtain ⟨P,hP⟩ := h0
  obtain ⟨s,z,hz,hs⟩ := (mem_filter.mp hP).2
  have hdist (Q) (hQ : Q∈F) : (distance P Q:ℝ) ≤ η*K := by
    obtain ⟨t,w,hw,ht⟩ := (mem_filter.mp hQ).2
    exact hn X P Q s t z w hz hw hs ht
  apply (count_in_ball F P hθ.le hdist).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have hge := (Real.add_one_le_exp θ)
  have hbudget : exp (-θ)≤1/θ := by
    rw [Real.exp_neg,one_div]
    exact inv_anti₀ hθ (by linarith only [hge])
  have hcost : θ*η=c/2 := by dsimp only [η]; field_simp
  rw [hcost]
  have hprice : 1/θ=c/6 := by dsimp only [θ]; field_simp
  rw [hprice] at hbudget
  linarith only [hbudget]

#print axioms gaussian_frame_count
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
