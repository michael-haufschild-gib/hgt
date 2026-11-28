import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.MomentPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.SitePair

/-! # Two unit path fields with separated spectral skewness -/

open Matrix Real Finset
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields.ClockAdjustment
open private bond_product from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.PathConjugation
noncomputable section

/-- Coordinates outside the left onsite Pauli, its right neighbor and their bond product. -/
abbrev Exterior {n : ℕ} (e : Fin (n+1)) := {i : PathLabel n //
  i≠leftSite e 0 ∧ i≠rightSite e 0 ∧ i≠Dephasing.PairedFields.ClockAdjustment.edgeLabel e 0 0}

/-- All field readings except the three on the specified bond. -/
def outside {n : ℕ} (e : Fin (n+1)) (h : PathShell n) (i : Exterior e) : ℝ := h i.val

private abbrev basis {n : ℕ} (i : PathLabel n) : PathShell n := EuclideanSpace.single i 1
private abbrev pauli {n : ℕ} (i : PathLabel n) := finitePauliMatrix (pathWord i)

private theorem generator_basis {n : ℕ} (p : PathLabel n) : pathHamiltonian (basis p)=pauli p := by
  rw [pathHamiltonian_eq_sum,Finset.sum_eq_single p]
  · simp [basis,EuclideanSpace.single]
  · intro q _ hq
    simp [basis,EuclideanSpace.single,hq]
  · simp

private theorem triple_cube {R : Type*} [Ring R] {P Q B : R}
    (hP : P*P=1) (hQ : Q*Q=1) (hB : B*B=1) (hpq : P*Q=B) (hqp : Q*P=B) :
    (P+Q+B)^3=6 • (1:R)+7 • (P+Q+B) := by
  have hpb : P*B=Q := by rw [←hpq,←mul_assoc,hP,one_mul]
  have hqb : Q*B=P := by rw [←hqp,←mul_assoc,hQ,one_mul]
  have hbp : B*P=Q := by rw [←hqp,mul_assoc,hP,mul_one]
  have hbq : B*Q=P := by rw [←hpq,mul_assoc,hQ,mul_one]
  have hs : (P+Q+B)^2=3 • (1:R)+2 • (P+Q+B) := by
    simp only [sq,add_mul,mul_add,hP,hQ,hB,hpq,hqp,hpb,hbp,hqb,hbq]
    abel
  rw [pow_succ,hs,add_mul,smul_mul_assoc,smul_mul_assoc,one_mul,←sq,hs]
  abel

private theorem third_scale {n : ℕ} (a : ℝ) (h : PathShell n) :
    thirdMoment (a • h)=a^3*thirdMoment h := by
  have hg : pathHamiltonian (a • h)=a • pathHamiltonian h := (pathHamiltonianLM n).map_smul a h
  rw [thirdMoment,thirdMoment,hg,smul_pow,Matrix.trace_smul,Complex.real_smul,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- A single onsite Pauli has squared skewness zero. The normalized sum of
two neighboring onsite Paulis and their product has squared skewness 4/3. -/
theorem local_directions {n : ℕ} (e : Fin (n+1)) :
    ∃ u v : PathShell n, ‖u‖=1 ∧ ‖v‖=1 ∧ thirdMoment u=0 ∧ thirdMoment v^2=4/3 ∧
      outside e u=0 ∧ outside e v=0 := by
  let p : PathLabel n := leftSite e 0
  let q : PathLabel n := rightSite e 0
  let b : PathLabel n := Dephasing.PairedFields.ClockAdjustment.edgeLabel e 0 0
  have hpq : p≠q := fun he => e.castSucc_lt_succ.ne (congrArg Prod.fst (Sum.inl.inj he))
  have hpb : p≠b := Sum.inl_ne_inr
  have hqb : q≠b := Sum.inl_ne_inr
  let h := basis p+basis q+basis b
  have hn (j : PathLabel n) : ‖basis j‖=1 := by simp [basis]
  have hip {i j : PathLabel n} (hij : i≠j) : inner ℝ (basis i) (basis j)=0 := by
    rw [EuclideanSpace.inner_single_left]
    simp [basis,EuclideanSpace.single,hij]
  have hnorm : ‖h‖^2=3 := by
    dsimp only [h]
    rw [norm_add_sq_real,norm_add_sq_real,inner_add_left,hip hpq,hip hpb,hip hqb,hn,hn,hn]
    norm_num
  have hroot : ‖h‖=sqrt 3 := by rw [←hnorm,sqrt_sq (norm_nonneg _)]
  let a := (sqrt 3)⁻¹
  have ha : 0<sqrt (3:ℝ) := sqrt_pos.mpr (by norm_num)
  have hh : pathHamiltonian h=pauli p+pauli q+pauli b := by
    change pathHamiltonianLM n ((basis p+basis q)+basis b)=_
    simp only [map_add]
    exact congrArg₂ (·+·) (congrArg₂ (·+·) (generator_basis p) (generator_basis q)) (generator_basis b)
  have hprod : pauli p*pauli q=pauli b := (bond_product e 0 0).symm
  have hcomm : pauli q*pauli p=pauli b := by
    have hs (j : PathLabel n) : star (pauli j)=pauli j := (finitePauliMatrix_isHermitian _).eq
    simpa only [star_mul,hs] using congrArg star hprod
  have ht (i : PathLabel n) : (pauli i).trace=0 :=
    finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity i)
  have h3 : thirdMoment h=6 := by
    rw [thirdMoment,hh,triple_cube (finitePauliMatrix_mul_self _) (finitePauliMatrix_mul_self _)
      (finitePauliMatrix_mul_self _) hprod hcomm]
    simp only [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,ht,add_zero,smul_zero]
    have hc : (6:ℕ) • (Fintype.card (Fin (n+2)→Bool):ℂ)=((6*(2:ℝ)^(n+2):ℝ):ℂ) := by
      simp [nsmul_eq_mul]
    rw [hc,Complex.ofReal_re]
    exact mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num))
  refine ⟨basis p,a • h,hn p,?_,?_,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),hroot]
    exact inv_mul_cancel₀ ha.ne'
  · rw [thirdMoment,generator_basis,pow_succ,sq,finitePauliMatrix_mul_self,one_mul,ht]
    simp
  · rw [third_scale,h3]
    dsimp only [a]
    have hsq := sq_sqrt (by norm_num : (0:ℝ)≤3)
    field_simp
    nlinarith only [show (sqrt 3)^6=27 by calc
      _ = ((sqrt 3)^2)^3 := by ring
      _ = _ := by rw [hsq]; norm_num]
  · funext i
    change (basis p) i.val=0
    simp [basis,EuclideanSpace.single,p,i.property.1]
  · funext i
    change a*((basis p) i.val+(basis q) i.val+(basis b) i.val)=0
    simp [basis,EuclideanSpace.single,p,q,b,i.property.1,i.property.2.1,i.property.2.2]

#print axioms local_directions
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
