import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.QuadraticResponse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.PathConjugation

/-! # Variation of the quadratic trace under a single onsite field -/

open Matrix Finset Function
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
open private bond_product from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.PathConjugation
open private trace_local from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.ResponseWeights.PauliTrace
noncomputable section

abbrev leftSite {n : ℕ} (e : Fin (n+1)) (a : Fin 3) : PathLabel n := .inl (e.castSucc,a)
abbrev rightSite {n : ℕ} (e : Fin (n+1)) (b : Fin 3) : PathLabel n := .inl (e.succ,b)
abbrev edgeLabel {n : ℕ} (e : Fin (n+1)) (a b : Fin 3) : PathLabel n := .inr (e,(a,b))

private abbrev pauli {n : ℕ} (i : PathLabel n) := finitePauliMatrix (pathWord i)

private theorem generator_at {n : ℕ} (h : Coeff n) (p : PathLabel n) (x : ℝ) :
    (generator (update h p x)).val=(generator (update h p 0)).val+(x:ℂ) • pauli p := by
  change pathHamiltonian _=pathHamiltonian _+_
  rw [pathHamiltonian_eq_sum,pathHamiltonian_eq_sum]
  have hi (i : PathLabel n) : (((update h p x i:ℝ):ℂ) • pauli i) =
      (((update h p 0 i:ℝ):ℂ) • pauli i)+(if i=p then (x:ℂ) • pauli p else 0) := by
    by_cases he : i=p
    · subst i; simp
    · simp [he]
  change (∑ i, ((update h p x i:ℝ):ℂ) • pauli i)= (∑ i, ((update h p 0 i:ℝ):ℂ) • pauli i)+_
  simp only [hi,sum_add_distrib]
  simp

private theorem trace_generator_zero {n : ℕ} (h : Coeff n) : (generator h).val.trace=0 := by
  change (pathHamiltonian _).trace=0
  rw [pathHamiltonian_eq_sum,Matrix.trace_sum]
  exact sum_eq_zero fun l _ => by
    rw [Matrix.trace_smul,finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity l),smul_zero]

/-- Both cross terms in the square have the same trace against a commuting probe.
The pure onsite square disappears because every probe is traceless. -/
private theorem update_squareTrace {n : ℕ} (h : Coeff n) (p q : PathLabel n) (x : ℝ)
    (hpq : pauli q*pauli p=pauli p*pauli q) :
    squareTrace (update h p x) q=squareTrace (update h p 0) q+
      2*x*(((generator (update h p 0)).val*(pauli p*pauli q)).trace).re := by
  let A := (generator (update h p 0)).val
  let P := pauli p
  let Q := pauli q
  have hPP : P*P=1 := finitePauliMatrix_mul_self _
  have hQ : Q.trace=0 := finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity q)
  have htr : (P*A*Q).trace=(A*P*Q).trace := by
    rw [mul_assoc,Matrix.trace_mul_comm P (A*Q),mul_assoc,hpq,←mul_assoc]
  change (((generator (update h p x)).val^2*Q).trace).re=(A^2*Q).trace.re+_
  rw [generator_at]
  change (((A+(x:ℂ) • P)^2*Q).trace).re=_
  simp only [sq,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,
    hPP,one_mul,hQ,htr,Complex.add_re,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.zero_re]
  change _=(A*A*Q).trace.re+2*x*(A*(P*Q)).trace.re
  rw [← mul_assoc A P Q]
  ring

/-- The angular response determinant along an onsite resampling is quadratic.
Its leading coefficient is twice the adjacent bond coefficient times the register dimension. -/
theorem edge_response_polynomial {n : ℕ} (h : Coeff n) (e : Fin (n+1)) (a b : Fin 3) (x : ℝ) :
    let p := leftSite e a
    let q := rightSite e b
    let v := update h p x
    let y := update h p 0
    v p*squareTrace v q-v q*squareTrace v p =
      (2*(2:ℝ)^(n+2)*h (edgeLabel e a b))*x^2+squareTrace y q*x-h q*squareTrace y p := by
  intro p q v y
  have hqp : q≠p := fun he => e.castSucc_lt_succ.ne (congrArg Prod.fst (Sum.inl.inj he)).symm
  have hrp : edgeLabel e a b ≠ p := Sum.inr_ne_inl
  have hPQ : pauli p*pauli q=pauli (edgeLabel e a b) := (bond_product e a b).symm
  have hQP : pauli q*pauli p=pauli p*pauli q := by
    have h := congrArg star hPQ
    have hstar (i : PathLabel n) : star (pauli i)=pauli i := (finitePauliMatrix_isHermitian _).eq
    simp only [star_mul,hstar] at h
    exact h.trans hPQ.symm
  have hp : squareTrace v p=squareTrace y p := by
    rw [update_squareTrace h p p x rfl,finitePauliMatrix_mul_self,mul_one,trace_generator_zero,
      Complex.zero_re,mul_zero,add_zero]
  have hq := update_squareTrace h p q x hQP
  rw [hPQ] at hq
  have ht : (((generator y).val*pauli (edgeLabel e a b)).trace).re =
      (2:ℝ)^(n+2)*h (edgeLabel e a b) := by
    change (pathHamiltonian (WithLp.toLp 2 y)*finitePauliMatrix (pathWord (edgeLabel e a b))).trace.re=_
    rw [trace_local]
    change (2:ℝ)^(n+2)*update h p 0 (edgeLabel e a b)=_
    rw [update_of_ne hrp]
  change squareTrace v q=squareTrace y q+2*x*_ at hq
  rw [ht] at hq
  change update h p x p*squareTrace v q-update h p x q*squareTrace v p=_
  rw [update_self,update_of_ne hqp,hq,hp]
  ring

#print axioms edge_response_polynomial
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
