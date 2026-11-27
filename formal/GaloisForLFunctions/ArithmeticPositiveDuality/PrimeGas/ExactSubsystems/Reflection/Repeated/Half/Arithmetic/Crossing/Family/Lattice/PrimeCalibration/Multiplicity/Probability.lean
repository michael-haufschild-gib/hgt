import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Counting

/-! # Symmetric polynomial of the normalized probabilities for an even packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Finset Real

variable {I : Type*} [Fintype I]

/-- The elementary symmetric polynomial immediately below the top degree. -/
def cofactorSum (P : I → ℝ) : ℝ := by classical exact ∑ i, ∏ j ∈ univ.erase i, P j

private theorem cofactor_eq (P : I → ℝ) (pos : ∀ i, 0<P i) :
    cofactorSum P=(∏ j, P j)*∑ i, (P i)⁻¹ := by
  classical
  rw [mul_sum,cofactorSum]
  apply sum_congr rfl
  intro i _
  rw [←prod_erase_mul _ _ (mem_univ i),mul_assoc,mul_inv_cancel₀ (pos i).ne',mul_one]

/-- For any positive normalized law on an even number of states, the
order-one reflection test is a symmetric polynomial equality. -/
theorem even_probability_law [Nonempty I] (P : I → ℝ) (pos : ∀ i, 0<P i)
    (mass : ∑ i, P i=1) (m : ℕ) (size : Fintype.card I=2*(m+1)) :
    lawOrder P 1 ↔ (cofactorSum P)^(m+1)=(∏ i, P i)^m := by
  let E := centered (Observation.information P)
  let g := exp (-meanEnergy (Observation.information P))
  let D := ∏ i, P i
  let A := ∑ i, (P i)⁻¹
  have gp : 0<g := exp_pos _
  have dp : 0<D := prod_pos (fun i _ => pos i)
  have ap : 0≤A := sum_nonneg fun i _ => (inv_pos.mpr (pos i)).le
  have gpow : g^(Fintype.card I)=D := by
    have ne : (Fintype.card I : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [←exp_nat_mul]
    change exp ((Fintype.card I : ℝ)*(-((∑ i, -log (P i))/Fintype.card I)))=D
    rw [sum_neg_distrib,neg_div,neg_neg,mul_comm,div_mul_cancel₀ _ ne,exp_sum]
    exact prod_congr rfl fun i _ => exp_log (pos i)
  have forward (i : I) : exp (E i)=(P i)⁻¹*g := by
    change exp (-log (P i)-meanEnergy (Observation.information P))=_
    rw [sub_eq_add_neg,exp_add,exp_neg,exp_log (pos i)]
  have reverse (i : I) : exp (-E i)=P i*g⁻¹ := by
    rw [exp_neg,forward,mul_inv,inv_inv]
  rw [lawOrder,agrees_odd]
  change (∑ i, oddTerm 1 (E i))=0 ↔ _
  simp only [oddTerm,one_mul,neg_one_mul,forward,reverse,sum_sub_distrib,←sum_mul,mass,one_mul,sub_eq_zero]
  change A*g=g⁻¹ ↔ _
  have balance : A*g=g⁻¹ ↔ g^2*A=1 := by
    constructor
    · intro h
      calc _ = (A*g)*g := by ring
           _ = 1 := by rw [h,inv_mul_cancel₀ gp.ne']
    · intro h
      apply mul_right_cancel₀ gp.ne'
      calc (A*g)*g=g^2*A := by ring
           _ = g⁻¹*g := by rw [h,inv_mul_cancel₀ gp.ne']
  have powEquiv := (pow_left_inj₀ (mul_nonneg (sq_nonneg g) ap) zero_le_one (Nat.succ_ne_zero m)).symm
  rw [balance,powEquiv,mul_pow,←pow_mul,←size,gpow,one_pow,cofactor_eq P pos]
  change D*A^(m+1)=1 ↔ (D*A)^(m+1)=D^m
  have fac : (D*A)^(m+1)=D^m*(D*A^(m+1)) := by rw [mul_pow,pow_succ D]; ring
  rw [fac]
  constructor
  · intro h; rw [h,mul_one]
  · intro h
    exact mul_left_cancel₀ (pow_ne_zero _ dp.ne') (by simpa only [mul_one] using h : D^m*(D*A^(m+1))=D^m*1)

#print axioms even_probability_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
