import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution.Variation

/-! # Four reflected branches of a finite energy spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder

open Filter Finset Real
open scoped Topology

variable {I : Type*} [Fintype I]

abbrev Four (I : Type*) := (I ⊕ I) ⊕ (I ⊕ I)

/-- Two shifted copies and two reflected copies, with all states retained. -/
def branches (E : I → ℝ) (h : ℝ) : Four I → ℝ :=
  Sum.elim (Sum.elim (fun i => E i+h) (fun i => E i-h))
    (Sum.elim (fun i => -E i) (fun i => -E i))

theorem centered_branches (E : I → ℝ) (h : ℝ) : centered (branches E h)=branches E h := by
  apply centered_eq_of_sum_zero
  simp only [branches,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_add_distrib,
    sum_sub_distrib,sum_neg_distrib]
  ring

/-- The multiplier is a square divided by a strictly positive exponential. -/
def multiplier (h t : ℝ) := (exp (t*h)-1)^2/exp (t*h)

theorem branch_response (E : I → ℝ) (h t : ℝ) :
    oddTrace (branches E h) t=multiplier h t*oddTrace E t := by
  have alg (u : ℝ) :
      (oddTerm t (u+h)+oddTerm t (u-h))+(oddTerm t (-u)+oddTerm t (-u))=
      multiplier h t*oddTerm t u := by
    simp only [oddTerm,multiplier,mul_add,mul_sub,neg_mul,mul_neg,neg_neg,
      exp_add,exp_sub,exp_neg]
    field_simp
    ring
  rw [oddTrace,branches,Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,oddTrace,mul_sum,←sum_add_distrib]
  exact sum_congr rfl fun i _ => alg (E i)

theorem multiplier_pos {h t : ℝ} (ht : t≠0) (hh : h≠0) : 0 < multiplier h t := by
  have ne : exp (t*h)-1≠0 := sub_ne_zero.mpr fun z => mul_ne_zero ht hh ((exp_eq_one_iff _).mp z)
  exact div_pos (sq_pos_of_ne_zero ne) (exp_pos _)

/-- Two extra orders are contributed at zero, and their scale is the
square of the step in energy. -/
theorem multiplier_limit (h : ℝ) : Tendsto (fun t => multiplier h t/t^2) (𝓝[≠] 0) (𝓝 (h^2)) := by
  have lin : HasDerivAt (fun t : ℝ => t*h) h 0 := by
    simpa only [id_eq,one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const h
  have num : Tendsto (fun t : ℝ => (exp (t*h)-1)/t) (𝓝[≠] 0) (𝓝 h) := by
    simpa only [zero_add,zero_mul,exp_zero,one_mul,smul_eq_mul,div_eq_inv_mul] using
      lin.exp.tendsto_slope_zero
  have ex : Tendsto (fun t : ℝ => exp (t*h)) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [zero_mul,exp_zero] using lin.exp.continuousAt.continuousWithinAt.tendsto
  have lim := (num.pow 2).div ex one_ne_zero
  simpa only [Pi.div_def,div_one,div_pow,multiplier,div_div, mul_comm (exp _) ] using lim

/-- Every nonzero order of contact at zero increases by two with the
same set of nonzero ties. -/
theorem branch_leading (E : I → ℝ) (h : ℝ) (m : ℕ) (c : ℝ)
    (lim : Tendsto (fun t => oddTrace E t/t^m) (𝓝[≠] 0) (𝓝 c)) :
    Tendsto (fun t => oddTrace (branches E h) t/t^(m+2)) (𝓝[≠] 0) (𝓝 (h^2*c)) := by
  apply ((multiplier_limit h).mul lim).congr' (Eventually.of_forall fun t => ?_)
  rw [branch_response,pow_add,div_mul_div_comm,mul_comm (t^2)]

/-- At any nonzero damping the multiplier is a smooth unit. In particular
every finite order and every nonzero leading coefficient transfers. -/
theorem branch_at (E : I → ℝ) (h a : ℝ) (m : ℕ) (c : ℝ)
    (lim : Tendsto (fun t => oddTrace E t/(t-a)^m) (𝓝[≠] a) (𝓝 c)) :
    Tendsto (fun t => oddTrace (branches E h) t/(t-a)^m) (𝓝[≠] a)
      (𝓝 (multiplier h a*c)) := by
  have ce : Continuous (fun t : ℝ => exp (t*h)) := (continuous_id.mul_const h).rexp
  have cont : Continuous (multiplier h) := ((ce.sub continuous_const).pow 2).div ce (fun _ => exp_ne_zero _)
  have factor : Tendsto (multiplier h) (𝓝[≠] a) (𝓝 (multiplier h a)) :=
    cont.continuousAt.continuousWithinAt.tendsto
  simpa only [branch_response,mul_div_assoc] using factor.mul lim

#print axioms branch_at
#print axioms centered_branches
#print axioms branch_response
#print axioms multiplier_pos
#print axioms multiplier_limit
#print axioms branch_leading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder
