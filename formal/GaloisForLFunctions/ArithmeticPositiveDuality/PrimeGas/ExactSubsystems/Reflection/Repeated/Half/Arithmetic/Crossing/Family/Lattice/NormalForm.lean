import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Prescribe

/-! # Unique polynomial normal form for centered integer heat-trace differences -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice

open Finset Real Polynomial

private theorem chebyshev_term (t : ℝ) (k : ℤ) :
    oddTerm t (k : ℝ) =
      (exp t-exp (-t))*aeval (coordinate t) (Chebyshev.S ℤ (k-1)) := by
  have y : coordinate t=2*cosh t := by rw [coordinate,cosh_eq]; ring
  have eval : aeval (coordinate t) (Chebyshev.S ℤ (k-1)) =
      (Chebyshev.S ℝ (k-1)).eval (2*cosh t) := by
    rw [aeval_def,eval₂_eq_eval_map,Chebyshev.map_S,y]
  have trig := Chebyshev.S_two_mul_real_cosh t (k-1)
  rw [eval]
  have h : (Chebyshev.S ℝ (k-1)).eval (2*cosh t) * sinh t = sinh ((k : ℝ)*t) := by
    simpa only [Int.cast_sub,Int.cast_one,sub_add_cancel] using trig
  rw [sinh_eq,sinh_eq] at h
  unfold oddTerm
  rw [neg_mul,mul_comm t (k : ℝ)]
  linear_combination -2*h

private theorem canonical {n : ℕ} (k : Fin n → ℤ) (mean : ∑ i, k i=0) :
    ∃ Q : ℤ[X], ∀ t : ℝ, trace k t=base t*aeval (coordinate t) Q := by
  let R : ℤ[X] := ∑ i, Chebyshev.S ℤ (k i-1)
  have root : R.IsRoot 2 := by
    simp only [R,Polynomial.IsRoot,eval_finsetSum,Chebyshev.S_eval_two,Int.cast_id,sub_add_cancel,mean]
  obtain ⟨Q,div⟩ := dvd_iff_isRoot.mpr root
  refine ⟨Q,fun t => ?_⟩
  have reading : trace k t=(exp t-exp (-t))*aeval (coordinate t) R := by
    simp only [trace,oddTrace,chebyshev_term,R,map_sum,mul_sum]
  rw [reading,div,map_mul,map_sub,aeval_X,aeval_C,map_ofNat,base]
  ring

/-- The class of all attainable centered integer heat-trace differences is
represented without redundancy by the integer polynomial ring. -/
theorem realized_iff_unique (f : ℝ → ℝ) :
    Realized f ↔ ∃! Q : ℤ[X], ∀ t : ℝ, f t=base t*aeval (coordinate t) Q := by
  constructor
  · rintro ⟨n,k,mean,trace_eq⟩
    obtain ⟨Q,canon⟩ := canonical k mean
    have eq (t : ℝ) := (trace_eq t).symm.trans (canon t)
    refine ⟨Q,eq,fun P hp => ?_⟩
    by_contra ne
    obtain ⟨t,ht,detect⟩ := exists_detecting_coordinate (sub_ne_zero.mpr ne)
    have same := mul_left_cancel₀ (base_pos ht).ne' ((hp t).symm.trans (eq t))
    exact detect (by rw [map_sub,same,sub_self])
  · rintro ⟨Q,eq,_⟩
    rw [funext eq]
    exact polynomial_realized Q

#print axioms realized_iff_unique

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice
