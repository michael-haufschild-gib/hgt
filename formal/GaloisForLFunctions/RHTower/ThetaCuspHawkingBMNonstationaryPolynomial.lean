import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryWeight

/-! Exact upper endpoint coefficients of the actual second and fourth source weights. -/
namespace RHTower.D4BMJointSource
open Complex Set
open scoped Polynomial BigOperators
noncomputable section
set_option autoImplicit false

def nonstationaryWeightFactor (Q : ℂ[X]) (j n : ℕ) : ℂ[X] :=
  Polynomial.X*(-(n+1:ℂ[X])*(2-Polynomial.X)*(2+3*Polynomial.X)*Q+
    (1-Polynomial.X)*((2-Polynomial.X)*(2+3*Polynomial.X)*Q.derivative+
      (12*Polynomial.X-3*(j:ℂ[X])*(2-Polynomial.X))*Q))

theorem nonstationaryWeightStep_factor (Q : ℂ[X]) (j n : ℕ) :
    nonstationaryWeightStep ((1-Polynomial.X)^(n+1)*Q) j =
      (1-Polynomial.X)^n*nonstationaryWeightFactor Q j n := by
  simp only [nonstationaryWeightStep,nonstationaryWeightFactor,Polynomial.derivative_mul,
    Polynomial.derivative_pow_succ,Polynomial.derivative_sub,Polynomial.derivative_one,
    Polynomial.derivative_X,zero_sub,Polynomial.C_add,Polynomial.C_eq_natCast,Polynomial.C_1]
  rw [pow_succ]
  ring

theorem nonstationaryWeightFactor_one (Q : ℂ[X]) (j n : ℕ) :
    (nonstationaryWeightFactor Q j n).eval 1 = -5*(n+1:ℂ)*Q.eval 1 := by
  norm_num [nonstationaryWeightFactor]
  ring

def nonstationaryPolynomial (n : ℕ) : ℕ → ℂ[X]
  | 0 => (1-Polynomial.X)^n
  | k+1 => nonstationaryWeightStep (nonstationaryPolynomial n k) (2*k)

/-- The recurrence removes exactly one upper endpoint zero at each step. -/
theorem nonstationaryPolynomial_factor (n k : ℕ) (hk : k ≤ n) :
    ∃ Q : ℂ[X], nonstationaryPolynomial n k=(1-Polynomial.X)^(n-k)*Q ∧
      Q.eval 1=∏ i ∈ Finset.range k, (-5*((n-i:ℕ):ℂ)) := by
  induction k generalizing n with
  | zero =>
    refine ⟨1,?_,?_⟩ <;> simp [nonstationaryPolynomial]
  | succ k ih =>
    obtain ⟨Q,hQ,hQ1⟩ := ih n (by omega)
    have hn : n-k=(n-(k+1))+1 := by omega
    refine ⟨nonstationaryWeightFactor Q (2*k) (n-(k+1)),?_,?_⟩
    · rw [nonstationaryPolynomial,hQ,hn,nonstationaryWeightStep_factor]
    · rw [nonstationaryWeightFactor_one,hQ1,Finset.prod_range_succ]
      have hc : ((n-(k+1)+1:ℕ):ℂ)=((n-k:ℕ):ℂ) := congrArg (fun m : ℕ => (m:ℂ)) hn.symm
      simp only [Nat.cast_add,Nat.cast_one] at hc
      rw [hc]
      ring

theorem nonstationaryPolynomial_one_eq_zero (n k : ℕ) (hk : k < n) :
    (nonstationaryPolynomial n k).eval 1 = 0 := by
  obtain ⟨Q,hQ,_⟩ := nonstationaryPolynomial_factor n k hk.le
  rw [hQ,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X]
  simp only [sub_self,zero_pow (by omega : n-k ≠ 0),zero_mul]

theorem nonstationaryPolynomial_one_leading (n : ℕ) :
    (nonstationaryPolynomial n n).eval 1 = ∏ i ∈ Finset.range n, (-5*((n-i:ℕ):ℂ)) := by
  obtain ⟨Q,hQ,hQ1⟩ := nonstationaryPolynomial_factor n n le_rfl
  rw [hQ,Nat.sub_self,pow_zero,one_mul,hQ1]

theorem nonstationaryPolynomial_second_leading : (nonstationaryPolynomial 2 2).eval 1=50 := by
  rw [nonstationaryPolynomial_one_leading]
  norm_num [Finset.prod_range_succ]

theorem nonstationaryPolynomial_fourth_leading : (nonstationaryPolynomial 4 4).eval 1=15000 := by
  rw [nonstationaryPolynomial_one_leading]
  norm_num [Finset.prod_range_succ]

end
end RHTower.D4BMJointSource
