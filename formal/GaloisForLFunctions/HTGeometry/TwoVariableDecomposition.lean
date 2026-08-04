import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative

/-!
# Two-variable polynomials as polynomials in the second variable

An order-zero algebraic differential equation is a two-variable polynomial relation between `z` and
`g z`.  Reading it as a polynomial in the second variable, with coefficients polynomial in the first,
is what lets the algebraic root estimate bound `g`.

The decomposition is the fibrewise grouping of the support by the second exponent — the same device
used for the constituents' equations.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open scoped Classical in
/-- The coefficient of `u^k` in a two-variable polynomial, as a polynomial in the first variable. -/
noncomputable def twoVarCoeff (P : MvPolynomial (Fin 2) ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ m ∈ P.support.filter (fun m => m 1 = k),
    Polynomial.C (MvPolynomial.coeff m P) * Polynomial.X ^ (m 0)

open scoped Classical in
/-- **The two-variable decomposition.**  Evaluating a two-variable polynomial is the same as
evaluating the polynomial in the second variable whose coefficients are `twoVarCoeff`. -/
theorem eval_eq_sum_twoVarCoeff (P : MvPolynomial (Fin 2) ℂ) (d : ℕ)
    (hd : ∀ m ∈ P.support, m 1 ∈ Finset.range (d + 1)) (z u : ℂ) :
    MvPolynomial.eval (fun i : Fin 2 => ![z, u] i) P
      = ∑ k ∈ Finset.range (d + 1), (twoVarCoeff P k).eval z * u ^ k := by
  have hfiber := Finset.sum_fiberwise_of_maps_to (s := P.support)
    (t := Finset.range (d + 1)) (g := fun m : Fin 2 →₀ ℕ => m 1) hd
    (f := fun m : Fin 2 →₀ ℕ => MvPolynomial.coeff m P * (z ^ (m 0) * u ^ (m 1)))
  have hpull : ∀ k ∈ Finset.range (d + 1),
      (twoVarCoeff P k).eval z * u ^ k
      = ∑ m ∈ P.support.filter (fun m => m 1 = k),
          MvPolynomial.coeff m P * (z ^ (m 0) * u ^ (m 1)) := by
    intro k _
    rw [twoVarCoeff, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      (Finset.mem_filter.mp hm).2]
    ring
  rw [Finset.sum_congr rfl hpull, hfiber, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl ?_
  intro m _
  congr 1
  simp [Fin.prod_univ_two]

/-! ## Order-zero relations in coefficient form -/

open scoped Classical in
/-- **An order-zero equation, in coefficient form.**  A two-variable relation `P(z, g z) = 0` is a
polynomial relation in `g z` with coefficients polynomial in `z`. -/
theorem exists_coeff_relation_of_order_zero {g : ℂ → ℂ}
    (h : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder g 0) :
    ∃ (d : ℕ) (a : ℕ → Polynomial ℂ),
      ∀ z : ℂ, ∑ k ∈ Finset.range (d + 1), (a k).eval z * (g z) ^ k = 0 := by
  obtain ⟨P, _, hPz⟩ := h
  set d : ℕ := P.support.sup (fun m => m 1) with hdef
  have hd : ∀ m ∈ P.support, m 1 ∈ Finset.range (d + 1) := by
    intro m hm
    refine Finset.mem_range.mpr ?_
    have hle : m 1 ≤ d := by
      rw [hdef]
      exact Finset.le_sup (f := fun m : Fin 2 →₀ ℕ => m 1) hm
    omega
  refine ⟨d, fun k => twoVarCoeff P k, ?_⟩
  intro z
  have hvec : (Fin.cons z fun j : Fin 1 => iteratedDeriv (j : ℕ) g z)
      = fun i : Fin 2 => ![z, g z] i := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · rw [Fin.cons_succ]
      fin_cases i
      simp [iteratedDeriv_zero]
  have hbase := hPz z
  rw [hvec] at hbase
  rw [← eval_eq_sum_twoVarCoeff P d hd z (g z)]
  exact hbase

/-! ## Coefficient identification

The nondegeneracy of the coefficient form needs to see the coefficients of `twoVarCoeff` as
coefficients of the original two-variable polynomial.  Exponent vectors on `Fin 2` are determined by
their two values, which is what makes the fibre sum collapse to a single term. -/

/-- The exponent vector on `Fin 2` with the given entries. -/
noncomputable def fin2Exp (j k : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j + Finsupp.single 1 k

@[simp] theorem fin2Exp_zero (j k : ℕ) : fin2Exp j k 0 = j := by
  simp [fin2Exp]

@[simp] theorem fin2Exp_one (j k : ℕ) : fin2Exp j k 1 = k := by
  simp [fin2Exp]

/-- An exponent vector on `Fin 2` is determined by its two entries. -/
theorem fin2Exp_eq (m : Fin 2 →₀ ℕ) : m = fin2Exp (m 0) (m 1) := by
  refine Finsupp.ext ?_
  intro i
  fin_cases i <;> simp

/-- Two exponent vectors on `Fin 2` agreeing in both entries are equal. -/
theorem fin2_ext {m m' : Fin 2 →₀ ℕ} (h0 : m 0 = m' 0) (h1 : m 1 = m' 1) : m = m' := by
  rw [fin2Exp_eq m, fin2Exp_eq m', h0, h1]

open scoped Classical in
/-- **The coefficients of `twoVarCoeff` are coefficients of the original polynomial.** -/
theorem coeff_twoVarCoeff (P : MvPolynomial (Fin 2) ℂ) (j k : ℕ) :
    Polynomial.coeff (twoVarCoeff P k) j = MvPolynomial.coeff (fin2Exp j k) P := by
  rw [twoVarCoeff, Polynomial.finsetSum_coeff]
  have hterm : ∀ m ∈ P.support.filter (fun m => m 1 = k),
      Polynomial.coeff (Polynomial.C (MvPolynomial.coeff m P) * Polynomial.X ^ (m 0)) j
        = if m = fin2Exp j k then MvPolynomial.coeff m P else 0 := by
    intro m hm
    have hm1 : m 1 = k := (Finset.mem_filter.mp hm).2
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hj : m 0 = j
    · have hmeq : m = fin2Exp j k := fin2_ext (by simpa using hj) (by simpa using hm1)
      rw [if_pos hj.symm, if_pos hmeq, mul_one]
    · have hmne : m ≠ fin2Exp j k := by
        intro hcon
        exact hj (by rw [hcon]; simp)
      rw [if_neg (fun hcon => hj hcon.symm), if_neg hmne, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hmem : fin2Exp j k ∈ P.support.filter (fun m => m 1 = k)
  · rw [Finset.sum_ite_eq' (P.support.filter (fun m => m 1 = k)) (fin2Exp j k)
      (fun m => MvPolynomial.coeff m P)]
    rw [if_pos hmem]
  · rw [Finset.sum_ite_eq' (P.support.filter (fun m => m 1 = k)) (fin2Exp j k)
      (fun m => MvPolynomial.coeff m P), if_neg hmem]
    by_contra hne
    exact hmem (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr (Ne.symm hne), by simp⟩)

open scoped Classical in
/-- **An order-zero equation in nondegenerate coefficient form.**  Some coefficient is nonzero, so
the relation is not vacuous and the algebraic root estimate applies. -/
theorem exists_nonzero_coeff_relation_of_order_zero {g : ℂ → ℂ}
    (h : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder g 0) :
    ∃ (d : ℕ) (a : ℕ → Polynomial ℂ), (∃ k, k ≤ d ∧ a k ≠ 0) ∧
      ∀ z : ℂ, ∑ k ∈ Finset.range (d + 1), (a k).eval z * (g z) ^ k = 0 := by
  obtain ⟨P, hP0, hPz⟩ := h
  set d : ℕ := P.support.sup (fun m => m 1) with hdef
  have hd : ∀ m ∈ P.support, m 1 ∈ Finset.range (d + 1) := by
    intro m hm
    refine Finset.mem_range.mpr ?_
    have hle : m 1 ≤ d := by
      rw [hdef]
      exact Finset.le_sup (f := fun m : Fin 2 →₀ ℕ => m 1) hm
    omega
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hP0
  have hmle : m 1 ≤ d := by
    have := hd m (MvPolynomial.mem_support_iff.mpr hm)
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
  have hne : twoVarCoeff P (m 1) ≠ 0 := by
    intro hcon
    apply hm
    have hcoef := coeff_twoVarCoeff P (m 0) (m 1)
    rw [hcon, Polynomial.coeff_zero] at hcoef
    rw [fin2Exp_eq m]
    exact hcoef.symm
  refine ⟨d, fun k => twoVarCoeff P k, ⟨m 1, hmle, hne⟩, ?_⟩
  intro z
  have hvec : (Fin.cons z fun j : Fin 1 => iteratedDeriv (j : ℕ) g z)
      = fun i : Fin 2 => ![z, g z] i := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · rw [Fin.cons_succ]
      fin_cases i
      simp [iteratedDeriv_zero]
  have hbase := hPz z
  rw [hvec] at hbase
  rw [← eval_eq_sum_twoVarCoeff P d hd z (g z)]
  exact hbase

end GaloisForLFunctions.HTGeometry
