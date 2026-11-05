import GaloisForLFunctions.FiniteFreeProbability.AdditiveConvolution
import GaloisForLFunctions.HTGeometry.JensenPolynomialSplits
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The Jensen dictionary of the finite free convolution

`p ⊞_d q` is the differential operator with symbol `S_q` applied to `p`, where `S_q` is the unique
symbol of degree `≤ d` with `S_q(D) X^d = q`. Symbols agreeing through degree `d` act equally on
polynomials of degree `≤ d`, so `⊞_d` is commutative with unit `X^d`.

The reversed Jensen polynomial of a power series `f` is `R_d(f) = f(D) X^d` (only the truncation
of `f` below degree `d + 1` enters). It is a ring map onto `(K[X]_{≤ d}, ⊞_d)`:

`R_d(f · g) = R_d(f) ⊞_d R_d(g)`.

Thus a multiplicative factorization of an entire function is the same thing, at every degree, as a
finite free factorization of its Jensen polynomials. Exponentials become translations,
`R_d(e^{cz}) = (X + c)^d`, and `⊞_d` against `R_d(g)` is the operator `g(D)` truncated at degree
`d`; for a Gaussian `g` this is the heat operator.
-/

open Polynomial Finset

namespace FiniteFreeProbability

noncomputable section

variable {K : Type*} [Field K]

/-- The constant-coefficient differential operator with symbol `h`. -/
def diffOp (h p : K[X]) : K[X] :=
  (aeval (derivative : Module.End K K[X]) h) p

theorem diffOp_eq_sum (h p : K[X]) {n : ℕ} (hn : h.natDegree < n) :
    diffOp h p = ∑ i ∈ range n, C (h.coeff i) * derivative^[i] p := by
  rw [diffOp, aeval_eq_sum_range' hn]
  simp [LinearMap.sum_apply, Module.End.pow_apply, smul_eq_C_mul]

theorem diffOp_mul (h₁ h₂ p : K[X]) : diffOp (h₁ * h₂) p = diffOp h₁ (diffOp h₂ p) := by
  simp [diffOp, Module.End.mul_apply]

theorem diffOp_comm (h₁ h₂ p : K[X]) : diffOp h₁ (diffOp h₂ p) = diffOp h₂ (diffOp h₁ p) := by
  rw [← diffOp_mul, mul_comm, diffOp_mul]

theorem natDegree_diffOp_le (h p : K[X]) : (diffOp h p).natDegree ≤ p.natDegree := by
  rw [diffOp_eq_sum h p (Nat.lt_succ_self _)]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact (natDegree_C_mul_le _ _).trans ((natDegree_iterate_derivative p i).trans (Nat.sub_le _ _))

/-- Symbols agreeing through degree `d` act equally on polynomials of degree `≤ d`. -/
theorem diffOp_congr {h h' p : K[X]} {d : ℕ} (hp : p.natDegree ≤ d)
    (hh : ∀ i ≤ d, h.coeff i = h'.coeff i) : diffOp h p = diffOp h' p := by
  set n := max (max h.natDegree h'.natDegree) d + 1
  rw [diffOp_eq_sum h p (n := n) (by omega), diffOp_eq_sum h' p (n := n) (by omega)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hid : i ≤ d
  · rw [hh i hid]
  · rw [iterate_derivative_eq_zero (by omega)]; simp

theorem diffOp_X_pow (h : K[X]) (d : ℕ) :
    diffOp h (X ^ d) = ∑ i ∈ range (d + 1), C (h.coeff i * (d.descFactorial i : K)) * X ^ (d - i) := by
  rw [diffOp_congr (h' := ∑ i ∈ range (d + 1), C (h.coeff i) * X ^ i) (natDegree_X_pow_le d)
    (fun i hi => by
      rw [finsetSum_coeff, Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [coeff_X_pow, Ne.symm hj]
      · intro hi'; exact absurd (Finset.mem_range.2 (by omega)) hi')]
  rw [diffOp_eq_sum _ _ (n := d + 1)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [iterate_derivative_X_pow_eq_C_mul, finsetSum_coeff, Finset.sum_eq_single i]
    · simp only [coeff_C_mul, coeff_X_pow, if_true, mul_one, C_mul]
      ring
    · intro j _ hj; simp [coeff_X_pow, Ne.symm hj]
    · intro h0; exact absurd hi h0
  · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i hi => ?_) (Nat.lt_succ_self d)
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

/-- The symbol `S_q = Σ_{j ≤ d} ((d-j)!/d!) q_{d-j} X^j` of `q` at degree `d`. -/
def ffSymbol (d : ℕ) (q : K[X]) : K[X] :=
  ∑ j ∈ range (d + 1), C (q.coeff (d - j) * ((d - j).factorial : K) / (d.factorial : K)) * X ^ j

theorem coeff_ffSymbol (d : ℕ) (q : K[X]) (j : ℕ) :
    (ffSymbol d q).coeff j =
      if j ≤ d then q.coeff (d - j) * ((d - j).factorial : K) / (d.factorial : K) else 0 := by
  rw [ffSymbol, finsetSum_coeff]
  split_ifs with hj
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [coeff_X_pow, Ne.symm hij]
    · intro h0; exact absurd (Finset.mem_range.2 (by omega)) h0
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : i ≠ j := by have := Finset.mem_range.1 hi; omega
    simp [coeff_X_pow, Ne.symm this]

theorem natDegree_ffSymbol_le (d : ℕ) (q : K[X]) : (ffSymbol d q).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))

/-- `p ⊞_d q = S_q(D) p`. -/
theorem ffConv_eq_diffOp (d : ℕ) (p q : K[X]) : ffConv d p q = diffOp (ffSymbol d q) p := by
  rw [diffOp_eq_sum _ _ (Nat.lt_succ_of_le (natDegree_ffSymbol_le d q)), ffConv]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [coeff_ffSymbol, if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]

/-- The reversed Jensen polynomial `R_d(f) = f(D) X^d` of a power series. -/
def jensenRev (d : ℕ) (f : PowerSeries K) : K[X] :=
  diffOp (PowerSeries.trunc (d + 1) f) (X ^ d)

theorem natDegree_jensenRev_le (d : ℕ) (f : PowerSeries K) : (jensenRev d f).natDegree ≤ d :=
  (natDegree_diffOp_le _ _).trans (natDegree_X_pow_le d)

/-- The coefficient form `R_d(f) = Σ_{i ≤ d} d^{(i)} f_i X^{d-i}`. -/
theorem jensenRev_eq_sum (d : ℕ) (f : PowerSeries K) :
    jensenRev d f =
      ∑ i ∈ range (d + 1), C (PowerSeries.coeff i f * (d.descFactorial i : K)) * X ^ (d - i) := by
  rw [jensenRev, diffOp_X_pow]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [PowerSeries.coeff_trunc, if_pos (Finset.mem_range.1 hi)]

section CharZero

variable [CharZero K]

/-- The symbol of `q` reproduces `q`: `S_q(D) X^d = q`. -/
theorem diffOp_ffSymbol_X_pow {d : ℕ} {q : K[X]} (hq : q.natDegree ≤ d) :
    diffOp (ffSymbol d q) (X ^ d) = q := by
  have hfac : (d.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [diffOp_X_pow]
  have hterm : ∀ i ∈ range (d + 1), C ((ffSymbol d q).coeff i * (d.descFactorial i : K)) *
      X ^ (d - i) = C (q.coeff (d - i)) * X ^ (d - i) := by
    intro i hi
    have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hdesc : ((d - i).factorial : K) * (d.descFactorial i : K) = d.factorial := by
      exact_mod_cast Nat.factorial_mul_descFactorial hi'
    rw [coeff_ffSymbol, if_pos hi']
    congr 2
    calc q.coeff (d - i) * ((d - i).factorial : K) / (d.factorial : K) * (d.descFactorial i : K)
        = q.coeff (d - i) * (((d - i).factorial : K) * (d.descFactorial i : K)) /
          (d.factorial : K) := by ring
      _ = q.coeff (d - i) := by rw [hdesc, mul_div_assoc, div_self hfac, mul_one]
  rw [Finset.sum_congr rfl hterm]
  have hrefl := Finset.sum_range_reflect (fun j => C (q.coeff j) * X ^ j) (d + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  rw [hrefl]
  conv_rhs => rw [as_sum_range' q (d + 1) (by omega)]
  simp only [← C_mul_X_pow_eq_monomial]

/-- The symbol of `h(D) X^d` agrees with `h` through degree `d`. -/
theorem coeff_ffSymbol_diffOp_X_pow (h : K[X]) {d i : ℕ} (hi : i ≤ d) :
    (ffSymbol d (diffOp h (X ^ d))).coeff i = h.coeff i := by
  have hfac : (d.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hdesc : ((d - i).factorial : K) * (d.descFactorial i : K) = d.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hi
  rw [coeff_ffSymbol, if_pos hi, diffOp_X_pow, finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    calc h.coeff i * (d.descFactorial i : K) * ((d - i).factorial : K) / (d.factorial : K)
        = h.coeff i * (((d - i).factorial : K) * (d.descFactorial i : K)) /
          (d.factorial : K) := by ring
      _ = h.coeff i := by rw [hdesc, mul_div_assoc, div_self hfac, mul_one]
  · intro j hj hji
    have hj' : j ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  · intro h0; exact absurd (Finset.mem_range.2 (by omega)) h0

/-- Every polynomial of degree `≤ d` is its own symbol applied to `X^d`. -/
theorem ffConv_X_pow_left {d : ℕ} {q : K[X]} (hq : q.natDegree ≤ d) : ffConv d (X ^ d) q = q := by
  rw [ffConv_eq_diffOp, diffOp_ffSymbol_X_pow hq]

/-- `X^d` is the unit of `⊞_d`. -/
theorem ffConv_X_pow_right {d : ℕ} {p : K[X]} (hp : p.natDegree ≤ d) : ffConv d p (X ^ d) = p := by
  rw [ffConv_eq_diffOp, diffOp_congr (h' := 1) hp]
  · simp [diffOp]
  · intro i hi
    rw [coeff_ffSymbol, if_pos hi, coeff_X_pow, coeff_one]
    by_cases h0 : i = 0
    · subst h0; simp [Nat.factorial_ne_zero]
    · rw [if_neg (by omega), if_neg h0]; ring

/-- `⊞_d` against `h(D) X^d` is the operator `h(D)`. -/
theorem ffConv_diffOp_X_pow_right {d : ℕ} {p : K[X]} (hp : p.natDegree ≤ d) (h : K[X]) :
    ffConv d p (diffOp h (X ^ d)) = diffOp h p := by
  rw [ffConv_eq_diffOp]
  exact diffOp_congr hp fun i hi => coeff_ffSymbol_diffOp_X_pow h hi

/-- **Commutativity of `⊞_d`.** -/
theorem ffConv_comm {d : ℕ} {p q : K[X]} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    ffConv d p q = ffConv d q p := by
  rw [ffConv_eq_diffOp, ffConv_eq_diffOp]
  conv_lhs => rw [← diffOp_ffSymbol_X_pow hp]
  conv_rhs => rw [← diffOp_ffSymbol_X_pow hq]
  exact diffOp_comm _ _ _

/-- **The Jensen dictionary.** Reversed Jensen polynomials turn products into `⊞_d`:
`R_d(f g) = R_d(f) ⊞_d R_d(g)`. -/
theorem jensenRev_mul (d : ℕ) (f g : PowerSeries K) :
    jensenRev d (f * g) = ffConv d (jensenRev d f) (jensenRev d g) := by
  rw [show jensenRev d g = diffOp (PowerSeries.trunc (d + 1) g) (X ^ d) from rfl,
    ffConv_diffOp_X_pow_right (natDegree_jensenRev_le d f), jensenRev, jensenRev, ← diffOp_mul,
    mul_comm (PowerSeries.trunc (d + 1) g)]
  refine diffOp_congr (natDegree_X_pow_le d) fun i hi => ?_
  rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le hi),
    PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g (Nat.lt_succ_of_le hi),
    ← Polynomial.coe_mul, Polynomial.coeff_coe]

/-- `⊞_d` against a Jensen polynomial is its truncated symbol acting as a differential operator. -/
theorem ffConv_jensenRev_right {d : ℕ} {p : K[X]} (hp : p.natDegree ≤ d) (g : PowerSeries K) :
    ffConv d p (jensenRev d g) = diffOp (PowerSeries.trunc (d + 1) g) p :=
  ffConv_diffOp_X_pow_right hp _

/-- Exponentials are translations: `R_d(e^{cz}) = (X + c)^d`. -/
theorem jensenRev_exp (d : ℕ) (c : K) :
    jensenRev d (PowerSeries.mk fun k => c ^ k / (k.factorial : K)) = (X + C c) ^ d := by
  rw [jensenRev_eq_sum, add_pow,
    ← Finset.sum_range_reflect (fun m => X ^ m * C c ^ (d - m) * (d.choose m : K[X])) (d + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hfac : (i.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hdesc : (d.descFactorial i : K) = (i.factorial : K) * (d.choose i : K) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose d i
  have hc : c ^ i / (i.factorial : K) * (d.descFactorial i : K) = c ^ i * (d.choose i : K) := by
    rw [hdesc]; field_simp
  simp only [PowerSeries.coeff_mk, Nat.add_sub_cancel, show d - (d - i) = i by omega,
    Nat.choose_symm hi', hc, map_mul, map_pow, map_natCast]
  ring

end CharZero

/-- Over `ℝ`, `diffOp` is the corpus operator `diffOpApply`. -/
theorem diffOp_eq_diffOpApply (h p : ℝ[X]) :
    diffOp h p = GaloisForLFunctions.HTGeometry.diffOpApply h p := rfl

/-- Over `ℝ`, `jensenRev` is the corpus reversed Jensen polynomial `jensenReverse`. -/
theorem jensenRev_mk_eq_jensenReverse (c : ℕ → ℝ) (d : ℕ) :
    jensenRev d (PowerSeries.mk c) = GaloisForLFunctions.HTGeometry.jensenReverse c d := by
  rw [jensenRev_eq_sum, GaloisForLFunctions.HTGeometry.jensenReverse]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_mk]

end

end FiniteFreeProbability
