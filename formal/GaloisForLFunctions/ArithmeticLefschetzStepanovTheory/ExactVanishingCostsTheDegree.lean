import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheStepanovCountOfTheClosedPoints

/-!
# Exact vanishing costs the degree

The norm amplifier turns smallness into exact vanishing at closed torsion points to every uniform
order (`vanishesToOrder_of_small`). This file prices that order. Over `𝔽_q` Stepanov's auxiliary
vanishes to order `p^μ` at the cost of one condition, because `p^μ`-th powers have vanishing
derivatives; without inseparability the order of a polynomial at any point is at most its degree.

* **Order at a point is at most the total degree** (`le_totalDegree_of_vanishesToOrder`). If all
  partial derivatives of order `< J` of a nonzero integer polynomial vanish at a point of `ℂ^σ`,
  then `J ≤ deg F`: derivatives lower the degree (`totalDegree_pderiv_lt`), and an integer
  polynomial with all partial derivatives zero is constant (`eq_C_of_forall_pderiv_eq_zero`).
* **The degree is at most `log N/log 2`** (`two_pow_totalDegree_le_length`): every monomial
  `u^α` of a `P`-smooth auxiliary is an integer `Π p^{α_p} ≥ 2^{|α|}`.
* **Exact order `J` at any torus point needs length `2^J`** (`two_pow_le_length_of_vanishesToOrder`).

So exactness at the torsion — the one place where `ℤ` has an exact Frobenius — is paid in length
like vanishing at a point of `𝔸^n` over a field of characteristic zero: one order per unit of
`log₂ N`. The cheap orders of Stepanov's count are exactly the inseparable ones, and the
archimedean place has none.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {σ : Type*}

/-- The degree `|s| = Σ_i s_i` of a monomial. -/
theorem sum_add_single (s : σ →₀ ℕ) (i : σ) :
    ((s + Finsupp.single i 1).sum fun _ e => e) = (s.sum fun _ e => e) + 1 := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

/-- **Derivatives lower the degree.** -/
theorem totalDegree_pderiv_lt (F : MvPolynomial σ ℤ) (i : σ) (h : MvPolynomial.pderiv i F ≠ 0) :
    (MvPolynomial.pderiv i F).totalDegree < F.totalDegree := by
  classical
  obtain ⟨s, hs, hdeg⟩ := exists_mem_eq_sup (MvPolynomial.pderiv i F).support
    (MvPolynomial.support_nonempty.mpr h) (fun s => s.sum fun _ e => e)
  have hcoeff : MvPolynomial.coeff (s + Finsupp.single i 1) F ≠ 0 := by
    have := MvPolynomial.mem_support_iff.mp hs
    rw [MvPolynomial.coeff_pderiv] at this
    exact left_ne_zero_of_mul this
  have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
  rw [sum_add_single] at hle
  rw [MvPolynomial.totalDegree, hdeg]
  omega

/-- **An integer polynomial with all partial derivatives zero is constant.** -/
theorem eq_C_of_forall_pderiv_eq_zero (F : MvPolynomial σ ℤ)
    (h : ∀ i, MvPolynomial.pderiv i F = 0) : F = MvPolynomial.C (F.coeff 0) := by
  classical
  ext s
  rw [MvPolynomial.coeff_C]
  split_ifs with hs
  · rw [hs]
  · obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hs (Finsupp.ext fun i => by simp [hcon i])
    have hsplit : s - Finsupp.single i 1 + Finsupp.single i 1 = s := by
      ext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Ne.symm hj]
    have h0 := congrArg (MvPolynomial.coeff (s - Finsupp.single i 1)) (h i)
    rw [MvPolynomial.coeff_pderiv, hsplit, MvPolynomial.coeff_zero] at h0
    have hne : (((s - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) + 1 : ℤ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h0).resolve_right hne

theorem iterDeriv_pderiv (F : MvPolynomial σ ℤ) (i : σ) (l : List σ) :
    iterDeriv (MvPolynomial.pderiv i F) l = iterDeriv F (l ++ [i]) := by
  simp [iterDeriv, List.foldr_append]

theorem vanishesToOrder_pderiv {F : MvPolynomial σ ℤ} {ω : σ → ℂ} {J : ℕ}
    (h : VanishesToOrder F ω (J + 1)) (i : σ) : VanishesToOrder (MvPolynomial.pderiv i F) ω J := by
  intro l hl
  rw [iterDeriv_pderiv]
  exact h _ (by simp; omega)

/-- **No vanishing beyond the degree.** -/
theorem eq_zero_of_vanishesToOrder {ω : σ → ℂ} :
    ∀ (J : ℕ) (F : MvPolynomial σ ℤ), VanishesToOrder F ω J → F.totalDegree < J → F = 0 := by
  intro J
  induction J with
  | zero => intro F _ h; omega
  | succ J ih =>
    intro F hF hdeg
    have hpd : ∀ i, MvPolynomial.pderiv i F = 0 := by
      intro i
      by_contra hne
      have := totalDegree_pderiv_lt F i hne
      exact hne (ih _ (vanishesToOrder_pderiv hF i) (by omega))
    have hC := eq_C_of_forall_pderiv_eq_zero F hpd
    have hval := hF [] (by simp)
    simp only [iterDeriv, List.foldr_nil] at hval
    rw [hC, MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast, Int.cast_eq_zero] at hval
    rw [hC, hval, map_zero]

/-- **Order at a point is at most the total degree.** -/
theorem le_totalDegree_of_vanishesToOrder {F : MvPolynomial σ ℤ} (hF : F ≠ 0) {ω : σ → ℂ}
    {J : ℕ} (h : VanishesToOrder F ω J) : J ≤ F.totalDegree := by
  by_contra hlt
  exact hF (eq_zero_of_vanishesToOrder J F h (not_le.mp hlt))

variable {P : Finset Nat.Primes}

/-- **The degree is at most `log N / log 2`.** -/
theorem two_pow_totalDegree_le_length {F : MvPolynomial P ℤ} (hF : F ≠ 0) :
    2 ^ F.totalDegree ≤ length F := by
  classical
  obtain ⟨α, hα, hdeg⟩ := exists_mem_eq_sup F.support (MvPolynomial.support_nonempty.mpr hF)
    (fun s => s.sum fun _ e => e)
  have hw : 2 ^ (α.sum fun _ e => e) ≤ weight α := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), weight, ← prod_pow_eq_pow_sum]
    exact prod_le_prod' fun p _ => Nat.pow_le_pow_left (p : Nat.Primes).2.two_le _
  rw [MvPolynomial.totalDegree, hdeg]
  exact hw.trans (le_sup (f := weight) hα)

/-- **Exact order `J` at any point costs length `2^J`.** -/
theorem two_pow_le_length_of_vanishesToOrder {F : MvPolynomial P ℤ} (hF : F ≠ 0) {ω : P → ℂ}
    {J : ℕ} (h : VanishesToOrder F ω J) : 2 ^ J ≤ length F :=
  (Nat.pow_le_pow_right (by norm_num) (le_totalDegree_of_vanishesToOrder hF h)).trans
    (two_pow_totalDegree_le_length hF)

/-- **The amplifier's order is paid in length.** If the norm amplifier gives vanishing to uniform
order `J` on a closed torsion point, the auxiliary has length at least `2^J`. -/
theorem two_pow_le_length_of_small {m : ℕ} (hm : 0 < m) {F : MvPolynomial P ℤ} (hF : F ≠ 0)
    (b : P → ℕ) (J : ℕ)
    (hsmall : ∀ l : List P, l.length < J →
      ∏ μ ∈ primitiveRoots m ℂ, ‖MvPolynomial.aeval (torsionPoint μ b) (iterDeriv F l)‖ < 1) :
    2 ^ J ≤ length F := by
  obtain ⟨μ, hμ⟩ : (primitiveRoots m ℂ).Nonempty := by
    rw [← card_pos, (Complex.isPrimitiveRoot_exp m hm.ne').card_primitiveRoots]
    exact Nat.totient_pos.mpr hm
  exact two_pow_le_length_of_vanishesToOrder hF (vanishesToOrder_of_small hm F b J hsmall μ hμ)

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
