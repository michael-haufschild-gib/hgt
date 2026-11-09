import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheMinimalTorsionAuxiliaryIsRigid

/-!
# Arithmetic triangularity of the torsion Newton polynomials

The polynomial indexed by `a` is
`∏ p, u_p^(a_p mod q) (u_p^q - 1)^(a_p div q)`.
Its top arithmetic monomial is `u^a`, with coefficient one; every other
monomial has smaller integer weight. These integral polynomials preserve
the arithmetic length filtration and have full torsion multiplicity at
least the sum of their quotient exponents.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open ArithmeticHarmonicAnalysis
variable {P : Finset Nat.Primes}

/-- A polynomial with prescribed leading exponent and leading coefficient one. -/
def ArithmeticMonicAt (F : MvPolynomial P ℤ) (a : P →₀ ℕ) : Prop :=
  F.coeff a = 1 ∧ ∀ b ∈ F.support, weight b ≤ weight a

/-- Arithmetic top coefficients multiply without cancellation. -/
theorem coeff_mul_at_weight_top (F G : MvPolynomial P ℤ) (a b : P →₀ ℕ)
    (hF : ∀ d ∈ F.support, weight d ≤ weight a)
    (hG : ∀ d ∈ G.support, weight d ≤ weight b) :
    (F * G).coeff (a + b) = F.coeff a * G.coeff b := by
  classical
  rw [MvPolynomial.coeff_mul, sum_eq_single (a, b)]
  · rintro ⟨c, d⟩ hcd hne
    have hsum : c + d = a + b := Finset.HasAntidiagonal.mem_antidiagonal.mp hcd
    by_cases hc : F.coeff c = 0
    · rw [hc, zero_mul]
    by_cases hd : G.coeff d = 0
    · rw [hd, mul_zero]
    have hcw := hF c (MvPolynomial.mem_support_iff.mpr hc)
    have hdw := hG d (MvPolynomial.mem_support_iff.mpr hd)
    have heq : weight c * weight d = weight a * weight b := by
      rw [← weight_add, hsum, weight_add]
    have hca : weight c = weight a := by
      apply le_antisymm hcw
      by_contra hnot
      have hlt : weight c < weight a := lt_of_not_ge hnot
      have hm := Nat.mul_le_mul_left (weight c) hdw
      have hs := Nat.mul_lt_mul_of_pos_right hlt (weight_pos b)
      omega
    have hca' : c = a := weight_injective hca
    have hdb : d = b := by simpa only [hca', add_left_cancel_iff] using hsum
    exact (hne (Prod.ext hca' hdb)).elim
  · simp

/-- The arithmetic leading monomial of a product is the product of its leading monomials. -/
theorem ArithmeticMonicAt.mul {F G : MvPolynomial P ℤ} {a b : P →₀ ℕ}
    (hF : ArithmeticMonicAt F a) (hG : ArithmeticMonicAt G b) :
    ArithmeticMonicAt (F * G) (a + b) := by
  constructor
  · rw [coeff_mul_at_weight_top F G a b hF.2 hG.2, hF.1, hG.1, one_mul]
  · intro d hd
    obtain ⟨e, he, f, hf, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul F G hd)
    rw [weight_add, weight_add]
    exact Nat.mul_le_mul (hF.2 e he) (hG.2 f hf)

/-- A pure monomial has arithmetic leading coefficient one. -/
theorem arithmeticMonicAt_monomial (a : P →₀ ℕ) :
    ArithmeticMonicAt (MvPolynomial.monomial a (1 : ℤ)) a := by
  classical
  constructor
  · simp only [MvPolynomial.coeff_monomial, if_true]
  · intro b hb
    have hb' : b = a := by simpa using MvPolynomial.support_monomial_subset hb
    exact hb' ▸ le_rfl

theorem arithmeticMonicAt_one : ArithmeticMonicAt (1 : MvPolynomial P ℤ) 0 := by
  classical
  constructor
  · simp only [MvPolynomial.coeff_one, if_true]
  · intro b hb
    rw [MvPolynomial.support_one, mem_singleton] at hb
    exact hb ▸ le_rfl

theorem ArithmeticMonicAt.pow {F : MvPolynomial P ℤ} {a : P →₀ ℕ}
    (hF : ArithmeticMonicAt F a) (k : ℕ) : ArithmeticMonicAt (F ^ k) (k • a) := by
  induction k with
  | zero => simpa only [pow_zero, zero_nsmul] using arithmeticMonicAt_one (P := P)
  | succ k ih => simpa only [pow_succ, add_nsmul, one_nsmul] using ih.mul hF

theorem arithmeticMonicAt_prod {κ : Type*} (S : Finset κ)
    (F : κ → MvPolynomial P ℤ) (a : κ → P →₀ ℕ)
    (h : ∀ k ∈ S, ArithmeticMonicAt (F k) (a k)) :
    ArithmeticMonicAt (∏ k ∈ S, F k) (∑ k ∈ S, a k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty, sum_empty] using arithmeticMonicAt_one (P := P)
  | @insert k S hk ih =>
    rw [prod_insert hk, sum_insert hk]
    exact (h k (mem_insert_self _ _)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

/-- The torsion equation is monic at its highest prime power. -/
theorem arithmeticMonicAt_torsion (q : ℕ) [NeZero q] (p : P) :
    ArithmeticMonicAt ((X p : MvPolynomial P ℤ) ^ q - 1) (Finsupp.single p q) := by
  classical
  have hsingle : Finsupp.single p q ≠ (0 : P →₀ ℕ) :=
    Finsupp.single_ne_zero.mpr (NeZero.ne q)
  constructor
  · simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_X_pow, if_true,
      MvPolynomial.coeff_one, if_neg hsingle.symm, sub_zero]
  · intro b hb
    have hmem := MvPolynomial.support_sub P (X p ^ q) 1 hb
    rw [MvPolynomial.support_X_pow, MvPolynomial.support_one] at hmem
    rcases mem_union.mp hmem with hb | hb
    · rw [mem_singleton.mp hb]
    · have hb0 : b = 0 := mem_singleton.mp hb
      rw [hb0]
      have hz : weight (0 : P →₀ ℕ) = 1 := by
        simp only [weight, Finsupp.zero_apply, pow_zero, prod_const_one]
      rw [hz]
      have hpos := weight_pos (Finsupp.single p q)
      omega

/-- Integral Newton polynomial indexed by the original prime exponent vector. -/
def torsionNewtonPolynomial (q : ℕ) (a : P →₀ ℕ) : MvPolynomial P ℤ :=
  ∏ p : P, X p ^ (a p % q) * (X p ^ q - 1) ^ (a p / q)

/-- The Newton change of basis is integral and has diagonal coefficient one. -/
theorem torsionNewtonPolynomial_monic (q : ℕ) [NeZero q] (a : P →₀ ℕ) :
    ArithmeticMonicAt (torsionNewtonPolynomial q a) a := by
  have hp (p : P) : ArithmeticMonicAt
      (X p ^ (a p % q) * (X p ^ q - 1) ^ (a p / q) : MvPolynomial P ℤ)
      (Finsupp.single p (a p)) := by
    have hm := (arithmeticMonicAt_monomial (Finsupp.single p (a p % q))).mul
      ((arithmeticMonicAt_torsion q p).pow (a p / q))
    rw [← MvPolynomial.X_pow_eq_monomial] at hm
    have he : Finsupp.single p (a p % q) + (a p / q) • Finsupp.single p q =
        Finsupp.single p (a p) := by
      ext s
      by_cases hs : s = p
      · subst s
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.smul_apply,
          smul_eq_mul]
        simpa only [Nat.mul_comm] using Nat.mod_add_div (a p) q
      · simp [Finsupp.single_eq_of_ne hs]
    rwa [he] at hm
  have h := arithmeticMonicAt_prod univ _ _ (fun p _ => hp p)
  have he : (∑ p : P, Finsupp.single p (a p)) = a := by
    have hh := Finsupp.sum_fintype a (fun p n => Finsupp.single p n)
      (fun p => by simp only [Finsupp.single_zero])
    rw [Finsupp.sum_single] at hh
    exact hh.symm
  simpa only [torsionNewtonPolynomial, he] using h

/-- The Newton polynomial has exactly the arithmetic length of its index. -/
theorem length_torsionNewtonPolynomial (q : ℕ) [NeZero q] (a : P →₀ ℕ) :
    length (torsionNewtonPolynomial q a) = weight a := by
  have h := torsionNewtonPolynomial_monic q a
  apply le_antisymm (Finset.sup_le h.2)
  exact le_sup (f := weight) (MvPolynomial.mem_support_iff.mpr (by rw [h.1]; exact one_ne_zero))

/-- A Newton polynomial has no monomial above the arithmetic weight of its index. -/
theorem coeff_torsionNewtonPolynomial_eq_zero_of_weight_lt
    (q : ℕ) [NeZero q] (a b : P →₀ ℕ) (h : weight a < weight b) :
    (torsionNewtonPolynomial q a).coeff b = 0 := by
  apply MvPolynomial.notMem_support_iff.mp
  intro hb
  exact (not_le_of_gt h) ((torsionNewtonPolynomial_monic q a).2 b hb)

/-- Each quotient block contributes one exact order at every torsion point. -/
theorem torsionNewtonPolynomial_mem_pointIdeal_pow
    (q r : ℕ) [NeZero q] (a : P →₀ ℕ) (hr : r ≤ torsionQuotientOrder q a)
    (t : P → ZMod q) :
    MvPolynomial.map (Int.castRingHom ℂ) (torsionNewtonPolynomial q a) ∈
      vanishingIdeal ℂ {fun p => ZMod.stdAddChar (t p)} ^ r := by
  classical
  let I := vanishingIdeal ℂ {fun p => ZMod.stdAddChar (t p)}
  have hfactor (p : P) :
      MvPolynomial.map (Int.castRingHom ℂ)
        (X p ^ (a p % q) * (X p ^ q - 1) ^ (a p / q)) ∈ I ^ (a p / q) := by
    rw [map_mul]
    apply Ideal.mul_mem_left
    rw [map_pow]
    apply Ideal.pow_mem_pow
    rw [map_sub, map_pow, MvPolynomial.map_X, map_one]
    rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval]
    simp only [map_sub, map_pow, eval_X, map_one]
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self,
      zero_mul, AddChar.map_zero_eq_one, sub_self]
  have hprod (S : Finset P) :
      (∏ p ∈ S, MvPolynomial.map (Int.castRingHom ℂ)
        (X p ^ (a p % q) * (X p ^ q - 1) ^ (a p / q))) ∈ I ^ (∑ p ∈ S, a p / q) := by
    induction S using Finset.induction_on with
    | empty => simp only [prod_empty, sum_empty, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    | @insert p S hp ih =>
      rw [prod_insert hp, sum_insert hp, pow_add]
      exact Ideal.mul_mem_mul (hfactor p) ih
  apply Ideal.pow_le_pow_right hr
  simpa only [torsionNewtonPolynomial, map_prod, torsionQuotientOrder] using hprod univ

#print axioms torsionNewtonPolynomial_monic
#print axioms torsionNewtonPolynomial_mem_pointIdeal_pow

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
