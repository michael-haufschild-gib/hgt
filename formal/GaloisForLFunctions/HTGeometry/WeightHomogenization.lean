import GaloisForLFunctions.HTGeometry.InitialIdealDegeneration

/-!
# The homogenization of a weight degeneration

Writing the weight filtration out in a new variable turns a polynomial into a polynomial in one more
variable whose value at `t = 0` is the lowest-weight form and whose value at `t = 1` is the
polynomial itself:

```text
homogenize             the weight filtration written in a new variable
homogenize_coeff_zero  ** the special fibre is the lowest form **
homogenize_eval_one    ** the generic fibre is the polynomial **
homogenize_mul         ** homogenization is multiplicative **
```

Multiplicativity is where the Laurent picture pays.  Substituting `x i ↦ T ^ w i * x i` is a ring
homomorphism into the Laurent polynomials, and the homogenization is that substitution multiplied by
`T ^ (-minWeight)`:

```text
weightSub              the substitution x i ↦ T ^ w i * x i
toLaurent_homogenize   ** toLaurent (homogenize f) = T ^ (-minWeight f) * weightSub f **
```

so multiplicativity is the additivity of the minimal weight (`minWeight_mul`) together with the
injectivity of `Polynomial.toLaurent`.  This is the coordinate ring of the flat family whose special
fibre is the initial degeneration and whose generic fibre is the original ideal.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- The weight substitution into Laurent polynomials: `x i ↦ T ^ (w i) * x i`. -/
noncomputable def weightSub (w : σ → ℤ) :
    MvPolynomial σ K →ₐ[K] LaurentPolynomial (MvPolynomial σ K) :=
  MvPolynomial.aeval fun i => LaurentPolynomial.T (w i) * LaurentPolynomial.C (X i)

theorem weightSub_monomial (w : σ → ℤ) (α : σ →₀ ℕ) (c : K) :
    weightSub (K := K) w (MvPolynomial.monomial α c)
      = LaurentPolynomial.T (Finsupp.weight w α) *
        LaurentPolynomial.C (MvPolynomial.monomial α c) := by
  classical
  have hprod : ∀ s : Finset σ,
      (∏ i ∈ s, (LaurentPolynomial.T (w i) *
          LaurentPolynomial.C (X i : MvPolynomial σ K)) ^ (α i))
        = LaurentPolynomial.T (∑ i ∈ s, (α i : ℤ) * w i) *
          LaurentPolynomial.C (∏ i ∈ s, (X i : MvPolynomial σ K) ^ (α i)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, Finset.prod_insert ha,
        mul_pow, LaurentPolynomial.T_pow, ← map_pow, map_mul,
        LaurentPolynomial.T_add]
      ring
  rw [weightSub, MvPolynomial.aeval_monomial]
  simp only [Finsupp.prod]
  rw [hprod, Finsupp.weight_apply, MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, nsmul_eq_mul]
  rw [map_mul]
  have halg : (algebraMap K (LaurentPolynomial (MvPolynomial σ K))) c
      = LaurentPolynomial.C (MvPolynomial.C c) := by
    rfl
  rw [halg, Finsupp.sum]
  ring

theorem weightSub_eq_sum (w : σ → ℤ) (f : MvPolynomial σ K) :
    weightSub (K := K) w f
      = ∑ α ∈ f.support, weightSub (K := K) w
          (MvPolynomial.monomial α (MvPolynomial.coeff α f)) := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
  rw [map_sum]

/-- The homogenization of `f`: the weight filtration written out in a new variable, with the
lowest-weight form in degree zero. -/
noncomputable def homogenize (w : σ → ℤ) (f : MvPolynomial σ K) :
    Polynomial (MvPolynomial σ K) :=
  ∑ α ∈ f.support, Polynomial.monomial ((Finsupp.weight w α - minWeight w f).toNat)
    (MvPolynomial.monomial α (MvPolynomial.coeff α f))

theorem toLaurent_homogenize (w : σ → ℤ) (f : MvPolynomial σ K) :
    Polynomial.toLaurent (homogenize w f)
      = LaurentPolynomial.T (-minWeight w f) * weightSub (K := K) w f := by
  classical
  rw [homogenize, map_sum, weightSub_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Polynomial.toLaurent_C_mul_T, weightSub_monomial]
  have hle : minWeight w f ≤ Finsupp.weight w α := minWeight_le hα
  have hcast : ((Finsupp.weight w α - minWeight w f).toNat : ℤ)
      = Finsupp.weight w α - minWeight w f := Int.toNat_of_nonneg (by omega)
  rw [hcast, show Finsupp.weight w α - minWeight w f
      = (-minWeight w f) + Finsupp.weight w α by ring, LaurentPolynomial.T_add]
  ring

/-- **Homogenization is multiplicative.** -/
theorem homogenize_mul {w : σ → ℤ} {p q : MvPolynomial σ K} (hp : p ≠ 0) (hq : q ≠ 0) :
    homogenize w (p * q) = homogenize w p * homogenize w q := by
  refine Polynomial.toLaurent_injective ?_
  rw [map_mul, toLaurent_homogenize, toLaurent_homogenize, toLaurent_homogenize,
    minWeight_mul hp hq, map_mul]
  rw [show -(minWeight w p + minWeight w q) = (-minWeight w p) + (-minWeight w q) by ring,
    LaurentPolynomial.T_add]
  ring

/-- **The special fibre.**  The constant term of the homogenization is the lowest-weight form. -/
theorem homogenize_coeff_zero (w : σ → ℤ) (f : MvPolynomial σ K) :
    (homogenize w f).coeff 0 = lowestForm w f := by
  classical
  rw [homogenize, Polynomial.finsetSum_coeff, lowestForm,
    MvPolynomial.weightedHomogeneousComponent_apply]
  rw [← Finset.sum_filter_add_sum_filter_not f.support
    (fun α => Finsupp.weight w α = minWeight w f)]
  rw [show (∑ α ∈ f.support.filter (fun α => ¬ Finsupp.weight w α = minWeight w f),
      (Polynomial.monomial ((Finsupp.weight w α - minWeight w f).toNat)
        (MvPolynomial.monomial α (MvPolynomial.coeff α f))).coeff 0) = 0 from ?_]
  · rw [add_zero]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.mem_filter] at hα
    rw [hα.2]
    simp
  · refine Finset.sum_eq_zero fun α hα => ?_
    rw [Finset.mem_filter] at hα
    have hle : minWeight w f ≤ Finsupp.weight w α := minWeight_le hα.1
    have hne : (Finsupp.weight w α - minWeight w f).toNat ≠ 0 := by
      have := hα.2
      omega
    rw [Polynomial.coeff_monomial, if_neg (fun h => hne h)]

/-- **The generic fibre.**  Setting the new variable to one recovers the polynomial. -/
theorem homogenize_eval_one (w : σ → ℤ) (f : MvPolynomial σ K) :
    Polynomial.eval 1 (homogenize w f) = f := by
  classical
  rw [homogenize, Polynomial.eval_finsetSum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Polynomial.eval_monomial, one_pow, mul_one]

theorem homogenize_zero (w : σ → ℤ) : homogenize w (0 : MvPolynomial σ K) = 0 := by
  rw [homogenize]
  simp

theorem homogenize_ne_zero {w : σ → ℤ} {f : MvPolynomial σ K} (hf : f ≠ 0) :
    homogenize w f ≠ 0 := by
  intro hcon
  have heval := homogenize_eval_one w f
  rw [hcon, Polynomial.eval_zero] at heval
  exact hf heval.symm

end GaloisForLFunctions.HTGeometry
