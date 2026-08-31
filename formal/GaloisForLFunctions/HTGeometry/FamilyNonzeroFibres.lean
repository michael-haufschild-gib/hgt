import GaloisForLFunctions.HTGeometry.WeightHomogenization

/-!
# The nonzero fibres of the family are all the same

Rescaling the variables by a nonzero scalar according to the weight is an algebra map, and it is
what the homogenization becomes when the extra variable is evaluated:

```text
familyWeightScale      the rescaling x i ↦ lam ^ (w i) * x i
familyWeightScale_monomial   its effect on a monomial: multiplication by lam raised to the weight
eval_homogenize        ** evaluating the homogenization at lam returns the rescaled polynomial,
                          up to an invertible scalar **
```

So the fibre of the family over any nonzero point is the image of the original ideal under an
automorphism of the polynomial ring, hence isomorphic to the fibre over `1`.  This is what makes the
generic fibre *generic*: every nonzero point sees the same ring, so a property that holds at all but
finitely many points holds at every nonzero point — the form in which semicontinuity is actually
used.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- The weight rescaling `x i ↦ lam ^ (w i) * x i`. -/
noncomputable def familyWeightScale (w : σ → ℤ) (lam : K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval fun i => MvPolynomial.C (lam ^ (w i)) * X i

theorem familyWeightScale_monomial (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) (α : σ →₀ ℕ) (c : K) :
    familyWeightScale (K := K) w lam (MvPolynomial.monomial α c)
      = MvPolynomial.C (lam ^ (Finsupp.weight w α)) * MvPolynomial.monomial α c := by
  classical
  have hstep : ∀ a : σ, (MvPolynomial.C (lam ^ (w a)) * (X a : MvPolynomial σ K)) ^ (α a)
      = MvPolynomial.C (lam ^ ((α a : ℤ) * w a)) * (X a : MvPolynomial σ K) ^ (α a) := by
    intro a
    rw [mul_pow, ← map_pow, ← zpow_natCast (lam ^ (w a)) (α a), ← zpow_mul,
      mul_comm (w a) ((α a : ℤ))]
  have hprod : ∀ s : Finset σ,
      (∏ i ∈ s, (MvPolynomial.C (lam ^ (w i)) * (X i : MvPolynomial σ K)) ^ (α i))
        = MvPolynomial.C (lam ^ (∑ i ∈ s, (α i : ℤ) * w i)) *
          (∏ i ∈ s, (X i : MvPolynomial σ K) ^ (α i)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, hstep a, ih, Finset.sum_insert ha, Finset.prod_insert ha,
        zpow_add₀ hlam, map_mul]
      ring
  rw [familyWeightScale, MvPolynomial.aeval_monomial]
  simp only [Finsupp.prod]
  rw [hprod, Finsupp.weight_apply]
  simp only [Finsupp.sum, nsmul_eq_mul]
  rw [MvPolynomial.monomial_eq]
  simp only [Finsupp.prod]
  have halg : (algebraMap K (MvPolynomial σ K)) c = MvPolynomial.C c := rfl
  rw [halg]
  exact mul_left_comm _ _ _

theorem familyWeightScale_eq_sum (w : σ → ℤ) (lam : K) (f : MvPolynomial σ K) :
    familyWeightScale (K := K) w lam f
      = ∑ α ∈ f.support, familyWeightScale (K := K) w lam
          (MvPolynomial.monomial α (MvPolynomial.coeff α f)) := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
  rw [map_sum]

/-- **The fibre of the family at a nonzero point is the rescaled ideal.**  Evaluating the
homogenization at `lam` returns the polynomial rescaled by the weight, up to an invertible scalar. -/
theorem eval_homogenize (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) (f : MvPolynomial σ K) :
    Polynomial.eval (MvPolynomial.C lam) (homogenize w f)
      = MvPolynomial.C (lam ^ (-minWeight w f)) * familyWeightScale (K := K) w lam f := by
  classical
  rw [homogenize, Polynomial.eval_finsetSum, familyWeightScale_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Polynomial.eval_monomial, familyWeightScale_monomial w hlam, ← map_pow]
  have hle : minWeight w f ≤ Finsupp.weight w α := minWeight_le hα
  have hcast : (((Finsupp.weight w α - minWeight w f).toNat : ℤ))
      = Finsupp.weight w α - minWeight w f := Int.toNat_of_nonneg (by omega)
  have hz : (lam ^ ((Finsupp.weight w α - minWeight w f).toNat))
      = lam ^ (-minWeight w f) * lam ^ (Finsupp.weight w α) := by
    rw [← zpow_natCast lam _, hcast, ← zpow_add₀ hlam]
    congr 1
    ring
  rw [hz, map_mul]
  ring

end GaloisForLFunctions.HTGeometry
