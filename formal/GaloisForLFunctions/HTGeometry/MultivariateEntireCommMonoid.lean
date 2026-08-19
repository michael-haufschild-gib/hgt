import GaloisForLFunctions.HTGeometry.MultivariateEntireVanishingPower

/-!
# The multiplicative structure of entire sources

`multivariateEntireMul` is associative, commutative and unital, so the entire sources form a
commutative monoid.  Recording that as an instance makes `Finset.prod` available, which any
construction multiplying one factor per packet point needs.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

instance multivariateEntireCommMonoid (d : ℕ) : CommMonoid (MultivariateEntire d) where
  mul := multivariateEntireMul
  one := mvPolynomialMultivariateEntire 1
  mul_assoc := by
    intro a b c
    ext x
    show (a.1 x * b.1 x) * c.1 x = a.1 x * (b.1 x * c.1 x)
    ring
  one_mul := by
    intro a
    ext x
    show (mvPolynomialMultivariateEntire (1 : MvPolynomial (Fin d) ℂ)).1 x * a.1 x = a.1 x
    simp [mvPolynomialMultivariateEntire]
  mul_one := by
    intro a
    ext x
    show a.1 x * (mvPolynomialMultivariateEntire (1 : MvPolynomial (Fin d) ℂ)).1 x = a.1 x
    simp [mvPolynomialMultivariateEntire]
  mul_comm := by
    intro a b
    ext x
    show a.1 x * b.1 x = b.1 x * a.1 x
    ring

@[simp] theorem multivariateEntire_mul_apply {d : ℕ} (f g : MultivariateEntire d)
    (x : Fin d → ℂ) : (f * g).1 x = f.1 x * g.1 x := by
  show (multivariateEntireMul f g).1 x = f.1 x * g.1 x
  rw [multivariateEntireMul_apply]

@[simp] theorem multivariateEntire_one_apply {d : ℕ} (x : Fin d → ℂ) :
    ((1 : MultivariateEntire d)).1 x = 1 := by
  show (mvPolynomialMultivariateEntire (1 : MvPolynomial (Fin d) ℂ)).1 x = 1
  simp [mvPolynomialMultivariateEntire]

/-- The value of a finite product of entire sources is the product of the values. -/
theorem multivariateEntire_prod_apply {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MultivariateEntire d) (x : Fin d → ℂ) :
    (∏ i ∈ s, f i).1 x = ∏ i ∈ s, (f i).1 x := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha, multivariateEntire_mul_apply, ih]

end

end GaloisForLFunctions.HTGeometry
