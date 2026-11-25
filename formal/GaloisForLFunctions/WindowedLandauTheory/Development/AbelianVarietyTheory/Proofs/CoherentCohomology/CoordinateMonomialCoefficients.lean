import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.HomogeneousLocalizationLift
import Mathlib.Algebra.MonoidAlgebra.Module

/-! A coordinate denominator shifts each exponent associated to an inverted variable. -/

noncomputable section

open MvPolynomial

namespace GlobalTheory

variable {ι R : Type} [CommRing R]

def coordinateExponent (s : Finset ι) : ι →₀ ℕ :=
  ∑ i ∈ s, Finsupp.single i 1

theorem coordinateExponent_apply [DecidableEq ι] (s : Finset ι) (i : ι) :
    coordinateExponent s i = if i ∈ s then 1 else 0 := by
  simp [coordinateExponent, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]

theorem xProd_eq_monomial (s : Finset ι) :
    xProd R s = (monomial (coordinateExponent s) 1 : MvPolynomial ι R) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coordinateExponent]
  | insert i s hi ih =>
    rw [xProd, Finset.prod_insert hi, ih]
    simp only [X, monomial_mul, one_mul, coordinateExponent, Finset.sum_insert hi]

/-- The Laurent exponent of a numerator monomial after division by `xProd s ^ k`. -/
def shiftedExponent (s : Finset ι) (k : ℕ) (a : ι →₀ ℕ) : ι → ℤ :=
  fun i => (a i : ℤ) - k * coordinateExponent s i

theorem shiftedExponent_injective (s : Finset ι) (k : ℕ) :
    Function.Injective (shiftedExponent s k) := by
  intro a b h
  ext i
  have hi := congrFun h i
  dsimp only [shiftedExponent] at hi
  omega

theorem shiftedExponent_add (s : Finset ι) (k j : ℕ) (a : ι →₀ ℕ) :
    shiftedExponent s (k + j) (j • coordinateExponent s + a) = shiftedExponent s k a := by
  funext i
  simp only [shiftedExponent, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Nat.cast_add, Nat.cast_mul]
  ring

theorem coordinateExponent_sum [Fintype ι] (s : Finset ι) : ∑ i, coordinateExponent s i = s.card := by
  classical
  simp only [coordinateExponent_apply]
  rw [Finset.sum_ite]
  simp

theorem shiftedExponent_sum [Fintype ι] (s : Finset ι) (k : ℕ) (a : ι →₀ ℕ) :
    ∑ i, shiftedExponent s k a i = (a.degree : ℤ) - k * s.card := by
  simp only [shiftedExponent, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum,
    coordinateExponent_sum]
  congr 2
  rw [Finsupp.degree_apply, Finsupp.sum_fintype _ _ (fun _ => rfl)]

variable (R) in
def shiftedCoefficients (s : Finset ι) (k : ℕ) : MvPolynomial ι R →ₗ[R] (ι → ℤ) →₀ R :=
  Finsupp.lmapDomain R R (shiftedExponent s k) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem shiftedCoefficients_monomial (s : Finset ι) (k : ℕ) (a : ι →₀ ℕ) (r : R) :
    shiftedCoefficients R s k (monomial a r) = Finsupp.single (shiftedExponent s k a) r :=
  Finsupp.mapDomain_single

theorem shiftedCoefficients_injective (s : Finset ι) (k : ℕ) :
    Function.Injective (shiftedCoefficients R s k) :=
  (Finsupp.mapDomain_injective (shiftedExponent_injective s k)).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).injective

theorem shiftedCoefficients_mul (s : Finset ι) (k j : ℕ) (p : MvPolynomial ι R) :
    shiftedCoefficients R s (k + j) (xProd R s ^ j * p) = shiftedCoefficients R s k p := by
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    rw [xProd_eq_monomial, monomial_pow, one_pow, monomial_mul, one_mul,
      shiftedCoefficients_monomial, shiftedCoefficients_monomial, shiftedExponent_add]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq]

theorem shiftedCoefficients_restrict [DecidableEq ι] {s t : Finset ι} (h : s ⊆ t)
    (k : ℕ) (p : MvPolynomial ι R) :
    shiftedCoefficients R t k (xProd R (t \ s) ^ k * p) = shiftedCoefficients R s k p := by
  have hsum : coordinateExponent (t \ s) + coordinateExponent s = coordinateExponent t :=
    Finset.sum_sdiff h
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    rw [xProd_eq_monomial, monomial_pow, one_pow, monomial_mul, one_mul,
      shiftedCoefficients_monomial, shiftedCoefficients_monomial]
    congr 1
    funext i
    simp only [shiftedExponent, ← hsum, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_mul]
    ring
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq]

theorem mem_shiftedCoefficients_support (s : Finset ι) (k : ℕ) (p : MvPolynomial ι R)
    {a : ι → ℤ} (ha : a ∈ (shiftedCoefficients R s k p).support) :
    ∃ b ∈ p.support, shiftedExponent s k b = a := by
  classical
  change a ∈ (Finsupp.mapDomain (shiftedExponent s k) (AddMonoidAlgebra.coeffLinearEquiv R p)).support at ha
  rw [Finsupp.mapDomain_support_of_injective (shiftedExponent_injective s k)] at ha
  exact Finset.mem_image.1 ha

end GlobalTheory
