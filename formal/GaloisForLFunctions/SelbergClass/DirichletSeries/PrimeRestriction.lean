import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Algebra.Hom

/-!+# Restricting Dirichlet coefficients to a set of primes

Keeping coefficients whose prime divisors belong to a fixed set is a ring endomorphism for
Dirichlet convolution. A multiplicative function factors into its restrictions to a prime set
and its complement. This is the coefficient identity underlying separation of Euler factors;
the prime set need not be finite.
-/

noncomputable section

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction
open scoped Classical

variable {R : Type*} [CommRing R]

/-- Retain precisely the coefficients whose prime divisors lie in `S`. -/
def primeRestrict (S : Set ℕ) (f : ArithmeticFunction R) : ArithmeticFunction R where
  toFun n := if (↑n.primeFactors : Set ℕ) ⊆ S then f n else 0
  map_zero' := by simp

theorem primeRestrict_apply (S : Set ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    primeRestrict S f n = if (↑n.primeFactors : Set ℕ) ⊆ S then f n else 0 := rfl

@[simp] theorem primeRestrict_apply_one (S : Set ℕ) (f : ArithmeticFunction R) :
    primeRestrict S f 1 = f 1 := by simp [primeRestrict_apply]

@[simp] theorem primeRestrict_add (S : Set ℕ) (f g : ArithmeticFunction R) :
    primeRestrict S (f + g) = primeRestrict S f + primeRestrict S g := by
  ext n
  by_cases h : (↑n.primeFactors : Set ℕ) ⊆ S <;>
    simp [primeRestrict_apply, h]

@[simp] theorem primeRestrict_one (S : Set ℕ) :
    primeRestrict S (1 : ArithmeticFunction R) = 1 := by
  ext n
  by_cases h : n = 1
  · subst n; simp
  · simp [primeRestrict_apply, h]

/-- Restriction commutes with convolution because both factors of a supported integer are
supported, and an unsupported integer has an unsupported factor in every divisor pair. -/
@[simp] theorem primeRestrict_mul (S : Set ℕ) (f g : ArithmeticFunction R) :
    primeRestrict S (f * g) = primeRestrict S f * primeRestrict S g := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [primeRestrict_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  have hz : (∑ _x ∈ n.divisorsAntidiagonal, (0 : R)) = 0 := Finset.sum_const_zero
  rw [← hz, ← Finset.sum_ite_irrel]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hmul, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hx0 : x.1 ≠ 0 ∧ x.2 ≠ 0 := mul_ne_zero_iff.mp (hmul ▸ hn)
  have hs : (↑n.primeFactors : Set ℕ) ⊆ S ↔
      (↑x.1.primeFactors : Set ℕ) ⊆ S ∧ (↑x.2.primeFactors : Set ℕ) ⊆ S := by
    rw [← hmul, Nat.primeFactors_mul hx0.1 hx0.2, Finset.coe_union, Set.union_subset_iff]
  by_cases h₁ : (↑x.1.primeFactors : Set ℕ) ⊆ S <;>
    by_cases h₂ : (↑x.2.primeFactors : Set ℕ) ⊆ S <;>
      simp [primeRestrict_apply, hs, h₁, h₂]

/-- The projection onto a prime-supported convolution subring. -/
def primeRestriction (S : Set ℕ) : ArithmeticFunction R →+* ArithmeticFunction R where
  toFun := primeRestrict S
  map_zero' := by ext n; simp [primeRestrict_apply]
  map_one' := primeRestrict_one S
  map_add' := primeRestrict_add S
  map_mul' := primeRestrict_mul S

/-- Two successive prime restrictions keep precisely their intersection. -/
theorem primeRestrict_inter (S T : Set ℕ) (f : ArithmeticFunction R) :
    primeRestrict S (primeRestrict T f) = primeRestrict (S ∩ T) f := by
  ext n
  by_cases hS : (↑n.primeFactors : Set ℕ) ⊆ S <;>
    by_cases hT : (↑n.primeFactors : Set ℕ) ⊆ T <;>
      simp [primeRestrict_apply, Set.subset_inter_iff, hS, hT]

@[simp] theorem primeRestrict_idem (S : Set ℕ) (f : ArithmeticFunction R) :
    primeRestrict S (primeRestrict S f) = primeRestrict S f := by
  rw [primeRestrict_inter, Set.inter_self]

/-- Restriction also commutes with pointwise multiplication, hence with arithmetic twists. -/
theorem primeRestrict_pmul (S : Set ℕ) (f g : ArithmeticFunction R) :
    primeRestrict S (f.pmul g) = (primeRestrict S f).pmul g := by
  ext n
  by_cases h : (↑n.primeFactors : Set ℕ) ⊆ S <;>
    simp [primeRestrict_apply, ArithmeticFunction.pmul_apply, h]

@[simp] theorem primeRestrict_smul (S : Set ℕ) (r : R) (f : ArithmeticFunction R) :
    primeRestrict S (r • f) = r • primeRestrict S f := by
  ext n
  by_cases h : (↑n.primeFactors : Set ℕ) ⊆ S <;>
    simp [primeRestrict_apply, ArithmeticFunction.smul_map, h]

/-- Prime restriction fixes scalars and is an algebra endomorphism. -/
def primeRestrictionAlgHom (S : Set ℕ) :
    ArithmeticFunction R →ₐ[R] ArithmeticFunction R where
  __ := primeRestriction S
  commutes' r := by
    change primeRestrict S (algebraMap R (ArithmeticFunction R) r) = _
    rw [Algebra.algebraMap_eq_smul_one, primeRestrict_smul, primeRestrict_one]

/-- Prime restriction preserves exactly the units of the full formal Dirichlet algebra. -/
theorem isUnit_primeRestrict_iff (S : Set ℕ) (f : ArithmeticFunction R) :
    IsUnit (primeRestrict S f) ↔ IsUnit f := by
  rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one,
    ArithmeticFunction.isUnit_iff_isUnit_apply_one, primeRestrict_apply_one]

/-- Dirichlet inverse identities survive arbitrary prime restriction. -/
theorem primeRestrict_inverse_pair (S : Set ℕ) (f g : ArithmeticFunction R)
    (hfg : f * g = 1) : primeRestrict S f * primeRestrict S g = 1 := by
  rw [← primeRestrict_mul, hfg, primeRestrict_one]

@[simp] theorem primeRestrict_prime_pow (S : Set ℕ) (f : ArithmeticFunction R)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeRestrict S f (p ^ k) = if k = 0 ∨ p ∈ S then f (p ^ k) else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [primeRestrict_apply, Nat.primeFactors_prime_pow hk hp, hk]

theorem isMultiplicative_primeRestrict (S : Set ℕ) (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) : (primeRestrict S f).IsMultiplicative := by
  refine ⟨by simpa using hf.1, fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [primeRestrict_apply, Nat.primeFactors_mul hm hn, Finset.coe_union,
    Set.union_subset_iff, hf.2 hmn]
  by_cases h₁ : (↑m.primeFactors : Set ℕ) ⊆ S <;>
    by_cases h₂ : (↑n.primeFactors : Set ℕ) ⊆ S <;> simp [h₁, h₂]

private theorem convolution_prime_pow {p : ℕ} (hp : p.Prime)
    (f g : ArithmeticFunction R) (k : ℕ) :
    (f * g) (p ^ k) = ∑ j ∈ Finset.range (k + 1), f (p ^ j) * g (p ^ (k - j)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]

/-- Complementary prime restrictions recover every multiplicative coefficient stream. -/
theorem primeRestrict_mul_compl (S : Set ℕ) (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) : primeRestrict S f * primeRestrict Sᶜ f = f := by
  apply (((isMultiplicative_primeRestrict S f hf).mul
    (isMultiplicative_primeRestrict Sᶜ f hf)).eq_iff_eq_on_prime_powers _ _ hf).mpr
  intro p k hp
  rw [convolution_prime_pow hp]
  by_cases hpS : p ∈ S
  · rw [Finset.sum_eq_single k]
    · simp [primeRestrict_prime_pow, hp, hpS, hf.1]
    · intro j hj hjk
      have hkj : k - j ≠ 0 := by
        have := Finset.mem_range.mp hj
        omega
      simp [primeRestrict_prime_pow, hp, hpS, hkj]
    · intro hk
      exact (hk (Finset.mem_range.mpr (Nat.lt_succ_self k))).elim
  · rw [Finset.sum_eq_single 0]
    · simp [primeRestrict_prime_pow, hp, hpS, hf.1]
    · intro j _ hj
      simp [primeRestrict_prime_pow, hp, hpS, hj]
    · intro hk
      exact (hk (Finset.mem_range.mpr (Nat.succ_pos k))).elim

/-- Equal Euler factors outside `S` give an exact relation with coefficients supported in `S`. -/
theorem euler_cross_relation (S : Set ℕ) (f g : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (h : primeRestrict Sᶜ f = primeRestrict Sᶜ g) :
    primeRestrict S g * f = primeRestrict S f * g := by
  calc
    _ = primeRestrict S g * (primeRestrict S f * primeRestrict Sᶜ f) := by
      rw [primeRestrict_mul_compl S f hf]
    _ = primeRestrict S f * (primeRestrict S g * primeRestrict Sᶜ g) := by
      rw [h]; ring
    _ = _ := by rw [primeRestrict_mul_compl S g hg]

/-- Zeta splits over every partition of the primes. -/
theorem zeta_prime_partition (S : Set ℕ) :
    primeRestrict S (zeta : ArithmeticFunction R) *
      primeRestrict Sᶜ (zeta : ArithmeticFunction R) = zeta :=
  primeRestrict_mul_compl S _ isMultiplicative_zeta.natCast

/-- Möbius inversion splits over the same prime partition as zeta. -/
theorem moebius_prime_partition (S : Set ℕ) :
    primeRestrict S (moebius : ArithmeticFunction R) *
      primeRestrict Sᶜ (moebius : ArithmeticFunction R) = moebius :=
  primeRestrict_mul_compl S _ isMultiplicative_moebius.intCast

/-- Each partial Möbius function inverts the corresponding partial zeta function. -/
theorem restricted_moebius_mul_zeta (S : Set ℕ) :
    primeRestrict S (moebius : ArithmeticFunction R) *
      primeRestrict S (zeta : ArithmeticFunction R) = 1 :=
  primeRestrict_inverse_pair S _ _ coe_moebius_mul_coe_zeta

/-- Every divisor-power sum admits arbitrary prime separation. -/
theorem sigma_prime_partition (S : Set ℕ) (k : ℕ) :
    primeRestrict S (sigma k : ArithmeticFunction R) *
      primeRestrict Sᶜ (sigma k : ArithmeticFunction R) = sigma k :=
  primeRestrict_mul_compl S _ isMultiplicative_sigma.natCast

/-- Natural power coefficients split without restricting the exponent or the prime set. -/
theorem pow_prime_partition (S : Set ℕ) (k : ℕ) :
    primeRestrict S (ArithmeticFunction.pow k : ArithmeticFunction R) *
      primeRestrict Sᶜ (ArithmeticFunction.pow k : ArithmeticFunction R) =
        ArithmeticFunction.pow k :=
  primeRestrict_mul_compl S _ isMultiplicative_pow.natCast

/-- The Liouville stream splits over arbitrary complementary prime sets. -/
theorem liouville_prime_partition (S : Set ℕ) :
    primeRestrict S (liouville : ArithmeticFunction R) *
      primeRestrict Sᶜ (liouville : ArithmeticFunction R) = liouville :=
  primeRestrict_mul_compl S _ isMultiplicative_liouville.intCast

end GaloisForLFunctions.SelbergClass.DirichletSeries

#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.primeRestrictionAlgHom
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.primeRestrict_inter
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.primeRestrict_pmul
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.isUnit_primeRestrict_iff
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.euler_cross_relation
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.zeta_prime_partition
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.moebius_prime_partition
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.restricted_moebius_mul_zeta
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.sigma_prime_partition
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.pow_prime_partition
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.liouville_prime_partition
