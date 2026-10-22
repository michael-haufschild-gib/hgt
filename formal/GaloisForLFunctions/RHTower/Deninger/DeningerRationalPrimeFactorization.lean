import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The positive rationals are free abelian on the primes

The prime-exponent vector `deningerRatExp q`, whose value at a prime `p` is the `p`-adic
valuation `ord_p q`, is a finitely supported integer-valued function supported on the primes.
It is additive on nonzero rationals, insensitive to sign, and restricts to a bijection from the
positive rationals onto the finitely supported functions supported on primes.

This is the unique-factorization input identifying the degree-one part of the arithmetic
endpoint complex over `ℚ` with a free module on the primes, whose coordinates are the Milnor
`K₁` residues `ord_p`.
-/

namespace RHTower

open Nat

open scoped TensorProduct

/-- The prime-exponent vector of a rational number: the numerator's factorization minus the
denominator's. -/
noncomputable def deningerRatExp (q : ℚ) : ℕ →₀ ℤ :=
  q.num.natAbs.factorization.mapRange (fun n : ℕ => (n : ℤ)) (by simp) -
    q.den.factorization.mapRange (fun n : ℕ => (n : ℤ)) (by simp)

@[simp] theorem deningerRatExp_apply (q : ℚ) (p : ℕ) :
    deningerRatExp q p = (q.num.natAbs.factorization p : ℤ) - (q.den.factorization p : ℤ) := rfl

/-- Away from the primes the exponent vector vanishes. -/
theorem deningerRatExp_apply_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (q : ℚ) :
    deningerRatExp q p = 0 := by
  simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- At a prime the exponent vector is the `p`-adic valuation. -/
theorem deningerRatExp_apply_of_prime {p : ℕ} (hp : p.Prime) (q : ℚ) :
    deningerRatExp q p = padicValRat p q := by
  rw [deningerRatExp_apply, padicValRat_def, padicValInt,
    Nat.factorization_def _ hp, Nat.factorization_def _ hp]

@[simp] theorem deningerRatExp_one : deningerRatExp 1 = 0 := by
  ext p
  simp

/-- The exponent vector is additive on nonzero rationals. -/
theorem deningerRatExp_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    deningerRatExp (q * r) = deningerRatExp q + deningerRatExp r := by
  ext p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [deningerRatExp_apply_of_prime hp, Finsupp.add_apply, deningerRatExp_apply_of_prime hp,
      deningerRatExp_apply_of_prime hp, padicValRat.mul hq hr]
  · simp [deningerRatExp_apply_of_not_prime hp]

/-- The exponent vector of an inverse is the negative. -/
theorem deningerRatExp_inv {q : ℚ} (hq : q ≠ 0) :
    deningerRatExp q⁻¹ = -deningerRatExp q := by
  have h := deningerRatExp_mul (inv_ne_zero hq) hq
  rw [inv_mul_cancel₀ hq, deningerRatExp_one] at h
  rw [← sub_eq_zero, sub_neg_eq_add]
  exact h.symm

/-- The exponent vector of a natural power. -/
theorem deningerRatExp_pow {q : ℚ} (hq : q ≠ 0) (n : ℕ) :
    deningerRatExp (q ^ n) = n • deningerRatExp q := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, deningerRatExp_mul (pow_ne_zero n hq) hq, ih, succ_nsmul]

/-- The exponent vector of an integer power. -/
theorem deningerRatExp_zpow {q : ℚ} (hq : q ≠ 0) (n : ℤ) :
    deningerRatExp (q ^ n) = n • deningerRatExp q := by
  cases n with
  | ofNat m => simpa using deningerRatExp_pow hq m
  | negSucc m =>
      rw [zpow_negSucc, deningerRatExp_inv (pow_ne_zero _ hq), deningerRatExp_pow hq (m + 1),
        Int.negSucc_eq]
      ext p
      push_cast
      simp
      ring

/-- The exponent vector of a finite product. -/
theorem deningerRatExp_prod {s : Finset ℕ} {g : ℕ → ℚ} (hg : ∀ p ∈ s, g p ≠ 0) :
    deningerRatExp (∏ p ∈ s, g p) = ∑ p ∈ s, deningerRatExp (g p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hane : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
      have hrest : ∀ p ∈ s, g p ≠ 0 := fun p hp => hg p (Finset.mem_insert_of_mem hp)
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        deningerRatExp_mul hane (Finset.prod_ne_zero_iff.mpr hrest), ih hrest]

/-- The exponent vector of a prime is the corresponding basis vector. -/
theorem deningerRatExp_natCast_prime {p : ℕ} (hp : p.Prime) :
    deningerRatExp (p : ℚ) = Finsupp.single p 1 := by
  ext p'
  have hnum : ((p : ℚ)).num.natAbs = p := by simp
  have hden : ((p : ℚ)).den = 1 := by simp
  rw [deningerRatExp_apply, hnum, hden]
  simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, sub_zero,
    hp.factorization, Finsupp.single_apply]
  by_cases h : p = p' <;> simp [h]

/-- The exponent vector vanishes exactly at `1` among the positive rationals. -/
theorem deningerRatExp_eq_zero_iff {q : ℚ} (hq : 0 < q) :
    deningerRatExp q = 0 ↔ q = 1 := by
  constructor
  · intro h
    have hfac : q.num.natAbs.factorization = q.den.factorization := by
      ext p
      have hp := congrArg (fun g : ℕ →₀ ℤ => g p) h
      simp only [deningerRatExp_apply, Finsupp.coe_zero, Pi.zero_apply, sub_eq_zero] at hp
      exact_mod_cast hp
    have hnumpos : 0 < q.num := Rat.num_pos.mpr hq
    have hnum0 : q.num.natAbs ≠ 0 := by
      simpa [Int.natAbs_eq_zero] using hnumpos.ne'
    have hden0 : q.den ≠ 0 := q.den_nz
    have heq : q.num.natAbs = q.den := Nat.factorization_inj hnum0 hden0 hfac
    have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
    have hone : q.den = 1 := by
      rw [heq] at hcop
      simpa [Nat.Coprime] using hcop
    have hnum : q.num = 1 := by
      have h1 : q.num.natAbs = 1 := by rw [heq, hone]
      omega
    exact Rat.ext hnum (by simpa using hone)
  · rintro rfl
    exact deningerRatExp_one

/-- The exponent vector is injective on the positive rationals. -/
theorem deningerRatExp_injOn_pos {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (h : deningerRatExp q = deningerRatExp r) : q = r := by
  have hrne : r ≠ 0 := hr.ne'
  have hdivpos : (0 : ℚ) < q / r := div_pos hq hr
  have hqr : deningerRatExp (q / r) = 0 := by
    have hstep : deningerRatExp ((q / r) * r) = deningerRatExp (q / r) + deningerRatExp r :=
      deningerRatExp_mul hdivpos.ne' hrne
    rw [div_mul_cancel₀ _ hrne, h] at hstep
    have := hstep.symm
    simpa using this
  have hone := (deningerRatExp_eq_zero_iff hdivpos).mp hqr
  have hmul : q / r * r = 1 * r := by rw [hone]
  rwa [div_mul_cancel₀ _ hrne, one_mul] at hmul

/-- The canonical prime-power product attached to an exponent vector is positive. -/
theorem deningerPrimeProd_pos (f : ℕ →₀ ℤ) (hf : ∀ p ∈ f.support, p.Prime) :
    (0 : ℚ) < ∏ p ∈ f.support, (p : ℚ) ^ (f p) := by
  refine Finset.prod_pos fun p hp => zpow_pos ?_ _
  exact_mod_cast (hf p hp).pos

/-- The exponent vector of the canonical prime-power product is the vector itself. -/
theorem deningerRatExp_primeProd (f : ℕ →₀ ℤ) (hf : ∀ p ∈ f.support, p.Prime) :
    deningerRatExp (∏ p ∈ f.support, (p : ℚ) ^ (f p)) = f := by
  classical
  have hpos : ∀ p ∈ f.support, (0 : ℚ) < (p : ℚ) := by
    intro p hp
    exact_mod_cast (hf p hp).pos
  have hne : ∀ p ∈ f.support, ((p : ℚ) ^ (f p)) ≠ 0 := fun p hp =>
    (zpow_pos (hpos p hp) _).ne'
  rw [deningerRatExp_prod hne]
  have hterm : ∀ p ∈ f.support,
      deningerRatExp ((p : ℚ) ^ (f p)) = Finsupp.single p (f p) := by
    intro p hp
    rw [deningerRatExp_zpow (hpos p hp).ne' (f p), deningerRatExp_natCast_prime (hf p hp)]
    ext p'
    simp [Finsupp.single_apply]
  rw [Finset.sum_congr rfl hterm]
  exact Finsupp.sum_single f

/-- Every finitely supported exponent vector supported on primes is realized by a positive
rational. -/
theorem deningerRatExp_surjective_on_primes (f : ℕ →₀ ℤ) (hf : ∀ p ∈ f.support, p.Prime) :
    ∃ q : ℚ, 0 < q ∧ deningerRatExp q = f :=
  ⟨_, deningerPrimeProd_pos f hf, deningerRatExp_primeProd f hf⟩

/-- **Unique factorization of the positive rationals.**  The prime-exponent vector is a
bijection from the positive rationals onto the finitely supported integer vectors supported on
the primes. -/
theorem deningerRatExp_existsUnique (f : ℕ →₀ ℤ) (hf : ∀ p ∈ f.support, p.Prime) :
    ∃! q : ℚ, 0 < q ∧ deningerRatExp q = f := by
  obtain ⟨q, hqpos, hq⟩ := deningerRatExp_surjective_on_primes f hf
  refine ⟨q, ⟨hqpos, hq⟩, ?_⟩
  rintro r ⟨hrpos, hr⟩
  exact deningerRatExp_injOn_pos hrpos hqpos (by rw [hr, hq])

/-- The exponent vector does not see the sign, so it factors through `ℚ^× / {±1}`. -/
@[simp] theorem deningerRatExp_neg (q : ℚ) : deningerRatExp (-q) = deningerRatExp q := by
  ext p
  simp

/-- The exponent vector of an absolute value. -/
theorem deningerRatExp_abs (q : ℚ) : deningerRatExp |q| = deningerRatExp q := by
  rcases abs_choice q with h | h
  · rw [h]
  · rw [h, deningerRatExp_neg]

/-- The exponent vector is supported on primes. -/
theorem deningerRatExp_support_prime (q : ℚ) {p : ℕ} (hp : p ∈ (deningerRatExp q).support) :
    p.Prime := by
  by_contra h
  exact (Finsupp.mem_support_iff.mp hp) (deningerRatExp_apply_of_not_prime h q)

/-- **Unique factorization, product form.**  A positive rational is the product of its prime
powers. -/
theorem deningerRatExp_prod_eq {q : ℚ} (hq : 0 < q) :
    ∏ p ∈ (deningerRatExp q).support, (p : ℚ) ^ (deningerRatExp q p) = q := by
  classical
  have hprime : ∀ p ∈ (deningerRatExp q).support, p.Prime := fun p hp =>
    deningerRatExp_support_prime q hp
  exact deningerRatExp_injOn_pos (deningerPrimeProd_pos _ hprime) hq
    (deningerRatExp_primeProd _ hprime)

/-- **Logarithmic product formula.**  The logarithm of a positive rational is the sum of its
prime residues weighted by `log p`. -/
theorem deningerLog_eq_sum {q : ℚ} (hq : 0 < q) :
    Real.log q =
      ∑ p ∈ (deningerRatExp q).support, (deningerRatExp q p : ℝ) * Real.log p := by
  classical
  have hprime : ∀ p ∈ (deningerRatExp q).support, p.Prime := fun p hp =>
    deningerRatExp_support_prime q hp
  have hposR : ∀ p ∈ (deningerRatExp q).support, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    exact_mod_cast (hprime p hp).pos
  have hcast : ((q : ℚ) : ℝ)
      = ∏ p ∈ (deningerRatExp q).support, ((p : ℝ) ^ (deningerRatExp q p)) := by
    conv_lhs => rw [← deningerRatExp_prod_eq hq]
    push_cast
    rfl
  rw [hcast, Real.log_prod fun p hp => (zpow_pos (hposR p hp) _).ne']
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Real.log_zpow]

/-- **Real coefficients.**  Tensoring the free abelian group on the primes with `ℝ` gives the
real coordinate space `⨁_p ℝ`.  Combined with `deningerRatExp_existsUnique` this identifies
`(ℚ^× / {±1}) ⊗ ℝ` with `⨁_p ℝ`, with coordinates the residues `ord_p`. -/
noncomputable def deningerRatExpTensorReal :
    (ℕ →₀ ℤ) ⊗[ℤ] ℝ ≃ₗ[ℤ] (ℕ →₀ ℝ) :=
  TensorProduct.finsuppScalarLeft ℤ ℝ ℕ

@[simp] theorem deningerRatExpTensorReal_tmul_apply (f : ℕ →₀ ℤ) (x : ℝ) (p : ℕ) :
    deningerRatExpTensorReal (f ⊗ₜ[ℤ] x) p = f p • x :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply f x p

end RHTower
