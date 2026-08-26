import GaloisForLFunctions.RHTower.Sieve.BivariateDiagonalShift

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

private theorem sum_divisor_subtype_eq_sum' {M : Type*} [AddCommMonoid M]
    (s : Finset ℕ) (f : ℕ → M) :
    (∑ x : {x // x ∈ s}, f x.1) = ∑ x ∈ s, f x := by
  change (∑ x ∈ s.attach, f x.1) = _
  exact Finset.sum_attach s f

theorem bivariateDirichletConvolution_prime_pow
    (f g : ℕ → ℕ → ℝ) {p i j : ℕ} (hp : p.Prime) :
    bivariateDirichletConvolution f g (p ^ i) (p ^ j) =
      additiveBivariateConvolution
        (fun a b => f (p ^ a) (p ^ b))
        (fun a b => g (p ^ a) (p ^ b)) i j := by
  rw [bivariateDirichletConvolution, if_neg (by simp [hp.ne_zero]),
    Fintype.sum_prod_type]
  change (∑ x : {x // x ∈ (p ^ i).divisors},
      ∑ y : {y // y ∈ (p ^ j).divisors},
        f x.1 y.1 * g ((p ^ i) / x.1) ((p ^ j) / y.1)) = _
  have houter := sum_divisor_subtype_eq_sum' (p ^ i).divisors
    (fun x => ∑ y : {y // y ∈ (p ^ j).divisors},
      f x y.1 * g ((p ^ i) / x) ((p ^ j) / y.1))
  rw [houter]
  have hinner :
      (∑ x ∈ (p ^ i).divisors, ∑ y : {y // y ∈ (p ^ j).divisors},
        f x y.1 * g ((p ^ i) / x) ((p ^ j) / y.1)) =
      ∑ x ∈ (p ^ i).divisors, ∑ y ∈ (p ^ j).divisors,
        f x y * g ((p ^ i) / x) ((p ^ j) / y) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact sum_divisor_subtype_eq_sum' (p ^ j).divisors
      (fun y => f x y * g ((p ^ i) / x) ((p ^ j) / y))
  rw [hinner, Nat.sum_divisors_prime_pow hp]
  rw [additiveBivariateConvolution]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro b hb
  have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  rw [Nat.pow_div hai hp.pos, Nat.pow_div hbj hp.pos]

end

end RHTower.Sieve
