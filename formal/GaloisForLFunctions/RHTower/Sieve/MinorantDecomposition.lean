import GaloisForLFunctions.RHTower.Sieve.HarmanMinorant
import GaloisForLFunctions.RHTower.Sieve.AdicBlocks

/-!
# The first step of the minorant decomposition

Matomäki–Teräväinen, Lemma 2.3(i): a divisor sum against the sifting function at level `z₁` equals
a truncated Legendre main term at level `z₀` minus a Buchstab remainder over the primes in
`[z₀, z₁)`, up to an error controlled by the discarded divisors.  Here the identity is proved with
the error named and bounded pointwise; the `(1+δ)`-adic grouping of the prime variable is supplied
by `Sieve/AdicBlocks`, and replacing the sieve level `q` by the bottom of its block costs the
Buchstab remainder over the block, which is `rho_sub_rho_eq_sum`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The truncated Legendre main term at level `z` with divisors cut at `D`. -/
def truncLegendre (k z D : ℕ) : ℤ :=
  ∑ e ∈ (Nat.gcd k (siftModulus z)).divisors.filter (fun e => e ≤ D), moebius e

/-- The number of divisors discarded by the truncation. -/
def truncTail (k z D : ℕ) : ℕ :=
  ((Nat.gcd k (siftModulus z)).divisors.filter (fun e => ¬ e ≤ D)).card

theorem abs_rho_sub_truncLegendre_le {k z D : ℕ} (hk : 0 < k) :
    |(rho k z : ℤ) - truncLegendre k z D| ≤ (truncTail k z D : ℤ) :=
  abs_rho_sub_truncated_moebius_le hk

/-- **Replacing the sieve level by the bottom of its block.**  The difference is the Buchstab
remainder over the primes of the block. -/
theorem rho_sub_rho_eq_sum {k Q q : ℕ} (hk : 0 < k) (hQq : Q ≤ q) :
    (rho k Q : ℤ) - (rho k q : ℤ) = ∑ p ∈ primeWindow k Q q, (rho (k / p) p : ℤ) := by
  have h := buchstab_window (n := k) (w := Q) (z := q) hk hQq
  have hZ : (rho k q : ℤ) + ((∑ p ∈ primeWindow k Q q, rho (k / p) p : ℕ) : ℤ)
      = (rho k Q : ℤ) := by exact_mod_cast h
  push_cast at hZ
  linarith

theorem rho_sub_rho_le_card {k Q q : ℕ} (hk : 0 < k) (hQq : Q ≤ q) :
    (rho k Q : ℤ) - (rho k q : ℤ) ≤ ((primeWindow k Q q).card : ℤ) := by
  rw [rho_sub_rho_eq_sum hk hQq]
  have h1 : ∑ p ∈ primeWindow k Q q, (rho (k / p) p : ℤ)
      ≤ ∑ _p ∈ primeWindow k Q q, (1 : ℤ) :=
    Finset.sum_le_sum fun p _ => by exact_mod_cast rho_le_one (k / p) p
  simpa using h1

/-- **Lemma 2.3(i), the exact identity with a named error.**  A divisor sum against the level-`z₁`
sifting function splits into the truncated Legendre term at level `z₀` and the Buchstab remainder
over `[z₀, z₁)`. -/
theorem divisor_sum_rho_decomp {n z₀ z₁ D : ℕ} (α : ℕ → ℤ) (hn : 0 < n) (hz : z₀ ≤ z₁) :
    |(∑ m ∈ n.divisors, α m * (rho (n / m) z₁ : ℤ))
        - (∑ m ∈ n.divisors, α m * truncLegendre (n / m) z₀ D
          - ∑ m ∈ n.divisors, ∑ q ∈ primeWindow (n / m) z₀ z₁,
              α m * (rho (n / m / q) q : ℤ))|
      ≤ ∑ m ∈ n.divisors, |α m| * (truncTail (n / m) z₀ D : ℤ) := by
  classical
  have e1 : (∑ m ∈ n.divisors, α m * truncLegendre (n / m) z₀ D
        - ∑ m ∈ n.divisors, ∑ q ∈ primeWindow (n / m) z₀ z₁, α m * (rho (n / m / q) q : ℤ))
      = ∑ m ∈ n.divisors, (α m * truncLegendre (n / m) z₀ D
          - ∑ q ∈ primeWindow (n / m) z₀ z₁, α m * (rho (n / m / q) q : ℤ)) :=
    (Finset.sum_sub_distrib _ _).symm
  have e2 : (∑ m ∈ n.divisors, α m * (rho (n / m) z₁ : ℤ))
        - ∑ m ∈ n.divisors, (α m * truncLegendre (n / m) z₀ D
          - ∑ q ∈ primeWindow (n / m) z₀ z₁, α m * (rho (n / m / q) q : ℤ))
      = ∑ m ∈ n.divisors, (α m * (rho (n / m) z₁ : ℤ)
          - (α m * truncLegendre (n / m) z₀ D
            - ∑ q ∈ primeWindow (n / m) z₀ z₁, α m * (rho (n / m / q) q : ℤ))) :=
    (Finset.sum_sub_distrib _ _).symm
  have hrw : (∑ m ∈ n.divisors, α m * (rho (n / m) z₁ : ℤ))
        - (∑ m ∈ n.divisors, α m * truncLegendre (n / m) z₀ D
          - ∑ m ∈ n.divisors, ∑ q ∈ primeWindow (n / m) z₀ z₁, α m * (rho (n / m / q) q : ℤ))
      = ∑ m ∈ n.divisors, α m * ((rho (n / m) z₁ : ℤ) - truncLegendre (n / m) z₀ D
          + ∑ q ∈ primeWindow (n / m) z₀ z₁, (rho (n / m / q) q : ℤ)) := by
    rw [e1, e2]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_add, mul_sub, Finset.mul_sum]
    ring
  rw [hrw]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun m hm => ?_)
  have hmn : m ∣ n := (Nat.mem_divisors.1 hm).1
  have hk : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmn) (Nat.pos_of_mem_divisors hm)
  have hbuch : (rho (n / m) z₀ : ℤ) - (rho (n / m) z₁ : ℤ)
      = ∑ q ∈ primeWindow (n / m) z₀ z₁, (rho (n / m / q) q : ℤ) := rho_sub_rho_eq_sum hk hz
  have hval : (rho (n / m) z₁ : ℤ) - truncLegendre (n / m) z₀ D
      + ∑ q ∈ primeWindow (n / m) z₀ z₁, (rho (n / m / q) q : ℤ)
      = (rho (n / m) z₀ : ℤ) - truncLegendre (n / m) z₀ D := by
    rw [← hbuch]; ring
  rw [hval, abs_mul]
  refine mul_le_mul_of_nonneg_left (abs_rho_sub_truncLegendre_le hk) (abs_nonneg _)

end RHTower.Sieve
