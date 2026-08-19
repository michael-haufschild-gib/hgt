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

/-! ## The Rankin atom for the truncation tail -/

/-- **Rankin's trick for large divisors.**  The number of divisors of `m` exceeding `D` is at most
`D^{-α}` times the `α`-th divisor moment, for any positive `α`.  This is the atom of the mean-square
bound for the term `c₁,n` of Matomäki–Teräväinen, Lemma 2.3. -/
theorem card_large_divisors_le_rankin {m D : ℕ} {α : ℝ} (hα : 0 < α) (hD : 0 < D) :
    (((m.divisors.filter (fun e => D < e)).card : ℕ) : ℝ)
      ≤ (D : ℝ) ^ (-α) * ∑ e ∈ m.divisors, (e : ℝ) ^ α := by
  classical
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDpow : (0 : ℝ) < (D : ℝ) ^ (-α) := Real.rpow_pos_of_pos hDR _
  -- each large divisor contributes at least one unit of `D^{-α}e^α`
  have hterm : ∀ e ∈ m.divisors.filter (fun e => D < e),
      (1 : ℝ) ≤ (D : ℝ) ^ (-α) * (e : ℝ) ^ α := by
    intro e he
    rw [Finset.mem_filter] at he
    have hDe : (D : ℝ) ≤ (e : ℝ) := by exact_mod_cast he.2.le
    have hepow : (D : ℝ) ^ α ≤ (e : ℝ) ^ α := Real.rpow_le_rpow hDR.le hDe hα.le
    have hDα : (0 : ℝ) < (D : ℝ) ^ α := Real.rpow_pos_of_pos hDR _
    have hinv : (D : ℝ) ^ (-α) = ((D : ℝ) ^ α)⁻¹ := by
      rw [Real.rpow_neg hDR.le]
    rw [hinv, ← div_eq_inv_mul, le_div_iff₀ hDα]
    linarith [hepow]
  have hcard : (((m.divisors.filter (fun e => D < e)).card : ℕ) : ℝ)
      ≤ ∑ e ∈ m.divisors.filter (fun e => D < e), (D : ℝ) ^ (-α) * (e : ℝ) ^ α := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact this
  refine hcard.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hDpow.le
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun e _ _ => ?_
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The same, applied to the truncation tail of the Legendre expansion. -/
theorem truncTail_le_rankin {k z D : ℕ} {α : ℝ} (hα : 0 < α) (hD : 0 < D) :
    ((truncTail k z D : ℕ) : ℝ)
      ≤ (D : ℝ) ^ (-α) * ∑ e ∈ (Nat.gcd k (siftModulus z)).divisors, (e : ℝ) ^ α := by
  classical
  have hfilter : (Nat.gcd k (siftModulus z)).divisors.filter (fun e => ¬ e ≤ D)
      = (Nat.gcd k (siftModulus z)).divisors.filter (fun e => D < e) := by
    refine Finset.filter_congr fun e _ => ?_
    simp [not_le]
  rw [truncTail, hfilter]
  exact card_large_divisors_le_rankin hα hD

end RHTower.Sieve
