import GaloisForLFunctions.RHTower.Sieve.HardyRamanujanCut

/-!
# The real-valued Hardy–Ramanujan step

The cut recursion is a statement about cardinalities; the analytic induction needs it in the shape
`count ≤ A · length + B`.  Transporting the recursion through the interval-multiple bound
`⌊v/q⌋ - ⌊u/q⌋ ≤ (v-u)/q + 1` turns one step into

`(j - R) · S_j(a,b) ≤ A · (b-a) · ∑_{q ≤ Q} 1/q + (A + B) · #{q ≤ Q}`,

so the density constant is multiplied by the prime power reciprocal sum — `log log b + O(1)` by
Mertens — while the additive error is multiplied by the number of prime powers below the cut, which
is at most `Q`.

Both weights are the ones evaluated in `PrimePowerSum.lean`, so a single step of the induction is
completely explicit.
-/

namespace RHTower.Sieve

open Finset Nat

/-- Every member of the prime power set is at least two. -/
theorem two_le_of_mem_primePowerSet {z Y q : ℕ} (hq : q ∈ primePowerSet z Y) : 2 ≤ q := by
  rw [primePowerSet] at hq
  obtain ⟨⟨p, e⟩, hmem, rfl⟩ := Finset.mem_image.1 hq
  obtain ⟨hp, he⟩ := Finset.mem_product.1 hmem
  have hprime : p.Prime := Nat.prime_of_mem_primesLE hp
  have he1 : 1 ≤ e := (Finset.mem_Icc.1 he).1
  calc 2 = 2 ^ (1 : ℕ) := by norm_num
    _ ≤ p ^ (1 : ℕ) := Nat.pow_le_pow_left hprime.two_le 1
    _ ≤ p ^ e := Nat.pow_le_pow_right hprime.pos he1

/-- The cut prime power set has at most `Q` members. -/
theorem card_primePowerSet_cut_le (z Y Q : ℕ) :
    (#{q ∈ primePowerSet z Y | q ≤ Q}) ≤ Q := by
  classical
  have hsub : {q ∈ primePowerSet z Y | q ≤ Q} ⊆ Finset.Icc 1 Q := by
    intro q hq
    obtain ⟨hmem, hle⟩ := Finset.mem_filter.1 hq
    have := two_le_of_mem_primePowerSet hmem
    exact Finset.mem_Icc.2 ⟨by omega, hle⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Icc]
  omega

/-- **Real-valued cut step.**  One Hardy–Ramanujan step in the `A · length + B` shape. -/
theorem card_omegaLevel_step {b j Q R : ℕ} (hQ : 2 ≤ Q) (hR : b < Q ^ (R + 1))
    {A B : ℝ} (hA : 0 ≤ A)
    (hind : ∀ u v : ℕ, u ≤ v → v ≤ b →
      ((omegaLevel u v (j - 1)).card : ℝ) ≤ A * ((v : ℝ) - u) + B)
    (a : ℕ) (hab : a ≤ b) :
    ((j - R : ℕ) : ℝ) * ((omegaLevel a b j).card : ℝ)
      ≤ A * ((b : ℝ) - a) * (∑ q ∈ {q ∈ primePowerSet b b | q ≤ Q}, (1 : ℝ) / q)
        + (A + B) * ((#{q ∈ primePowerSet b b | q ≤ Q} : ℕ) : ℝ) := by
  classical
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hnat := card_omegaLevel_mul_le_cut a b j Q R hQ hR
  have hstart : ((j - R : ℕ) : ℝ) * ((omegaLevel a b j).card : ℝ)
      ≤ ∑ q ∈ {q ∈ primePowerSet b b | q ≤ Q},
          ((omegaLevel (a / q) (b / q) (j - 1)).card : ℝ) := by
    exact_mod_cast hnat
  have hterm : ∀ q ∈ {q ∈ primePowerSet b b | q ≤ Q},
      ((omegaLevel (a / q) (b / q) (j - 1)).card : ℝ)
        ≤ A * (((b : ℝ) - a) * (1 / q)) + (A + B) := by
    intro q hq
    obtain ⟨hmem, -⟩ := Finset.mem_filter.1 hq
    have hq2 : 2 ≤ q := two_le_of_mem_primePowerSet hmem
    have hqpos : 0 < q := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hdivle : a / q ≤ b / q := Nat.div_le_div_right hab
    have hbq : b / q ≤ b := Nat.div_le_self b q
    have hbase := hind (a / q) (b / q) hdivle hbq
    have hgap : ((b / q : ℕ) : ℝ) - ((a / q : ℕ) : ℝ) ≤ ((b : ℝ) - a) / q + 1 := by
      have hb := (cast_div_bounds (d := q) (n := b) hqpos).1
      have ha := (cast_div_bounds (d := q) (n := a) hqpos).2
      have hsp : ((b : ℝ) - a) / q = (b : ℝ) / q - (a : ℝ) / q := by ring
      rw [hsp]
      linarith
    have hmul : A * (((b / q : ℕ) : ℝ) - ((a / q : ℕ) : ℝ)) ≤ A * (((b : ℝ) - a) / q + 1) :=
      mul_le_mul_of_nonneg_left hgap hA
    have hrw : ((b : ℝ) - a) / q = ((b : ℝ) - a) * (1 / q) := by ring
    rw [hrw] at hmul
    linarith
  refine le_trans hstart (le_trans (Finset.sum_le_sum hterm) ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hcong : ∑ q ∈ {q ∈ primePowerSet b b | q ≤ Q}, ((b : ℝ) - a) * (1 / q)
      = ((b : ℝ) - a) * ∑ q ∈ {q ∈ primePowerSet b b | q ≤ Q}, (1 : ℝ) / q :=
    (Finset.mul_sum _ _ _).symm
  rw [hcong, ← mul_assoc, mul_comm ((#{q ∈ primePowerSet b b | q ≤ Q} : ℕ) : ℝ) (A + B)]

end RHTower.Sieve
