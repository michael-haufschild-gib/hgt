import GaloisForLFunctions.RHTower.Sieve.PrimeProfileExponentTransfer
import GaloisForLFunctions.RHTower.Sieve.PrimeRangeSplit

/-!
# Partitioning a prime profile sum at equally spaced exponents

Cutting the scale at the exponents `j/m` splits the prime profile sum into a small-prime head
below `N^{1/m}` and `m - 1` windows,

`primeProfileSum g N = head + Σ_{j=1}^{m-1} Σ_{⌊N^{j/m}⌋ < p ≤ ⌊N^{(j+1)/m}⌋} g(log p/log N)/p`.

Because the exponent localization is exact, a Lipschitz profile is constant on each window up to
`L/m`, so the whole sum is the step sum `Σ_j g(j/m)·W_j` up to `(L/m)·Σ_j W_j`, where `W_j` is the
window's reciprocal prime mass.  Both statements are exact finite identities and inequalities: no
limit is taken here.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

theorem exponentCutoff_one (N : ℕ) : exponentCutoff 1 N = N := by
  rw [exponentCutoff, Real.rpow_one, Nat.floor_natCast]

theorem exponentCutoff_mono {a b : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 1 ≤ N) :
    exponentCutoff a N ≤ exponentCutoff b N := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hNR hab)

/-! ## The exact partition -/

theorem sum_primesLE_exponentCutoff_telescope (f : ℕ → ℝ) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m →
      ∑ p ∈ Nat.primesLE (exponentCutoff ((k : ℝ) / m) N), f p
        = ∑ p ∈ Nat.primesLE (exponentCutoff (1 / m) N), f p
          + ∑ j ∈ Finset.Ico 1 k,
              ∑ p ∈ bigPrimeSet (exponentCutoff ((j : ℝ) / m) N)
                (exponentCutoff (((j : ℝ) + 1) / m) N), f p := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ n ih =>
    intro _ hle
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero n)) with heq | hlt
    · -- `n + 1 = 1`
      have hn : n = 0 := by omega
      subst hn
      simp
    · have hn1 : 1 ≤ n := by omega
      have hnm : n ≤ m := by omega
      have hstep := ih hn1 hnm
      have hmono : exponentCutoff ((n : ℝ) / m) N ≤ exponentCutoff (((n : ℝ) + 1) / m) N := by
        refine exponentCutoff_mono ?_ hN
        have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        gcongr
        linarith
      have hsplit := sum_primesLE_split hmono f
      rw [Finset.sum_Ico_succ_top hn1]
      push_cast
      rw [hsplit, hstep]
      ring

/-- **The exact partition of a prime profile sum at equally spaced exponents.** -/
theorem primeProfileSum_partition (g : ℝ → ℝ) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    primeProfileSum g N
      = (∑ p ∈ Nat.primesLE (exponentCutoff (1 / m) N),
          g (Real.log p / Real.log N) / (p : ℝ))
        + ∑ j ∈ Finset.Ico 1 m,
            primeProfileWindowSum g N (exponentCutoff ((j : ℝ) / m) N)
              (exponentCutoff (((j : ℝ) + 1) / m) N) := by
  have hbase := sum_primesLE_exponentCutoff_telescope
    (fun p => g (Real.log p / Real.log N) / (p : ℝ)) hm hN m hm le_rfl
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by
    have : 0 < m := hm
    exact_mod_cast this.ne'
  rw [show ((m : ℕ) : ℝ) / (m : ℝ) = 1 from by field_simp, exponentCutoff_one] at hbase
  rw [primeProfileSum, hbase]
  rfl

/-! ## The step approximation on a Lipschitz profile -/

/-- The reciprocal prime mass of the `j`-th exponent window. -/
def exponentWindowMass (m N j : ℕ) : ℝ :=
  ∑ p ∈ bigPrimeSet (exponentCutoff ((j : ℝ) / m) N) (exponentCutoff (((j : ℝ) + 1) / m) N),
    1 / (p : ℝ)

theorem exponentWindowMass_nonneg (m N j : ℕ) : 0 ≤ exponentWindowMass m N j := by
  refine Finset.sum_nonneg ?_
  intro p _
  positivity

/-- **Each window is a step of the profile, up to `L/m`.** -/
theorem abs_primeProfileWindowSum_sub_step_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, |g s - g t| ≤ L * |s - t|) {m N : ℕ} (hm : 1 ≤ m) (hN : 2 ≤ N) (j : ℕ) :
    |primeProfileWindowSum g N (exponentCutoff ((j : ℝ) / m) N)
          (exponentCutoff (((j : ℝ) + 1) / m) N)
        - g ((j : ℝ) / m) * exponentWindowMass m N j|
      ≤ L / m * exponentWindowMass m N j := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hε : (0 : ℝ) ≤ L / m := by positivity
  have hgb : ∀ t : ℝ, (j : ℝ) / m < t → t ≤ ((j : ℝ) + 1) / m →
      |g t - g ((j : ℝ) / m)| ≤ L / m := by
    intro t hlow hhigh
    refine le_trans (hlip t ((j : ℝ) / m)) ?_
    have habs : |t - (j : ℝ) / m| ≤ 1 / m := by
      rw [abs_of_nonneg (by linarith)]
      have hgap : ((j : ℝ) + 1) / m - (j : ℝ) / m = 1 / m := by
        field_simp
        ring
      linarith
    calc L * |t - (j : ℝ) / m| ≤ L * (1 / m) := mul_le_mul_of_nonneg_left habs hL
      _ = L / m := by ring
  exact abs_primeProfileWindowSum_sub_le hε hgb hN

/-- **The profile sum is its step sum, up to `(L/m)` times the total window mass.** -/
theorem abs_primeProfileSum_sub_stepSum_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, |g s - g t| ≤ L * |s - t|) {m N : ℕ} (hm : 1 ≤ m) (hN : 2 ≤ N) :
    |primeProfileSum g N
        - ((∑ p ∈ Nat.primesLE (exponentCutoff (1 / m) N),
              g (Real.log p / Real.log N) / (p : ℝ))
          + ∑ j ∈ Finset.Ico 1 m, g ((j : ℝ) / m) * exponentWindowMass m N j)|
      ≤ L / m * ∑ j ∈ Finset.Ico 1 m, exponentWindowMass m N j := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  rw [primeProfileSum_partition g hm hN1]
  have hrw : (∑ p ∈ Nat.primesLE (exponentCutoff (1 / m) N),
        g (Real.log p / Real.log N) / (p : ℝ))
      + ∑ j ∈ Finset.Ico 1 m,
          primeProfileWindowSum g N (exponentCutoff ((j : ℝ) / m) N)
            (exponentCutoff (((j : ℝ) + 1) / m) N)
      - ((∑ p ∈ Nat.primesLE (exponentCutoff (1 / m) N),
            g (Real.log p / Real.log N) / (p : ℝ))
        + ∑ j ∈ Finset.Ico 1 m, g ((j : ℝ) / m) * exponentWindowMass m N j)
      = ∑ j ∈ Finset.Ico 1 m,
          (primeProfileWindowSum g N (exponentCutoff ((j : ℝ) / m) N)
              (exponentCutoff (((j : ℝ) + 1) / m) N)
            - g ((j : ℝ) / m) * exponentWindowMass m N j) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hrw, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro j _
  exact abs_primeProfileWindowSum_sub_step_le hL hlip hm hN j

end

end RHTower.Sieve
