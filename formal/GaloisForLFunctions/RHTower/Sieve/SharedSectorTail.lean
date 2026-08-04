import GaloisForLFunctions.RHTower.Sieve.SharedSectorBound
import GaloisForLFunctions.RHTower.Sieve.SharedPrimeTailLimit

/-!
# The large-prime part of the union bound

Feeding the sector bound `(10)` into the tail estimate `(11)` gives

    ∑_{P < p ≤ 2√x} C_p(x,h) / (h√x)  ≤  9/P + 3·(the excess already shown to vanish).

The crude replacements `√x + 2 ≤ 3√x` and `h + 2 ≤ 3h` cost only the constant `9` in place of `1`,
and `(11)` needs nothing sharper: the whole point is that the bound tends to zero as the cut-off `P`
grows, uniformly in `x`.  The sharp constant `D²A` of the card's `(12)` comes from the *small*
primes, through `(9)`, not from this tail.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- **The large-prime part of the union bound.** -/
theorem sharedSector_tail_le {x h : ℝ} (hx : 4 ≤ x) (hh : 1 ≤ h) {P Q : ℕ} (hP : 1 ≤ P) :
    ∑ p ∈ bigPrimeSet P Q, sharedSectorCount x h p
      ≤ 3 * Real.sqrt x * (3 * h) / (P : ℝ)
        + (3 * Real.sqrt x + 3 * h) * mertensS Q + (Q : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    have heq : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h4, heq.le, heq.ge]
  have hterm : ∀ p ∈ bigPrimeSet P Q,
      sharedSectorCount x h p ≤ (3 * Real.sqrt x / (p : ℝ) + 1) * (3 * h / (p : ℝ) + 1) := by
    intro p hp
    have hprime : p.Prime := prime_of_mem_bigPrimeSet hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    refine le_trans (sharedSectorCount_le_product hx (by linarith) hprime.pos) ?_
    have h1 : (Real.sqrt x + 2) / (p : ℝ) + 1 ≤ 3 * Real.sqrt x / (p : ℝ) + 1 := by
      have : (Real.sqrt x + 2) / (p : ℝ) ≤ 3 * Real.sqrt x / (p : ℝ) := by
        gcongr
        linarith
      linarith
    have h2 : (h + 2) / (p : ℝ) + 1 ≤ 3 * h / (p : ℝ) + 1 := by
      have : (h + 2) / (p : ℝ) ≤ 3 * h / (p : ℝ) := by
        gcongr
        linarith
      linarith
    have h10 : (0 : ℝ) ≤ (Real.sqrt x + 2) / (p : ℝ) + 1 := by positivity
    have h20 : (0 : ℝ) ≤ (h + 2) / (p : ℝ) + 1 := by positivity
    exact mul_le_mul h1 h2 h20 (by linarith)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  exact sum_pair_tail_le hP Q (by positivity) (by linarith)

/-- **The normalised large-prime tail**, reduced to the excess already shown to vanish. -/
theorem sharedSector_tail_normalized_le {x h : ℝ} (hx : 4 ≤ x) (hh : 1 ≤ h) {P : ℕ} (hP : 1 ≤ P) :
    (∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊, sharedSectorCount x h p) / (h * Real.sqrt x)
      ≤ 9 / (P : ℝ)
        + 3 * (((Real.sqrt x + h) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x)
          / (h * Real.sqrt x)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hh0 : (0 : ℝ) < h := by linarith
  have hden : (0 : ℝ) < h * Real.sqrt x := by positivity
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hQle : ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x := Nat.floor_le (by positivity)
  have hbase := sharedSector_tail_le hx hh (Q := ⌊2 * Real.sqrt x⌋₊) hP
  rw [div_le_iff₀ hden]
  refine le_trans hbase ?_
  have hrw : (9 / (P : ℝ)
      + 3 * (((Real.sqrt x + h) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x)
        / (h * Real.sqrt x))) * (h * Real.sqrt x)
      = 9 * (h * Real.sqrt x) / (P : ℝ)
        + 3 * ((Real.sqrt x + h) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x) := by
    field_simp
  rw [hrw]
  have hfirst : 3 * Real.sqrt x * (3 * h) / (P : ℝ) = 9 * (h * Real.sqrt x) / (P : ℝ) := by
    ring
  rw [hfirst]
  have hsecond : (3 * Real.sqrt x + 3 * h) * mertensS ⌊2 * Real.sqrt x⌋₊
      = 3 * ((Real.sqrt x + h) * mertensS ⌊2 * Real.sqrt x⌋₊) := by ring
  rw [hsecond]
  linarith [hQle]

/-- **Card equation (11) for the sectors.**  The large-prime tail is uniformly small. -/
theorem exists_sharedSector_tail_small {hh : ℝ → ℝ}
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, 1 ≤ P ∧ ∀ᶠ x in atTop,
      (∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊, sharedSectorCount x (hh x) p)
        / (hh x * Real.sqrt x) ≤ ε := by
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  have hexc := tendsto_shared_prime_excess hgrow
  obtain ⟨M, hM⟩ := exists_nat_gt (18 / ε)
  refine ⟨max M 1, le_max_right _ _, ?_⟩
  have hP1 : 1 ≤ max M 1 := le_max_right _ _
  have hPpos : (0 : ℝ) < ((max M 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((max M 1 : ℕ) : ℝ) := by exact_mod_cast hP1
    linarith
  have hPM : ((M : ℕ) : ℝ) ≤ ((max M 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_left M 1
  have hsmall : 9 / ((max M 1 : ℕ) : ℝ) ≤ ε / 2 := by
    rw [div_le_div_iff₀ hPpos (by norm_num)]
    have h2 : 18 / ε < ((max M 1 : ℕ) : ℝ) := lt_of_lt_of_le hM hPM
    rw [div_lt_iff₀ hε] at h2
    linarith
  filter_upwards [eventually_ge_atTop (4 : ℝ), hhtop.eventually_ge_atTop (1 : ℝ),
    hexc.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 6))] with x hx hh1 hE
  have hbound := sharedSector_tail_normalized_le hx hh1 hP1
  have hEle : ((Real.sqrt x + hh x) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x)
      / (hh x * Real.sqrt x) ≤ ε / 6 := hE.le
  linarith

end RHTower.Sieve
