import GaloisForLFunctions.RHTower.Sieve.DivisorSquareSum
import GaloisForLFunctions.RHTower.Sieve.OmegaTail

/-!
# The lower tail through the Selberg sieve

Brun's pure sieve pays for its truncation twice: the defect `(log z)^λ / λ^r` forces `r ≳ log log z`,
and the `2^r`-sized divisor error forces `r log z ≲ log(b-a)`.  Together they cap the sifting range
at `log z ≍ log(b-a) / log log (b-a)`, so the density gained is `1/log z` rather than the expected
`1/log(b-a)`.

The Selberg sieve has no truncation defect.  Its density is `2 / log Y` for every level `Y ≤ z`, and
its whole error is confined to divisors `d ≤ Y²` with `|Λ²_d| ≤ 4^{ω d}`, so it is at most
`Y² exp(4 c₁)(log z)^(4 : ℕ)`.  Choosing `Y` a small power of the interval length therefore gives the
lower-tail bound with `log Y ≍ log(b-a)`, with no `log log` loss.

This module transports that fibrewise bound through the same smooth/rough fibring used for the pure
sieve, giving the Selberg form of the lower tail.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The per-fibre Selberg error: the level `Y²` times a fourth power of `log z`. -/
noncomputable def selbergFibreError (z Y : ℕ) : ℝ :=
  ((Y * Y : ℕ) : ℝ) * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))

theorem selbergFibreError_nonneg {z : ℕ} (hz : 2 ≤ z) (Y : ℕ) : 0 ≤ selbergFibreError z Y := by
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hpow : (0 : ℝ) ≤ (Real.log z) ^ (4 : ℝ) := Real.rpow_nonneg hlogz.le 4
  unfold selbergFibreError
  positivity

/-- **Rough integers in an interval, Selberg form.**  Density `2/log Y` with an error confined to
the level `Y²`, for every `1 ≤ Y ≤ z`. -/
theorem card_rough_Ioc_le_selberg (a b z Y : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z)
    (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    (#{n ∈ Finset.Ioc a b | ∀ p ∈ Nat.primesLE z, ¬ p ∣ n} : ℝ)
      ≤ ((b : ℝ) - a) * (2 / Real.log Y) + selbergFibreError z Y := by
  classical
  have hset : {n ∈ Finset.Ioc a b | ∀ p ∈ Nat.primesLE z, ¬ p ∣ n}
      = {n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n} := by
    refine Finset.filter_congr ?_
    intro n _
    exact ((coprime_primorial_iff (z := z) (n := n)).symm).trans Nat.coprime_comm
  rw [hset]
  have hbase := card_coprime_Ioc_le_explicit a b z Y hab hY hYz hz hlog
  have hring : 2 * ((b : ℝ) - a) / Real.log Y = ((b : ℝ) - a) * (2 / Real.log Y) := by ring
  rw [hring] at hbase
  exact hbase

/-- **Lower-tail bound, Selberg form.**  The number of integers of `Ioc a b` with at most `k`
distinct prime factors is bounded by the Selberg density `2/log Y` times the tilted weight of the
surviving smooth parts, plus one Selberg error per surviving smooth part. -/
theorem card_omega_le_le_selberg (a b z Y k : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z)
    (hz : 2 ≤ z) (hlog : 0 < Real.log Y) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℝ)
      ≤ ((b : ℝ) - a) * (2 / Real.log Y) * smoothTiltBound z k t
        + (2 / Real.log Y + selbergFibreError z Y) * smoothIndexBound z b k := by
  classical
  set T : Finset ℕ := {s ∈ smoothUpTo (Nat.primesLE z) b | s.primeFactors.card ≤ k} with hT
  set R : ℝ := 2 / Real.log Y with hR
  set E : ℝ := selbergFibreError z Y with hE
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hE0 : 0 ≤ E := selbergFibreError_nonneg hz Y
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hstart : (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℝ)
      ≤ ∑ σ ∈ T, ((#{m ∈ Finset.Ioc (a / σ) (b / σ) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) : ℝ) := by
    have := card_omega_le_le_sum a b z k
    exact_mod_cast this
  have hfibre : ∀ σ ∈ T,
      ((#{m ∈ Finset.Ioc (a / σ) (b / σ) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) : ℝ)
        ≤ ((b : ℝ) - a) * R * (1 / σ) + (R + E) := by
    intro σ hσ
    obtain ⟨hσmem, -⟩ := Finset.mem_filter.1 hσ
    obtain ⟨⟨hσ1, hσb⟩, -⟩ := mem_smoothUpTo.1 hσmem
    have hσpos : 0 < σ := hσ1
    have hσR : (0 : ℝ) < σ := by exact_mod_cast hσpos
    have hdivle : a / σ ≤ b / σ := Nat.div_le_div_right hab
    have hsieve := card_rough_Ioc_le_selberg (a / σ) (b / σ) z Y hdivle hY hYz hz hlog
    have hgap : ((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ) ≤ ((b : ℝ) - a) / σ + 1 := by
      have hb := (cast_div_bounds (d := σ) (n := b) hσpos).1
      have ha := (cast_div_bounds (d := σ) (n := a) hσpos).2
      have hsplit : ((b : ℝ) - a) / σ = (b : ℝ) / σ - (a : ℝ) / σ := by ring
      rw [hsplit]
      linarith
    have hmul : (((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ)) * R ≤ (((b : ℝ) - a) / σ + 1) * R :=
      mul_le_mul_of_nonneg_right hgap hR0
    have hfin : (((b : ℝ) - a) / σ + 1) * R = ((b : ℝ) - a) * R * (1 / σ) + R := by
      field_simp
    linarith
  refine le_trans hstart (le_trans (Finset.sum_le_sum hfibre) ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hsum : ∑ σ ∈ T, (1 : ℝ) / σ ≤ smoothTiltBound z k t := by
    rw [hT]
    exact sum_smoothUpTo_card_le_inv_le_exp ht0 ht1 k hz b
  have hcard : (T.card : ℝ) ≤ smoothIndexBound z b k := by
    rw [hT, smoothIndexBound]
    have := card_smoothUpTo_card_primeFactors_le z b k
    exact_mod_cast this
  have hpos1 : 0 ≤ ((b : ℝ) - a) * R := mul_nonneg hlen hR0
  have h1 : ((b : ℝ) - a) * R * ∑ σ ∈ T, (1 : ℝ) / σ
      ≤ ((b : ℝ) - a) * R * smoothTiltBound z k t :=
    mul_le_mul_of_nonneg_left hsum hpos1
  have h2 : (T.card : ℝ) * (R + E) ≤ smoothIndexBound z b k * (R + E) :=
    mul_le_mul_of_nonneg_right hcard (by linarith)
  calc ((b : ℝ) - a) * R * ∑ σ ∈ T, (1 : ℝ) / σ + (T.card : ℝ) * (R + E)
      ≤ ((b : ℝ) - a) * R * smoothTiltBound z k t + smoothIndexBound z b k * (R + E) := by
        linarith
    _ = ((b : ℝ) - a) * R * smoothTiltBound z k t + (R + E) * smoothIndexBound z b k := by ring

end RHTower.Sieve
