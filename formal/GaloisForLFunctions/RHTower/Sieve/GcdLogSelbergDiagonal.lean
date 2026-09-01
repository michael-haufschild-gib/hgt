import GaloisForLFunctions.RHTower.Sieve.DivisorSquareMoment
import GaloisForLFunctions.RHTower.Sieve.MaskedSymmetry

/-!
# Selberg diagonalisation of the gcd-logarithm pair weight

The lcm quadratic forms of an origin-based harmonic window carry the factor `log [q,r]`, which the
identity `log [q,r] = log q + log r - log (q,r)` reduces to the pair weight `(q,r) · log (q,r)`.
That weight is separable in exactly the same way as the gcd itself:

`(q,r) = ∑_{e ∣ q, e ∣ r} φ(e)` and `log (q,r) = ∑_{d ∣ q, d ∣ r} Λ(d)`,

so their product is a double indicator sum, and `e ∣ n ∧ d ∣ n ↔ [e,d] ∣ n` turns the quadratic form
into a diagonal one against the two-variable weight `φ(e) Λ(d)` on the lcm fibres.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction

noncomputable section

namespace RHTower.Sieve

/-- Indicator form of the logarithm of a gcd. -/
theorem log_gcd_eq_sum_vonMangoldt_indicator {N a b : ℕ} (ha : 1 ≤ a) (haN : a ≤ N)
    (_hb : 1 ≤ b) :
    Real.log (Nat.gcd a b) =
      ∑ d ∈ Finset.Icc 1 N, (if d ∣ a ∧ d ∣ b then Λ d else 0) := by
  have hg1 : 1 ≤ Nat.gcd a b := Nat.gcd_pos_of_pos_left b (by omega)
  have hgN : Nat.gcd a b ≤ N :=
    le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)) haN
  have hsum : ∑ d ∈ (Nat.gcd a b).divisors, Λ d = Real.log (Nat.gcd a b) :=
    vonMangoldt_sum
  have hfilter : (Nat.gcd a b).divisors = (Finset.Icc 1 N).filter (fun d => d ∣ a ∧ d ∣ b) := by
    rw [divisors_eq_filter_Icc hg1 hgN]
    refine Finset.filter_congr fun d _ => ?_
    simp [Nat.dvd_gcd_iff]
  rw [← hsum, hfilter, Finset.sum_filter]

/-- **Diagonalisation of the gcd-logarithm quadratic form.** -/
theorem sum_gcdLog_weight_eq_double_diagonal
    {S : Finset ℕ} {M : ℕ} (f : ℕ → ℝ)
    (hpos : ∀ d ∈ S, 0 < d) (hM : ∀ d ∈ S, d ≤ M) :
    (∑ p ∈ S ×ˢ S,
        ((Nat.gcd p.1 p.2 : ℝ) * Real.log (Nat.gcd p.1 p.2)) * f p.1 * f p.2) =
      ∑ w ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        (Nat.totient w.1 : ℝ) * Λ w.2 *
          (∑ d ∈ S.filter (fun d => Nat.lcm w.1 w.2 ∣ d), f d) ^ 2 := by
  classical
  have hpair : ∀ p ∈ S ×ˢ S,
      ((Nat.gcd p.1 p.2 : ℝ) * Real.log (Nat.gcd p.1 p.2)) * f p.1 * f p.2 =
        ∑ w ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
          (Nat.totient w.1 : ℝ) * Λ w.2 *
            (if Nat.lcm w.1 w.2 ∣ p.1 then f p.1 else 0) *
              (if Nat.lcm w.1 w.2 ∣ p.2 then f p.2 else 0) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have ha1 : 1 ≤ p.1 := hpos p.1 hp1
    have ha2 : 1 ≤ p.2 := hpos p.2 hp2
    rw [log_gcd_eq_sum_vonMangoldt_indicator ha1 (hM p.1 hp1) ha2,
      gcd_eq_sum_totient_indicator ha1 (hM p.1 hp1) ha2]
    rw [Finset.sum_product]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro e _
    refine Finset.sum_congr rfl ?_
    intro d _
    by_cases h1 : e ∣ p.1 <;> by_cases h2 : e ∣ p.2 <;>
      by_cases h3 : d ∣ p.1 <;> by_cases h4 : d ∣ p.2 <;>
      simp [Nat.lcm_dvd_iff, h1, h2, h3, h4]
  rw [Finset.sum_congr rfl hpair, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [Finset.sum_product]
  have hfac :
      (∑ m ∈ S, ∑ n ∈ S,
        (Nat.totient w.1 : ℝ) * Λ w.2 *
          (if Nat.lcm w.1 w.2 ∣ m then f m else 0) *
            (if Nat.lcm w.1 w.2 ∣ n then f n else 0)) =
        (Nat.totient w.1 : ℝ) * Λ w.2 *
          ((∑ m ∈ S, if Nat.lcm w.1 w.2 ∣ m then f m else 0) *
            (∑ n ∈ S, if Nat.lcm w.1 w.2 ∣ n then f n else 0)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n _
    ring
  rw [hfac, ← Finset.sum_filter]
  ring

end RHTower.Sieve

end
