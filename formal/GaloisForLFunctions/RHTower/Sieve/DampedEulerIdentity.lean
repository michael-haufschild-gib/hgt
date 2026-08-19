import GaloisForLFunctions.RHTower.Sieve.DampedLocalFactor
import GaloisForLFunctions.RHTower.Sieve.DampedTsumCompare

/-!
# The damped series is the Möbius series times a finite correction

Both series have Euler products, and their local factors agree off `P` while on `P` they differ by
`Sieve/DampedEulerCorrection.dampedEulerFactor`.  Since `P` is finite, the two partial products over
`primesBelow n` differ by that fixed finite product as soon as `n` exceeds every member of `P`, so
the limits differ by it too:

`∑'_m μ(m)·t^{ω_P(m)}·m^{-s} = (∏_{p ∈ P} dampedEulerFactor t p s) · ∑'_m μ(m)·m^{-s}`.

Combined with `Sieve/DampedEulerCorrection.norm_prod_dampedEulerFactor_le`, this is what lets the
corpus's Möbius contour argument be run for the damped series: every edge estimate acquires one
bounded, `t`-uniform multiplier.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

noncomputable section

/-- At `t = 1` the damping is trivial. -/
theorem dampedOmegaMoebius_one_eq (P : Finset ℕ) :
    dampedOmegaMoebius P 1 = fun m => ((moebius m : ℤ) : ℂ) := by
  funext m
  rw [dampedOmegaMoebius, one_pow]
  push_cast
  ring

/-- The local Euler factor of the plain Möbius series. -/
theorem tsum_twistedSummand_moebius_primePow {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ∑' k : ℕ, twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s (p ^ k)
      = 1 - (p : ℂ) ^ (-s) := by
  have h := tsum_twistedSummand_dampedOmegaMoebius_primePow hPprime 1 hp s
  rw [dampedOmegaMoebius_one_eq] at h
  rw [h]
  by_cases hmem : p ∈ P <;> simp [hmem]

/-- The plain local factor never vanishes to the right of the one-line. -/
theorem one_sub_cpow_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [RHTower.norm_natCast_cpow hp1, Complex.neg_re]
  have hlt : (p : ℝ) ^ (-s.re) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  intro hcon
  have : (p : ℂ) ^ (-s) = 1 := by linear_combination -hcon
  rw [this] at hnorm
  simp only [norm_one] at hnorm
  linarith [hnorm, hlt]

/-- **The damped series is the Möbius series times the finite correction.** -/
theorem tsum_damped_eq_prod_mul_tsum_moebius {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, twistedSummand (dampedOmegaMoebius P t) s n
      = (∏ p ∈ P, dampedEulerFactor t p s)
        * ∑' n : ℕ, twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s n := by
  classical
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hbddD : ∀ n, ‖dampedOmegaMoebius P t n‖ ≤ 1 :=
    fun n => norm_dampedOmegaMoebius_le_one ht0 ht1 n
  have hbddM : ∀ n, ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [show ((moebius n : ℤ) : ℂ) = (((moebius n : ℤ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_moebius_real_le_one n
  -- the two Euler products
  have hED := EulerProduct.eulerProduct (f := twistedSummand (dampedOmegaMoebius P t) s)
    (twistedSummand_one (dampedOmegaMoebius_one hPprime t))
    (fun h => twistedSummand_mul (fun {a b} hab =>
      dampedOmegaMoebius_mul_of_coprime hPprime t hab) h)
    (summable_norm_twistedSummand hbddD hs) (twistedSummand_zero hs0)
  have hEM := EulerProduct.eulerProduct
    (f := twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s)
    (twistedSummand_one (by simp))
    (fun h => twistedSummand_mul (fun {a b} hab => by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab]
      push_cast
      ring) h)
    (summable_norm_twistedSummand hbddM hs) (twistedSummand_zero hs0)
  -- the partial products differ by the fixed finite correction
  have hfac : ∀ᶠ n : ℕ in atTop,
      (∏ p ∈ Nat.primesBelow n, ∑' k : ℕ,
          twistedSummand (dampedOmegaMoebius P t) s (p ^ k))
        = (∏ p ∈ P, dampedEulerFactor t p s)
          * ∏ p ∈ Nat.primesBelow n, ∑' k : ℕ,
              twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s (p ^ k) := by
    filter_upwards [eventually_ge_atTop (P.sup id + 1)] with n hn
    have hPsub : P ⊆ Nat.primesBelow n := by
      intro p hp
      rw [Nat.mem_primesBelow]
      refine ⟨?_, hPprime p hp⟩
      have hle : p ≤ P.sup id := Finset.le_sup (f := id) hp
      omega
    have hterm : ∀ p ∈ Nat.primesBelow n,
        (∑' k : ℕ, twistedSummand (dampedOmegaMoebius P t) s (p ^ k))
          = (if p ∈ P then dampedEulerFactor t p s else 1)
            * ∑' k : ℕ, twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s (p ^ k) := by
      intro p hpb
      have hp : p.Prime := (Nat.mem_primesBelow.1 hpb).2
      rw [tsum_twistedSummand_dampedOmegaMoebius_primePow hPprime t hp s,
        tsum_twistedSummand_moebius_primePow hPprime hp s]
      by_cases hmem : p ∈ P
      · rw [if_pos hmem, if_pos hmem, dampedEulerFactor,
          div_mul_cancel₀ _ (one_sub_cpow_ne_zero hp hs)]
      · rw [if_neg hmem, if_neg hmem]
        push_cast
        ring
    have hprod : (∏ p ∈ Nat.primesBelow n, (if p ∈ P then dampedEulerFactor t p s else 1))
        = ∏ p ∈ P, dampedEulerFactor t p s := by
      rw [← Finset.prod_subset hPsub (fun x _ hx => by rw [if_neg hx])]
      exact Finset.prod_congr rfl (fun p hp => by rw [if_pos hp])
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, hprod]
  -- pass to the limit
  have hlim : Tendsto (fun n : ℕ => (∏ p ∈ P, dampedEulerFactor t p s)
      * ∏ p ∈ Nat.primesBelow n, ∑' k : ℕ,
          twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s (p ^ k)) atTop
      (𝓝 ((∏ p ∈ P, dampedEulerFactor t p s)
        * ∑' n : ℕ, twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s n)) :=
    hEM.const_mul _
  exact tendsto_nhds_unique (hED.congr' hfac) hlim

end

end RHTower.Sieve
