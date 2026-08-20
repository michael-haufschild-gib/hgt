import GaloisForLFunctions.RHTower.RouteECofactorUnsignedMass
import GaloisForLFunctions.RHTower.Sieve.PrimeRangeMertensMass

/-!
# The polylogarithmic band carries negligible Mertens mass

`RouteECofactorUnsignedMass` proves the Route E cofactor card's `(7)` and `(9)` for any band `B` of
primes with `∑_{p ∈ B} 1/p ≤ 1/8`.  The card's band is the primes in `[V^{a₀}, 2V^{a₁}]` with
`V = log U` and `a₁ − a₀ = 10⁻⁴`, and the sharp Mertens range bound of
`Sieve/PrimeRangeMertensMass` evaluates its mass:

```text
   ∑_{V^{a₀} ≤ p ≤ 2V^{a₁}} 1/p  ≤  (log 2 + (a₁ − a₀) log V + 2c)/(a₀ log V)
                                 →  (a₁ − a₀)/a₀  =  10⁻⁴/1.0999  <  1/8 .
```

So the hypothesis is discharged for all large `U`, and the two unsigned estimates hold for the
card's own band with no side condition.
-/

namespace RHTower

open Finset Filter Topology

noncomputable section

/-- **The Mertens mass of a polylogarithmic band is its exponent ratio.**  For every target `c`
above `(a₁ − a₀)/a₀` the band mass is below `c` once the scale is large. -/
theorem eventually_sum_inv_primesRange_polylog_le
    {a₀ a₁ c : ℝ} (ha₀ : 0 < a₀) (hc : 0 < c) (hratio : a₁ - a₀ < c * a₀) :
    ∀ᶠ V : ℝ in atTop, ∀ z₀ z : ℕ, 2 ≤ z₀ → z₀ ≤ z →
      V ^ a₀ ≤ (z₀ : ℝ) → (z : ℝ) ≤ 2 * V ^ a₁ →
      ∑ p ∈ Sieve.primesRange z₀ z, 1 / (p : ℝ) ≤ c := by
  have hcst : (0 : ℝ) ≤ 2 * Sieve.mertensFirstConst := by
    have := Sieve.mertensFirstConst_nonneg
    linarith
  have hgap : (0 : ℝ) < c * a₀ - (a₁ - a₀) := by linarith
  have hthr : ∀ᶠ W : ℝ in atTop,
      Real.log 2 + 2 * Sieve.mertensFirstConst ≤ (c * a₀ - (a₁ - a₀)) * W := by
    have := (tendsto_atTop_atTop_of_monotone (f := fun W : ℝ => (c * a₀ - (a₁ - a₀)) * W)
      (fun x y hxy => by nlinarith [hgap]) (fun b => ⟨(b + |b|) / (c * a₀ - (a₁ - a₀)) + 1, by
        have h1 : b ≤ (b + |b|) := by
          have := abs_nonneg b; linarith
        have h2 : (c * a₀ - (a₁ - a₀)) * ((b + |b|) / (c * a₀ - (a₁ - a₀)) + 1)
            = (b + |b|) + (c * a₀ - (a₁ - a₀)) := by
          field_simp
        rw [h2]; linarith⟩)).eventually_ge_atTop
      (Real.log 2 + 2 * Sieve.mertensFirstConst)
    exact this
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually hthr,
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with V hV1 hVthr hVlog
  intro z₀ z h2 hz hlo hhi
  have hV0 : (0 : ℝ) < V := by linarith
  have hz₀R : (2 : ℝ) ≤ (z₀ : ℝ) := by exact_mod_cast h2
  have hzR : (z₀ : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz₀ : a₀ * Real.log V ≤ Real.log (z₀ : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hV0 a₀) hlo
    rwa [Real.log_rpow hV0] at h
  have hlogz : Real.log (z : ℝ) ≤ Real.log 2 + a₁ * Real.log V := by
    have hz0 : (0 : ℝ) < (z : ℝ) := by linarith
    have h := Real.log_le_log hz0 hhi
    rwa [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hV0 a₁)),
      Real.log_rpow hV0] at h
  have hlogz₀pos : (0 : ℝ) < Real.log (z₀ : ℝ) := Real.log_pos (by linarith)
  have hmain := Sieve.sum_inv_primesRange_le h2 hz
  refine le_trans hmain ?_
  rw [div_le_iff₀ hlogz₀pos]
  have ha₀V : (0 : ℝ) < a₀ * Real.log V := by positivity
  nlinarith [hVthr, hlogz, hlogz₀, hlogz₀pos, hgap, hcst]

end

end RHTower

namespace RHTower

open Finset Filter Topology

noncomputable section

/-- The band is a set of primes not containing `2`. -/
theorem two_not_mem_primesRange {z₀ z : ℕ} (h2 : 2 ≤ z₀) :
    (2 : ℕ) ∉ Sieve.primesRange z₀ z := by
  rw [Sieve.primesRange, Finset.mem_sdiff]
  intro hcon
  exact hcon.2 (Sieve.mem_primesLE.2 ⟨h2, Nat.prime_two⟩)

/-- **The card's `(7)`, with the band hypothesis discharged.**  Every Möbius parity class of
integers below `T` avoiding the polylogarithmic band carries square-root mass `≫ √T`, with no side
condition beyond the scale being large. -/
theorem eventually_sum_inv_sqrt_parityClass_band_ge
    {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hratio : a₁ - a₀ < a₀ / 8) :
    ∀ᶠ V : ℝ in atTop, ∀ z₀ z : ℕ, 2 ≤ z₀ → z₀ ≤ z →
      V ^ a₀ ≤ (z₀ : ℝ) → (z : ℝ) ≤ 2 * V ^ a₁ →
      ∀ σ : ℤ, σ = 1 ∨ σ = -1 → ∀ T : ℕ,
        (1 / 8 : ℝ) * Real.sqrt ((T / 2 : ℕ) : ℝ) - 1
          ≤ ∑ t ∈ CofactorParity.parityClass (fun p => p ∈ Sieve.primesRange z₀ z) σ T,
              1 / Real.sqrt (t : ℝ) := by
  filter_upwards [eventually_sum_inv_primesRange_polylog_le (a₀ := a₀) (a₁ := a₁) (c := 1 / 8)
    ha₀ (by norm_num) (by linarith)] with V hV
  intro z₀ z h2 hz hlo hhi σ hσ T
  exact sum_inv_sqrt_parityClass_ge (B := Sieve.primesRange z₀ z)
    (fun p hp => Sieve.primesRange_prime hp) (hV z₀ z h2 hz hlo hhi)
    (two_not_mem_primesRange h2) hσ T

/-- **The card's `(9)`, with the band hypothesis discharged.**  Every Möbius parity class of
integers below `T` avoiding the polylogarithmic band carries harmonic mass `≫ log T`. -/
theorem eventually_sum_inv_parityClass_band_ge
    {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hratio : a₁ - a₀ < a₀ / 8) :
    ∀ᶠ V : ℝ in atTop, ∀ z₀ z : ℕ, 2 ≤ z₀ → z₀ ≤ z →
      V ^ a₀ ≤ (z₀ : ℝ) → (z : ℝ) ≤ 2 * V ^ a₁ →
      ∀ σ : ℤ, σ = 1 ∨ σ = -1 → ∀ T : ℕ, 1 ≤ T / 2 →
        (1 / 16 : ℝ) * Real.log ((T / 2 : ℕ) : ℝ) - 7 / 16
          ≤ ∑ t ∈ CofactorParity.parityClass (fun p => p ∈ Sieve.primesRange z₀ z) σ T,
              1 / (t : ℝ) := by
  filter_upwards [eventually_sum_inv_primesRange_polylog_le (a₀ := a₀) (a₁ := a₁) (c := 1 / 8)
    ha₀ (by norm_num) (by linarith)] with V hV
  intro z₀ z h2 hz hlo hhi σ hσ T hT
  exact sum_inv_parityClass_ge (B := Sieve.primesRange z₀ z)
    (fun p hp => Sieve.primesRange_prime hp) (hV z₀ z h2 hz hlo hhi)
    (two_not_mem_primesRange h2) hσ hT

/-- **The card's band, at its own exponents.**  With `a₀ = 1.1 − 10⁻⁴` and `a₁ = 1.1` the band mass
is below `1/8`, so both unsigned estimates hold for all large scales. -/
theorem eventually_routeE_band_parity_mass :
    ∀ᶠ V : ℝ in atTop, ∀ z₀ z : ℕ, 2 ≤ z₀ → z₀ ≤ z →
      V ^ (1.1 - 1 / 10000 : ℝ) ≤ (z₀ : ℝ) → (z : ℝ) ≤ 2 * V ^ (1.1 : ℝ) →
      ∀ σ : ℤ, σ = 1 ∨ σ = -1 → ∀ T : ℕ,
        ((1 / 8 : ℝ) * Real.sqrt ((T / 2 : ℕ) : ℝ) - 1
            ≤ ∑ t ∈ CofactorParity.parityClass (fun p => p ∈ Sieve.primesRange z₀ z) σ T,
                1 / Real.sqrt (t : ℝ))
          ∧ (1 ≤ T / 2 →
            (1 / 16 : ℝ) * Real.log ((T / 2 : ℕ) : ℝ) - 7 / 16
              ≤ ∑ t ∈ CofactorParity.parityClass (fun p => p ∈ Sieve.primesRange z₀ z) σ T,
                  1 / (t : ℝ)) := by
  filter_upwards [eventually_sum_inv_sqrt_parityClass_band_ge
      (a₀ := (1.1 - 1 / 10000 : ℝ)) (a₁ := (1.1 : ℝ)) (by norm_num) (by norm_num),
    eventually_sum_inv_parityClass_band_ge
      (a₀ := (1.1 - 1 / 10000 : ℝ)) (a₁ := (1.1 : ℝ)) (by norm_num) (by norm_num)]
    with V h7 h9
  intro z₀ z h2 hz hlo hhi σ hσ T
  exact ⟨h7 z₀ z h2 hz hlo hhi σ hσ T, fun hT => h9 z₀ z h2 hz hlo hhi σ hσ T hT⟩

end

end RHTower
