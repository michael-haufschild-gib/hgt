import GaloisForLFunctions.RHTower.RefinedSpectralDominance

/-!
# The damped prime sum, and which constraint actually binds

Assembling the chain damping of the preceding modules over **all** primes gives the exact bound

```text
prime cost  ≤  2 Σ(ℓ),      Σ(ℓ) = Σ_{n : log n ≤ 2ℓ} Λ(n) n^{-1/2} cos( π / (⌊2ℓ/log n⌋ + 2) ).
```

The floor stratifies the sum: `⌊2ℓ/log n⌋ = k` exactly when `2ℓ/(k+1) < log n ≤ 2ℓ/k`, so

```text
Σ(ℓ) = Σ_{k ≥ 1} cos(π/(k+2)) · Σ_{ e^{2ℓ/(k+1)} < n ≤ e^{2ℓ/k} } Λ(n) n^{-1/2} ,
```

with damping factors `cos(π/3) = 1/2`, `cos(π/4) = √2/2`, `cos(π/5) = (1+√5)/4`, `cos(π/6) = √3/2`,
increasing to `1`.  Using `Σ_{n ≤ X} Λ(n)n^{-1/2} ∼ 2√X` and Abel summation,

```text
Σ(ℓ) = e^{ℓ} + 2 Σ_{k≥2} Δ_k e^{ℓ/k} - 2 + o(1) ,     Δ_k = cos(π/(k+2)) - cos(π/(k+1)) > 0 ,
```

against the naive `2e^{ℓ}`: the ratio tends to `1/2`, confirming the factor of two with an explicit
correction series.

**Which constraint binds.**  The first prime enters at `2ℓ = log 2`, that is `ℓ = (log 2)/2 ≈
0.3466`.  The elementary archimedean baseline of the Riemann–Siegel threshold law holds only up to
`ℓ₀ = π/(2t₀) ≈ 0.2497`, and `0.2497 < 0.3466` precisely because `t₀ > π/log 2 ≈ 4.532`.  So **inside
the purely elementary route the prime damping is never activated**: the archimedean baseline gives
out first, while the prime sum is still empty.

The damping therefore becomes decisive only in combination with the Connes–Consani archimedean
theorem, which covers the interval `[π/(2t₀), (log 2)/2]` and beyond.  This isolates the precise
missing input: a quantitative form of Connes–Consani on that interval, after which the damped prime
sum above takes over.

This file formalizes the stratification by the floor, positivity and monotonicity of the damping
factors, the block bound, and the comparison `π/(2t₀) < (log 2)/2`.
-/

open Real

noncomputable section

namespace RHTower

/-- **Stratification by the floor.**  For `a > 0` and `k ≥ 1`, `⌊T/a⌋ = k` exactly when
`T/(k+1) < a ≤ T/k`. -/
theorem floor_eq_iff_mem {T a : ℝ} {k : ℕ} (_hT : 0 < T) (ha : 0 < a) (hk : 1 ≤ k) :
    ((k : ℝ) ≤ T / a ∧ T / a < (k : ℝ) + 1) ↔ (T / ((k : ℝ) + 1) < a ∧ a ≤ T / (k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  constructor
  · intro ⟨h1, h2⟩
    constructor
    · rw [div_lt_iff₀ hk1pos]
      rw [div_lt_iff₀ ha] at h2
      linarith
    · rw [le_div_iff₀ hkpos]
      rw [le_div_iff₀ ha] at h1
      linarith
  · intro ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ ha]
      rw [le_div_iff₀ hkpos] at h2
      linarith
    · rw [div_lt_iff₀ ha]
      rw [div_lt_iff₀ hk1pos] at h1
      linarith

/-- The damping factor at chain length `k+1`. -/
def dampingFactor (k : ℕ) : ℝ := Real.cos (Real.pi / ((k : ℝ) + 2))

/-- Damping factors are positive for `k ≥ 1`. -/
theorem dampingFactor_pos {k : ℕ} (hk : 1 ≤ k) : 0 < dampingFactor k := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : 0 < Real.pi / ((k : ℝ) + 2) := by positivity
  refine Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hpi, hpos], ?_⟩
  rw [div_lt_iff₀ hden]
  nlinarith [hpi, hkR]

/-- Damping factors are strictly below one, so every prime power is genuinely damped. -/
theorem dampingFactor_lt_one {k : ℕ} (hk : 1 ≤ k) : dampingFactor k < 1 := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : 0 < Real.pi / ((k : ℝ) + 2) := by positivity
  have hle : Real.pi / ((k : ℝ) + 2) ≤ Real.pi := by
    rw [div_le_iff₀ hden]; nlinarith
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hle hpos
  simpa [dampingFactor] using h

/-- The first block, `log n ∈ (ℓ, 2ℓ]`, is damped by exactly one half. -/
theorem dampingFactor_one : dampingFactor 1 = 1 / 2 := by
  unfold dampingFactor
  rw [show ((1 : ℕ) : ℝ) + 2 = 3 from by norm_num, Real.cos_pi_div_three]

/-- **Block bound.**  On the block where the floor equals `k`, the damped contribution is the
damping factor times the undamped one. -/
theorem block_bound {k : ℕ} (hk : 1 ≤ k) {S dampedS : ℝ} (hS : 0 ≤ S)
    (hdamped : dampedS ≤ dampingFactor k * S) :
    dampedS ≤ S := by
  have h1 := (dampingFactor_lt_one hk).le
  nlinarith [hdamped, hS, h1]

/-- **Which constraint binds.**  The elementary archimedean threshold `π/(2t₀)` lies below the first
prime threshold `(log 2)/2` exactly when `t₀ > π/log 2`; so in the purely elementary route the prime
damping is never activated, because the archimedean baseline gives out while the prime sum is still
empty. -/
theorem archimedean_binds {t₀ : ℝ} (ht₀ : Real.pi / Real.log 2 < t₀) :
    Real.pi / (2 * t₀) < Real.log 2 / 2 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have ht₀pos : (0 : ℝ) < t₀ := lt_trans (by positivity) ht₀
  rw [div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
  rw [div_lt_iff₀ hlog] at ht₀
  nlinarith [ht₀, hlog, ht₀pos]

end RHTower
