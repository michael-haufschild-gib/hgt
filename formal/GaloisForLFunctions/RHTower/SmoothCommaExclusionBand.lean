import GaloisForLFunctions.RHTower.LiouvillePointReachability

/-!
# Smooth commas exclude a band of heights for prime conspiracies

The upper extreme of the prime symbol is reached when every prime is phase-aligned,
`ξ log p ∈ 2πℤ` for all `p ≤ N`.  Any multiplicative relation among the small primes turns that into
a constraint on a *single* small number, and small numbers give long exclusions.

Let `A/B` be a ratio of `N`-smooth positive integers with `A ≠ B` — a **comma** — and write
`λ = log(A/B) = Σ_p c_p log p` with integer exponents `c_p`.  If every prime `p ≤ N` satisfies
`ξ log p = 2π b_p + δ_p` with `|δ_p| ≤ ε`, then summing against `c`,

```text
| ξ λ - 2π K | ≤ ε ‖c‖₁,      K = Σ_p c_p b_p ∈ ℤ.
```

If `K = 0` this forces `ξ ≤ ε‖c‖₁/λ`; otherwise `|K| ≥ 1` forces `ξ λ ≥ 2π - ε‖c‖₁`.  So the
interval

```text
(  ε‖c‖₁ / λ  ,  (2π - ε‖c‖₁) / λ  )
```

contains **no** height at which the primes up to `N` are `ε`-aligned.  The band has length
essentially `2π/λ`, and `λ` can be made tiny by choosing a good comma: `log(9/8) ≈ 0.118` excludes up
to `ξ ≈ 53`, `log(81/80) ≈ 0.0124` up to `ξ ≈ 506`, `log(2401/2400) ≈ 4.2·10⁻⁴` up to
`ξ ≈ 1.5·10⁴`, and the smallest `N`-smooth comma shrinks rapidly with `N` by Størmer–Lehmer theory.

This is an unconditional, effective, transcendence-free lower bound on the first height at which the
primes can conspire — the upper-extreme counterpart of the Liouville-point bound of the previous
module.  Its strength comes purely from the *integrality* of the smooth numbers `A` and `B`.
-/

open Real Finset

noncomputable section

namespace RHTower

/-- **Elimination against a comma.**  Pairing the alignment relations with an integer relation
`Σ c_p log p = λ` gives a single constraint on `ξλ` modulo `2π`, with error `ε‖c‖₁`. -/
theorem comma_alignment {ι : Type*} (s : Finset ι) (lp c b d : ι → ℝ) (ξ ε lam : ℝ)
    (hlam : ∑ i ∈ s, c i * lp i = lam)
    (halign : ∀ i ∈ s, ξ * lp i = 2 * Real.pi * b i + d i)
    (hd : ∀ i ∈ s, |d i| ≤ ε) :
    |ξ * lam - 2 * Real.pi * (∑ i ∈ s, c i * b i)| ≤ ε * ∑ i ∈ s, |c i| := by
  have hexp : ξ * lam = 2 * Real.pi * (∑ i ∈ s, c i * b i) + ∑ i ∈ s, c i * d i := by
    rw [← hlam, Finset.mul_sum]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := halign i hi
    calc ξ * (c i * lp i) = c i * (ξ * lp i) := by ring
      _ = c i * (2 * Real.pi * b i + d i) := by rw [h]
      _ = 2 * Real.pi * (c i * b i) + c i * d i := by ring
  rw [hexp]
  have hsimp : 2 * Real.pi * (∑ i ∈ s, c i * b i) + (∑ i ∈ s, c i * d i)
      - 2 * Real.pi * (∑ i ∈ s, c i * b i) = ∑ i ∈ s, c i * d i := by ring
  rw [hsimp]
  calc |∑ i ∈ s, c i * d i| ≤ ∑ i ∈ s, |c i * d i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |c i| * |d i| := by
        exact Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ ∑ i ∈ s, |c i| * ε := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul_of_nonneg_left (hd i hi) (abs_nonneg _)
    _ = ε * ∑ i ∈ s, |c i| := by rw [← Finset.sum_mul]; ring

/-- **The exclusion band.**  If `ξλ` is within `ε‖c‖₁` of `2πK` for an integer `K`, and `ξ` already
exceeds `ε‖c‖₁/λ`, then `ξ` must have jumped past `(2π - ε‖c‖₁)/λ`: the open interval between the
two is excluded. -/
theorem exclusion_band {ξ ε lam w : ℝ} {K : ℤ}
    (hlam : 0 < lam) (_hw : 0 ≤ w) (hbound : |ξ * lam - 2 * Real.pi * (K : ℝ)| ≤ ε * w)
    (hsmall : ε * w < Real.pi) (hpast : ε * w / lam < ξ) :
    (2 * Real.pi - ε * w) / lam ≤ ξ := by
  have hεw : 0 ≤ ε * w := by
    rcases le_or_gt 0 (ε * w) with h | h
    · exact h
    · exact absurd (lt_of_le_of_lt (abs_nonneg _) (lt_of_le_of_lt hbound h)) (by norm_num)
  have hξ : 0 < ξ := lt_of_le_of_lt (by positivity) hpast
  have hξlam : 0 < ξ * lam := mul_pos hξ hlam
  have habs := abs_le.mp hbound
  -- `K = 0` is impossible: it would contradict `hpast`.
  have hK0 : K ≠ 0 := by
    intro h
    rw [h] at habs
    have : ξ * lam ≤ ε * w := by push_cast at habs; linarith [habs.2]
    have : ξ ≤ ε * w / lam := by rw [le_div_iff₀ hlam]; linarith
    linarith
  -- `K ≥ 1`, since `K ≤ -1` would make `ξλ` negative.
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    rcases lt_or_gt_of_ne hK0 with h | h
    · exfalso
      have hKint : K ≤ -1 := by omega
      have hKle : (K : ℝ) ≤ -1 := by exact_mod_cast hKint
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have : ξ * lam ≤ 2 * Real.pi * (K : ℝ) + ε * w := by linarith [habs.2]
      nlinarith [hξlam, hKle, hpi, hsmall]
    · exact_mod_cast h
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlow : 2 * Real.pi * (K : ℝ) - ε * w ≤ ξ * lam := by linarith [habs.1]
  have hge : 2 * Real.pi - ε * w ≤ ξ * lam := by nlinarith [hK1, hpi]
  rw [div_le_iff₀ hlam]
  linarith

end RHTower
