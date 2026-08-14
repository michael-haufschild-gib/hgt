import GaloisForLFunctions.RHTower.RouteEGibbsPrefixModulus

/-!
# The batch rapidity at the terminal frequency

The complete odd cube of a growing batch `Y < p ≤ X` is one additive rapidity

```text
R_X = ∑_{Y < p ≤ X} artanh(2 d_p cos(t_X log p)),   d_p = p^{-1/2}/(1 + p^{-1}),
```

and at the terminal frequency `t_X = π/log X` with `Y = (log X)^A` it equals
`-(4√X/log X)(1 + o(1))`: the linear grade is the critical cosine sum, the `artanh` correction is
`O(∑ 1/p)`, the `d_p` versus `p^{-1/2}` correction is `O(∑ 1/p)`, and the discarded prefix is
`O(√Y)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The critical half density `d_p = p^{-1/2}/(1 + p^{-1})`. -/
def criticalHalfDensity (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 : ℝ) / 2) / (1 + (p : ℝ)⁻¹)

/-- The batch rapidity `∑_{Y < p ≤ X} artanh(2 d_p cos(t_X log p))`. -/
def batchRapidity (Y X : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊,
    (if k.Prime then Real.artanh (2 * criticalHalfDensity k *
      Real.cos (terminalFrequency X * Real.log k)) else 0)

theorem criticalHalfDensity_pos {p : ℕ} (hp : 0 < p) : 0 < criticalHalfDensity p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hden : (0 : ℝ) < 1 + (p : ℝ)⁻¹ := by positivity
  rw [criticalHalfDensity]
  positivity

theorem criticalHalfDensity_le {p : ℕ} (hp : 0 < p) :
    criticalHalfDensity p ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hden : (1 : ℝ) ≤ 1 + (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    linarith
  rw [criticalHalfDensity, div_le_iff₀ (by linarith)]
  nlinarith [hrp, hden]

/-- The square-root density and the critical half density differ by at most `1/p`. -/
theorem sub_criticalHalfDensity_le {p : ℕ} (hp : 1 ≤ p) :
    (p : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity p ≤ (p : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hrple : (p : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 := by
    have hsq : ((p : ℝ) ^ (-(1 : ℝ) / 2)) * ((p : ℝ) ^ (-(1 : ℝ) / 2)) = (p : ℝ)⁻¹ := by
      rw [← Real.rpow_add hp0]
      norm_num
      rw [Real.rpow_neg_one]
    have hinv : (p : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hp1
    nlinarith [hrp, hsq, hinv]
  have hden : (0 : ℝ) < 1 + (p : ℝ)⁻¹ := by positivity
  have hval : (p : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity p
      = (p : ℝ) ^ (-(1 : ℝ) / 2) * ((p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹)) := by
    rw [criticalHalfDensity]
    field_simp
    ring
  rw [hval]
  have hfrac : (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) ≤ (p : ℝ)⁻¹ := by
    rw [div_le_iff₀ hden]
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    nlinarith
  have hinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  calc (p : ℝ) ^ (-(1 : ℝ) / 2) * ((p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹))
      ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hfrac hrp.le
    _ ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hrple hinv0
    _ = (p : ℝ)⁻¹ := by ring

/-- Past `16` the local rapidity argument is at most `1/2` in absolute value. -/
theorem abs_two_mul_criticalHalfDensity_mul_cos_le {p : ℕ} (hp : 16 ≤ p) (φ : ℝ) :
    |2 * criticalHalfDensity p * Real.cos φ| ≤ 1 / 2 := by
  have hp0 : 0 < p := by omega
  have hp16 : (16 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0R : (0 : ℝ) < (p : ℝ) := by linarith
  have hd0 := criticalHalfDensity_pos hp0
  have hdle := criticalHalfDensity_le hp0
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0R _
  have hsq : ((p : ℝ) ^ (-(1 : ℝ) / 2)) * ((p : ℝ) ^ (-(1 : ℝ) / 2)) = (p : ℝ)⁻¹ := by
    rw [← Real.rpow_add hp0R]
    norm_num
    rw [Real.rpow_neg_one]
  have hinv16 : (p : ℝ)⁻¹ ≤ 1 / 16 := by
    rw [inv_le_comm₀ hp0R (by norm_num)]
    linarith
  have hquarter : (p : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 / 4 := by nlinarith [hrp, hsq, hinv16]
  have hcos : |Real.cos φ| ≤ 1 := Real.abs_cos_le_one φ
  have habs : |2 * criticalHalfDensity p * Real.cos φ|
      = 2 * criticalHalfDensity p * |Real.cos φ| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * criticalHalfDensity p)]
  rw [habs]
  nlinarith [hd0, hdle, hquarter, hcos, abs_nonneg (Real.cos φ)]

/-! ## The linear grade of the batch -/

/-- The batch cosine sum with the pure square-root density. -/
def batchCosSum (Y X : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊,
    (if k.Prime then (k : ℝ) ^ (-(1 : ℝ) / 2) *
      Real.cos (terminalFrequency X * Real.log k) else 0)

/-- **The rapidity is its linear grade up to a Mertens remainder.** -/
theorem abs_batchRapidity_sub_two_mul_batchCosSum_le {Y X : ℝ} (hY : 16 ≤ Y)
    (hYX : Y ≤ X) (hX : 0 < X) :
    |batchRapidity Y X - 2 * batchCosSum Y X| ≤ 18 * Sieve.mertensS ⌊X⌋₊ := by
  have hfloorY : 16 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hfloorle : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hYX
  have hdiff : batchRapidity Y X - 2 * batchCosSum Y X
      = ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊,
        (if k.Prime then Real.artanh (2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k))
          - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
            Real.cos (terminalFrequency X * Real.log k)) else 0) := by
    rw [batchRapidity, batchCosSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp, if_neg hp]
      ring
  rw [hdiff]
  have hterm : ∀ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊,
      |(if k.Prime then Real.artanh (2 * criticalHalfDensity k *
          Real.cos (terminalFrequency X * Real.log k))
        - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
          Real.cos (terminalFrequency X * Real.log k)) else 0)|
        ≤ (if k.Prime then 18 * (k : ℝ)⁻¹ else 0) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp]
      have hk16 : 16 ≤ k := by omega
      have hk0 : 0 < k := by omega
      have hk0R : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
      have hk1 : 1 ≤ k := by omega
      have hcos : |Real.cos (terminalFrequency X * Real.log k)| ≤ 1 :=
        Real.abs_cos_le_one _
      have hrp : (0 : ℝ) < (k : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hk0R _
      have hd0 := criticalHalfDensity_pos hk0
      have hdle := criticalHalfDensity_le hk0
      have habs := abs_two_mul_criticalHalfDensity_mul_cos_le hk16
        (terminalFrequency X * Real.log k)
      have hartanh := HTGeometry.abs_artanh_sub_self_le habs
      have hsq : ((k : ℝ) ^ (-(1 : ℝ) / 2)) * ((k : ℝ) ^ (-(1 : ℝ) / 2)) = (k : ℝ)⁻¹ := by
        rw [← Real.rpow_add hk0R]
        norm_num
        rw [Real.rpow_neg_one]
      -- the quadratic `artanh` correction
      have hquad : (2 * criticalHalfDensity k *
          Real.cos (terminalFrequency X * Real.log k)) ^ 2 ≤ 4 * (k : ℝ)⁻¹ := by
        have hbase : |2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k)| ≤ 2 * (k : ℝ) ^ (-(1 : ℝ) / 2) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * criticalHalfDensity k)]
          nlinarith [hcos, hd0, hdle, abs_nonneg (Real.cos (terminalFrequency X * Real.log k))]
        have hsqabs := sq_abs (2 * criticalHalfDensity k *
          Real.cos (terminalFrequency X * Real.log k))
        nlinarith [hbase, abs_nonneg (2 * criticalHalfDensity k *
          Real.cos (terminalFrequency X * Real.log k)), hsq, hrp]
      -- the density correction
      have hdens : |2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
          - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
            Real.cos (terminalFrequency X * Real.log k))|
          ≤ 2 * (k : ℝ)⁻¹ := by
        have hval : 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
            - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
              Real.cos (terminalFrequency X * Real.log k))
            = -(2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity k)) *
              Real.cos (terminalFrequency X * Real.log k) := by ring
        rw [hval, abs_mul, abs_neg]
        have hgap := sub_criticalHalfDensity_le hk1
        have hgap0 : (0 : ℝ) ≤ (k : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity k := by linarith
        have habs2 : |2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity k)|
            = 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity k) := by
          rw [abs_of_nonneg (by linarith)]
        rw [habs2]
        nlinarith [hcos, hgap, hgap0, abs_nonneg (Real.cos (terminalFrequency X * Real.log k))]
      have hsplit : |Real.artanh (2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k))
          - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
            Real.cos (terminalFrequency X * Real.log k))|
          ≤ |Real.artanh (2 * criticalHalfDensity k *
              Real.cos (terminalFrequency X * Real.log k))
            - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)|
            + |2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
              - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
                Real.cos (terminalFrequency X * Real.log k))| := by
        have h := abs_add_le
          (Real.artanh (2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k))
            - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k))
          (2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
            - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
              Real.cos (terminalFrequency X * Real.log k)))
        have heq : (Real.artanh (2 * criticalHalfDensity k *
              Real.cos (terminalFrequency X * Real.log k))
            - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k))
            + (2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
              - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
                Real.cos (terminalFrequency X * Real.log k)))
            = Real.artanh (2 * criticalHalfDensity k *
                Real.cos (terminalFrequency X * Real.log k))
              - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
                Real.cos (terminalFrequency X * Real.log k)) := by ring
        rw [heq] at h
        exact h
      have hfirst : |Real.artanh (2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k))
          - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)|
          ≤ 16 * (k : ℝ)⁻¹ := by
        have hmul : 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
            = 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k) := rfl
        calc |Real.artanh (2 * criticalHalfDensity k *
              Real.cos (terminalFrequency X * Real.log k))
            - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)|
            ≤ 4 * (2 * criticalHalfDensity k *
                Real.cos (terminalFrequency X * Real.log k)) ^ 2 := hartanh
          _ ≤ 4 * (4 * (k : ℝ)⁻¹) := by linarith
          _ = 16 * (k : ℝ)⁻¹ := by ring
      linarith [hsplit, hfirst, hdens]
    · rw [if_neg hp, if_neg hp, abs_zero]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- compare with the Mertens sum
  have hsub : (Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊).filter Nat.Prime ⊆ Nat.primesLE ⌊X⌋₊ := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ioc] at hk
    rw [Nat.mem_primesLE]
    exact ⟨hk.1.2, hk.2⟩
  have hrw : ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊, (if k.Prime then 18 * (k : ℝ)⁻¹ else 0)
      = ∑ k ∈ (Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊).filter Nat.Prime, 18 * (k : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
  rw [hrw, Sieve.mertensS, Finset.mul_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_ |>.trans (le_of_eq ?_)
  · intro k hk _
    have hprime := Nat.prime_of_mem_primesLE hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hprime.pos
    positivity
  · exact Finset.sum_congr rfl fun p _ => by rw [one_div]

end

end RHTower
