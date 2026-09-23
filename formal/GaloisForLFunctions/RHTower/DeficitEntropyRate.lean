import GaloisForLFunctions.RHTower.TwistedDistanceTransfer

/-!
# The entropy split of a two-source Halász density

The sharp Halász main term is an entropy `ρ log(C/ρ)` in the normalized Euler size `ρ`.  When `ρ` is
the sum of an ordinary-cell density `a` and an antitwist density `b`, the entropy is subadditive,

```text
(a+b)·log(C/(a+b)) ≤ a·log(C/a) + b·log(C/b),
```

because the difference is `a·log((a+b)/a) + b·log((a+b)/b) ≥ 0`.  With `a = exp(-Δ/4)` and `b = 1/|t|`
this is exactly

```text
ρ log(C/ρ) ≤ exp(-Δ/4)(log C + Δ/4) + (1 + log|t|·)/|t| · …,
```

so a merely *subpower* deficit `Δ` still produces a decaying bound: the entropy-decayed shape
`exp(-Δ/4)(1+Δ)` tends to zero for every unbounded `Δ`, while the crude bound `ρ·log log Y` would have
destroyed it.  The Littlewood deficit `Δ = log log log Y - O(1)` therefore gives the qualitative rate
`(log log Y)^{-1/4} log log log Y`, and a power-law deficit `Δ = (1-θ) log log x - O(1)` gives the fixed
negative power `(log x)^{-(1-θ)/4}`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## The entropy split -/

/-- **(Z13a) Entropy is subadditive.**  Splitting a density into two positive parts never decreases the
entropy `ρ ↦ ρ log(C/ρ)`. -/
theorem entropy_split {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    (a + b) * Real.log (C / (a + b)) ≤ a * Real.log (C / a) + b * Real.log (C / b) := by
  have hab : 0 < a + b := by linarith
  have hCne : C ≠ 0 := ne_of_gt hC
  have hsplit : ∀ u : ℝ, 0 < u → Real.log (C / u) = Real.log C - Real.log u := fun u hu =>
    Real.log_div hCne (ne_of_gt hu)
  rw [hsplit _ hab, hsplit _ ha, hsplit _ hb]
  have hkey : a * Real.log ((a + b) / a) + b * Real.log ((a + b) / b)
      = (a * Real.log C - a * Real.log a) + (b * Real.log C - b * Real.log b)
        - (a + b) * (Real.log C - Real.log (a + b)) := by
    rw [Real.log_div (ne_of_gt hab) (ne_of_gt ha), Real.log_div (ne_of_gt hab) (ne_of_gt hb)]
    ring
  have hA : 0 ≤ a * Real.log ((a + b) / a) := by
    refine mul_nonneg ha.le (Real.log_nonneg ?_)
    rw [le_div_iff₀ ha]
    linarith
  have hB : 0 ≤ b * Real.log ((a + b) / b) := by
    refine mul_nonneg hb.le (Real.log_nonneg ?_)
    rw [le_div_iff₀ hb]
    linarith
  nlinarith [hkey, hA, hB]

/-- **(Z13) The two-source entropy bound.**  For an ordinary-cell density `exp(-Δ/4)` and an antitwist
density `1/t`, the Halász entropy splits into a deficit term and an escape term. -/
theorem entropy_split_deficit {C Δ t : ℝ} (hC : 0 < C) (ht : 0 < t) :
    (Real.exp (-(Δ / 4)) + 1 / t) * Real.log (C / (Real.exp (-(Δ / 4)) + 1 / t))
      ≤ Real.exp (-(Δ / 4)) * (Real.log C + Δ / 4)
        + (1 / t) * (Real.log C + Real.log t) := by
  have ha : 0 < Real.exp (-(Δ / 4)) := Real.exp_pos _
  have hb : 0 < 1 / t := by positivity
  have h := entropy_split ha hb hC
  have hA : Real.exp (-(Δ / 4)) * Real.log (C / Real.exp (-(Δ / 4)))
      = Real.exp (-(Δ / 4)) * (Real.log C + Δ / 4) := by
    rw [Real.log_div (ne_of_gt hC) (ne_of_gt ha), Real.log_exp]
    ring
  have hB : (1 / t) * Real.log (C / (1 / t)) = (1 / t) * (Real.log C + Real.log t) := by
    rw [Real.log_div (ne_of_gt hC) (ne_of_gt hb), one_div, Real.log_inv]
    ring
  rw [hA, hB] at h
  exact h

/-! ## The entropy-decayed shape tends to zero -/

/-- An exponentially damped affine function tends to zero. -/
theorem tendsto_exp_neg_mul_linear_deficitEntropyRate {c A K : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => Real.exp (-(c * u)) * (A + K * u)) atTop (nhds 0) := by
  have hconst : Tendsto (fun u : ℝ => A * Real.exp (-(c * u))) atTop (nhds (A * 0)) := by
    refine Tendsto.const_mul A ?_
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_atTop_atTop_of_monotone (fun u v huv => by nlinarith)
        (fun b => ⟨b / c, by rw [mul_div_cancel₀ _ (ne_of_gt hc)]⟩))
  have hlin : Tendsto (fun u : ℝ => (K / c) * ((c * u) ^ 1 * Real.exp (-(c * u)))) atTop
      (nhds ((K / c) * 0)) := by
    refine Tendsto.const_mul (K / c) ?_
    exact (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (Filter.tendsto_atTop_atTop_of_monotone (fun u v huv => by nlinarith)
        (fun b => ⟨b / c, by rw [mul_div_cancel₀ _ (ne_of_gt hc)]⟩))
  have hsum := hconst.add hlin
  rw [mul_zero, mul_zero, add_zero] at hsum
  refine hsum.congr fun u => ?_
  rw [pow_one]
  field_simp

/-! ## The Littlewood qualitative rate -/

/-- The exponential of the negative cell gap is a fixed negative power of `log log x`. -/
theorem exp_neg_littlewoodCellGap_eq {B x : ℝ}
    (hx : zetaHorizonLogThreshold ≤ Real.log x) :
    Real.exp (-littlewoodCellGap B x)
      = Real.exp ((Real.log (37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
            + zetaDeficitConst) / 4)
          * Real.log (Real.log x) ^ (-(1 : ℝ) / 4) := by
  have h4 : (4 : ℝ) ≤ Real.log x := four_le_log_of_horizon hx
  have hll : 0 < Real.log (Real.log x) := by
    have h1 : (1 : ℝ) < Real.log x := by linarith
    exact Real.log_pos h1
  rw [Real.rpow_def_of_pos hll, littlewoodCellGap, ← Real.exp_add]
  congr 1
  ring

/-- **(Z18a) The entropy-decayed Littlewood shape tends to zero.**  Every unbounded deficit — in
particular `Δ = log log log Y - O(1)` — makes `exp(-Δ/4)(1 + Δ)` vanish, so the sharp Halász main term
is `o(1)` even without a fixed power saving. -/
theorem tendsto_entropy_decayed_shape {K : ℝ} :
    Tendsto (fun Δ : ℝ => Real.exp (-(Δ / 4)) * (K + Δ / 4)) atTop (nhds 0) := by
  have h := tendsto_exp_neg_mul_linear_deficitEntropyRate (c := (1 : ℝ) / 4) (A := K) (K := (1 : ℝ) / 4)
    (by norm_num)
  refine h.congr fun u => ?_
  congr 2 <;> ring

/-! ## The power-law rate -/

/-- The exponential of a negative power-law gap is a fixed negative power of `log x`. -/
theorem exp_neg_power_law_gap {C θ x : ℝ} (hx : 1 < Real.log x) :
    Real.exp (-(((1 - θ) * Real.log (Real.log x) - Real.log C - zetaDeficitConst) / 4))
      = Real.exp ((Real.log C + zetaDeficitConst) / 4)
          * Real.log x ^ (-(1 - θ) / 4) := by
  have hll : 0 < Real.log x := by linarith
  rw [Real.rpow_def_of_pos hll, ← Real.exp_add]
  congr 1
  ring

/-- **(Z18) Both sources decay at every exponent strictly below their own.**  Written in the scale
`u = log log x`, the ordinary-cell term decays at rate `(1-θ)/4` and the antitwist term at rate `η`, so
after multiplication by `exp(ε u)` with `ε` below both, each still tends to zero. -/
theorem tendsto_ordinary_cell_term {θ ε A : ℝ} (hε : 0 < (1 - θ) / 4 - ε) :
    Tendsto (fun u : ℝ =>
        Real.exp (ε * u) * (Real.exp (-((1 - θ) * u / 4)) * (A + (1 - θ) * u / 4)))
      atTop (nhds 0) := by
  have h := tendsto_exp_neg_mul_linear_deficitEntropyRate (c := (1 - θ) / 4 - ε) (A := A) (K := (1 - θ) / 4) hε
  refine h.congr fun u => ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  · congr 1
    ring
  · ring

theorem tendsto_antitwist_term {η ε A : ℝ} (hε : 0 < η - ε) :
    Tendsto (fun u : ℝ => Real.exp (ε * u) * (Real.exp (-(η * u)) * (A + η * u)))
      atTop (nhds 0) := by
  have h := tendsto_exp_neg_mul_linear_deficitEntropyRate (c := η - ε) (A := A) (K := η) hε
  refine h.congr fun u => ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end

end RHTower
