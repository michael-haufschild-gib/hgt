import Mathlib

/-!
# The secular equation of a hyperplane-constrained diagonal operator

Compressing a diagonal operator `diag(d 0, d 1, …)` to the hyperplane orthogonal to a vector `ℓ`
produces the secular equation

```text
F(μ) = Σ_j (ℓ j)² / (d j − μ) = 0 .
```

Between two consecutive diagonal entries the function is continuous and strictly increasing, and it
runs from `−∞` at the left end to `+∞` at the right end, because exactly one term changes sign
there.  Hence **each gap contains exactly one root**: the constrained spectrum interlaces the
unconstrained one.

This is the mechanism behind the constrained prolate ladder: with `d j` the leakages and `ℓ j` the
integrals, the `k`-th constrained eigenvalue is the unique root in `(d k, d (k+1))`.
-/

noncomputable section

open Set Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The secular function of a diagonal operator constrained to a hyperplane. -/
def secular (d ℓ : ℕ → ℝ) (N : ℕ) (μ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), (ℓ j) ^ 2 / (d j - μ)

variable {d ℓ : ℕ → ℝ} {N k : ℕ}

/-- Inside a gap every denominator is nonzero, with the sign determined by the index. -/
theorem secular_denom_ne (hd : StrictMono d) (_hk : k + 1 ≤ N) {μ : ℝ}
    (hμ : μ ∈ Ioo (d k) (d (k + 1))) {j : ℕ} (_hj : j ∈ Finset.range (N + 1)) :
    d j - μ ≠ 0 := by
  rcases le_or_gt j k with h | h
  · have : d j ≤ d k := hd.monotone h
    have := hμ.1
    intro hcon
    linarith [hcon]
  · have hj1 : k + 1 ≤ j := h
    have : d (k + 1) ≤ d j := hd.monotone hj1
    have := hμ.2
    intro hcon
    linarith [hcon]

/-- **The secular function is strictly increasing inside a gap.** -/
theorem secular_strictMonoOn (hd : StrictMono d) (hk : k + 1 ≤ N)
    (hℓ : ℓ k ≠ 0) :
    StrictMonoOn (secular d ℓ N) (Ioo (d k) (d (k + 1))) := by
  intro x hx y hy hxy
  have hterm : ∀ j ∈ Finset.range (N + 1),
      (ℓ j) ^ 2 / (d j - x) ≤ (ℓ j) ^ 2 / (d j - y) := by
    intro j hj
    have hxne := secular_denom_ne hd hk hx hj
    have hyne := secular_denom_ne hd hk hy hj
    have hprod : 0 < (d j - x) * (d j - y) := by
      rcases le_or_gt j k with h | h
      · have hdj : d j ≤ d k := hd.monotone h
        have hx0 : d j - x < 0 := by linarith [hx.1]
        have hy0 : d j - y < 0 := by linarith [hy.1]
        exact mul_pos_of_neg_of_neg hx0 hy0
      · have hj1 : k + 1 ≤ j := h
        have hdj : d (k + 1) ≤ d j := hd.monotone hj1
        have hx0 : 0 < d j - x := by linarith [hx.2]
        have hy0 : 0 < d j - y := by linarith [hy.2]
        exact mul_pos hx0 hy0
    have hxne : d j - x ≠ 0 := by
      intro h0
      rw [h0] at hprod
      simp at hprod
    have hyne : d j - y ≠ 0 := by
      intro h0
      rw [h0] at hprod
      simp at hprod
    rw [← sub_nonneg]
    have heq : (ℓ j) ^ 2 / (d j - y) - (ℓ j) ^ 2 / (d j - x)
        = (ℓ j) ^ 2 * (y - x) / ((d j - x) * (d j - y)) := by
      field_simp
      ring
    rw [heq]
    refine div_nonneg ?_ hprod.le
    nlinarith [sq_nonneg (ℓ j), hxy]
  have hstrict : (ℓ k) ^ 2 / (d k - x) < (ℓ k) ^ 2 / (d k - y) := by
    have hx0 : d k - x < 0 := by linarith [hx.1]
    have hy0 : d k - y < 0 := by linarith [hy.1]
    have hprod : 0 < (d k - x) * (d k - y) := mul_pos_of_neg_of_neg hx0 hy0
    have hpos : 0 < (ℓ k) ^ 2 := by positivity
    have hxne : d k - x ≠ 0 := ne_of_lt hx0
    have hyne : d k - y ≠ 0 := ne_of_lt hy0
    rw [← sub_pos]
    have heq : (ℓ k) ^ 2 / (d k - y) - (ℓ k) ^ 2 / (d k - x)
        = (ℓ k) ^ 2 * (y - x) / ((d k - x) * (d k - y)) := by
      field_simp
      ring
    rw [heq]
    refine div_pos ?_ hprod
    nlinarith [hpos, hxy]
  have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  exact Finset.sum_lt_sum hterm ⟨k, hmem, hstrict⟩

/-- The secular function is continuous inside a gap. -/
theorem continuousOn_secular (hd : StrictMono d) (hk : k + 1 ≤ N) :
    ContinuousOn (secular d ℓ N) (Ioo (d k) (d (k + 1))) := by
  refine continuousOn_finsetSum _ fun j hj => ?_
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun μ hμ => ?_
  exact secular_denom_ne hd hk hμ hj

/-- The secular function runs to `−∞` at the left end of the gap. -/
theorem tendsto_secular_atBot (hd : StrictMono d) (hk : k + 1 ≤ N) (hℓ : ℓ k ≠ 0) :
    Tendsto (secular d ℓ N) (𝓝[>] (d k)) atBot := by
  have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  have hsplit : ∀ μ : ℝ, secular d ℓ N μ
      = (∑ j ∈ (Finset.range (N + 1)).erase k, (ℓ j) ^ 2 / (d j - μ))
        + (ℓ k) ^ 2 / (d k - μ) := by
    intro μ
    rw [secular, ← Finset.sum_erase_add _ _ hmem]
  -- the singular term
  have hden : Tendsto (fun μ : ℝ => d k - μ) (𝓝[>] (d k)) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous fun μ : ℝ => d k - μ := by fun_prop
      have h : Tendsto (fun μ : ℝ => d k - μ) (𝓝[>] (d k)) (𝓝 (d k - d k)) :=
        (hcont.tendsto (d k)).mono_left nhdsWithin_le_nhds
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      have : d k < μ := hμ
      simp only [Set.mem_Iio]
      linarith
  have hinv : Tendsto (fun μ : ℝ => (d k - μ)⁻¹) (𝓝[>] (d k)) atBot :=
    tendsto_inv_nhdsLT_zero.comp hden
  have hsing : Tendsto (fun μ : ℝ => (ℓ k) ^ 2 / (d k - μ)) (𝓝[>] (d k)) atBot := by
    have hpos : (0 : ℝ) < (ℓ k) ^ 2 := by positivity
    have := (hinv.const_mul_atBot hpos)
    refine this.congr fun μ => ?_
    rw [div_eq_mul_inv]
  -- the regular part is continuous at the left end
  have hreg : Tendsto (fun μ : ℝ => ∑ j ∈ (Finset.range (N + 1)).erase k,
      (ℓ j) ^ 2 / (d j - μ)) (𝓝[>] (d k))
      (𝓝 (∑ j ∈ (Finset.range (N + 1)).erase k, (ℓ j) ^ 2 / (d j - d k))) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    have hne : d j - d k ≠ 0 := by
      intro hcon
      exact hjk (hd.injective (by linarith))
    have hcont : ContinuousAt (fun μ : ℝ => (ℓ j) ^ 2 / (d j - μ)) (d k) :=
      ContinuousAt.div continuousAt_const (by fun_prop) hne
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have := hreg.add_atBot hsing
  refine this.congr fun μ => ?_
  rw [hsplit μ]

/-- The secular function runs to `+∞` at the right end of the gap. -/
theorem tendsto_secular_atTop (hd : StrictMono d) (hk : k + 1 ≤ N) (hℓ : ℓ (k + 1) ≠ 0) :
    Tendsto (secular d ℓ N) (𝓝[<] (d (k + 1))) atTop := by
  have hmem : k + 1 ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  have hsplit : ∀ μ : ℝ, secular d ℓ N μ
      = (∑ j ∈ (Finset.range (N + 1)).erase (k + 1), (ℓ j) ^ 2 / (d j - μ))
        + (ℓ (k + 1)) ^ 2 / (d (k + 1) - μ) := by
    intro μ
    rw [secular, ← Finset.sum_erase_add _ _ hmem]
  have hden : Tendsto (fun μ : ℝ => d (k + 1) - μ) (𝓝[<] (d (k + 1))) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous fun μ : ℝ => d (k + 1) - μ := by fun_prop
      have h : Tendsto (fun μ : ℝ => d (k + 1) - μ) (𝓝[<] (d (k + 1))) (𝓝 (d (k + 1) - d (k + 1))) :=
        (hcont.tendsto (d (k + 1))).mono_left nhdsWithin_le_nhds
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      have : μ < d (k + 1) := hμ
      simp only [Set.mem_Ioi]
      linarith
  have hinv : Tendsto (fun μ : ℝ => (d (k + 1) - μ)⁻¹) (𝓝[<] (d (k + 1))) atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  have hsing : Tendsto (fun μ : ℝ => (ℓ (k + 1)) ^ 2 / (d (k + 1) - μ))
      (𝓝[<] (d (k + 1))) atTop := by
    have hpos : (0 : ℝ) < (ℓ (k + 1)) ^ 2 := by positivity
    have := hinv.const_mul_atTop hpos
    refine this.congr fun μ => ?_
    rw [div_eq_mul_inv]
  have hreg : Tendsto (fun μ : ℝ => ∑ j ∈ (Finset.range (N + 1)).erase (k + 1),
      (ℓ j) ^ 2 / (d j - μ)) (𝓝[<] (d (k + 1)))
      (𝓝 (∑ j ∈ (Finset.range (N + 1)).erase (k + 1), (ℓ j) ^ 2 / (d j - d (k + 1)))) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hjk : j ≠ k + 1 := Finset.ne_of_mem_erase hj
    have hne : d j - d (k + 1) ≠ 0 := by
      intro hcon
      exact hjk (hd.injective (by linarith))
    have hcont : ContinuousAt (fun μ : ℝ => (ℓ j) ^ 2 / (d j - μ)) (d (k + 1)) :=
      ContinuousAt.div continuousAt_const (by fun_prop) hne
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have := hsing.atTop_add hreg
  refine this.congr fun μ => ?_
  rw [hsplit μ]
  ring

/-- **Interlacing.**  Each gap of the diagonal contains a root of the secular equation, and it is
unique there. -/
theorem exists_unique_secular_root (hd : StrictMono d) (hk : k + 1 ≤ N)
    (hℓk : ℓ k ≠ 0) (hℓk1 : ℓ (k + 1) ≠ 0) :
    ∃! μ : ℝ, μ ∈ Ioo (d k) (d (k + 1)) ∧ secular d ℓ N μ = 0 := by
  have hgap : d k < d (k + 1) := hd (by omega)
  -- a point where the secular function is negative
  have hneg : ∃ x ∈ Ioo (d k) (d (k + 1)), secular d ℓ N x < 0 := by
    have h1 := (tendsto_secular_atBot hd hk hℓk).eventually_lt_atBot 0
    have h2 : ∀ᶠ x in 𝓝[>] (d k), x ∈ Ioo (d k) (d (k + 1)) := by
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hgap)] with x hx1 hx2
      exact ⟨hx1, hx2⟩
    obtain ⟨x, hx1, hx2⟩ := ((h1.and h2)).exists
    exact ⟨x, hx2, hx1⟩
  have hpos : ∃ y ∈ Ioo (d k) (d (k + 1)), 0 < secular d ℓ N y := by
    have h1 := (tendsto_secular_atTop hd hk hℓk1).eventually_gt_atTop 0
    have h2 : ∀ᶠ y in 𝓝[<] (d (k + 1)), y ∈ Ioo (d k) (d (k + 1)) := by
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hgap)] with y hy1 hy2
      exact ⟨hy2, hy1⟩
    obtain ⟨y, hy1, hy2⟩ := ((h1.and h2)).exists
    exact ⟨y, hy2, hy1⟩
  obtain ⟨x, hxmem, hxneg⟩ := hneg
  obtain ⟨y, hymem, hypos⟩ := hpos
  have hxy : x < y := by
    by_contra hle
    have hyx : y ≤ x := le_of_not_gt hle
    rcases eq_or_lt_of_le hyx with h | h
    · rw [h] at hypos
      linarith
    · have := secular_strictMonoOn hd hk hℓk hymem hxmem h
      linarith
  -- the intermediate value theorem on the closed subinterval
  have hsub : Icc x y ⊆ Ioo (d k) (d (k + 1)) := by
    intro t ht
    exact ⟨lt_of_lt_of_le hxmem.1 ht.1, lt_of_le_of_lt ht.2 hymem.2⟩
  have hcont : ContinuousOn (secular d ℓ N) (Icc x y) :=
    (continuousOn_secular (ℓ := ℓ) hd hk).mono hsub
  have hivt := intermediate_value_Icc hxy.le hcont
  have hzero : (0 : ℝ) ∈ Icc (secular d ℓ N x) (secular d ℓ N y) := ⟨hxneg.le, hypos.le⟩
  obtain ⟨μ, hμmem, hμ0⟩ := hivt hzero
  refine ⟨μ, ⟨hsub hμmem, hμ0⟩, ?_⟩
  rintro ν ⟨hνmem, hν0⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := secular_strictMonoOn hd hk hℓk hνmem (hsub hμmem) h
    rw [hν0, hμ0] at this
    exact lt_irrefl 0 this
  · have := secular_strictMonoOn hd hk hℓk (hsub hμmem) hνmem h
    rw [hν0, hμ0] at this
    exact lt_irrefl 0 this

/-! ## Scale covariance and the limiting root -/

/-- **The secular function is scale covariant.**  Rescaling the diagonal rescales the equation, so
the roots rescale with it; this is what lets the `k`-th root be studied in the normalized variable
`θ = μ / d (k+1)`. -/
theorem secular_smul (c : ℝ) (hc : c ≠ 0) (d ℓ : ℕ → ℝ) (N : ℕ) (μ : ℝ) :
    secular (fun j => c * d j) ℓ N (c * μ) = secular d ℓ N μ / c := by
  rw [secular, secular, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show c * d j - c * μ = c * (d j - μ) by ring]
  by_cases h : d j - μ = 0
  · rw [h, mul_zero, div_zero, div_zero, zero_div]

  · field_simp

/-- **The limiting secular equation has the explicit root `S/(S+T)`.**  In the normalized variable
the equation degenerates to `−S/θ + T/(1−θ) = 0`, whose root is the ratio the card calls
`θ_k = Q_k/Q_{k+1}`. -/
theorem limit_secular_root_iff {S T θ : ℝ} (hS : 0 < S) (hT : 0 < T)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    -(S / θ) + T / (1 - θ) = 0 ↔ θ = S / (S + T) := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have hST : S + T ≠ 0 := by positivity
  constructor
  · intro h
    have hmul : S * (1 - θ) = T * θ := by
      field_simp at h
      linarith
    field_simp
    linarith [hmul]
  · intro h
    rw [h]
    have hval : (1 : ℝ) - S / (S + T) = T / (S + T) := by
      field_simp
      ring
    rw [hval]
    have hSne : S ≠ 0 := ne_of_gt hS
    have hTne : T ≠ 0 := ne_of_gt hT
    field_simp
    ring

end GaloisForLFunctions.RHTower

end
