import GaloisForLFunctions.RHTower.BeurlingDeletionSawtoothBlock
import GaloisForLFunctions.RHTower.Sieve.AbelIncreasingWeight

/-!
# The integers free of a deletion set: the sawtooth bound

Let `S` be a deletion set (`DeletionData α`, `1/2 < α < 1`) and `N'(x)` the number of `n ≤ x`
free of `S`.  Under RH, for every `η > 0`,

`N'(x) = a' x + O(x^{3α/(α+4) + η})`   (`exists_norm_count_sub_le_saw`),

with `a'` the density of the Perron asymptotic.

**Proof.**  `1_{N'} = 1 ⋆ μ_S` (`sFreeInd_eq_sum_divisors`, by uniqueness of Dirichlet series), so
`N'(x) = Σ_{m ≤ x} μ_S(m) ⌊x/m⌋` (`count_eq_sum_floor`).  With the smooth cut `w(m) = φ(m/M₂)`:

* the hyperbola method moves `Σ μ_S(m)(1 − w(m)) ⌊x/m⌋` onto `Σ_{k ≤ x/M₂} Σ_{m ≤ x/k}` and Abel's
  inequality bounds each inner sum by twice the Möbius partial sums, `≪ (x/k)^{α/2+ε}`;
* `⌊y⌋ = y − 1/2 − ψ(y)` splits the rest into `x Σ μ_S(m) w(m)/m`, which is `A x + O(x M₂^{σ₀−1})`
  by dyadic contour bounds (`norm_mainSum_sub_le`), a Möbius sum, and the sawtooth sum;
* the sawtooth sum is cut into `φ(m/M₁)` (Rankin) and dyadic blocks `F(m/2^j M₁)`, each bounded by
  `exists_norm_block_le` with `Δ = M^{−(α+1)/3} x^{1/3}`.

With `M₁ = x^{1/(1+α)}` and `M₂ ≍ x^{4/(α+4)}` every piece is `≪ x^{3α/(α+4) + O(ε)}`.  The
coefficient `A` equals the Perron density because both asymptotics have exponent `< 1`.
-/

open Complex Finset Filter Topology Real
open GaloisForLFunctions.HTGeometry.TestFunctionPerron GaloisForLFunctions.HTGeometry.SmoothedSawtooth

noncomputable section

namespace RHTower.BeurlingDeletion

/-- The hyperbola reversal `Σ_{m ≤ n} f(m) ⌊n/m⌋ = Σ_{j ≤ n} Σ_{m ≤ n/j} f(m)`. -/
theorem sum_mul_div_eq_sum_sum (f : ℕ → ℂ) (n : ℕ) :
    ∑ m ∈ Finset.Ioc 0 n, f m * ((n / m : ℕ) : ℂ) =
      ∑ j ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Ioc 0 (n / j), f m := by
  have hrow : ∀ m ∈ Finset.Ioc 0 n, f m * ((n / m : ℕ) : ℂ) =
      ∑ j ∈ Finset.Icc 1 n, if j ≤ n / m then f m else 0 := by
    intro m hm
    have hmlo := (Finset.mem_Ioc.mp hm).1
    have hbound : n / m ≤ n := Nat.div_le_self n m
    have hset : (Finset.Icc 1 n).filter (fun j => j ≤ n / m) = Finset.Icc 1 (n / m) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter, hset]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, _⟩ := Finset.mem_Icc.mp hj
  have hset : (Finset.Ioc 0 n).filter (fun m => j ≤ n / m) = Finset.Ioc 0 (n / j) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hm0, hmn⟩, hdiv⟩
      refine ⟨hm0, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
      have h := (Nat.le_div_iff_mul_le hm0).mp hdiv
      simpa only [Nat.mul_comm] using h
    · rintro ⟨hm0, hmdiv⟩
      refine ⟨⟨hm0, hmdiv.trans (Nat.div_le_self n j)⟩, ?_⟩
      apply (Nat.le_div_iff_mul_le hm0).mpr
      have h := (Nat.le_div_iff_mul_le (by omega : 0 < j)).mp hmdiv
      simpa only [Nat.mul_comm] using h
  rw [← Finset.sum_filter, hset]

/-- Abel's inequality for an increasing weight in `[0, 1]`. -/
theorem norm_sum_Ioc_mul_le {μ : ℕ → ℂ} (hμ0 : μ 0 = 0) {v : ℕ → ℝ} (hv0 : 0 ≤ v 0)
    (hv1 : ∀ i, v i ≤ 1) (hmono : ∀ i, v i ≤ v (i + 1)) {K : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k, k ≤ K → ‖∑ i ∈ Finset.Iic k, μ i‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc 0 K, (v m : ℂ) * μ m‖ ≤ 2 * B := by
  have hrange : ∑ m ∈ Finset.range (K + 1), (v m : ℂ) * μ m =
      ∑ m ∈ Finset.Ioc 0 K, (v m : ℂ) * μ m := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hμ0, mul_zero, zero_add]
    rfl
  have hpart : ∀ k, k ≤ K + 1 → ‖∑ i ∈ Finset.range k, μ i‖ ≤ B := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa using hB0
    · have : Finset.range k = Finset.Iic (k - 1) := by
        ext i; simp only [Finset.mem_range, Finset.mem_Iic]; omega
      rw [this]; exact hB (k - 1) (by omega)
  have h := RHTower.Sieve.norm_sum_mul_le_of_bounded_partial_mono (K + 1) v μ hv0 hmono hpart
  rw [hrange] at h
  calc _ ≤ 2 * B * v (K + 1 - 1) := h
    _ ≤ 2 * B * 1 := mul_le_mul_of_nonneg_left (hv1 _) (by positivity)
    _ = 2 * B := mul_one _

/-! ## Exponents -/

/-- The first block exponent. -/
theorem exponent_one_le {α ε l L : ℝ} (hα1 : 1 / 2 < α) (hα : α < 1) (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) (hL0 : 0 ≤ L) (hl2 : l ≤ Real.log 2 + 4 / (α + 4) * L) :
    ((2 * α - 1) / 3 + 2 * ε * (α + 1) / 3) * l + (1 / 3 + ε / 3) * L ≤
      Real.log 2 + (3 * α / (α + 4) + 3 * ε) * L := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hα4 : 0 < α + 4 := by linarith
  set e₁ := (2 * α - 1) / 3 + 2 * ε * (α + 1) / 3 with he₁
  have he₁0 : 0 ≤ e₁ := by
    have : 0 ≤ 2 * ε * (α + 1) := by positivity
    rw [he₁]; linarith
  have he₁1 : e₁ ≤ 1 := by
    have : 2 * ε * (α + 1) ≤ 2 * (1 / 8) * 2 := by
      have : α + 1 ≤ 2 := by linarith
      calc 2 * ε * (α + 1) ≤ 2 * (1 / 8) * (α + 1) := by gcongr
        _ ≤ 2 * (1 / 8) * 2 := by gcongr
    rw [he₁]; linarith
  have h1 : e₁ * l ≤ e₁ * Real.log 2 + e₁ * (4 / (α + 4) * L) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hl2 he₁0
  have h2 : e₁ * Real.log 2 ≤ Real.log 2 := mul_le_of_le_one_left hlog2 he₁1
  have hcoef : 3 * α / (α + 4) + 3 * ε = e₁ * (4 / (α + 4)) + (1 / 3 + ε / 3) +
      8 * ε / (α + 4) := by rw [he₁]; field_simp; ring
  have h3 : 0 ≤ 8 * ε / (α + 4) * L := by positivity
  have h4 : (3 * α / (α + 4) + 3 * ε) * L =
      e₁ * (4 / (α + 4) * L) + (1 / 3 + ε / 3) * L + 8 * ε / (α + 4) * L := by
    rw [hcoef]; ring
  have h5 : e₁ * l + (1 / 3 + ε / 3) * L ≤
      Real.log 2 + (e₁ * (4 / (α + 4) * L) + (1 / 3 + ε / 3) * L) := by linarith
  rw [h4]; linarith

/-- The second block exponent. -/
theorem exponent_two_le {α ε l L : ℝ} (hα1 : 1 / 2 < α) (hα : α < 1) (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) (hL0 : 0 ≤ L) (hl2 : l ≤ Real.log 2 + 4 / (α + 4) * L) :
    ((2 * α - 1) / 3 + ε * (α + 1) / 3) * l + (1 - ε) / 3 * L ≤
      Real.log 2 + (3 * α / (α + 4) + 3 * ε) * L := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hα4 : 0 < α + 4 := by linarith
  set e₂ := (2 * α - 1) / 3 + ε * (α + 1) / 3 with he₂
  have he₂0 : 0 ≤ e₂ := by
    have : 0 ≤ ε * (α + 1) := by positivity
    rw [he₂]; linarith
  have he₂1 : e₂ ≤ 1 := by
    have : ε * (α + 1) ≤ (1 / 8) * 2 := by
      have : α + 1 ≤ 2 := by linarith
      calc ε * (α + 1) ≤ (1 / 8) * (α + 1) := by gcongr
        _ ≤ (1 / 8) * 2 := by gcongr
    rw [he₂]; linarith
  have h1 : e₂ * l ≤ e₂ * Real.log 2 + e₂ * (4 / (α + 4) * L) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hl2 he₂0
  have h2 : e₂ * Real.log 2 ≤ Real.log 2 := mul_le_of_le_one_left hlog2 he₂1
  have hcoef : 3 * α / (α + 4) + 3 * ε = e₂ * (4 / (α + 4)) + (1 - ε) / 3 +
      (2 * ε * α + 12 * ε) / (α + 4) := by rw [he₂]; field_simp; ring
  have h3 : 0 ≤ (2 * ε * α + 12 * ε) / (α + 4) * L := by
    have : 0 ≤ 2 * ε * α + 12 * ε := by positivity
    positivity
  have h4 : (3 * α / (α + 4) + 3 * ε) * L =
      e₂ * (4 / (α + 4) * L) + (1 - ε) / 3 * L + (2 * ε * α + 12 * ε) / (α + 4) * L := by
    rw [hcoef]; ring
  have h5 : e₂ * l + (1 - ε) / 3 * L ≤
      Real.log 2 + (e₂ * (4 / (α + 4) * L) + (1 - ε) / 3 * L) := by linarith
  rw [h4]; linarith

/-- **Block exponents.**  For `X^{1/(1+α)} ≤ u ≤ 2X^{4/(α+4)}` and `Δ = u^{−(α+1)/3} X^{1/3}`,
`0 < Δ ≤ 1` and `u^{α/2+ε} (X/u)^{1/2+ε} Δ^{−1/2−2ε} + Δ^{1−ε} u^α ≤ 4 X^{3α/(α+4) + 3ε}`. -/
theorem block_exponent_le {α ε X u Δ : ℝ} (hα1 : 1 / 2 < α) (hα : α < 1) (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) (hX : 1 ≤ X) (hu1 : X ^ (1 / (1 + α)) ≤ u)
    (hu2 : u ≤ 2 * X ^ (4 / (α + 4))) (hΔ : Δ = u ^ (-((α + 1) / 3)) * X ^ (1 / 3 : ℝ)) :
    0 < Δ ∧ Δ ≤ 1 ∧ u ^ (α / 2 + ε) * (X / u) ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε)) +
      Δ ^ (1 - ε) * u ^ α ≤ 4 * X ^ (3 * α / (α + 4) + 3 * ε) := by
  have hX0 : 0 < X := by linarith
  have hu0 : 0 < u := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hu1
  set L := Real.log X with hL
  set l := Real.log u with hl
  have hL0 : 0 ≤ L := Real.log_nonneg hX
  have hl1 : 1 / (1 + α) * L ≤ l := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hu1
    rwa [Real.log_rpow hX0] at this
  have hl2 : l ≤ Real.log 2 + 4 / (α + 4) * L := by
    have := Real.log_le_log hu0 hu2
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hX0 _).ne', Real.log_rpow hX0] at this
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set a : ℝ := (α + 1) / 3 with ha
  have hΔe : Δ = Real.exp (-a * l + L / 3) := by
    rw [hΔ, Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos hX0, ← Real.exp_add]
    congr 1; ring
  have hlogΔ : Real.log Δ = -a * l + L / 3 := by rw [hΔe, Real.log_exp]
  have hΔ0 : 0 < Δ := by rw [hΔe]; exact Real.exp_pos _
  have hΔexp : -a * l + L / 3 ≤ 0 := by
    have h1 : a * (1 / (1 + α) * L) = L / 3 := by rw [ha]; field_simp; ring
    have : a * (1 / (1 + α) * L) ≤ a * l := mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith
  have hΔ1 : Δ ≤ 1 := by rw [hΔe]; exact Real.exp_le_one_iff.mpr hΔexp
  refine ⟨hΔ0, hΔ1, ?_⟩
  have hγ : ∀ E : ℝ, E ≤ Real.log 2 + (3 * α / (α + 4) + 3 * ε) * L →
      Real.exp E ≤ 2 * X ^ (3 * α / (α + 4) + 3 * ε) := by
    intro E hE
    calc Real.exp E ≤ Real.exp (Real.log 2 + (3 * α / (α + 4) + 3 * ε) * L) := Real.exp_le_exp.mpr hE
      _ = 2 * X ^ (3 * α / (α + 4) + 3 * ε) := by
          rw [Real.exp_add, Real.exp_log (by norm_num), Real.rpow_def_of_pos hX0, mul_comm L]
  have hT1 : u ^ (α / 2 + ε) * (X / u) ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε)) =
      Real.exp (((2 * α - 1) / 3 + 2 * ε * (α + 1) / 3) * l + (1 / 3 + ε / 3) * L) := by
    rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos (div_pos hX0 hu0), Real.rpow_def_of_pos hΔ0,
      Real.log_div hX0.ne' hu0.ne', hlogΔ, ← Real.exp_add, ← Real.exp_add]
    congr 1; rw [ha]; ring
  have hT2 : Δ ^ (1 - ε) * u ^ α =
      Real.exp (((2 * α - 1) / 3 + ε * (α + 1) / 3) * l + (1 - ε) / 3 * L) := by
    rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos hΔ0, hlogΔ, ← Real.exp_add]
    congr 1; rw [ha]; ring
  have hE1 := exponent_one_le hα1 hα hε hε8 hL0 hl2
  have hE2 := exponent_two_le hα1 hα hε hε8 hL0 hl2
  rw [hT1, hT2]
  have := hγ _ hE1
  have := hγ _ hE2
  linarith

/-- **The dyadic range.**  With `M₁ = X^{1/(1+α)}` and `J = ⌈log₂(X^{4/(α+4)}/M₁)⌉`,
`X^{4/(α+4)} ≤ 2^J M₁ ≤ 2 X^{4/(α+4)}` and `J ≤ log X / log 2 + 1`. -/
theorem dyadic_range {α X : ℝ} (hα0 : 0 < α) (hα : α < 1) (hX : 1 ≤ X) :
    X ^ (4 / (α + 4)) ≤ 2 ^ ⌈Real.logb 2 (X ^ (4 / (α + 4)) / X ^ (1 / (1 + α)))⌉₊ *
        X ^ (1 / (1 + α)) ∧
      2 ^ ⌈Real.logb 2 (X ^ (4 / (α + 4)) / X ^ (1 / (1 + α)))⌉₊ * X ^ (1 / (1 + α)) ≤
        2 * X ^ (4 / (α + 4)) ∧
      (⌈Real.logb 2 (X ^ (4 / (α + 4)) / X ^ (1 / (1 + α)))⌉₊ : ℝ) ≤ Real.log X / Real.log 2 + 1 := by
  have hX0 : 0 < X := by linarith
  set M₁ := X ^ (1 / (1 + α)) with hM₁
  set K := X ^ (4 / (α + 4)) with hK
  have hM₁0 : 0 < M₁ := Real.rpow_pos_of_pos hX0 _
  have hK0 : 0 < K := Real.rpow_pos_of_pos hX0 _
  set ρ := K / M₁ with hρ
  have hρeq : ρ = X ^ (4 / (α + 4) - 1 / (1 + α)) := by
    rw [hρ, hK, hM₁, Real.rpow_sub hX0]
  have hexp0 : 0 ≤ 4 / (α + 4) - 1 / (1 + α) := by
    rw [div_sub_div _ _ (by linarith) (by linarith), le_div_iff₀ (by positivity)]; nlinarith
  have hexp1 : 4 / (α + 4) - 1 / (1 + α) ≤ 1 := by
    have : 4 / (α + 4) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have : 0 ≤ 1 / (1 + α) := by positivity
    linarith
  have hρ1 : 1 ≤ ρ := by rw [hρeq]; exact Real.one_le_rpow hX hexp0
  have hρX : ρ ≤ X := by
    rw [hρeq]; calc X ^ (4 / (α + 4) - 1 / (1 + α)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX hexp1
      _ = X := Real.rpow_one X
  have hρ0 : 0 < ρ := by linarith
  set b := Real.logb 2 ρ with hb
  have hb0 : 0 ≤ b := Real.logb_nonneg (by norm_num) hρ1
  set J := ⌈b⌉₊ with hJ
  have hJb : b ≤ J := Nat.le_ceil b
  have hJb' : (J : ℝ) < b + 1 := Nat.ceil_lt_add_one hb0
  have h2b : (2 : ℝ) ^ b = ρ := Real.rpow_logb (by norm_num) (by norm_num) hρ0
  have hJlow : ρ ≤ (2 : ℝ) ^ J := by
    rw [← h2b, ← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hJb
  have hJup : (2 : ℝ) ^ J ≤ 2 * ρ := by
    rw [← h2b, ← Real.rpow_natCast, show (2 : ℝ) * 2 ^ b = 2 ^ (b + 1) by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hJb'.le
  refine ⟨?_, ?_, ?_⟩
  · calc K = ρ * M₁ := by rw [hρ]; field_simp
      _ ≤ 2 ^ J * M₁ := mul_le_mul_of_nonneg_right hJlow hM₁0.le
  · calc (2 : ℝ) ^ J * M₁ ≤ 2 * ρ * M₁ := mul_le_mul_of_nonneg_right hJup hM₁0.le
      _ = 2 * K := by rw [hρ]; field_simp
  · have hbX : b ≤ Real.log X / Real.log 2 := by
      rw [hb, Real.logb, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))]
      exact Real.log_le_log hρ0 hρX
    linarith

/-- `X M^{θ−1} ≤ X^{3α/(α+4) + 5ε}` for `M ≥ X^{4/(α+4)}`, `θ = α/2 + ε`. -/
theorem mul_rpow_sub_one_le {α ε X M : ℝ} (hα0 : 0 < α) (hα : α < 1) (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) (hX : 1 ≤ X) (hM : X ^ (4 / (α + 4)) ≤ M) :
    X * M ^ (α / 2 + ε - 1) ≤ X ^ (3 * α / (α + 4) + 5 * ε) := by
  have hX0 : 0 < X := by linarith
  have hK0 : 0 < X ^ (4 / (α + 4)) := Real.rpow_pos_of_pos hX0 _
  calc X * M ^ (α / 2 + ε - 1) ≤ X * (X ^ (4 / (α + 4))) ^ (α / 2 + ε - 1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hK0 hM (by linarith)) hX0.le
    _ = X ^ (1 + 4 / (α + 4) * (α / 2 + ε - 1)) := by
        rw [← Real.rpow_mul hX0.le, Real.rpow_add hX0, Real.rpow_one]
    _ ≤ X ^ (3 * α / (α + 4) + 5 * ε) := by
        apply Real.rpow_le_rpow_of_exponent_le hX
        have e : 1 + 4 / (α + 4) * (α / 2 + ε - 1) = 3 * α / (α + 4) + 4 * ε / (α + 4) := by
          field_simp; ring
        rw [e]
        have : 4 * ε / (α + 4) ≤ ε := by rw [div_le_iff₀ (by linarith)]; nlinarith
        linarith

theorem rpow_theta_le {α ε X : ℝ} (hα0 : 0 < α) (hα : α < 1) (hε : 0 < ε) (hX : 1 ≤ X) :
    X ^ (α / 2 + ε) ≤ X ^ (3 * α / (α + 4) + 5 * ε) := by
  apply Real.rpow_le_rpow_of_exponent_le hX
  have : α / 2 ≤ 3 * α / (α + 4) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  linarith

theorem two_mul_rpow_le {α ε X : ℝ} (hα1 : 1 / 2 < α) (hα : α < 1) (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) (hX : 1 ≤ X) :
    (2 * X ^ (1 / (1 + α))) ^ (α + ε) ≤ 4 * X ^ (3 * α / (α + 4) + 5 * ε) := by
  have hX0 : 0 < X := by linarith
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hX0.le]
  have h2 : (2 : ℝ) ^ (α + ε) ≤ 4 := by
    calc (2 : ℝ) ^ (α + ε) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by linarith)
      _ = 4 := by norm_num
  have hx : X ^ (1 / (1 + α) * (α + ε)) ≤ X ^ (3 * α / (α + 4) + 5 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hX
    have e : 1 / (1 + α) * (α + ε) = α / (1 + α) + ε / (1 + α) := by field_simp
    rw [e]
    have h1 : α / (1 + α) ≤ 3 * α / (α + 4) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have h2 : ε / (1 + α) ≤ ε := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  calc (2 : ℝ) ^ (α + ε) * X ^ (1 / (1 + α) * (α + ε)) ≤
        4 * X ^ (3 * α / (α + 4) + 5 * ε) :=
        mul_le_mul h2 hx (by positivity) (by norm_num)

theorem rpow_mul_div_rpow_le {α ε X M : ℝ} (hα0 : 0 < α) (hα : α < 1) (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) (hX : 1 ≤ X) (hM : X ^ (4 / (α + 4)) ≤ M) :
    X ^ (α / 2 + ε) * (X / M) ^ (1 - (α / 2 + ε)) ≤ X ^ (3 * α / (α + 4) + 5 * ε) := by
  have hX0 : 0 < X := by linarith
  have hK0 : 0 < X ^ (4 / (α + 4)) := Real.rpow_pos_of_pos hX0 _
  have hM0 : 0 < M := lt_of_lt_of_le hK0 hM
  have hθ : 0 ≤ 1 - (α / 2 + ε) := by linarith
  calc X ^ (α / 2 + ε) * (X / M) ^ (1 - (α / 2 + ε)) ≤
        X ^ (α / 2 + ε) * (X / X ^ (4 / (α + 4))) ^ (1 - (α / 2 + ε)) := by
        gcongr
    _ = X ^ (α / 2 + ε + (1 - 4 / (α + 4)) * (1 - (α / 2 + ε))) := by
        rw [show X / X ^ (4 / (α + 4)) = X ^ (1 - 4 / (α + 4)) by
          rw [Real.rpow_sub hX0, Real.rpow_one], ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    _ ≤ X ^ (3 * α / (α + 4) + 5 * ε) := by
        apply Real.rpow_le_rpow_of_exponent_le hX
        have e : α / 2 + ε + (1 - 4 / (α + 4)) * (1 - (α / 2 + ε)) =
            3 * α / (α + 4) + 4 * ε / (α + 4) := by field_simp; ring
        rw [e]
        have : 4 * ε / (α + 4) ≤ ε := by rw [div_le_iff₀ (by linarith)]; nlinarith
        linarith

/-- `J ≤ log X/log 2 + 1 ≤ (1/(2ε log 2) + 1) X^{2ε}`. -/
theorem nat_le_rpow_of_le_log {J : ℕ} {X ε : ℝ} (hX : 1 ≤ X) (hε : 0 < ε)
    (hJ : (J : ℝ) ≤ Real.log X / Real.log 2 + 1) :
    (J : ℝ) ≤ (1 / (2 * ε * Real.log 2) + 1) * X ^ (2 * ε) := by
  have hX0 : 0 < X := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_rpow_div hX0.le (show 0 < 2 * ε by linarith)
  have hX1 : 1 ≤ X ^ (2 * ε) := Real.one_le_rpow hX (by linarith)
  have h1 : Real.log X / Real.log 2 ≤ 1 / (2 * ε * Real.log 2) * X ^ (2 * ε) := by
    rw [div_le_iff₀ hlog2]
    calc Real.log X ≤ X ^ (2 * ε) / (2 * ε) := hlog
      _ = 1 / (2 * ε * Real.log 2) * X ^ (2 * ε) * Real.log 2 := by field_simp
  nlinarith

namespace DeletionData

variable {α : ℝ} (D : DeletionData α)

/-! ## `1_{N'} = 1 ⋆ μ_S` -/

theorem lseriesSummable_sFreeInd {s : ℂ} (hs : 1 < s.re) : LSeriesSummable D.sFreeInd s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) (by linarith)
    ⟨1, fun n _ => by simpa using D.norm_sFreeInd_le n⟩

omit D in
theorem lseriesSummable_one {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (1 : ℕ → ℂ) s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) (by linarith) ⟨1, fun n _ => by simp⟩

/-- **`1_{N'} = 1 ⋆ μ_S`.** -/
theorem sFreeInd_eq_sum_divisors (hα0 : 0 < α) (hα : α < 1) {n : ℕ} (hn : n ≠ 0) :
    D.sFreeInd n = ∑ d ∈ n.divisors, D.mobS d := by
  have habs : ∀ f : ℕ → ℂ, (∀ y : ℝ, 1 < y → LSeriesSummable f y) →
      LSeries.abscissaOfAbsConv f < ⊤ := fun f hf =>
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hf y hy).trans_lt
      (EReal.coe_lt_top _)
  have hg : ∀ y : ℝ, 1 < y → LSeriesSummable (LSeries.convolution D.mobS 1) y := fun y hy =>
    (D.lseriesSummable_mobS (by simpa using hy)).convolution (lseriesSummable_one (by simpa using hy))
  have hconv : LSeries.convolution D.mobS 1 n = ∑ d ∈ n.divisors, D.mobS d := by
    rw [LSeries.convolution_def]
    simp only [Pi.one_apply, mul_one]
    exact Nat.sum_divisorsAntidiagonal (fun a _ => D.mobS a)
  rw [← hconv]
  refine LSeries.eq_of_LSeries_eventually_eq
    (habs _ fun y hy => D.lseriesSummable_sFreeInd (by simpa using hy)) (habs _ hg) ?_ hn
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  have hy' : 1 < ((y : ℂ)).re := by simpa using hy
  have hy1 : (y : ℂ) ≠ 1 := fun h => by rw [h] at hy'; simp at hy'
  rw [← D.perronNum_div_eq_LSeries hα0 hα hy', D.perronNum_div_eq hy1,
    LSeries_convolution' (D.lseriesSummable_mobS hy') (lseriesSummable_one hy'),
    D.LSeries_mobS_eq hα0 hα hy', LSeries_one_eq_riemannZeta hy']
  ring

/-- **`N'(x) = Σ_{m ≤ x} μ_S(m) ⌊x/m⌋`.** -/
theorem count_eq_sum_floor (hα0 : 0 < α) (hα : α < 1) (X : ℝ) :
    D.count X = ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * ((⌊X⌋₊ / m : ℕ) : ℂ) := by
  set f : ArithmeticFunction ℂ := ⟨D.mobS, D.mobS_zero⟩ with hf
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum f ⌊X⌋₊
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h
  unfold count
  rw [show Finset.Iic ⌊X⌋₊ = Finset.Icc 0 ⌊X⌋₊ by ext n; simp, Finset.Icc_eq_cons_Ioc
    (Nat.zero_le _), Finset.sum_cons, D.sFreeInd_zero, zero_add]
  have hcongr : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, D.sFreeInd n =
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ∑ i ∈ n.divisors, f i := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [D.sFreeInd_eq_sum_divisors hα0 hα (Finset.mem_Ioc.mp hn).1.ne']
    rfl
  rw [hcongr, h]
  rfl

/-! ## The main term -/

/-- `c̃(M) = Σ_m μ_S(m) φ(m/M)/m`. -/
def mainSum (M : ℝ) : ℂ := ∑' m : ℕ, D.mobS m * ((cut (m / M) / m : ℝ) : ℂ)

/-- The full sum `A = Σ_m μ_S(m)/m`. -/
def mobSum : ℂ := ∑' m : ℕ, D.mobS m / m

theorem mainSum_eq_sum {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 2 * M ≤ N) :
    D.mainSum M = ∑ m ∈ Finset.Ioc 0 N, D.mobS m * ((cut (m / M) / m : ℝ) : ℂ) := by
  unfold mainSum
  refine tsum_eq_sum fun m hm => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · have hmN : N < m := by
      by_contra h; push Not at h; exact hm (Finset.mem_Ioc.mpr ⟨hpos, h⟩)
    have h2 : 2 ≤ (m : ℝ) / M := by
      rw [le_div_iff₀ hM]; have : (N : ℝ) < m := by exact_mod_cast hmN
      linarith
    simp [cut_eq_zero h2]

theorem mainSum_two_mul_sub {M : ℝ} (hM : 0 < M) :
    D.mainSum (2 * M) - D.mainSum M = (M : ℂ)⁻¹ * ∑' m : ℕ, D.mobS m * bumpDivC (m / M) := by
  set N : ℕ := ⌊4 * M⌋₊ + 1 with hN
  have hN4 : 4 * M ≤ N := by rw [hN]; push_cast; linarith [Nat.lt_floor_add_one (4 * M)]
  rw [D.mainSum_eq_sum (by positivity : (0 : ℝ) < 2 * M) (by linarith),
    D.mainSum_eq_sum hM (by linarith), ← Finset.sum_sub_distrib]
  have hb : ∑' m : ℕ, D.mobS m * bumpDivC (m / M) =
      ∑ m ∈ Finset.Ioc 0 N, D.mobS m * bumpDivC (m / M) := by
    refine tsum_eq_sum fun m hm => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp [D.mobS_zero]
    · have hmN : N < m := by
        by_contra h; push Not at h; exact hm (Finset.mem_Ioc.mpr ⟨hpos, h⟩)
      have h4 : 4 ≤ (m : ℝ) / M := by
        rw [le_div_iff₀ hM]; have : (N : ℝ) < m := by exact_mod_cast hmN
        linarith
      simp [bumpDivC, bump_eq_zero_of_ge h4]
  rw [hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Ioc.mp hm).1
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  simp only [bumpDivC, bump]
  rw [show (m : ℝ) / (2 * M) = (m : ℝ) / M / 2 by ring]
  push_cast
  field_simp

theorem tendsto_mainSum (hα0 : 0 < α) (hα : α < 1) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun J : ℕ => D.mainSum (2 ^ J * M)) atTop (𝓝 D.mobSum) := by
  unfold mainSum mobSum
  refine tendsto_tsum_of_dominated_convergence (D.summable_norm_mobS_div hα0 hα) (fun m => ?_)
    (Eventually.of_forall fun J m => ?_)
  · have hev : ∀ᶠ J : ℕ in atTop, D.mobS m * ((cut (m / (2 ^ J * M)) / m : ℝ) : ℂ) =
        D.mobS m / m := by
      obtain ⟨J₀, hJ₀⟩ := pow_unbounded_of_one_lt ((m : ℝ) / M) (by norm_num : (1 : ℝ) < 2)
      filter_upwards [eventually_ge_atTop J₀] with J hJ
      have hle : (m : ℝ) / (2 ^ J * M) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have h1 : (m : ℝ) / M < 2 ^ J :=
          lt_of_lt_of_le hJ₀ (pow_le_pow_right₀ (by norm_num) hJ)
        rw [div_lt_iff₀ hM] at h1
        linarith
      rw [cut_eq_one hle]
      push_cast
      ring
    exact tendsto_const_nhds.congr' (hev.mono fun J h => h.symm)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv (‖D.mobS m‖)]
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos
    rw [abs_of_nonneg (div_nonneg (cut_nonneg _) hm0.le), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (inv_nonneg.mpr hm0.le)
      (cut_le_one _)) (norm_nonneg _)

/-- **The main term.**  `|c̃(M) − A| ≪ M^{σ₀ − 1}` under RH. -/
theorem exists_norm_mainSum_sub_le (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1) {ε : ℝ}
    (hε : 0 < ε) (hεα : ε < α / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ‖D.mainSum M - D.mobSum‖ ≤ C * M ^ (α / 2 + ε - 1) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := D.exists_norm_tsum_mobS_le hRH hα0 hα hε hεα
  set L₃ := lineMass bumpDivC (α / 2 + ε) ε with hL₃
  have hL₃0 : 0 ≤ L₃ := MeasureTheory.integral_nonneg fun t => by positivity
  set r : ℝ := (2 : ℝ) ^ (α / 2 + ε - 1) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨K₁ * L₃ / (1 - r), by have := sub_pos.mpr hr1; positivity, fun M hM => ?_⟩
  have hM0 : 0 < M := by linarith
  have hstep : ∀ j : ℕ, ‖D.mainSum (2 ^ (j + 1) * M) - D.mainSum (2 ^ j * M)‖ ≤
      K₁ * L₃ * M ^ (α / 2 + ε - 1) * r ^ j := by
    intro j
    have hMj : 0 < 2 ^ j * M := by positivity
    rw [show (2 : ℝ) ^ (j + 1) * M = 2 * (2 ^ j * M) by ring, D.mainSum_two_mul_sub hMj,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMj]
    have h := hK₁ bumpDivC 1 4 isTest_bumpDivC (2 ^ j * M) hMj
    calc (2 ^ j * M)⁻¹ * ‖∑' m : ℕ, D.mobS m * bumpDivC (m / (2 ^ j * M))‖
        ≤ (2 ^ j * M)⁻¹ * (K₁ * (2 ^ j * M) ^ (α / 2 + ε) * L₃) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = K₁ * L₃ * (2 ^ j * M) ^ (α / 2 + ε - 1) := by
          rw [Real.rpow_sub hMj, Real.rpow_one]; field_simp
      _ = K₁ * L₃ * M ^ (α / 2 + ε - 1) * r ^ j := by
          rw [Real.mul_rpow (by positivity) hM0.le, hr, ← Real.rpow_natCast,
            ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
          ring_nf
  have hpartial : ∀ J : ℕ, ‖D.mainSum M - D.mainSum (2 ^ J * M)‖ ≤
      K₁ * L₃ * M ^ (α / 2 + ε - 1) / (1 - r) := by
    intro J
    have htel : D.mainSum M - D.mainSum (2 ^ J * M) =
        -∑ j ∈ Finset.range J, (D.mainSum (2 ^ (j + 1) * M) - D.mainSum (2 ^ j * M)) := by
      rw [Finset.sum_range_sub (fun j => D.mainSum (2 ^ j * M))]
      simp
    rw [htel, norm_neg]
    have hgeom : ∑ j ∈ Finset.range J, r ^ j ≤ 1 / (1 - r) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0.le hr1
      rwa [pow_zero, ← Finset.range_eq_Ico] at this
    have hK : 0 ≤ K₁ * L₃ * M ^ (α / 2 + ε - 1) := by positivity
    calc ‖∑ j ∈ Finset.range J, (D.mainSum (2 ^ (j + 1) * M) - D.mainSum (2 ^ j * M))‖
        ≤ ∑ j ∈ Finset.range J, ‖D.mainSum (2 ^ (j + 1) * M) - D.mainSum (2 ^ j * M)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range J, K₁ * L₃ * M ^ (α / 2 + ε - 1) * r ^ j :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = K₁ * L₃ * M ^ (α / 2 + ε - 1) * ∑ j ∈ Finset.range J, r ^ j := by rw [Finset.mul_sum]
      _ ≤ K₁ * L₃ * M ^ (α / 2 + ε - 1) * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeom hK
      _ = K₁ * L₃ * M ^ (α / 2 + ε - 1) / (1 - r) := by ring
  have hlim : Tendsto (fun J : ℕ => ‖D.mainSum M - D.mainSum (2 ^ J * M)‖) atTop
      (𝓝 ‖D.mainSum M - D.mobSum‖) :=
    ((tendsto_const_nhds.sub (D.tendsto_mainSum hα0 hα M hM0))).norm
  calc ‖D.mainSum M - D.mobSum‖ ≤ K₁ * L₃ * M ^ (α / 2 + ε - 1) / (1 - r) :=
        le_of_tendsto' hlim hpartial
    _ = K₁ * L₃ / (1 - r) * M ^ (α / 2 + ε - 1) := by ring

/-! ## The decomposition -/

omit D in
theorem floor_div_eq (X : ℝ) (hX : 0 ≤ X) (m : ℕ) :
    (((⌊X⌋₊ / m : ℕ) : ℝ)) = X / m - 1 / 2 - saw (X / m) := by
  rw [← Nat.floor_div_natCast, natCast_floor_eq_intCast_floor (div_nonneg hX (Nat.cast_nonneg _))]
  unfold saw; rw [Int.fract]; ring

/-- The block sums only see `m ≤ 4M`. -/
theorem sum_Ioc_block_eq {N : ℕ} {M X : ℝ} (hM : 0 < M) (hN : 4 * M ≤ N) :
    ∑ m ∈ Finset.Ioc 0 N, D.mobS m * bumpC (m / M) * (saw (X / m) : ℂ) =
      ∑ m ∈ Finset.Icc 1 ⌊4 * M⌋₊, D.mobS m * bumpC (m / M) * (saw (X / m) : ℂ) := by
  symm
  refine Finset.sum_subset (fun m hm => ?_) (fun m hm hm' => ?_)
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    refine Finset.mem_Ioc.mpr ⟨h1, ?_⟩
    have : (m : ℝ) ≤ N := le_trans ((Nat.le_floor_iff (by linarith)).mp h2) hN
    exact_mod_cast this
  · have h1 := (Finset.mem_Ioc.mp hm).1
    have h4 : 4 ≤ (m : ℝ) / M := by
      rw [le_div_iff₀ hM]
      have : ⌊4 * M⌋₊ < m := by
        by_contra h; push Not at h; exact hm' (Finset.mem_Icc.mpr ⟨h1, h⟩)
      have := Nat.lt_of_floor_lt this
      linarith
    simp [bumpC, bump_eq_zero_of_ge h4]

/-- **The decomposition of `N'(X)`.** -/
theorem count_decomposition (hα0 : 0 < α) (hα : α < 1) {X M₁ : ℝ} (hX : 0 ≤ X) (hM₁ : 0 < M₁)
    (J : ℕ) (hN : 2 * (2 ^ J * M₁) ≤ ⌊X⌋₊) :
    D.count X = X * D.mainSum (2 ^ J * M₁) -
      1 / 2 * ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / (2 ^ J * M₁)) : ℂ) -
      ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / M₁) : ℂ) * (saw (X / m) : ℂ) -
      ∑ j ∈ Finset.range J, ∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
        D.mobS m * bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ) +
      ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ∑ m ∈ Finset.Ioc 0 (⌊X⌋₊ / j),
        D.mobS m * (((1 - cut (m / (2 ^ J * M₁))) : ℝ) : ℂ) := by
  set N := ⌊X⌋₊ with hNdef
  set M₂ := 2 ^ J * M₁ with hM₂
  have hM₂0 : 0 < M₂ := by positivity
  rw [D.count_eq_sum_floor hα0 hα X, ← sum_mul_div_eq_sum_sum]
  -- the saw part
  have hsaw : ∑ m ∈ Finset.Ioc 0 N, D.mobS m * (cut (m / M₂) : ℂ) * (saw (X / m) : ℂ) =
      ∑ m ∈ Finset.Ioc 0 N, D.mobS m * (cut (m / M₁) : ℂ) * (saw (X / m) : ℂ) +
      ∑ j ∈ Finset.range J, ∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
        D.mobS m * bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ) := by
    have hpt : ∀ m : ℕ, D.mobS m * (cut (m / M₂) : ℂ) * (saw (X / m) : ℂ) =
        D.mobS m * (cut (m / M₁) : ℂ) * (saw (X / m) : ℂ) +
        ∑ j ∈ Finset.range J, D.mobS m * bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ) := by
      intro m
      have h := cut_sub_cut_eq_sum_bump (m : ℝ) M₁ J
      rw [← hM₂] at h
      have h' : (cut (m / M₂) : ℂ) = (cut (m / M₁) : ℂ) +
          ∑ j ∈ Finset.range J, bumpC (m / (2 ^ j * M₁)) := by
        simp only [bumpC]; rw [← Complex.ofReal_sum, ← h]; push_cast; ring
      rw [h', ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl fun m _ => hpt m, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    exact D.sum_Ioc_block_eq (by positivity) (by
      have hj' : j + 1 ≤ J := Finset.mem_range.mp hj
      have hpow : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj'
      have : (4 : ℝ) * (2 ^ j * M₁) ≤ 2 * M₂ := by
        rw [hM₂, pow_succ] at *
        nlinarith
      linarith)
  have hfloor : ∀ m ∈ Finset.Ioc 0 N, D.mobS m * ((N / m : ℕ) : ℂ) =
      X * (D.mobS m * ((cut (m / M₂) / m : ℝ) : ℂ)) - 1 / 2 * (D.mobS m * (cut (m / M₂) : ℂ)) -
        D.mobS m * (cut (m / M₂) : ℂ) * (saw (X / m) : ℂ) +
        D.mobS m * (((1 - cut (m / M₂)) : ℝ) : ℂ) * ((N / m : ℕ) : ℂ) := by
    intro m hm
    have hm0 : 0 < m := (Finset.mem_Ioc.mp hm).1
    have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
    have hf := floor_div_eq X hX m
    have hfc : ((N / m : ℕ) : ℂ) = (((X / m - 1 / 2 - saw (X / m)) : ℝ) : ℂ) := by
      rw [← hf]; push_cast; rfl
    rw [hfc]
    push_cast
    field_simp
    ring
  have hN' : 2 * M₂ ≤ (N : ℝ) := hN
  rw [Finset.sum_congr rfl hfloor, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← D.mainSum_eq_sum hM₂0 hN', hsaw]
  ring

/-! ## The pieces -/

/-- Partial sums of `μ_S` up to every `k ≤ K` are at most `C K^θ`. -/
theorem norm_sum_Iic_mobS_le {C θ : ℝ} (hC0 : 0 ≤ C) (hθ : 0 ≤ θ)
    (hC : ∀ Y : ℝ, 1 ≤ Y → ‖∑ n ∈ Finset.Iic ⌊Y⌋₊, D.mobS n‖ ≤ C * Y ^ θ) {K k : ℕ} (hk : k ≤ K) :
    ‖∑ i ∈ Finset.Iic k, D.mobS i‖ ≤ C * (K : ℝ) ^ θ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have : Finset.Iic (0 : ℕ) = {0} := by ext; simp
    rw [this, Finset.sum_singleton, D.mobS_zero, norm_zero]; positivity
  have h := hC k (by exact_mod_cast hk0)
  rw [Nat.floor_natCast] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast hk) hθ) hC0)

/-- **The hyperbola remainder.** -/
theorem norm_hyperbola_le {C θ : ℝ} (hC0 : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hC : ∀ Y : ℝ, 1 ≤ Y → ‖∑ n ∈ Finset.Iic ⌊Y⌋₊, D.mobS n‖ ≤ C * Y ^ θ) {X M₂ : ℝ} (hX : 1 ≤ X)
    (hM₂ : 1 ≤ M₂) :
    ‖∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ∑ m ∈ Finset.Ioc 0 (⌊X⌋₊ / j),
        D.mobS m * (((1 - cut (m / M₂)) : ℝ) : ℂ)‖ ≤
      2 * C / (1 - θ) * X ^ θ * (X / M₂) ^ (1 - θ) := by
  set N := ⌊X⌋₊ with hN
  have hX0 : 0 < X := by linarith
  have hM₀ : 0 < M₂ := by linarith
  have hinner : ∀ j ∈ Finset.Icc 1 N, ‖∑ m ∈ Finset.Ioc 0 (N / j),
      D.mobS m * (((1 - cut (m / M₂)) : ℝ) : ℂ)‖ ≤
      if (j : ℝ) ≤ X / M₂ then 2 * C * X ^ θ * (j : ℝ) ^ (-θ) else 0 := by
    intro j hj
    obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    set K := N / j with hK
    by_cases hKM : (K : ℝ) ≤ M₂
    · have hzero : ∑ m ∈ Finset.Ioc 0 K, D.mobS m * (((1 - cut (m / M₂)) : ℝ) : ℂ) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hmK : (m : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Ioc.mp hm).2
        rw [cut_eq_one (by rw [div_le_one hM₀]; linarith)]
        simp
      rw [hzero, norm_zero]
      split_ifs <;> positivity
    push Not at hKM
    have hjX : (j : ℝ) ≤ X / M₂ := by
      have h1 : (j : ℝ) * K ≤ X := by
        have : j * K ≤ N := Nat.mul_div_le N j
        have h2 : ((j * K : ℕ) : ℝ) ≤ N := by exact_mod_cast this
        push_cast at h2
        linarith [Nat.floor_le hX0.le]
      rw [le_div_iff₀ hM₀]
      nlinarith
    rw [if_pos hjX]
    have hcomm : ∑ m ∈ Finset.Ioc 0 K, D.mobS m * (((1 - cut (m / M₂)) : ℝ) : ℂ) =
        ∑ m ∈ Finset.Ioc 0 K, ((1 - cut (m / M₂) : ℝ) : ℂ) * D.mobS m :=
      Finset.sum_congr rfl fun m _ => mul_comm _ _
    rw [hcomm]
    have hab := norm_sum_Ioc_mul_le (μ := D.mobS) D.mobS_zero (v := fun m : ℕ => 1 - cut (m / M₂))
      (by show 0 ≤ 1 - cut (((0 : ℕ) : ℝ) / M₂); linarith [cut_le_one (((0 : ℕ) : ℝ) / M₂)])
      (fun i => by linarith [cut_nonneg ((i : ℝ) / M₂)])
      (fun i => by
        have : cut (((i + 1 : ℕ) : ℝ) / M₂) ≤ cut ((i : ℝ) / M₂) :=
          cut_antitone (div_le_div_of_nonneg_right (by push_cast; linarith) hM₀.le)
        linarith)
      (K := K) (B := C * (K : ℝ) ^ θ) (by positivity)
      (fun k hk => D.norm_sum_Iic_mobS_le hC0 hθ0.le hC hk)
    refine hab.trans ?_
    have hKX : (K : ℝ) ≤ X / j := by
      rw [le_div_iff₀ hj0]
      have : (K : ℝ) * j ≤ N := by
        have := Nat.div_mul_le_self N j
        exact_mod_cast this
      linarith [Nat.floor_le hX0.le]
    have hKpos : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
    calc 2 * (C * (K : ℝ) ^ θ) ≤ 2 * (C * (X / j) ^ θ) := by
          gcongr
      _ = 2 * C * X ^ θ * (j : ℝ) ^ (-θ) := by
          rw [Real.div_rpow hX0.le hj0.le, Real.rpow_neg hj0.le]; ring
  have hsum : ∑ j ∈ Finset.Icc 1 N, (if (j : ℝ) ≤ X / M₂ then 2 * C * X ^ θ * (j : ℝ) ^ (-θ) else 0)
      ≤ ∑ j ∈ Finset.Icc 1 ⌊X / M₂⌋₊, 2 * C * X ^ θ * (j : ℝ) ^ (-θ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun _ _ _ => by positivity)
    obtain ⟨hj1, hjX⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj1).1, Nat.le_floor hjX⟩
  have hrp := DeletionData.sum_rpow_le (α := 1 - θ) (by linarith) (by linarith) ⌊X / M₂⌋₊
  have hrp' : ∑ j ∈ Finset.Icc 1 ⌊X / M₂⌋₊, (j : ℝ) ^ (-θ) ≤ (X / M₂) ^ (1 - θ) / (1 - θ) := by
    have e : ∀ j : ℕ, (j : ℝ) ^ (-θ) = (j : ℝ) ^ (1 - θ - 1) := fun j => by ring_nf
    simp_rw [e]
    refine hrp.trans ?_
    gcongr
    exact Nat.floor_le (by positivity)
  calc _ ≤ ∑ j ∈ Finset.Icc 1 N, ‖∑ m ∈ Finset.Ioc 0 (N / j),
        D.mobS m * (((1 - cut (m / M₂)) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum hinner
    _ ≤ _ := hsum
    _ = 2 * C * X ^ θ * ∑ j ∈ Finset.Icc 1 ⌊X / M₂⌋₊, (j : ℝ) ^ (-θ) := by rw [Finset.mul_sum]
    _ ≤ 2 * C * X ^ θ * ((X / M₂) ^ (1 - θ) / (1 - θ)) :=
        mul_le_mul_of_nonneg_left hrp' (by positivity)
    _ = _ := by ring

/-- The smoothly cut Möbius sum. -/
theorem norm_sum_mobS_cut_le {C θ : ℝ} (hC0 : 0 ≤ C) (hθ0 : 0 ≤ θ)
    (hC : ∀ Y : ℝ, 1 ≤ Y → ‖∑ n ∈ Finset.Iic ⌊Y⌋₊, D.mobS n‖ ≤ C * Y ^ θ) {X M₂ : ℝ} (hX : 1 ≤ X)
    (hM₂ : 0 < M₂) :
    ‖∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / M₂) : ℂ)‖ ≤ 3 * C * X ^ θ := by
  have hX0 : 0 < X := by linarith
  have hsplit : ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / M₂) : ℂ) =
      ∑ m ∈ Finset.Iic ⌊X⌋₊, D.mobS m -
        ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, ((1 - cut (m / M₂) : ℝ) : ℂ) * D.mobS m := by
    rw [show Finset.Iic ⌊X⌋₊ = Finset.Icc 0 ⌊X⌋₊ by ext n; simp,
      Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, D.mobS_zero, zero_add,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast; ring
  have hab := norm_sum_Ioc_mul_le (μ := D.mobS) D.mobS_zero (v := fun m : ℕ => 1 - cut (m / M₂))
    (by show 0 ≤ 1 - cut (((0 : ℕ) : ℝ) / M₂); linarith [cut_le_one (((0 : ℕ) : ℝ) / M₂)])
    (fun i => by linarith [cut_nonneg ((i : ℝ) / M₂)])
    (fun i => by
      have : cut (((i + 1 : ℕ) : ℝ) / M₂) ≤ cut ((i : ℝ) / M₂) :=
        cut_antitone (div_le_div_of_nonneg_right (by push_cast; linarith) hM₂.le)
      linarith)
    (K := ⌊X⌋₊) (B := C * ((⌊X⌋₊ : ℕ) : ℝ) ^ θ) (by positivity)
    (fun k hk => D.norm_sum_Iic_mobS_le hC0 hθ0 hC hk)
  have hNX : C * ((⌊X⌋₊ : ℕ) : ℝ) ^ θ ≤ C * X ^ θ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (Nat.floor_le hX0.le) hθ0) hC0
  rw [hsplit]
  calc _ ≤ ‖∑ m ∈ Finset.Iic ⌊X⌋₊, D.mobS m‖ +
        ‖∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, ((1 - cut (m / M₂) : ℝ) : ℂ) * D.mobS m‖ := norm_sub_le _ _
    _ ≤ C * X ^ θ + 2 * (C * X ^ θ) := add_le_add (hC X hX) (hab.trans (by linarith))
    _ = 3 * C * X ^ θ := by ring

/-- **The small range** (Rankin). -/
theorem norm_small_le (hα0 : 0 < α) (hα : α < 1) {σ : ℝ} (hσ : α < σ) {X M₁ : ℝ}
    (hM₁ : 1 / 2 ≤ M₁) :
    ‖∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / M₁) : ℂ) * (saw (X / m) : ℂ)‖ ≤
      1 / 2 * ((2 * M₁) ^ σ * Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-σ)) n)) := by
  have hM₀ : 0 < M₁ := by linarith
  have hterm : ∀ m ∈ Finset.Ioc 0 ⌊X⌋₊,
      ‖D.mobS m * (cut (m / M₁) : ℂ) * (saw (X / m) : ℂ)‖ ≤
        1 / 2 * (if m ≤ ⌊2 * M₁⌋₊ then ‖D.mobS m‖ else 0) := by
    intro m _
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (cut_nonneg _)]
    have hs := abs_saw_le (X / m)
    split_ifs with h
    · calc ‖D.mobS m‖ * cut (m / M₁) * |saw (X / m)| ≤ ‖D.mobS m‖ * 1 * (1 / 2) := by
            gcongr
            exact cut_le_one _
        _ = _ := by ring
    · push Not at h
      have h2 : 2 ≤ (m : ℝ) / M₁ := by
        rw [le_div_iff₀ hM₀]; have := Nat.lt_of_floor_lt h; linarith
      rw [cut_eq_zero h2]; simp
  have hsub : ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, (if m ≤ ⌊2 * M₁⌋₊ then ‖D.mobS m‖ else 0) ≤
      ∑ m ∈ Finset.Icc 1 ⌊2 * M₁⌋₊, ‖D.mobS m‖ := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) (fun _ _ _ => norm_nonneg _)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp h1).1, h2⟩
  calc _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, ‖D.mobS m * (cut (m / M₁) : ℂ) * (saw (X / m) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, 1 / 2 * (if m ≤ ⌊2 * M₁⌋₊ then ‖D.mobS m‖ else 0) :=
        Finset.sum_le_sum hterm
    _ = 1 / 2 * ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, (if m ≤ ⌊2 * M₁⌋₊ then ‖D.mobS m‖ else 0) := by
        rw [Finset.mul_sum]
    _ ≤ 1 / 2 * ∑ m ∈ Finset.Icc 1 ⌊2 * M₁⌋₊, ‖D.mobS m‖ := by gcongr
    _ ≤ _ := by
        gcongr
        exact D.sum_norm_mobS_le hα0 hα hσ (by linarith)

/-! ## Assembly -/

/-- `8 X^{4/(α+4)} ≤ X` once `X ≥ 8^{(α+4)/α}`. -/
theorem eight_mul_rpow_le {α X : ℝ} (hα0 : 0 < α) (hX : (8 : ℝ) ^ ((α + 4) / α) ≤ X) :
    8 * X ^ (4 / (α + 4)) ≤ X := by
  have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((α + 4) / α) := Real.one_le_rpow (by norm_num) (by positivity)
  have hX0 : 0 < X := by linarith
  have hpow : 8 ≤ X ^ (α / (α + 4)) := by
    calc (8 : ℝ) = ((8 : ℝ) ^ ((α + 4) / α)) ^ (α / (α + 4)) := by
          rw [← Real.rpow_mul (by norm_num), show (α + 4) / α * (α / (α + 4)) = 1 by
            field_simp, Real.rpow_one]
      _ ≤ X ^ (α / (α + 4)) := Real.rpow_le_rpow (by positivity) hX (by positivity)
  calc 8 * X ^ (4 / (α + 4)) ≤ X ^ (α / (α + 4)) * X ^ (4 / (α + 4)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = X := by
        rw [← Real.rpow_add hX0, show α / (α + 4) + 4 / (α + 4) = 1 by field_simp,
          Real.rpow_one]

/-- **The sawtooth assembly** for large `X`. -/
theorem norm_count_sub_mobSum_le (hα1 : 1 / 2 < α) (hα : α < 1) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) {CM CA KB : ℝ} (hCM0 : 0 ≤ CM) (hCA0 : 0 ≤ CA) (hKB0 : 0 ≤ KB)
    (hCM : ∀ Y : ℝ, 1 ≤ Y → ‖∑ n ∈ Finset.Iic ⌊Y⌋₊, D.mobS n‖ ≤ CM * Y ^ (α / 2 + ε))
    (hCA : ∀ M : ℝ, 1 ≤ M → ‖D.mainSum M - D.mobSum‖ ≤ CA * M ^ (α / 2 + ε - 1))
    (hKB : ∀ M x Δ : ℝ, 1 ≤ M → M ≤ x → 0 < Δ → Δ ≤ 1 →
      ‖∑ m ∈ Finset.Icc 1 ⌊4 * M⌋₊, D.mobS m * bumpC (m / M) * (saw (x / m) : ℂ)‖ ≤
        KB * (M ^ (α / 2 + ε) * (x / M) ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε)) +
          Δ ^ (1 - ε) * M ^ α))
    {X : ℝ} (hX : (8 : ℝ) ^ ((α + 4) / α) ≤ X) :
    ‖D.count X - D.mobSum * X‖ ≤
      (CA + 2 * CM + 2 * Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-(α + ε))) n) +
        4 * KB * (1 / (2 * ε * Real.log 2) + 1) + 2 * CM / (1 - (α / 2 + ε))) *
        X ^ (3 * α / (α + 4) + 5 * ε) := by
  have hα0 : 0 < α := by linarith
  have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((α + 4) / α) := Real.one_le_rpow (by norm_num) (by positivity)
  have hX1 : 1 ≤ X := le_trans h8 hX
  have hX0 : 0 < X := by linarith
  set γ := 3 * α / (α + 4) + 5 * ε with hγ
  have hXγ : 1 ≤ X ^ γ := Real.one_le_rpow hX1 (by positivity)
  set M₁ := X ^ (1 / (1 + α)) with hM₁
  have hM₁1 : 1 ≤ M₁ := Real.one_le_rpow hX1 (by positivity)
  obtain ⟨hlo, hhi, hJ⟩ := dyadic_range hα0 hα hX1
  set J := ⌈Real.logb 2 (X ^ (4 / (α + 4)) / X ^ (1 / (1 + α)))⌉₊ with hJdef
  set M₂ := 2 ^ J * M₁ with hM₂
  have h8X := eight_mul_rpow_le hα0 hX
  have hK1 : 1 ≤ X ^ (4 / (α + 4)) := Real.one_le_rpow hX1 (by positivity)
  have hM₂1 : 1 ≤ M₂ := le_trans hK1 hlo
  have hN : 2 * M₂ ≤ (⌊X⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one X
    linarith
  have hdec := D.count_decomposition hα0 hα hX0.le (by linarith : (0 : ℝ) < M₁) J hN
  rw [hdec]
  set S₂ := ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / M₂) : ℂ)
  set Sm := ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / M₁) : ℂ) * (saw (X / m) : ℂ)
  set Bl := ∑ j ∈ Finset.range J, ∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
    D.mobS m * bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ)
  set Hy := ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ∑ m ∈ Finset.Ioc 0 (⌊X⌋₊ / j),
    D.mobS m * (((1 - cut (m / M₂)) : ℝ) : ℂ)
  have e : (X : ℂ) * D.mainSum M₂ - 1 / 2 * S₂ - Sm - Bl + Hy - D.mobSum * X =
      (X : ℂ) * (D.mainSum M₂ - D.mobSum) - 1 / 2 * S₂ - Sm - Bl + Hy := by ring
  rw [e]
  -- (a) the main term
  have ha : ‖(X : ℂ) * (D.mainSum M₂ - D.mobSum)‖ ≤ CA * X ^ γ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
    calc X * ‖D.mainSum M₂ - D.mobSum‖ ≤ X * (CA * M₂ ^ (α / 2 + ε - 1)) :=
          mul_le_mul_of_nonneg_left (hCA M₂ hM₂1) hX0.le
      _ = CA * (X * M₂ ^ (α / 2 + ε - 1)) := by ring
      _ ≤ CA * X ^ γ := mul_le_mul_of_nonneg_left
          (mul_rpow_sub_one_le hα0 hα hε hε8 hX1 hlo) hCA0
  -- (b) the Möbius sum
  have hb : ‖1 / 2 * S₂‖ ≤ 2 * CM * X ^ γ := by
    rw [norm_mul]
    have h := D.norm_sum_mobS_cut_le hCM0 (by positivity) hCM hX1 (by linarith : (0 : ℝ) < M₂)
    have ht := rpow_theta_le hα0 hα hε hX1
    calc ‖(1 / 2 : ℂ)‖ * ‖S₂‖ ≤ 1 / 2 * (3 * CM * X ^ (α / 2 + ε)) := by
          rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; gcongr
      _ ≤ 2 * CM * X ^ γ := by nlinarith
  -- (c) the small range
  have hc : ‖Sm‖ ≤ 2 * Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-(α + ε))) n) *
      X ^ γ := by
    have h := D.norm_small_le hα0 hα (σ := α + ε) (by linarith) (X := X) (M₁ := M₁)
      (by linarith)
    have h2 := two_mul_rpow_le hα1 hα hε hε8 hX1
    calc ‖Sm‖ ≤ 1 / 2 * ((2 * M₁) ^ (α + ε) *
          Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-(α + ε))) n)) := h
      _ ≤ 1 / 2 * ((4 * X ^ γ) *
          Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-(α + ε))) n)) := by gcongr
      _ = _ := by ring
  -- (d) the blocks
  have hd : ‖Bl‖ ≤ 4 * KB * (1 / (2 * ε * Real.log 2) + 1) * X ^ γ := by
    have hblock : ∀ j ∈ Finset.range J, ‖∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
        D.mobS m * bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ)‖ ≤
        KB * (4 * X ^ (3 * α / (α + 4) + 3 * ε)) := by
      intro j hj
      have hjJ : j + 1 ≤ J := Finset.mem_range.mp hj
      set u := 2 ^ j * M₁ with hu
      have hu1 : M₁ ≤ u := le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
      have hu2 : u ≤ M₂ := by
        rw [hu, hM₂]; exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (by omega)) (by linarith)
      have hu3 : u ≤ 2 * X ^ (4 / (α + 4)) := le_trans hu2 hhi
      have hux : u ≤ X := by linarith
      obtain ⟨hΔ0, hΔ1, hT⟩ := block_exponent_le hα1 hα hε hε8 hX1 hu1 hu3 rfl
      exact (hKB u X _ (le_trans hM₁1 hu1) hux hΔ0 hΔ1).trans
        (mul_le_mul_of_nonneg_left hT hKB0)
    have hJb := nat_le_rpow_of_le_log hX1 hε hJ
    have hx3 : X ^ (3 * α / (α + 4) + 3 * ε) * X ^ (2 * ε) = X ^ γ := by
      rw [← Real.rpow_add hX0]; congr 1; ring
    calc ‖Bl‖ ≤ ∑ j ∈ Finset.range J, ‖∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
          D.mobS m * bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range J, KB * (4 * X ^ (3 * α / (α + 4) + 3 * ε)) :=
          Finset.sum_le_sum hblock
      _ = (J : ℝ) * (KB * (4 * X ^ (3 * α / (α + 4) + 3 * ε))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((1 / (2 * ε * Real.log 2) + 1) * X ^ (2 * ε)) *
            (KB * (4 * X ^ (3 * α / (α + 4) + 3 * ε))) :=
          mul_le_mul_of_nonneg_right hJb (by positivity)
      _ = 4 * KB * (1 / (2 * ε * Real.log 2) + 1) *
            (X ^ (3 * α / (α + 4) + 3 * ε) * X ^ (2 * ε)) := by ring
      _ = _ := by rw [hx3]
  -- (e) the hyperbola remainder
  have he : ‖Hy‖ ≤ 2 * CM / (1 - (α / 2 + ε)) * X ^ γ := by
    have h := D.norm_hyperbola_le hCM0 (by positivity) (by linarith) hCM hX1 hM₂1
    have h2 := rpow_mul_div_rpow_le hα0 hα hε hε8 hX1 hlo
    calc ‖Hy‖ ≤ 2 * CM / (1 - (α / 2 + ε)) * X ^ (α / 2 + ε) * (X / M₂) ^ (1 - (α / 2 + ε)) := h
      _ = 2 * CM / (1 - (α / 2 + ε)) * (X ^ (α / 2 + ε) * (X / M₂) ^ (1 - (α / 2 + ε))) := by
          ring
      _ ≤ 2 * CM / (1 - (α / 2 + ε)) * X ^ γ := by
          have : 0 ≤ 2 * CM / (1 - (α / 2 + ε)) := div_nonneg (by positivity) (by linarith)
          exact mul_le_mul_of_nonneg_left h2 this
  calc ‖(X : ℂ) * (D.mainSum M₂ - D.mobSum) - 1 / 2 * S₂ - Sm - Bl + Hy‖
      ≤ ‖(X : ℂ) * (D.mainSum M₂ - D.mobSum)‖ + ‖1 / 2 * S₂‖ + ‖Sm‖ + ‖Bl‖ + ‖Hy‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
        exact norm_sub_le _ _
    _ ≤ CA * X ^ γ + 2 * CM * X ^ γ +
        2 * Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-(α + ε))) n) * X ^ γ +
        4 * KB * (1 / (2 * ε * Real.log 2) + 1) * X ^ γ +
        2 * CM / (1 - (α / 2 + ε)) * X ^ γ := by gcongr
    _ = _ := by ring

end DeletionData

end RHTower.BeurlingDeletion
