import GaloisForLFunctions.VerifiedHeightRungs.ZerosNearMostHeights

/-!
# Separated zeros in every long window

Verified zeros put `n + 1` pairwise `σ`-separated ordinates into every window of length `L ≥ 2e^{2Y}` above a floor
`t_* = exp(O(Y))`, where `Y³ ≳ σ⁻⁴` is the width of the gap test:

* `exists_zero_near_of_re_prime_le`: at a height `|t| ≥ t_*` with `Re Π(−t/2π) ≤ Y m₂ log(|t| + 3)/4` a zero lies within
  `σ` of `t` (the form of the modulated gap test beats the cost of a `σ`-gap);
* `volume_bad_heights_le`: in a window of length `L ≥ 2e^{2Y}` the heights with `‖Π(−t/2π)‖ ≥ A` have measure at most
  `8π m₂ V L/(3 m₁² A²)` (windowed variance law, transported to heights);
* `exists_separated_zeros_of_volume_lt`: cut the window into `M` slots of length `2σ`. A good height in the middle half-unit
  of a slot gives a zero within `σ/2` of the slot centre; if the bad measure is below `σ/2 · (M − n)`, at least `n + 1` slots
  are good, and their zeros have consecutive gaps above `σ`;
* `exists_spread_zeros_in_window`: the three together, for `M = 5(m + 1)` slots and `n + 1 = 4(m + 1)` zeros.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower _root_.RHTower.WeilRegular Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-! ### A small prime polynomial forces a zero -/

/-- **Good heights carry zeros.** -/
theorem exists_zero_near_of_re_prime_le {σ Y t : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 0 < Y)
    (hY3 : 32 * (400 * gapMass) ^ 2 * 5760 / (σ ^ 4 * gapEnergy) ≤ Y ^ 3)
    (ht30 : Real.exp 30 ≤ |t|) (htail : 4 * Real.exp Y * gapTail Y / (Y * gapEnergy) ≤ |t|)
    (hon : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| ≤ Real.exp Y → ρ.re = 1 / 2)
    (hP : (primePolynomial (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))).re ≤
      Y * gapEnergy * Real.log (|t| + 3) / 4) :
    ∃ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| < σ := by
  have hm := gapMass_pos
  have hEn := gapEnergy_pos
  refine exists_zero_near_of_re_W_gt hσ hσ1 hY hon ?_
  have hlow := re_W_modulatedTest_gapTest_ge hY t
  obtain ⟨E, hE⟩ : ∃ E, E = Y * gapEnergy := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  rw [← hE] at hlow htail hP
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (|t| + 3) := ⟨_, rfl⟩
  rw [← hL] at hP ⊢
  have ht0 : 0 < |t| := lt_of_lt_of_le (Real.exp_pos 30) ht30
  -- The zero side costs at most `E L / 4`.
  have hw : gapWeight σ Y * (24 * 240) ≤ E / 4 := by
    have h1 : 32 * (400 * gapMass) ^ 2 * 5760 ≤ Y ^ 3 * (σ ^ 4 * gapEnergy) :=
      (div_le_iff₀ (by positivity)).1 hY3
    have e : gapWeight σ Y * (24 * 240) = 32 * (400 * gapMass) ^ 2 * 5760 / (4 * σ ^ 4 * Y ^ 2) := by
      unfold gapWeight
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity), hE]
    calc 32 * (400 * gapMass) ^ 2 * 5760 ≤ Y ^ 3 * (σ ^ 4 * gapEnergy) := h1
      _ = Y * gapEnergy / 4 * (4 * σ ^ 4 * Y ^ 2) := by ring
  -- `L ≥ 30` and `log(1 + |t|/8) ≥ L − 3`.
  have hL30 : 30 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    linarith only [ht30]
  have h8 : Real.log 8 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    nlinarith only [h1]
  have hℓ : L - 3 ≤ Real.log (1 + |t| / 8) := by
    have h1 : Real.log ((|t| + 3) / 8) ≤ Real.log (1 + |t| / 8) :=
      Real.log_le_log (by positivity) (by linarith only)
    rw [Real.log_div (by positivity) (by norm_num), ← hL] at h1
    linarith only [h1, h8]
  -- The tails cost at most `9E/16`.
  obtain ⟨G, hG⟩ : ∃ G, G = gapTail Y := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG, gapTail]; positivity
  rw [← hG] at hlow htail
  have hG1 : 4 * Real.exp Y * G ≤ |t| * E := (div_le_iff₀ hE0).1 htail
  have heY : 1 ≤ Real.exp Y := Real.one_le_exp hY.le
  have hGt : 4 * G ≤ |t| * E := by nlinarith only [hG1, heY, hG0]
  have hT1 : G / (8 * (1 + |t| / 2)) ≤ E / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hGt, hE0, ht0]
  have hT2 : 2 * Real.exp Y * G / (1 + |t|) ^ 4 ≤ E / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 + |t| ≤ (1 + |t|) ^ 4 := by
      have : 1 ≤ 1 + |t| := by linarith only [ht0]
      calc 1 + |t| = (1 + |t|) ^ 1 := (pow_one _).symm
        _ ≤ (1 + |t|) ^ 4 := pow_le_pow_right₀ this (by norm_num)
    have h2 : E / 2 * (1 + |t|) ≤ E / 2 * (1 + |t|) ^ 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith only [hG1, h2, hE0]
  have hmain : (L - 3) * E ≤ Real.log (1 + |t| / 8) * E := mul_le_mul_of_nonneg_right hℓ hE0.le
  have hLE : 30 * E ≤ L * E := mul_le_mul_of_nonneg_right hL30 hE0.le
  have hZ : gapWeight σ Y * (24 * 240 * L) ≤ E / 4 * L := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hw (by linarith only [hL30])
  have e1 : (Real.log (1 + |t| / 8) - 10) * E = Real.log (1 + |t| / 8) * E - 10 * E := by ring
  have e2 : (L - 3) * E = L * E - 3 * E := by ring
  have e3 : E / 4 * L = L * E / 4 := by ring
  have e4 : E * L / 4 = L * E / 4 := by ring
  rw [e1] at hlow
  rw [e2] at hmain
  rw [e3] at hZ
  rw [e4] at hP
  linarith only [hlow, hmain, hLE, hZ, hP, hT1, hT2, hE0]

/-! ### Rare bad heights in every long window -/

/-- **The windowed Chebyshev bound in heights.** -/
theorem volume_bad_heights_le {Y L A : ℝ} (hY : 0 < Y) (hL : 2 * Real.exp (2 * Y) ≤ L) (hA : 0 < A) (c : ℝ) :
    volume (Icc c (c + L) ∩
        {t : ℝ | A ≤ ‖primePolynomial (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖}) ≤
      ENNReal.ofReal (8 * π * gapEnergy * primeVariance (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ * L /
        (3 * gapMass ^ 2 * A ^ 2)) := by
  have hπ := Real.pi_pos
  have hm := gapMass_pos
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨r, hr⟩ : ∃ r, r = 1 / L := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hX : 2 * r * Real.exp (2 * Y) ≤ 1 := by
    rw [hr, show 2 * (1 / L) * Real.exp (2 * Y) = 2 * Real.exp (2 * Y) / L by ring, div_le_one hL0]
    exact hL
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀, ξ₀ = -(c + L / 2) / (2 * π) := ⟨_, rfl⟩
  have hB := volume_window_prime_ge_le hY hr0 hX ξ₀ hA
  set S := Icc (-(1 / (4 * π * r))) (1 / (4 * π * r)) ∩
    {ξ | A ≤ ‖primePolynomial (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ (ξ + ξ₀)‖} with hS
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = -(2 * π)⁻¹ := ⟨_, rfl⟩
  have hk0 : k ≠ 0 := by rw [hk]; exact neg_ne_zero.2 (inv_ne_zero (by positivity))
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (c + L / 2) / (2 * π) := ⟨_, rfl⟩
  have hpre : Icc c (c + L) ∩
      {t : ℝ | A ≤ ‖primePolynomial (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖} =
      (fun t => k * t) ⁻¹' ((fun x => x + d) ⁻¹' S) := by
    ext t
    have hφ : k * t + d + ξ₀ = -t / (2 * π) := by
      rw [hk, hd, hξ₀]
      field_simp
      ring
    have hφ' : k * t + d = (c + L / 2 - t) / (2 * π) := by
      rw [hk, hd]
      field_simp
      ring
    have hD : 1 / (4 * π * r) = L / 2 / (2 * π) := by
      rw [hr]
      field_simp
      ring
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_preimage, hS, hφ, hD]
    rw [hφ']
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, ?_⟩, h3⟩
      · rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right (by positivity)]
        linarith only [h2]
      · rw [div_le_div_iff_of_pos_right (by positivity)]
        linarith only [h1]
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, ?_⟩, h3⟩
      · rw [div_le_div_iff_of_pos_right (by positivity)] at h2
        linarith only [h2]
      · rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right (by positivity)] at h1
        linarith only [h1]
  rw [hpre, Real.volume_preimage_mul_left hk0, measure_preimage_add_right]
  have hkabs : |k⁻¹| = 2 * π := by
    rw [hk, inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]
  rw [hkabs]
  calc ENNReal.ofReal (2 * π) * volume S
      ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal (4 * gapEnergy * primeVariance (gapTestC Y)
          ⌊Real.exp (2 * Y)⌋₊ / (3 * r * gapMass ^ 2 * A ^ 2)) := mul_le_mul_left' hB _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hr]
      field_simp
      ring

/-! ### Slots -/

/-- **Few bad heights give many separated zeros.** In `M` slots of length `2σ` starting at `c`, if the heights outside
`G` have measure below `σ/2 · (M − n)` and every height of `G` has a zero within `σ/4`, then `n + 1` zeros of the window
have pairwise gaps `σ|i − j|`. -/
theorem exists_separated_zeros_of_volume_lt {c σ : ℝ} (hσ : 0 < σ) {M n : ℕ} {G : Set ℝ}
    (hbad : volume (Icc c (c + 2 * M * σ) \ G) < ENNReal.ofReal (σ / 2 * ((M : ℝ) - n)))
    (hzero : ∀ t ∈ Icc c (c + 2 * M * σ), t ∈ G → ∃ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| < σ / 4) :
    ∃ node : ℕ → zetaZeroConfig.carrier,
      (∀ j ∈ range (n + 1), c ≤ ((node j : ℂ)).im ∧ ((node j : ℂ)).im ≤ c + 2 * M * σ) ∧
      ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1),
        σ * |(i : ℝ) - j| ≤ |((node i : ℂ)).im - ((node j : ℂ)).im| := by
  classical
  -- The middle half-unit of slot `k`.
  set J : ℕ → Set ℝ := fun k => Icc (c + 2 * k * σ + 3 * σ / 4) (c + 2 * k * σ + 5 * σ / 4) with hJ
  have hJsub : ∀ k ∈ range M, J k ⊆ Icc c (c + 2 * M * σ) := by
    intro k hk t ht
    have hkM : (k : ℝ) + 1 ≤ M := by exact_mod_cast Finset.mem_range.1 hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    obtain ⟨h1, h2⟩ := ht
    constructor <;> nlinarith only [h1, h2, hkM, hk0, hσ]
  set Good := (range M).filter (fun k => ∃ t ∈ J k, t ∈ G) with hGood
  -- At least `n + 1` slots are good.
  have hcard : n + 1 ≤ Good.card := by
    by_contra hlt
    push Not at hlt
    set Bad := range M \ Good with hBad
    have hBc : Bad.card = M - Good.card := by
      rw [hBad, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_range]
    have hGM : Good.card ≤ M := (Finset.card_filter_le _ _).trans (Finset.card_range M).le
    have hBcR : (M : ℝ) - n ≤ Bad.card := by
      rw [hBc, Nat.cast_sub hGM]
      have : (Good.card : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 hlt
      linarith only [this]
    have hsub : (⋃ k ∈ Bad, J k) ⊆ Icc c (c + 2 * M * σ) \ G := by
      intro t ht
      simp only [Set.mem_iUnion] at ht
      obtain ⟨k, hk, htk⟩ := ht
      have hkM : k ∈ range M := (Finset.mem_sdiff.1 hk).1
      have hkG : k ∉ Good := (Finset.mem_sdiff.1 hk).2
      refine ⟨hJsub k hkM htk, fun htG => hkG ?_⟩
      exact Finset.mem_filter.2 ⟨hkM, t, htk, htG⟩
    have hdisj : (Bad : Set ℕ).PairwiseDisjoint J := by
      intro i _ j _ hij
      refine Set.disjoint_left.2 fun t hti htj => hij ?_
      obtain ⟨h1, h2⟩ := hti
      obtain ⟨h3, h4⟩ := htj
      have hlt1 : (i : ℝ) < j + 1 := by nlinarith only [h1, h4, hσ]
      have hlt2 : (j : ℝ) < i + 1 := by nlinarith only [h2, h3, hσ]
      have a1 : i < j + 1 := by exact_mod_cast hlt1
      have a2 : j < i + 1 := by exact_mod_cast hlt2
      omega
    have hvol : volume (⋃ k ∈ Bad, J k) = ∑ k ∈ Bad, volume (J k) :=
      measure_biUnion_finset hdisj fun k _ => measurableSet_Icc
    have hJk : ∀ k, volume (J k) = ENNReal.ofReal (σ / 2) := fun k => by
      rw [hJ, Real.volume_Icc]
      congr 1
      ring
    simp only [hJk, Finset.sum_const, nsmul_eq_mul] at hvol
    have hlow : ENNReal.ofReal (σ / 2 * ((M : ℝ) - n)) ≤ volume (⋃ k ∈ Bad, J k) := by
      rw [hvol, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hBcR (by positivity : (0 : ℝ) ≤ σ / 2)
      linarith only [this]
    exact absurd ((hlow.trans (measure_mono hsub)).trans_lt hbad) (lt_irrefl _)
  -- A zero near the centre of every good slot.
  have hne : Nonempty zetaZeroConfig.carrier := by
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (lt_of_lt_of_le (Nat.succ_pos n) hcard)
    obtain ⟨hkM, t, htk, htG⟩ := Finset.mem_filter.1 hk
    obtain ⟨ρ, hρ, -⟩ := hzero t (hJsub k hkM htk) htG
    exact ⟨⟨ρ, hρ⟩⟩
  have hz : ∀ k : ℕ, ∃ ρ : zetaZeroConfig.carrier, k ∈ Good →
      c + 2 * k * σ + σ / 2 < (ρ : ℂ).im ∧ (ρ : ℂ).im < c + 2 * k * σ + 3 * σ / 2 := by
    intro k
    by_cases hk : k ∈ Good
    · obtain ⟨hkM, t, htk, htG⟩ := Finset.mem_filter.1 hk
      obtain ⟨ρ, hρ, hρt⟩ := hzero t (hJsub k hkM htk) htG
      obtain ⟨h1, h2⟩ := htk
      obtain ⟨h3, h4⟩ := abs_lt.1 hρt
      exact ⟨⟨ρ, hρ⟩, fun _ => ⟨by change _ < ρ.im; linarith only [h1, h3],
        by change ρ.im < _; linarith only [h2, h4]⟩⟩
    · exact ⟨hne.some, fun h => absurd h hk⟩
  choose z hzP using hz
  -- The good slots in increasing order.
  set e := Good.orderEmbOfFin rfl with he
  set s : ℕ → ℕ := fun j => if h : j < Good.card then e ⟨j, h⟩ else 0 with hs
  have hsG : ∀ j ∈ range (n + 1), s j ∈ Good := by
    intro j hj
    have hjc : j < Good.card := lt_of_lt_of_le (Finset.mem_range.1 hj) hcard
    simp only [hs, dif_pos hjc]
    exact Finset.orderEmbOfFin_mem Good rfl _
  have hsmono : ∀ j, j + 1 < n + 1 → s j < s (j + 1) := by
    intro j hj
    have hjc : j + 1 < Good.card := lt_of_lt_of_le hj hcard
    have hjc' : j < Good.card := by omega
    simp only [hs, dif_pos hjc, dif_pos hjc']
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self j))
  set v : ℕ → ℝ := fun j => ((z (s j) : ℂ)).im with hv
  have hstep : ∀ j, j + 1 < n + 1 → v j + σ ≤ v (j + 1) := by
    intro j hj
    have h1 := hzP (s j) (hsG j (Finset.mem_range.2 (by omega)))
    have h2 := hzP (s (j + 1)) (hsG (j + 1) (Finset.mem_range.2 hj))
    have h3 : ((s j : ℕ) : ℝ) + 1 ≤ (s (j + 1) : ℕ) := by exact_mod_cast hsmono j hj
    simp only [hv]
    nlinarith only [h1.2, h2.1, h3, hσ]
  have htel : ∀ i j, i ≤ j → j < n + 1 → ((j : ℝ) - i) * σ ≤ v j - v i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; simp
    | succ j hij ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j hj
      push_cast
      linarith only [h1, h2]
  refine ⟨fun j => z (s j), fun j hj => ?_, fun i hi j hj => ?_⟩
  · have hG := hsG j hj
    have hsM : (s j : ℝ) + 1 ≤ M := by exact_mod_cast Finset.mem_range.1 (Finset.mem_filter.1 hG).1
    have hs0 : (0 : ℝ) ≤ s j := Nat.cast_nonneg _
    obtain ⟨h1, h2⟩ := hzP (s j) hG
    constructor <;> nlinarith only [h1, h2, hsM, hs0, hσ]
  · have hin : i < n + 1 := Finset.mem_range.1 hi
    have hjn : j < n + 1 := Finset.mem_range.1 hj
    rcases le_total i j with hij | hji
    · have h := htel i j hij hjn
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      rw [abs_of_nonpos (by linarith only [hij']), abs_sub_comm]
      calc σ * -((i : ℝ) - j) = ((j : ℝ) - i) * σ := by ring
        _ ≤ v j - v i := h
        _ ≤ |v j - v i| := le_abs_self _
    · have h := htel j i hji hin
      have hji' : (j : ℝ) ≤ i := by exact_mod_cast hji
      rw [abs_of_nonneg (by linarith only [hji'])]
      calc σ * ((i : ℝ) - j) = ((i : ℝ) - j) * σ := by ring
        _ ≤ v i - v j := h
        _ ≤ |v i - v j| := le_abs_self _

/-! ### Spread zeros in a window -/

/-- **Spread zeros in every long window above the floor.** A window of length `10(m + 1)σ ≥ 2e^{2Y}` whose heights
are at least `t_*` and verified up to `T − e^Y` holds `4(m + 1)` zeros with pairwise gaps `σ|i − j|`. The floor `t_*`
pays the zero side (`e^{30}`), the tails, and the variance of the prime polynomial against the threshold
`Y m₂ log(t_* + 3)/4`. -/
theorem exists_spread_zeros_in_window {σ Y tₛ T c : ℝ} {m : ℕ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 0 < Y)
    (hY3 : 32 * (400 * gapMass) ^ 2 * 5760 / ((σ / 4) ^ 4 * gapEnergy) ≤ Y ^ 3)
    (hs30 : Real.exp 30 ≤ tₛ) (hstail : 4 * Real.exp Y * gapTail Y / (Y * gapEnergy) ≤ tₛ)
    (hsvar : 320 * π * gapEnergy * primeVariance (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ ≤
      3 * gapMass ^ 2 * (Y * gapEnergy * Real.log (tₛ + 3) / 4) ^ 2)
    (hL : 2 * Real.exp (2 * Y) ≤ 10 * ((m : ℝ) + 1) * σ)
    (hfar : ∀ t ∈ Icc c (c + 10 * ((m : ℝ) + 1) * σ), tₛ ≤ |t|)
    (hT : ∀ t ∈ Icc c (c + 10 * ((m : ℝ) + 1) * σ), |t| + Real.exp Y ≤ T) (hRH : RHVerifiedThrough T) :
    ∃ node : ℕ → zetaZeroConfig.carrier,
      (∀ j ∈ range (4 * m + 3 + 1),
        c ≤ ((node j : ℂ)).im ∧ ((node j : ℂ)).im ≤ c + 10 * ((m : ℝ) + 1) * σ) ∧
      ∀ i ∈ range (4 * m + 3 + 1), ∀ j ∈ range (4 * m + 3 + 1),
        σ * |(i : ℝ) - j| ≤ |((node i : ℂ)).im - ((node j : ℂ)).im| := by
  have hπ := Real.pi_pos
  have hm := gapMass_pos
  have hEn := gapEnergy_pos
  have hM : 2 * (((5 * (m + 1) : ℕ) : ℝ)) * σ = 10 * ((m : ℝ) + 1) * σ := by push_cast; ring
  have hMn : (((5 * (m + 1) : ℕ) : ℝ)) - ((4 * m + 3 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  set N := ⌊Real.exp (2 * Y)⌋₊ with hN
  set G : Set ℝ := {t | (primePolynomial (gapTestC Y) N (-t / (2 * π))).re ≤
    Y * gapEnergy * Real.log (|t| + 3) / 4} with hG
  have hs0 : 0 < tₛ := lt_of_lt_of_le (Real.exp_pos 30) hs30
  obtain ⟨A, hA⟩ : ∃ A, A = Y * gapEnergy * Real.log (tₛ + 3) / 4 := ⟨_, rfl⟩
  have hlog0 : 0 < Real.log (tₛ + 3) := Real.log_pos (by linarith only [hs0])
  have hA0 : 0 < A := by rw [hA]; positivity
  rw [← hA] at hsvar
  obtain ⟨node, hnode, hsep⟩ := exists_separated_zeros_of_volume_lt (c := c) hσ (M := 5 * (m + 1))
    (n := 4 * m + 3) (G := G) ?_ ?_
  · refine ⟨node, fun j hj => ?_, hsep⟩
    rw [← hM]
    exact hnode j hj
  · -- The bad heights.
    rw [hM, hMn]
    have hsub : Icc c (c + 10 * ((m : ℝ) + 1) * σ) \ G ⊆ Icc c (c + 10 * ((m : ℝ) + 1) * σ) ∩
        {t : ℝ | A ≤ ‖primePolynomial (gapTestC Y) N (-t / (2 * π))‖} := by
      rintro t ⟨ht, htG⟩
      refine ⟨ht, ?_⟩
      simp only [hG, Set.mem_setOf_eq, not_le] at htG
      simp only [Set.mem_setOf_eq]
      have h1 : Real.log (tₛ + 3) ≤ Real.log (|t| + 3) :=
        Real.log_le_log (by linarith only [hs0]) (by linarith only [hfar t ht])
      have h2 : A ≤ Y * gapEnergy * Real.log (|t| + 3) / 4 := by
        rw [hA]
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Y * gapEnergy)
        linarith only [this]
      exact h2.trans (htG.le.trans (Complex.re_le_norm _))
    refine (measure_mono hsub).trans_lt ((volume_bad_heights_le hY hL hA0 c).trans_lt ?_)
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hV : 8 * π * gapEnergy * primeVariance (gapTestC Y) N * (10 * ((m : ℝ) + 1) * σ) /
        (3 * gapMass ^ 2 * A ^ 2) ≤ ((m : ℝ) + 1) * σ / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left hsvar (by positivity : (0 : ℝ) ≤ ((m : ℝ) + 1) * σ / 4)
      have e1 : ((m : ℝ) + 1) * σ / 4 * (320 * π * gapEnergy * primeVariance (gapTestC Y) N) =
          8 * π * gapEnergy * primeVariance (gapTestC Y) N * (10 * ((m : ℝ) + 1) * σ) := by ring
      have e2 : ((m : ℝ) + 1) * σ / 4 * (3 * gapMass ^ 2 * A ^ 2) =
          ((m : ℝ) + 1) * σ / 4 * (3 * gapMass ^ 2 * A ^ 2) := rfl
      rw [e1] at h1
      exact h1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : ((m : ℝ) + 1) * σ / 4 < σ / 2 * ((m : ℝ) + 2) := by nlinarith only [hσ, hm0]
    linarith only [hV, this]
  · -- Good heights carry zeros.
    intro t ht htG
    rw [hM] at ht
    have hσ4 : 0 < σ / 4 := by positivity
    refine exists_zero_near_of_re_prime_le hσ4 (by linarith only [hσ1, hσ]) hY hY3
      (hs30.trans (hfar t ht)) (hstail.trans (hfar t ht)) ?_ htG
    intro ρ hρ hρt
    refine re_eq_half_of_mem_carrier hRH hρ ?_
    have h1 : |ρ.im| ≤ |ρ.im - t| + |t| := by
      have := abs_sub_abs_le_abs_sub ρ.im t
      linarith only [this]
    linarith only [h1, hρt, hT t ht]

end

end GaloisForLFunctions.VerifiedHeightRungs
