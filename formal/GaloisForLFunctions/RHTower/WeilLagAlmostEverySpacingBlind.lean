import GaloisForLFunctions.RHTower.WeilLagBandLimitedDichotomy

/-!
# Almost every spacing is blind to a non-attained top

The lag sum of a weighted configuration is `Φ(t) = Σ_i c_i e^{t(ρ_i − ½)}`; a lag progression samples
it at `t = mℓ`.

**Theorem** (`exists_lag_configuration_ae_spacing_bddAbove`). For every `Θ > 0` there is a countable
configuration `ρ_i` with positive summable weights `c_i` such that
* `½ < Re ρ_i < ½ + Θ`, and the supremum `½ + Θ` of the real parts is not attained;
* the ordinates are locally finite, and the configuration is invariant under conjugation;
* for Lebesgue-almost every spacing `ℓ > 0`, the samples `Re Φ(mℓ)`, `m ∈ ℕ`, are bounded above.

So a receiver reading single-base lag progressions along almost every spacing cannot see a
non-attained top from zero-side data. For the same configuration the good set of spacings is
meagre (`exists_lag_configuration_goodSpacings_ae_and_meagre`): it has full measure and is meagre,
so metric receivers are blind while the Baire receiver is not.

**Construction (Fejér blocks).** Block `b` consists of the points `½ + δ_b + i(j − k)ω_b`, `j ≠ k < K_b`,
each with weight `c_b/(2K_b)`, so that its lag sum is
`(c_b e^{δ_b t}/2)(F_b(t) − 1)` with `F_b(t) = K_b^{−1}|Σ_{k<K_b} e^{ikω_b t}|² ∈ [0, K_b]` and
`F_b(t) sin²(ω_b t/2) ≤ 1/K_b` (`sum_offDiag_cexp`, `norm_dirSum_mul_abs_sin_le`). Here
`δ_b = Θ(1 − 2^{−b−1})`, `K_b = 2^{8b+8}`, `c_{b+1} = c_b 2^{−10b−10}`, `ω_b = b + 1`.
* If `Φ(t) > 0` then some block has `a_b F_b > 2^{−b−1} Σ_i a_i`, `a_b = c_b e^{δ_b t}`. Either
  `t < τ_b = (19b + 19) 2^{b+2} log 2/Θ` (otherwise block `b + 1` dominates `K_b a_b`), and
  `|sin(ω_b t/2)| < ε_b = 2^{−3b−3}` (otherwise `F_b ≤ 2^{−2b−2}`) (`exists_block_of_pos`).
* The set `{0 ≤ t < τ : |sin(ωt/2)| < ε}` has measure at most `ετ + 4πε/ω` (Jordan's inequality),
  so `{t ≥ 0 : Φ(t) > 0}` has finite measure (`volume_posSet_lt_top`).
* For `ℓ ∈ [L, 2L]`, the event `(m+1)ℓ ∈ B` has measure `(m+1)^{−1}|B ∩ [(m+1)L, 2(m+1)L]|`; these
  sum to at most `3|B|`, and Borel–Cantelli gives, for almost every `ℓ`, only finitely many `m`
  with `Φ((m+1)ℓ) > 0`.
* **Category.** On `[τ_{b−1}, σ_b]` block `b` carries at least a third of the total amplitude
  (`tsum_amp_le_three`), and at a spike time `2πn/ω_b` in that window `F_b = K_b`, so
  `Φ ≥ a_b(K_b − 3)/2 → ∞` (`exists_lag_gt`). Since `Φ` is continuous, `{ℓ : ∀m, Φ(mℓ) ≤ M}` is
  closed; an interval inside it would bound `Φ` on a half-line, so it is nowhere dense
  (`isMeagre_goodSpacings`).
-/

open MeasureTheory Set Complex Filter Topology

noncomputable section

namespace RHTower.AlmostEverySpacing

/-! ## The Fejér pair sum -/

/-- `S_K(θ) = Σ_{k<K} e^{ikθ}`. -/
def dirSum (K : ℕ) (θ : ℝ) : ℂ := ∑ k ∈ Finset.range K, cexp (I * ((k : ℝ) * θ : ℝ))

/-- The ordered pairs `(j, k)` with `j ≠ k < K`. -/
def offDiag (K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range K ×ˢ Finset.range K).filter fun p => p.1 ≠ p.2

theorem cexp_pair (j k : ℕ) (θ : ℝ) :
    cexp (I * ((((j : ℝ) - k) * θ : ℝ))) =
      cexp (I * ((j : ℝ) * θ : ℝ)) * (starRingEnd ℂ) (cexp (I * ((k : ℝ) * θ : ℝ))) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **The off-diagonal pair sum.** `Σ_{j ≠ k} e^{i(j−k)θ} = |S_K(θ)|² − K`. -/
theorem sum_offDiag_cexp (K : ℕ) (θ : ℝ) :
    ∑ p ∈ offDiag K, cexp (I * ((((p.1 : ℝ) - p.2) * θ : ℝ))) =
      ((‖dirSum K θ‖ ^ 2 - K : ℝ) : ℂ) := by
  have hall : ∑ p ∈ Finset.range K ×ˢ Finset.range K, cexp (I * ((((p.1 : ℝ) - p.2) * θ : ℝ))) =
      ((‖dirSum K θ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_product]
    simp_rw [cexp_pair]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, dirSum, map_sum, Finset.sum_mul_sum]
  have hdiag : ∑ p ∈ (Finset.range K ×ˢ Finset.range K).filter (fun p => ¬ p.1 ≠ p.2),
      cexp (I * ((((p.1 : ℝ) - p.2) * θ : ℝ))) = (K : ℂ) := by
    rw [Finset.sum_filter, Finset.sum_product]
    have : ∀ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
        (if ¬ (j, k).1 ≠ (j, k).2 then cexp (I * ((((j, k).1 : ℝ) - (j, k).2) * θ : ℝ)) else 0) = 1 := by
      intro j hj
      simp only [ne_eq, not_not]
      rw [Finset.sum_ite_eq (Finset.range K) j, if_pos hj]
      simp
    rw [Finset.sum_congr rfl this]
    simp
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range K ×ˢ Finset.range K)
    (fun p : ℕ × ℕ => p.1 ≠ p.2) (fun p => cexp (I * ((((p.1 : ℝ) - p.2) * θ : ℝ))))
  rw [hall, hdiag] at h
  unfold offDiag
  rw [Complex.ofReal_sub, Complex.ofReal_natCast]
  linear_combination h

theorem norm_dirSum_le (K : ℕ) (θ : ℝ) : ‖dirSum K θ‖ ≤ K := by
  unfold dirSum
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ Finset.range K, ‖cexp (I * ((k : ℝ) * θ : ℝ))‖ = 1 := by
    intro k _
    rw [Complex.norm_exp]
    simp
  rw [Finset.sum_congr rfl this]
  simp

/-- **The geometric bound.** `|S_K(θ)| · |sin(θ/2)| ≤ 1`. -/
theorem norm_dirSum_mul_abs_sin_le (K : ℕ) (θ : ℝ) : ‖dirSum K θ‖ * |Real.sin (θ / 2)| ≤ 1 := by
  set x : ℂ := cexp (I * θ) with hx
  have hpow : ∀ k : ℕ, cexp (I * ((k : ℝ) * θ : ℝ)) = x ^ k := by
    intro k
    rw [hx, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hS : dirSum K θ = ∑ k ∈ Finset.range K, x ^ k := by
    unfold dirSum
    exact Finset.sum_congr rfl fun k _ => hpow k
  have hgeom := geom_sum_mul x K
  rw [← hS] at hgeom
  have hxnorm : ‖x‖ = 1 := by rw [hx, Complex.norm_exp]; simp
  have hnum : ‖x ^ K - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hxnorm, one_pow, norm_one]
    norm_num
  have hden : ‖x - 1‖ = 2 * |Real.sin (θ / 2)| := by
    rw [hx, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    norm_num
  have h := congrArg norm hgeom
  rw [norm_mul, hden] at h
  nlinarith [norm_nonneg (dirSum K θ), abs_nonneg (Real.sin (θ / 2))]

/-! ## Thin windows -/

/-- Jordan's inequality: `|y| ≤ (π/2)|sin y|` for `|y| ≤ π/2`. -/
theorem abs_le_pi_div_two_mul_abs_sin {y : ℝ} (hy : |y| ≤ Real.pi / 2) :
    |y| ≤ Real.pi / 2 * |Real.sin y| := by
  have hπ := Real.pi_pos
  rcases le_total 0 y with h0 | h0
  · have h := Real.mul_le_sin h0 (by rw [abs_of_nonneg h0] at hy; exact hy)
    have hp : 0 ≤ 2 / Real.pi * y := by positivity
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    have : 2 / Real.pi * y * (Real.pi / 2) = y := by field_simp
    nlinarith
  · have hy' : 0 ≤ -y := by linarith
    have h := Real.mul_le_sin hy' (by rw [abs_of_nonpos h0] at hy; exact hy)
    rw [Real.sin_neg] at h
    have hp : 0 ≤ 2 / Real.pi * -y := by positivity
    rw [abs_of_nonpos h0, abs_of_nonpos (by linarith)]
    have : 2 / Real.pi * -y * (Real.pi / 2) = -y := by field_simp
    nlinarith

/-- A point where `|sin(ωt/2)|` is small lies near a lattice point `2πn/ω`. -/
theorem exists_near_of_abs_sin_lt {ω t ε : ℝ} (hω : 0 < ω) (ht : 0 ≤ t)
    (h : |Real.sin (ω * t / 2)| < ε) :
    ∃ n : ℕ, (n : ℝ) ≤ ω * t / (2 * Real.pi) + 1 / 2 ∧
      |t - 2 * Real.pi * n / ω| < Real.pi * ε / ω := by
  have hπ := Real.pi_pos
  set x := ω * t / 2 with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  set z : ℤ := round (x / Real.pi) with hz
  have hz0 : 0 ≤ z := by
    rw [hz]
    have := abs_sub_round (x / Real.pi)
    have hxπ : 0 ≤ x / Real.pi := div_nonneg hx0 hπ.le
    by_contra hneg
    push Not at hneg
    have : (round (x / Real.pi) : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
    rw [abs_le] at *
    linarith [this]
  set y := x - z * Real.pi with hy
  have hyb : |y| ≤ Real.pi / 2 := by
    have h1 := abs_sub_round (x / Real.pi)
    rw [← hz] at h1
    have : y = Real.pi * (x / Real.pi - z) := by rw [hy]; field_simp
    rw [this, abs_mul, abs_of_pos hπ]
    nlinarith
  have hsin : |Real.sin x| = |Real.sin y| := by
    have : x = y + z * Real.pi := by rw [hy]; ring
    rw [this, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have hJ := abs_le_pi_div_two_mul_abs_sin hyb
  rw [← hsin] at hJ
  refine ⟨z.toNat, ?_, ?_⟩
  · have hzn : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz0
    rw [hzn]
    have h1 := abs_sub_round (x / Real.pi)
    rw [← hz, abs_le] at h1
    have : x / Real.pi = ω * t / (2 * Real.pi) := by rw [hxdef]; field_simp
    linarith [h1.1]
  · have hzn : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz0
    rw [hzn]
    have hyt : t - 2 * Real.pi * z / ω = 2 / ω * y := by
      rw [hy, hxdef]; field_simp
    rw [hyt, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ω)]
    have : |y| < Real.pi / 2 * ε := by
      calc |y| ≤ Real.pi / 2 * |Real.sin x| := hJ
        _ < Real.pi / 2 * ε := by
          rw [hxdef]; exact mul_lt_mul_of_pos_left h (by positivity)
    calc 2 / ω * |y| < 2 / ω * (Real.pi / 2 * ε) := mul_lt_mul_of_pos_left this (by positivity)
      _ = Real.pi * ε / ω := by field_simp

/-- **Measure of a thin window.** `|{0 ≤ t < τ : |sin(ωt/2)| < ε}| ≤ ετ + 4πε/ω`. -/
theorem volume_thinWindow_le {ω ε τ : ℝ} (hω : 0 < ω) (hε : 0 ≤ ε) (hτ : 0 ≤ τ) :
    volume {t : ℝ | 0 ≤ t ∧ t < τ ∧ |Real.sin (ω * t / 2)| < ε} ≤
      ENNReal.ofReal (ε * τ + 4 * Real.pi * ε / ω) := by
  have hπ := Real.pi_pos
  set N : ℕ := ⌊ω * τ / (2 * Real.pi) + 1 / 2⌋₊ with hN
  set r := Real.pi * ε / ω with hr
  have hsub : {t : ℝ | 0 ≤ t ∧ t < τ ∧ |Real.sin (ω * t / 2)| < ε} ⊆
      ⋃ n ∈ Finset.range (N + 1), Icc (2 * Real.pi * n / ω - r) (2 * Real.pi * n / ω + r) := by
    rintro t ⟨ht0, htτ, hts⟩
    obtain ⟨n, hn, hnt⟩ := exists_near_of_abs_sin_lt hω ht0 hts
    refine mem_iUnion₂.mpr ⟨n, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff, hN]
      refine Nat.le_floor ?_
      have : ω * t / (2 * Real.pi) ≤ ω * τ / (2 * Real.pi) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left htτ.le hω.le
      linarith
    · rw [abs_lt] at hnt
      exact ⟨by linarith [hnt.1], by linarith [hnt.2]⟩
  calc volume {t : ℝ | 0 ≤ t ∧ t < τ ∧ |Real.sin (ω * t / 2)| < ε}
      ≤ volume (⋃ n ∈ Finset.range (N + 1), Icc (2 * Real.pi * n / ω - r) (2 * Real.pi * n / ω + r)) :=
        measure_mono hsub
    _ ≤ ∑ n ∈ Finset.range (N + 1), volume (Icc (2 * Real.pi * n / ω - r) (2 * Real.pi * n / ω + r)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (2 * r) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Real.volume_Icc]; congr 1; ring
    _ = ENNReal.ofReal ((N + 1 : ℝ) * (2 * r)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        push_cast
        ring_nf
    _ ≤ ENNReal.ofReal (ε * τ + 4 * Real.pi * ε / ω) := by
        apply ENNReal.ofReal_le_ofReal
        have hNle : (N : ℝ) ≤ ω * τ / (2 * Real.pi) + 1 / 2 := Nat.floor_le (by positivity)
        have hr0 : 0 ≤ r := by rw [hr]; positivity
        calc (N + 1 : ℝ) * (2 * r) ≤ (ω * τ / (2 * Real.pi) + 3 / 2) * (2 * r) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
          _ = ε * τ + 3 * Real.pi * ε / ω := by rw [hr]; field_simp
          _ ≤ ε * τ + 4 * Real.pi * ε / ω := by
              have : 0 ≤ Real.pi * ε / ω := by positivity
              have h3 : 3 * Real.pi * ε / ω ≤ 4 * Real.pi * ε / ω :=
                div_le_div_of_nonneg_right (by nlinarith) hω.le
              linarith

/-! ## Block parameters -/

/-- Block sizes `K_b = 2^{8b+8}`. -/
def bK (b : ℕ) : ℕ := 2 ^ (8 * b + 8)

/-- Block masses `c_b = 2^{−5b(b+1)}`, so that `c_{b+1} = c_b 2^{−10b−10}`. -/
def bc (b : ℕ) : ℝ := (1 / 2 : ℝ) ^ (5 * b * b + 5 * b)

/-- Block depths `δ_b = Θ(1 − 2^{−b−1})`. -/
def bδ (Θ : ℝ) (b : ℕ) : ℝ := Θ * (1 - (1 / 2 : ℝ) ^ (b + 1))

/-- Block frequencies `ω_b = b + 1`. -/
def bω (b : ℕ) : ℝ := b + 1

/-- Activity horizons `τ_b = (19b + 19) 2^{b+2} log 2 / Θ`. -/
def bτ (Θ : ℝ) (b : ℕ) : ℝ := (19 * b + 19) * Real.log 2 * 2 ^ (b + 2) / Θ

/-- Window widths `ε_b = 2^{−3b−3}`. -/
def bε (b : ℕ) : ℝ := (1 / 2 : ℝ) ^ (3 * b + 3)

theorem bK_pos (b : ℕ) : (0 : ℝ) < bK b := by unfold bK; positivity

theorem bc_pos (b : ℕ) : 0 < bc b := by unfold bc; positivity

theorem bω_pos (b : ℕ) : 0 < bω b := by unfold bω; positivity

theorem bε_pos (b : ℕ) : 0 < bε b := by unfold bε; positivity

theorem bc_succ (b : ℕ) : bc (b + 1) = bc b * (1 / 2 : ℝ) ^ (10 * b + 10) := by
  unfold bc
  rw [← pow_add]
  congr 1
  ring

/-- `c_b K_b ≤ 2^8 · 2^{−b}`. -/
theorem bc_mul_bK_le (b : ℕ) : bc b * bK b ≤ 2 ^ 8 * (1 / 2 : ℝ) ^ b := by
  unfold bc bK
  push_cast
  rw [one_div_pow, one_div_pow, div_mul_eq_mul_div, one_mul, mul_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  rw [← pow_add, ← pow_add]
  have h := Nat.le_mul_self b
  exact pow_le_pow_right₀ (by norm_num) (by nlinarith [h])

theorem bδ_lt (Θ : ℝ) (hΘ : 0 < Θ) (b : ℕ) : bδ Θ b < Θ := by
  unfold bδ
  have : 0 < (1 / 2 : ℝ) ^ (b + 1) := by positivity
  nlinarith

theorem half_lt_bδ (Θ : ℝ) (hΘ : 0 < Θ) (b : ℕ) : Θ / 2 ≤ bδ Θ b := by
  unfold bδ
  have : (1 / 2 : ℝ) ^ (b + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (b + 1) ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  nlinarith

theorem bδ_succ_sub (Θ : ℝ) (b : ℕ) : bδ Θ (b + 1) - bδ Θ b = Θ * (1 / 2 : ℝ) ^ (b + 2) := by
  unfold bδ
  have h1 : (1 / 2 : ℝ) ^ (b + 1 + 1) = (1 / 2) ^ (b + 1) * (1 / 2) := pow_succ _ _
  rw [h1]
  ring

/-! ## The lag function of the blocks -/

/-- `a_b(t) = c_b e^{δ_b t}`. -/
def amp (Θ : ℝ) (b : ℕ) (t : ℝ) : ℝ := bc b * Real.exp (bδ Θ b * t)

/-- `F_b(t) = |S_{K_b}(ω_b t)|² / K_b`. -/
def fej (b : ℕ) (t : ℝ) : ℝ := ‖dirSum (bK b) (bω b * t)‖ ^ 2 / bK b

/-- The lag value of block `b`: `(a_b/2)(F_b − 1)`. -/
def blockVal (Θ : ℝ) (b : ℕ) (t : ℝ) : ℝ := amp Θ b t / 2 * (fej b t - 1)

/-- The lag function `Φ(t) = Σ_b (a_b(t)/2)(F_b(t) − 1)`. -/
def lag (Θ : ℝ) (t : ℝ) : ℝ := ∑' b, blockVal Θ b t

theorem amp_pos (Θ : ℝ) (b : ℕ) (t : ℝ) : 0 < amp Θ b t := by
  unfold amp; exact mul_pos (bc_pos b) (Real.exp_pos _)

theorem fej_nonneg (b : ℕ) (t : ℝ) : 0 ≤ fej b t := by
  unfold fej; exact div_nonneg (sq_nonneg _) (bK_pos b).le

theorem fej_le (b : ℕ) (t : ℝ) : fej b t ≤ bK b := by
  unfold fej
  rw [div_le_iff₀ (bK_pos b)]
  have h := norm_dirSum_le (bK b) (bω b * t)
  nlinarith [norm_nonneg (dirSum (bK b) (bω b * t))]

theorem amp_le (Θ : ℝ) (hΘ : 0 < Θ) (b : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    amp Θ b t ≤ bc b * Real.exp (Θ * t) := by
  unfold amp
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (bc_pos b).le
  exact mul_le_mul_of_nonneg_right (bδ_lt Θ hΘ b).le ht

theorem summable_bc_mul_bK : Summable fun b => bc b * bK b :=
  Summable.of_nonneg_of_le (fun b => (mul_pos (bc_pos b) (bK_pos b)).le) bc_mul_bK_le
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)

theorem summable_amp (Θ : ℝ) (hΘ : 0 < Θ) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun b => amp Θ b t := by
  refine Summable.of_nonneg_of_le (fun b => (amp_pos Θ b t).le) (fun b => (amp_le Θ hΘ b ht).trans ?_)
    (summable_bc_mul_bK.mul_right (Real.exp (Θ * t)))
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (bc_pos b).le
    (by unfold bK; exact_mod_cast Nat.one_le_two_pow)) (Real.exp_pos _).le

theorem summable_amp_mul_fej (Θ : ℝ) (hΘ : 0 < Θ) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun b => amp Θ b t * fej b t := by
  refine Summable.of_nonneg_of_le (fun b => mul_nonneg (amp_pos Θ b t).le (fej_nonneg b t))
    (fun b => ?_) (summable_bc_mul_bK.mul_right (Real.exp (Θ * t)))
  calc amp Θ b t * fej b t ≤ (bc b * Real.exp (Θ * t)) * bK b :=
        mul_le_mul (amp_le Θ hΘ b ht) (fej_le b t) (fej_nonneg b t)
          (mul_pos (bc_pos b) (Real.exp_pos _)).le
    _ = bc b * bK b * Real.exp (Θ * t) := by ring

theorem lag_eq (Θ : ℝ) (hΘ : 0 < Θ) {t : ℝ} (ht : 0 ≤ t) :
    lag Θ t = ((∑' b, amp Θ b t * fej b t) - ∑' b, amp Θ b t) / 2 := by
  unfold lag blockVal
  have h1 := summable_amp_mul_fej Θ hΘ ht
  have h2 := summable_amp Θ hΘ ht
  have : (fun b => amp Θ b t / 2 * (fej b t - 1)) =
      fun b => (amp Θ b t * fej b t - amp Θ b t) / 2 := by
    funext b; ring
  rw [this, tsum_div_const, h1.tsum_sub h2]

/-- After the horizon, block `b + 1` dominates `2^{b+1} K_b a_b`. -/
theorem amp_succ_ge (Θ : ℝ) (hΘ : 0 < Θ) (b : ℕ) {t : ℝ} (ht : bτ Θ b ≤ t) :
    2 ^ (b + 1) * bK b * amp Θ b t ≤ amp Θ (b + 1) t := by
  have hpos : (0 : ℝ) < (1 / 2) ^ (b + 2) := by positivity
  have h2 : (2 : ℝ) ^ (b + 2) * (1 / 2) ^ (b + 2) = 1 := by
    rw [← mul_pow]; norm_num
  have hlog : (19 * b + 19 : ℝ) * Real.log 2 ≤ Θ * (1 / 2 : ℝ) ^ (b + 2) * t := by
    unfold bτ at ht
    rw [div_le_iff₀ hΘ] at ht
    have hm := mul_le_mul_of_nonneg_right ht hpos.le
    calc (19 * b + 19 : ℝ) * Real.log 2
        = (19 * b + 19) * Real.log 2 * 2 ^ (b + 2) * (1 / 2) ^ (b + 2) := by
          rw [mul_assoc _ ((2 : ℝ) ^ (b + 2)), h2, mul_one]
      _ ≤ t * Θ * (1 / 2) ^ (b + 2) := hm
      _ = Θ * (1 / 2 : ℝ) ^ (b + 2) * t := by ring
  have hexp : (2 : ℝ) ^ (19 * b + 19) ≤ Real.exp ((bδ Θ (b + 1) - bδ Θ b) * t) := by
    rw [bδ_succ_sub, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (19 * b + 19)),
      Real.log_pow]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have hK : (2 : ℝ) ^ (b + 1) * bK b = (1 / 2 : ℝ) ^ (10 * b + 10) * 2 ^ (19 * b + 19) := by
    unfold bK
    push_cast
    rw [one_div_pow]
    field_simp
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hsplit : Real.exp (bδ Θ (b + 1) * t) =
      Real.exp (bδ Θ b * t) * Real.exp ((bδ Θ (b + 1) - bδ Θ b) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold amp
  rw [bc_succ, hsplit]
  have hA : 0 ≤ bc b * Real.exp (bδ Θ b * t) * (1 / 2 : ℝ) ^ (10 * b + 10) := by
    have := bc_pos b; positivity
  calc 2 ^ (b + 1) * (bK b : ℝ) * (bc b * Real.exp (bδ Θ b * t))
      = bc b * Real.exp (bδ Θ b * t) * (1 / 2 : ℝ) ^ (10 * b + 10) * 2 ^ (19 * b + 19) := by
        rw [hK]; ring
    _ ≤ bc b * Real.exp (bδ Θ b * t) * (1 / 2 : ℝ) ^ (10 * b + 10) *
          Real.exp ((bδ Θ (b + 1) - bδ Θ b) * t) := mul_le_mul_of_nonneg_left hexp hA
    _ = bc b * (1 / 2 : ℝ) ^ (10 * b + 10) *
          (Real.exp (bδ Θ b * t) * Real.exp ((bδ Θ (b + 1) - bδ Θ b) * t)) := by ring

/-- Off its thin window a block is small: `F_b ≤ 2^{−b−1}` when `|sin(ω_b t/2)| ≥ ε_b`. -/
theorem fej_le_of_abs_sin_ge (b : ℕ) {t : ℝ} (h : bε b ≤ |Real.sin (bω b * t / 2)|) :
    fej b t ≤ (1 / 2 : ℝ) ^ (b + 1) := by
  have hg := norm_dirSum_mul_abs_sin_le (bK b) (bω b * t)
  have hε := bε_pos b
  have hS0 := norm_nonneg (dirSum (bK b) (bω b * t))
  have hS : ‖dirSum (bK b) (bω b * t)‖ ≤ 1 / bε b := by
    rw [le_div_iff₀ hε]
    calc ‖dirSum (bK b) (bω b * t)‖ * bε b ≤ ‖dirSum (bK b) (bω b * t)‖ * |Real.sin (bω b * t / 2)| :=
          mul_le_mul_of_nonneg_left h hS0
      _ ≤ 1 := hg
  unfold fej
  rw [div_le_iff₀ (bK_pos b)]
  have hinv : (1 / bε b) ^ 2 = (2 : ℝ) ^ (6 * b + 6) := by
    unfold bε
    rw [div_pow, one_pow, ← pow_mul, one_div_pow, one_div_one_div]
    congr 1
    ring
  calc ‖dirSum (bK b) (bω b * t)‖ ^ 2 ≤ (1 / bε b) ^ 2 := pow_le_pow_left₀ hS0 hS 2
    _ = (2 : ℝ) ^ (6 * b + 6) := hinv
    _ ≤ (2 : ℝ) ^ (7 * b + 7) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = (1 / 2 : ℝ) ^ (b + 1) * bK b := by
        unfold bK
        push_cast
        rw [one_div_pow]
        field_simp
        rw [← pow_add]
        congr 1
        ring

/-- **Where the lag function is positive.** If `Φ(t) > 0` for `t ≥ 0`, then `t` lies in the thin
window of a block before its horizon. -/
theorem exists_block_of_pos (Θ : ℝ) (hΘ : 0 < Θ) {t : ℝ} (ht : 0 ≤ t) (hpos : 0 < lag Θ t) :
    ∃ b, t < bτ Θ b ∧ |Real.sin (bω b * t / 2)| < bε b := by
  by_contra hno
  push Not at hno
  have hA := summable_amp Θ hΘ ht
  set A := ∑' b, amp Θ b t with hAdef
  have hle : ∀ b, amp Θ b t ≤ A := fun b =>
    hA.le_tsum b fun j _ => (amp_pos Θ j t).le
  have hbound : ∀ b, amp Θ b t * fej b t ≤ (1 / 2 : ℝ) ^ (b + 1) * A := by
    intro b
    have hab := (amp_pos Θ b t).le
    by_cases hτ : t < bτ Θ b
    · have hf := fej_le_of_abs_sin_ge b (hno b hτ)
      calc amp Θ b t * fej b t ≤ amp Θ b t * (1 / 2 : ℝ) ^ (b + 1) :=
            mul_le_mul_of_nonneg_left hf hab
        _ ≤ A * (1 / 2 : ℝ) ^ (b + 1) := mul_le_mul_of_nonneg_right (hle b) (by positivity)
        _ = (1 / 2 : ℝ) ^ (b + 1) * A := by ring
    · push Not at hτ
      have hd := amp_succ_ge Θ hΘ b hτ
      have h2 : (2 : ℝ) ^ (b + 1) * (1 / 2) ^ (b + 1) = 1 := by rw [← mul_pow]; norm_num
      calc amp Θ b t * fej b t ≤ amp Θ b t * bK b := mul_le_mul_of_nonneg_left (fej_le b t) hab
        _ = (1 / 2 : ℝ) ^ (b + 1) * (2 ^ (b + 1) * bK b * amp Θ b t) := by
            rw [← mul_assoc, ← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ (b + 1)), h2]; ring
        _ ≤ (1 / 2 : ℝ) ^ (b + 1) * amp Θ (b + 1) t := mul_le_mul_of_nonneg_left hd (by positivity)
        _ ≤ (1 / 2 : ℝ) ^ (b + 1) * A := mul_le_mul_of_nonneg_left (hle (b + 1)) (by positivity)
  have hgeom : Summable fun b : ℕ => (1 / 2 : ℝ) ^ (b + 1) * A :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)).mul_right A
  have hsum : ∑' b, amp Θ b t * fej b t ≤ A := by
    calc ∑' b, amp Θ b t * fej b t ≤ ∑' b : ℕ, (1 / 2 : ℝ) ^ (b + 1) * A :=
          (summable_amp_mul_fej Θ hΘ ht).tsum_le_tsum hbound hgeom
      _ = A := by
          rw [tsum_mul_right]
          have : ∑' b : ℕ, (1 / 2 : ℝ) ^ (b + 1) = 1 := by
            simp_rw [pow_succ]
            rw [tsum_mul_right, tsum_geometric_two]
            norm_num
          rw [this, one_mul]
  rw [lag_eq Θ hΘ ht] at hpos
  linarith

/-! ## The set where the lag function is positive has finite measure -/

/-- The set `B = {t ≥ 0 : Φ(t) > 0}`. -/
def posSet (Θ : ℝ) : Set ℝ := {t | 0 ≤ t ∧ 0 < lag Θ t}

/-- The thin window of block `b`. -/
def window (Θ : ℝ) (b : ℕ) : Set ℝ :=
  {t | 0 ≤ t ∧ t < bτ Θ b ∧ |Real.sin (bω b * t / 2)| < bε b}

theorem posSet_subset (Θ : ℝ) (hΘ : 0 < Θ) : posSet Θ ⊆ ⋃ b, window Θ b := by
  rintro t ⟨ht0, htp⟩
  obtain ⟨b, hb1, hb2⟩ := exists_block_of_pos Θ hΘ ht0 htp
  exact mem_iUnion.mpr ⟨b, ht0, hb1, hb2⟩

theorem bτ_nonneg (Θ : ℝ) (hΘ : 0 < Θ) (b : ℕ) : 0 ≤ bτ Θ b := by
  unfold bτ
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

theorem windowBound_le (Θ : ℝ) (hΘ : 0 < Θ) (b : ℕ) :
    bε b * bτ Θ b + 4 * Real.pi * bε b / bω b ≤
      19 * Real.log 2 / Θ * (((b : ℝ) + 1) * (1 / 2 : ℝ) ^ b) + 4 * Real.pi * (1 / 2 : ℝ) ^ b := by
  have hπ := Real.pi_pos
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h1 : bε b * bτ Θ b ≤ 19 * Real.log 2 / Θ * (((b : ℝ) + 1) * (1 / 2 : ℝ) ^ b) := by
    unfold bε bτ
    have hk : (1 / 2 : ℝ) ^ (3 * b + 3) * 2 ^ (b + 2) ≤ (1 / 2 : ℝ) ^ b := by
      rw [one_div_pow, one_div_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity)
        (by positivity), one_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have : (1 / 2 : ℝ) ^ (3 * b + 3) * ((19 * b + 19) * Real.log 2 * 2 ^ (b + 2) / Θ) =
        19 * Real.log 2 / Θ * (((b : ℝ) + 1) * ((1 / 2 : ℝ) ^ (3 * b + 3) * 2 ^ (b + 2))) := by
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  have h2 : 4 * Real.pi * bε b / bω b ≤ 4 * Real.pi * (1 / 2 : ℝ) ^ b := by
    rw [div_le_iff₀ (bω_pos b)]
    have hω1 : (1 : ℝ) ≤ bω b := by unfold bω; have := Nat.cast_nonneg (α := ℝ) b; linarith
    have hε : bε b ≤ (1 / 2 : ℝ) ^ b := by
      unfold bε; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have : 0 ≤ (1 / 2 : ℝ) ^ b := by positivity
    calc 4 * Real.pi * bε b ≤ 4 * Real.pi * (1 / 2 : ℝ) ^ b :=
          mul_le_mul_of_nonneg_left hε (by positivity)
      _ ≤ 4 * Real.pi * (1 / 2 : ℝ) ^ b * bω b := le_mul_of_one_le_right (by positivity) hω1
  linarith

theorem summable_windowBound (Θ : ℝ) (hΘ : 0 < Θ) :
    Summable fun b => bε b * bτ Θ b + 4 * Real.pi * bε b / bω b := by
  have hg : Summable fun b : ℕ => (1 / 2 : ℝ) ^ b :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hn : Summable fun b : ℕ => (b : ℝ) ^ 1 * (1 / 2 : ℝ) ^ b :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have hmaj : Summable fun b : ℕ => 19 * Real.log 2 / Θ * (((b : ℝ) + 1) * (1 / 2 : ℝ) ^ b) +
      4 * Real.pi * (1 / 2 : ℝ) ^ b := by
    refine Summable.add (Summable.mul_left _ ?_) (hg.mul_left _)
    simp only [pow_one] at hn
    exact (hn.add hg).congr fun b => by ring
  refine Summable.of_nonneg_of_le (fun b => ?_) (windowBound_le Θ hΘ) hmaj
  have := bε_pos b; have := bω_pos b; have := bτ_nonneg Θ hΘ b; have := Real.pi_pos
  positivity

/-- **The positivity set has finite measure.** -/
theorem volume_posSet_lt_top (Θ : ℝ) (hΘ : 0 < Θ) : volume (posSet Θ) < ⊤ := by
  have hs := summable_windowBound Θ hΘ
  calc volume (posSet Θ) ≤ volume (⋃ b, window Θ b) := measure_mono (posSet_subset Θ hΘ)
    _ ≤ ∑' b, volume (window Θ b) := measure_iUnion_le _
    _ ≤ ∑' b, ENNReal.ofReal (bε b * bτ Θ b + 4 * Real.pi * bε b / bω b) :=
        ENNReal.tsum_le_tsum fun b =>
          volume_thinWindow_le (bω_pos b) (bε_pos b).le (bτ_nonneg Θ hΘ b)
    _ = ENNReal.ofReal (∑' b, (bε b * bτ Θ b + 4 * Real.pi * bε b / bω b)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun b => by
          have := bε_pos b; have := bω_pos b; have := bτ_nonneg Θ hΘ b; have := Real.pi_pos
          positivity) hs]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ## Borel–Cantelli in the spacing -/

/-- At most `s/(2L) + 1` integers `n ≥ 1` satisfy `nL ≤ s ≤ 2nL`, and each has `1/n ≤ 2L/s`, so
`Σ_n n^{−1} [nL ≤ s ≤ 2nL] ≤ 3`. -/
theorem sum_range_inv_le_three {L s : ℝ} (hL : 0 < L) (n : ℕ) :
    ∑ m ∈ Finset.range n, (if ((m : ℝ) + 1) * L ≤ s ∧ s ≤ 2 * (((m : ℝ) + 1) * L)
      then 1 / ((m : ℝ) + 1) else 0) ≤ 3 := by
  rw [← Finset.sum_filter]
  set T := (Finset.range n).filter
    (fun m : ℕ => ((m : ℝ) + 1) * L ≤ s ∧ s ≤ 2 * (((m : ℝ) + 1) * L)) with hT
  rcases T.eq_empty_or_nonempty with hE | ⟨m₀, hm₀⟩
  · rw [hE, Finset.sum_empty]; norm_num
  have hm₀' := (Finset.mem_filter.mp hm₀).2
  have hsL : L ≤ s := by
    have : (1 : ℝ) ≤ (m₀ : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) m₀; linarith
    nlinarith [hm₀'.1]
  have hs : 0 < s := lt_of_lt_of_le hL hsL
  have hterm : ∀ m ∈ T, 1 / ((m : ℝ) + 1) ≤ 2 * L / s := by
    intro m hm
    have h := (Finset.mem_filter.mp hm).2
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ hm1 hs]
    nlinarith [h.2]
  have hcard : (T.card : ℝ) ≤ s / (2 * L) + 1 := by
    have hsub : T ⊆ Finset.Icc ⌈s / (2 * L) - 1⌉₊ ⌊s / L - 1⌋₊ := by
      intro m hm
      have h := (Finset.mem_filter.mp hm).2
      rw [Finset.mem_Icc]
      constructor
      · refine Nat.ceil_le.mpr ?_
        rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
        nlinarith [h.2]
      · refine Nat.le_floor ?_
        rw [le_sub_iff_add_le, le_div_iff₀ hL]
        exact h.1
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hfl : (⌊s / L - 1⌋₊ : ℝ) ≤ s / L - 1 :=
      Nat.floor_le (by rw [sub_nonneg, le_div_iff₀ hL]; linarith)
    have hce : s / (2 * L) - 1 ≤ (⌈s / (2 * L) - 1⌉₊ : ℝ) := Nat.le_ceil _
    have hne : ⌈s / (2 * L) - 1⌉₊ ≤ ⌊s / L - 1⌋₊ + 1 := by
      have := Finset.card_pos.mpr ⟨m₀, hm₀⟩
      omega
    calc (T.card : ℝ) ≤ ((⌊s / L - 1⌋₊ + 1 - ⌈s / (2 * L) - 1⌉₊ : ℕ) : ℝ) := by exact_mod_cast hc
      _ = (⌊s / L - 1⌋₊ : ℝ) + 1 - ⌈s / (2 * L) - 1⌉₊ := by
          rw [Nat.cast_sub hne]; push_cast; ring
      _ ≤ (s / L - 1) + 1 - (s / (2 * L) - 1) := by linarith
      _ = s / (2 * L) + 1 := by field_simp; ring
  calc ∑ m ∈ T, 1 / ((m : ℝ) + 1) ≤ ∑ _m ∈ T, 2 * L / s := Finset.sum_le_sum hterm
    _ = (T.card : ℝ) * (2 * L / s) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (s / (2 * L) + 1) * (2 * L / s) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 + 2 * L / s := by field_simp
    _ ≤ 3 := by
        have : 2 * L / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith
        linarith

/-- The dyadic interval `[nL, 2nL]` of the `n`-th multiple. -/
def multInterval (L : ℝ) (m : ℕ) : Set ℝ := Icc (((m : ℝ) + 1) * L) (2 * (((m : ℝ) + 1) * L))

theorem measurableSet_multInterval (L : ℝ) (m : ℕ) : MeasurableSet (multInterval L m) :=
  measurableSet_Icc

theorem tsum_indicator_le_three {L : ℝ} (hL : 0 < L) (s : ℝ) :
    ∑' m : ℕ, (multInterval L m).indicator (fun _ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) s ≤ 3 := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  have h : ∀ m ∈ Finset.range n,
      (multInterval L m).indicator (fun _ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) s =
        ENNReal.ofReal (if ((m : ℝ) + 1) * L ≤ s ∧ s ≤ 2 * (((m : ℝ) + 1) * L)
          then 1 / ((m : ℝ) + 1) else 0) := by
    intro m _
    unfold multInterval
    by_cases hs : ((m : ℝ) + 1) * L ≤ s ∧ s ≤ 2 * (((m : ℝ) + 1) * L)
    · rw [indicator_of_mem (show s ∈ Icc _ _ from hs), if_pos hs]
    · rw [indicator_of_notMem (show s ∉ Icc _ _ from hs), if_neg hs, ENNReal.ofReal_zero]
  rw [Finset.sum_congr rfl h, ← ENNReal.ofReal_sum_of_nonneg (fun m _ => by
    split_ifs <;> positivity)]
  calc ENNReal.ofReal (∑ m ∈ Finset.range n, (if ((m : ℝ) + 1) * L ≤ s ∧ s ≤ 2 * (((m : ℝ) + 1) * L)
        then 1 / ((m : ℝ) + 1) else 0)) ≤ ENNReal.ofReal 3 :=
        ENNReal.ofReal_le_ofReal (sum_range_inv_le_three hL n)
    _ = 3 := by norm_num

/-- **Borel–Cantelli.** If `B` has finite measure, then for almost every `ℓ ∈ [L, 2L]` only finitely
many multiples `(m + 1)ℓ` lie in `B`. -/
theorem ae_eventually_mult_notMem {B : Set ℝ} (hB : volume B < ⊤) {L : ℝ} (hL : 0 < L) :
    ∀ᵐ ℓ ∂(volume.restrict (Icc L (2 * L))), ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 1) * ℓ ∉ B := by
  set B' := toMeasurable volume B with hB'
  have hB'm : MeasurableSet B' := measurableSet_toMeasurable _ _
  have hB'v : volume B' = volume B := measure_toMeasurable B
  have hstep : ∀ m : ℕ, (volume.restrict (Icc L (2 * L))) {ℓ | ((m : ℝ) + 1) * ℓ ∈ B} ≤
      ∫⁻ s in B', (multInterval L m).indicator (fun _ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) s := by
    intro m
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [Measure.restrict_apply' measurableSet_Icc]
    have hsub : {ℓ | ((m : ℝ) + 1) * ℓ ∈ B} ∩ Icc L (2 * L) ⊆
        (fun ℓ => ((m : ℝ) + 1) * ℓ) ⁻¹' (B' ∩ multInterval L m) := by
      rintro ℓ ⟨hℓB, hℓ1, hℓ2⟩
      refine ⟨subset_toMeasurable _ _ hℓB, ?_, ?_⟩
      · show ((m : ℝ) + 1) * L ≤ ((m : ℝ) + 1) * ℓ
        exact mul_le_mul_of_nonneg_left hℓ1 hm0.le
      · show ((m : ℝ) + 1) * ℓ ≤ 2 * (((m : ℝ) + 1) * L)
        nlinarith
    calc volume ({ℓ | ((m : ℝ) + 1) * ℓ ∈ B} ∩ Icc L (2 * L))
        ≤ volume ((fun ℓ => ((m : ℝ) + 1) * ℓ) ⁻¹' (B' ∩ multInterval L m)) := measure_mono hsub
      _ = ENNReal.ofReal |((m : ℝ) + 1)⁻¹| * volume (B' ∩ multInterval L m) :=
          Real.volume_preimage_mul_left hm _
      _ = ∫⁻ s in B', (multInterval L m).indicator (fun _ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) s := by
          rw [lintegral_indicator_const (measurableSet_multInterval L m),
            Measure.restrict_apply (measurableSet_multInterval L m),
            abs_of_pos (inv_pos.mpr hm0), one_div, Set.inter_comm]
  have hsum : ∑' m : ℕ, (volume.restrict (Icc L (2 * L))) {ℓ | ((m : ℝ) + 1) * ℓ ∈ B} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hstep)
    rw [← lintegral_tsum fun m =>
      (Measurable.indicator measurable_const (measurableSet_multInterval L m)).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' hB'm fun s _ => tsum_indicator_le_three hL s)
    rw [setLIntegral_const, hB'v]
    exact ENNReal.mul_ne_top (by norm_num) hB.ne
  have h0 := measure_setOf_frequently_eq_zero hsum
  rw [ae_iff]
  refine measure_mono_null (fun ℓ hℓ => ?_) h0
  have h1 : ¬ ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 1) * ℓ ∉ B := hℓ
  exact (Filter.not_eventually.mp h1).mono fun m hm => not_not.mp hm

/-! ## The configuration -/

/-- Index type: blocks `b` and ordered pairs `j ≠ k < K_b`. -/
abbrev Cfg := Σ b : ℕ, (offDiag (bK b) : Set (ℕ × ℕ))

/-- The points `½ + δ_b + i(j − k)ω_b`. -/
def cfgPoint (Θ : ℝ) (i : Cfg) : ℂ :=
  ((1 / 2 + bδ Θ i.1 : ℝ) : ℂ) + I * ((((i.2 : ℕ × ℕ).1 : ℝ) - (i.2 : ℕ × ℕ).2) * bω i.1 : ℝ)

/-- The weights `c_b/(2K_b)`. -/
def cfgWeight (i : Cfg) : ℝ := bc i.1 / (2 * bK i.1)

theorem zero_one_mem_offDiag (b : ℕ) : ((0, 1) : ℕ × ℕ) ∈ offDiag (bK b) := by
  unfold offDiag
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, ne_eq, zero_ne_one,
    not_false_eq_true, and_true]
  unfold bK
  exact ⟨by positivity, Nat.one_lt_two_pow (by omega)⟩

theorem cfgWeight_pos (i : Cfg) : 0 < cfgWeight i := by
  unfold cfgWeight; have := bc_pos i.1; have := bK_pos i.1; positivity

theorem card_offDiag_le (K : ℕ) : ((offDiag K).card : ℝ) ≤ (K : ℝ) * K := by
  have : (offDiag K).card ≤ K * K := by
    unfold offDiag
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Finset.card_range]
  exact_mod_cast this

theorem summable_cfgWeight_mul (C : ℝ) (hC : 0 ≤ C) : Summable fun i : Cfg => cfgWeight i * C := by
  rw [summable_sigma_of_nonneg (fun i => mul_nonneg (cfgWeight_pos i).le hC)]
  refine ⟨fun b => Summable.of_finite, ?_⟩
  have hfib : ∀ b, ∑' p : (offDiag (bK b) : Set (ℕ × ℕ)), cfgWeight ⟨b, p⟩ * C =
      (offDiag (bK b)).card * (bc b / (2 * bK b) * C) := by
    intro b
    simp [cfgWeight, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  simp_rw [hfib]
  refine Summable.of_nonneg_of_le (fun b => by have := bc_pos b; have := bK_pos b; positivity)
    (fun b => ?_) ((summable_bc_mul_bK.mul_right C).div_const 2)
  have hK := bK_pos b
  calc ((offDiag (bK b)).card : ℝ) * (bc b / (2 * bK b) * C) ≤ (bK b * bK b) * (bc b / (2 * bK b) * C) :=
        mul_le_mul_of_nonneg_right (card_offDiag_le _) (by have := bc_pos b; positivity)
    _ = bc b * bK b * C / 2 := by field_simp

theorem summable_cfgWeight : Summable cfgWeight := by
  simpa using summable_cfgWeight_mul 1 zero_le_one

theorem cexp_cfgPoint (Θ : ℝ) (i : Cfg) (t : ℝ) :
    cexp (t * (cfgPoint Θ i - 1 / 2)) = (Real.exp (bδ Θ i.1 * t) : ℂ) *
      cexp (I * ((((i.2 : ℕ × ℕ).1 : ℝ) - (i.2 : ℕ × ℕ).2) * (bω i.1 * t) : ℝ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold cfgPoint
  push_cast
  ring

theorem norm_cfg_term_le (Θ : ℝ) (hΘ : 0 < Θ) (i : Cfg) {t : ℝ} (ht : 0 ≤ t) :
    ‖(cfgWeight i : ℂ) * cexp (t * (cfgPoint Θ i - 1 / 2))‖ ≤ cfgWeight i * Real.exp (Θ * t) := by
  rw [cexp_cfgPoint, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cfgWeight_pos i), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  have hre : (I * ((((i.2 : ℕ × ℕ).1 : ℝ) - (i.2 : ℕ × ℕ).2) * (bω i.1 * t) : ℝ)).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (bδ_lt Θ hΘ i.1).le ht)) (cfgWeight_pos i).le

theorem blockVal_eq (Θ : ℝ) (b : ℕ) (t : ℝ) :
    blockVal Θ b t = bc b / (2 * bK b) * Real.exp (bδ Θ b * t) *
      (‖dirSum (bK b) (bω b * t)‖ ^ 2 - bK b) := by
  have hK := (bK_pos b).ne'
  unfold blockVal amp fej
  field_simp

theorem blockSum_eq (Θ : ℝ) (b : ℕ) (t : ℝ) :
    ∑ p : (offDiag (bK b) : Set (ℕ × ℕ)), (cfgWeight ⟨b, p⟩ : ℂ) * cexp (t * (cfgPoint Θ ⟨b, p⟩ - 1 / 2)) =
      (blockVal Θ b t : ℂ) := by
  have h := sum_offDiag_cexp (bK b) (bω b * t)
  rw [← Finset.sum_coe_sort] at h
  have hw : ∀ p : (offDiag (bK b) : Set (ℕ × ℕ)),
      (cfgWeight ⟨b, p⟩ : ℂ) * cexp (t * (cfgPoint Θ ⟨b, p⟩ - 1 / 2)) =
        ((bc b / (2 * bK b) * Real.exp (bδ Θ b * t) : ℝ) : ℂ) *
          cexp (I * ((((p : ℕ × ℕ).1 : ℝ) - (p : ℕ × ℕ).2) * (bω b * t) : ℝ)) := by
    intro p
    rw [cexp_cfgPoint]
    simp only [cfgWeight]
    push_cast
    ring
  have h2 : ∑ p : (offDiag (bK b) : Set (ℕ × ℕ)),
      cexp (I * ((((p : ℕ × ℕ).1 : ℝ) - (p : ℕ × ℕ).2) * (bω b * t) : ℝ)) =
        ((‖dirSum (bK b) (bω b * t)‖ ^ 2 - bK b : ℝ) : ℂ) := h
  rw [Finset.sum_congr rfl fun p _ => hw p, ← Finset.mul_sum, h2, blockVal_eq]
  push_cast
  ring

theorem summable_blockVal (Θ : ℝ) (hΘ : 0 < Θ) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun b => blockVal Θ b t := by
  unfold blockVal
  have h1 := summable_amp_mul_fej Θ hΘ ht
  have h2 := summable_amp Θ hΘ ht
  exact ((h1.sub h2).div_const 2).congr fun b => by ring

/-- **The configuration sums to the block lag function.** -/
theorem hasSum_cfg (Θ : ℝ) (hΘ : 0 < Θ) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun i : Cfg => (cfgWeight i : ℂ) * cexp (t * (cfgPoint Θ i - 1 / 2))) (lag Θ t : ℂ) := by
  have hs : Summable fun i : Cfg => (cfgWeight i : ℂ) * cexp (t * (cfgPoint Θ i - 1 / 2)) :=
    Summable.of_norm_bounded (summable_cfgWeight_mul _ (Real.exp_pos _).le)
      fun i => norm_cfg_term_le Θ hΘ i ht
  have hσ := hs.hasSum.sigma fun b => hasSum_fintype _
  simp_rw [blockSum_eq] at hσ
  have hb : HasSum (fun b => (blockVal Θ b t : ℂ)) (lag Θ t : ℂ) := by
    unfold lag
    exact Complex.hasSum_ofReal.mpr (summable_blockVal Θ hΘ ht).hasSum
  have heq := hσ.unique hb
  rw [← heq]
  exact hs.hasSum

theorem cfgPoint_re (Θ : ℝ) (i : Cfg) : (cfgPoint Θ i).re = 1 / 2 + bδ Θ i.1 := by
  unfold cfgPoint; simp

theorem cfgPoint_im (Θ : ℝ) (i : Cfg) :
    (cfgPoint Θ i).im = (((i.2 : ℕ × ℕ).1 : ℝ) - (i.2 : ℕ × ℕ).2) * bω i.1 := by
  unfold cfgPoint; simp

theorem bω_le_abs_im (Θ : ℝ) (i : Cfg) : bω i.1 ≤ |(cfgPoint Θ i).im| := by
  rw [cfgPoint_im, abs_mul, abs_of_pos (bω_pos _)]
  have hne := (Finset.mem_filter.mp i.2.2).2
  have h1 : (1 : ℝ) ≤ |(((i.2 : ℕ × ℕ).1 : ℝ) - (i.2 : ℕ × ℕ).2)| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have : ((i.2 : ℕ × ℕ).1 : ℝ) + 1 ≤ (i.2 : ℕ × ℕ).2 := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · have : ((i.2 : ℕ × ℕ).2 : ℝ) + 1 ≤ (i.2 : ℕ × ℕ).1 := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  have := bω_pos i.1
  nlinarith

theorem finite_im_le (Θ : ℝ) (T : ℝ) : {i : Cfg | |(cfgPoint Θ i).im| ≤ T}.Finite := by
  have hfin : (⋃ b ∈ ((Finset.range (⌊T⌋₊ + 1) : Finset ℕ) : Set ℕ),
      Set.range (fun p : (offDiag (bK b) : Set (ℕ × ℕ)) => (⟨b, p⟩ : Cfg))).Finite :=
    (Finset.range (⌊T⌋₊ + 1)).finite_toSet.biUnion fun b _ => Set.finite_range _
  refine hfin.subset fun i hi => ?_
  have h1 := bω_le_abs_im Θ i
  have hT : bω i.1 ≤ T := h1.trans hi
  unfold bω at hT
  have hb : i.1 ≤ ⌊T⌋₊ := Nat.le_floor (by linarith)
  exact mem_iUnion₂.mpr ⟨i.1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), ⟨i.2, rfl⟩⟩

/-! ## The theorem -/

/-- For almost every `ℓ ∈ [L, 2L]` the samples `Φ(mℓ)` are bounded above. -/
theorem ae_bddAbove_on_Icc (Θ : ℝ) (hΘ : 0 < Θ) {L : ℝ} (hL : 0 < L) :
    ∀ᵐ ℓ ∂(volume.restrict (Icc L (2 * L))), BddAbove (range fun m : ℕ => lag Θ (m * ℓ)) := by
  have hB := volume_posSet_lt_top Θ hΘ
  filter_upwards [ae_eventually_mult_notMem hB hL, ae_restrict_mem measurableSet_Icc] with ℓ hℓ hℓI
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hL hℓI.1
  obtain ⟨M, hM⟩ := eventually_atTop.mp hℓ
  refine ⟨∑ k ∈ Finset.range (M + 1), |lag Θ (k * ℓ)|, ?_⟩
  rintro _ ⟨m, rfl⟩
  by_cases hm : m ≤ M
  · exact (le_abs_self _).trans (Finset.single_le_sum (f := fun k : ℕ => |lag Θ (k * ℓ)|)
      (fun k _ => abs_nonneg _) (Finset.mem_range.mpr (by omega)))
  · push Not at hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hnot := hM m' (by omega)
    have hnn : (0 : ℝ) ≤ ((m' + 1 : ℕ) : ℝ) * ℓ := by positivity
    have hle : lag Θ (((m' + 1 : ℕ) : ℝ) * ℓ) ≤ 0 := by
      by_contra hc
      push Not at hc
      apply hnot
      refine ⟨by push_cast at hnn ⊢; exact hnn, ?_⟩
      push_cast at hc ⊢
      exact hc
    exact hle.trans (Finset.sum_nonneg fun k _ => abs_nonneg _)

/-- For almost every spacing, the samples of the configuration's lag sum are bounded above. -/
theorem ae_cfg_bddAbove (Θ : ℝ) (hΘ : 0 < Θ) :
    ∀ᵐ ℓ ∂volume, 0 < ℓ →
      BddAbove (range fun m : ℕ =>
        (∑' i, (cfgWeight i : ℂ) * cexp (((m : ℝ) * ℓ : ℝ) * (cfgPoint Θ i - 1 / 2))).re) := by
  rw [ae_iff]
  have hcover : {ℓ : ℝ | ¬(0 < ℓ → BddAbove (range fun m : ℕ =>
      (∑' i, (cfgWeight i : ℂ) * cexp (((m : ℝ) * ℓ : ℝ) * (cfgPoint Θ i - 1 / 2))).re))} ⊆
      ⋃ k : ℤ, ({ℓ | ¬ BddAbove (range fun m : ℕ => lag Θ (m * ℓ))} ∩ Icc ((2 : ℝ) ^ k) (2 * 2 ^ k)) := by
    intro ℓ hℓ
    simp only [mem_setOf_eq, Classical.not_imp] at hℓ
    obtain ⟨hℓ0, hnb⟩ := hℓ
    obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow hℓ0 (show (1 : ℝ) < 2 by norm_num)
    refine mem_iUnion.mpr ⟨k, ?_, hk1, ?_⟩
    · intro hb
      apply hnb
      have heq : (fun m : ℕ => (∑' i, (cfgWeight i : ℂ) *
          cexp (((m : ℝ) * ℓ : ℝ) * (cfgPoint Θ i - 1 / 2))).re) = fun m : ℕ => lag Θ (m * ℓ) := by
        funext m
        rw [(hasSum_cfg Θ hΘ (by positivity : (0 : ℝ) ≤ m * ℓ)).tsum_eq, Complex.ofReal_re]
      rw [heq]; exact hb
    · rw [zpow_add_one₀ (by norm_num)] at hk2; linarith
  refine measure_mono_null hcover (measure_iUnion_null fun k => ?_)
  have h := ae_bddAbove_on_Icc Θ hΘ (L := (2 : ℝ) ^ k) (by positivity)
  rw [ae_iff, Measure.restrict_apply' measurableSet_Icc] at h
  exact h

/-! ## The good set of spacings is meagre -/

theorem continuous_blockVal (Θ : ℝ) (b : ℕ) : Continuous fun t => blockVal Θ b t := by
  unfold blockVal amp fej dirSum
  fun_prop

theorem bδ_nonneg (Θ : ℝ) (hΘ : 0 < Θ) (b : ℕ) : 0 ≤ bδ Θ b := by
  have := half_lt_bδ Θ hΘ b; linarith

theorem abs_blockVal_le (Θ : ℝ) (hΘ : 0 < Θ) (b : ℕ) {t R : ℝ} (ht : |t| ≤ R) :
    |blockVal Θ b t| ≤ bc b * bK b * Real.exp (Θ * R) := by
  unfold blockVal
  have ha := amp_pos Θ b t
  have hf0 := fej_nonneg b t
  have hf := fej_le b t
  have hK1 : (1 : ℝ) ≤ bK b := by unfold bK; exact_mod_cast Nat.one_le_two_pow
  have hamp : amp Θ b t ≤ bc b * Real.exp (Θ * R) := by
    unfold amp
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (bc_pos b).le
    calc bδ Θ b * t ≤ bδ Θ b * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) (bδ_nonneg Θ hΘ b)
      _ ≤ Θ * R := mul_le_mul (bδ_lt Θ hΘ b).le ht (abs_nonneg t) hΘ.le
  rw [abs_mul, abs_of_pos (by positivity : 0 < amp Θ b t / 2)]
  have h1 : |fej b t - 1| ≤ 2 * bK b := by rw [abs_le]; constructor <;> linarith
  calc amp Θ b t / 2 * |fej b t - 1| ≤ amp Θ b t / 2 * (2 * bK b) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = amp Θ b t * bK b := by ring
    _ ≤ bc b * Real.exp (Θ * R) * bK b := mul_le_mul_of_nonneg_right hamp (bK_pos b).le
    _ = bc b * bK b * Real.exp (Θ * R) := by ring

theorem continuous_lag (Θ : ℝ) (hΘ : 0 < Θ) : Continuous (lag Θ) := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  have hon : ContinuousOn (lag Θ) (Icc (t₀ - 1) (t₀ + 1)) := by
    refine continuousOn_tsum (fun b => (continuous_blockVal Θ b).continuousOn)
      (summable_bc_mul_bK.mul_right (Real.exp (Θ * (|t₀| + 1)))) fun b t ht => ?_
    rw [Real.norm_eq_abs]
    refine abs_blockVal_le Θ hΘ b ?_
    have := abs_sub_abs_le_abs_sub t t₀
    have h2 : |t - t₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith
  exact (hon t₀ ⟨by linarith, by linarith⟩).continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- At a spike time `t = 2πn/ω_b` block `b` takes its maximum `F_b = K_b`. -/
theorem fej_spike (b n : ℕ) : fej b (2 * Real.pi * n / bω b) = bK b := by
  have hω := (bω_pos b).ne'
  unfold fej dirSum
  have h1 : ∀ k ∈ Finset.range (bK b),
      cexp (I * ((k : ℝ) * (bω b * (2 * Real.pi * n / bω b)) : ℝ)) = 1 := by
    intro k _
    have : I * ((k : ℝ) * (bω b * (2 * Real.pi * n / bω b)) : ℝ) =
        ((k * n : ℕ) : ℂ) * (2 * Real.pi * I) := by
      field_simp
      push_cast
      ring
    rw [this, Complex.exp_nat_mul_two_pi_mul_I]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Complex.norm_natCast]
  have hK := (bK_pos b).ne'
  field_simp

theorem bτ_mono (Θ : ℝ) (hΘ : 0 < Θ) {i j : ℕ} (h : i ≤ j) : bτ Θ i ≤ bτ Θ j := by
  unfold bτ
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  apply div_le_div_of_nonneg_right _ hΘ.le
  have hij : (i : ℝ) ≤ j := by exact_mod_cast h
  have h1 : (19 * i + 19 : ℝ) ≤ 19 * j + 19 := by linarith
  have h2 : (2 : ℝ) ^ (i + 2) ≤ 2 ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (0 : ℝ) < 2 ^ (i + 2) := by positivity
  calc (19 * i + 19 : ℝ) * Real.log 2 * 2 ^ (i + 2) ≤ (19 * j + 19) * Real.log 2 * 2 ^ (i + 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hl.le) h4.le
    _ ≤ (19 * j + 19) * Real.log 2 * 2 ^ (j + 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- After the horizons of the earlier blocks, they are dominated by block `b`. -/
theorem sum_amp_lt_le (Θ : ℝ) (hΘ : 0 < Θ) {t : ℝ} {b : ℕ} (ht : ∀ i < b, bτ Θ i ≤ t) :
    ∑ i ∈ Finset.range b, amp Θ i t ≤ amp Θ b t := by
  induction b with
  | zero => simp [(amp_pos Θ 0 t).le]
  | succ b ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih fun i hi => ht i (by omega)
    have h2 := amp_succ_ge Θ hΘ b (ht b (by omega))
    have h3 : 2 * amp Θ b t ≤ 2 ^ (b + 1) * bK b * amp Θ b t := by
      have hK1 : (1 : ℝ) ≤ bK b := by unfold bK; exact_mod_cast Nat.one_le_two_pow
      have h21 : (2 : ℝ) ≤ 2 ^ (b + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (b + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have ha := (amp_pos Θ b t).le
      have hprod : (2 : ℝ) ≤ 2 ^ (b + 1) * bK b := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hprod ha]
    linarith

/-- The horizon `σ_b = (10b + 9) 2^{b+2} log 2/Θ` up to which later blocks halve. -/
def bσ (Θ : ℝ) (b : ℕ) : ℝ := (10 * b + 9) * Real.log 2 * 2 ^ (b + 2) / Θ

theorem amp_succ_le_half (Θ : ℝ) (hΘ : 0 < Θ) {b i : ℕ} (hbi : b ≤ i) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ bσ Θ b) : 2 * amp Θ (i + 1) t ≤ amp Θ i t := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hexp : Real.exp ((bδ Θ (i + 1) - bδ Θ i) * t) ≤ (2 : ℝ) ^ (10 * i + 9) := by
    rw [bδ_succ_sub, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (10 * i + 9)), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have h1 : Θ * (1 / 2 : ℝ) ^ (i + 2) * t ≤ Θ * (1 / 2 : ℝ) ^ (b + 2) * t := by
      have : (1 / 2 : ℝ) ^ (i + 2) ≤ (1 / 2) ^ (b + 2) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have := hΘ.le
      gcongr
    have h2 : Θ * (1 / 2 : ℝ) ^ (b + 2) * t ≤ (10 * b + 9) * Real.log 2 := by
      unfold bσ at ht
      rw [le_div_iff₀ hΘ] at ht
      have hpos : (0 : ℝ) < (1 / 2) ^ (b + 2) := by positivity
      have h22 : (2 : ℝ) ^ (b + 2) * (1 / 2) ^ (b + 2) = 1 := by rw [← mul_pow]; norm_num
      calc Θ * (1 / 2 : ℝ) ^ (b + 2) * t = t * Θ * (1 / 2) ^ (b + 2) := by ring
        _ ≤ (10 * b + 9) * Real.log 2 * 2 ^ (b + 2) * (1 / 2) ^ (b + 2) :=
            mul_le_mul_of_nonneg_right ht hpos.le
        _ = (10 * b + 9) * Real.log 2 := by rw [mul_assoc _ ((2 : ℝ) ^ (b + 2)), h22, mul_one]
    have h3 : (10 * b + 9 : ℝ) * Real.log 2 ≤ ((10 * i + 9 : ℕ) : ℝ) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hl.le
      push_cast
      have : (b : ℝ) ≤ i := by exact_mod_cast hbi
      linarith
    linarith
  unfold amp
  rw [bc_succ]
  have hsplit : Real.exp (bδ Θ (i + 1) * t) =
      Real.exp (bδ Θ i * t) * Real.exp ((bδ Θ (i + 1) - bδ Θ i) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hc := bc_pos i
  have he := Real.exp_pos (bδ Θ i * t)
  have hk : 2 * (1 / 2 : ℝ) ^ (10 * i + 10) * (2 : ℝ) ^ (10 * i + 9) = 1 := by
    rw [one_div_pow]; field_simp; rw [← pow_succ']
  calc 2 * (bc i * (1 / 2 : ℝ) ^ (10 * i + 10) *
        (Real.exp (bδ Θ i * t) * Real.exp ((bδ Θ (i + 1) - bδ Θ i) * t)))
      ≤ 2 * (bc i * (1 / 2 : ℝ) ^ (10 * i + 10) * (Real.exp (bδ Θ i * t) * (2 : ℝ) ^ (10 * i + 9))) := by
        gcongr
    _ = bc i * Real.exp (bδ Θ i * t) * (2 * (1 / 2 : ℝ) ^ (10 * i + 10) * (2 : ℝ) ^ (10 * i + 9)) := by
        ring
    _ = bc i * Real.exp (bδ Θ i * t) := by rw [hk, mul_one]

theorem amp_add_le (Θ : ℝ) (hΘ : 0 < Θ) {b : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ bσ Θ b) (j : ℕ) :
    amp Θ (b + 1 + j) t ≤ (1 / 2 : ℝ) ^ (j + 1) * amp Θ b t := by
  induction j with
  | zero =>
    have := amp_succ_le_half Θ hΘ (le_refl b) ht0 ht
    simp only [add_zero, zero_add, pow_one]
    linarith
  | succ j ih =>
    have h := amp_succ_le_half Θ hΘ (show b ≤ b + 1 + j by omega) ht0 ht
    rw [show b + 1 + (j + 1) = b + 1 + j + 1 by ring, pow_succ]
    nlinarith [amp_pos Θ (b + 1 + j + 1) t]

theorem tsum_amp_le_three (Θ : ℝ) (hΘ : 0 < Θ) {b : ℕ} {t : ℝ} (ht0 : 0 ≤ t)
    (hlow : ∀ i < b, bτ Θ i ≤ t) (hup : t ≤ bσ Θ b) :
    ∑' i, amp Θ i t ≤ 3 * amp Θ b t := by
  have hs := summable_amp Θ hΘ ht0
  rw [← hs.sum_add_tsum_nat_add (b + 1), Finset.sum_range_succ]
  have h1 := sum_amp_lt_le Θ hΘ hlow
  have htail : ∑' j, amp Θ (j + (b + 1)) t ≤ amp Θ b t := by
    have hg : Summable fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * amp Θ b t :=
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
        (add_left_injective 1)).mul_right _
    calc ∑' j, amp Θ (j + (b + 1)) t ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * amp Θ b t :=
          ((summable_nat_add_iff (b + 1)).mpr hs).tsum_le_tsum
            (fun j => by rw [show j + (b + 1) = b + 1 + j by ring]; exact amp_add_le Θ hΘ ht0 hup j) hg
      _ = amp Θ b t := by
          rw [tsum_mul_right]
          have : ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) = 1 := by
            simp_rw [pow_succ]; rw [tsum_mul_right, tsum_geometric_two]; norm_num
          rw [this, one_mul]
  linarith

/-- **The lag function is unbounded above on every half-line.** -/
theorem exists_lag_gt (Θ : ℝ) (hΘ : 0 < Θ) (M s₀ : ℝ) : ∃ t, s₀ ≤ t ∧ M < lag Θ t := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hπ := Real.pi_pos
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨b₀, hb₀⟩ := pow_unbounded_of_one_lt (max (max M (|s₀| * Θ)) Θ) (by norm_num : (1 : ℝ) < 2)
  set b := b₀ + 1 with hb
  have hb₀b : (2 : ℝ) ^ b₀ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) (by omega)
  have hM : M < 2 ^ b := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _))
    (lt_of_lt_of_le hb₀ hb₀b)
  have hs₀ : |s₀| * Θ < 2 ^ b₀ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hb₀
  have hΘb : Θ < 2 ^ b := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hb₀ hb₀b)
  set τ := bτ Θ b₀ with hτ
  have hτ0 : 0 ≤ τ := bτ_nonneg Θ hΘ b₀
  set n : ℕ := ⌈τ * bω b / (2 * Real.pi)⌉₊ with hn
  set t := 2 * Real.pi * n / bω b with ht
  have hω := bω_pos b
  have ht1 : τ ≤ t := by
    have := Nat.le_ceil (τ * bω b / (2 * Real.pi))
    rw [← hn] at this
    rw [ht, le_div_iff₀ hω]
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have ht2 : t < τ + 2 * Real.pi / bω b := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ τ * bω b / (2 * Real.pi) by positivity)
    rw [← hn] at hc
    calc t = 2 * Real.pi * n / bω b := ht
      _ < 2 * Real.pi * (τ * bω b / (2 * Real.pi) + 1) / bω b := by
          apply div_lt_div_of_pos_right _ hω
          exact mul_lt_mul_of_pos_left hc (by positivity)
      _ = τ + 2 * Real.pi / bω b := by field_simp
  -- the window `[τ_{b−1}, σ_b]` is longer than one period
  have hwin : τ + 2 * Real.pi / bω b ≤ bσ Θ b := by
    have hp : 2 * Real.pi / bω b ≤ 2 * Real.pi := by
      rw [div_le_iff₀ hω]
      have : (1 : ℝ) ≤ bω b := by unfold bω; have := Nat.cast_nonneg (α := ℝ) b; linarith
      nlinarith
    have hb1 : (19 * b₀ + 19 : ℝ) = 19 * b := by rw [hb]; push_cast; ring
    have hpb : (2 : ℝ) ^ (b₀ + 2) = 2 ^ b * 2 := by rw [hb, pow_succ]
    have hpb2 : (2 : ℝ) ^ (b + 2) = 2 ^ b * 4 := by rw [pow_add]; norm_num
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have h2b : (0 : ℝ) < 2 ^ b := by positivity
    have hpi := Real.pi_lt_d2
    have key : τ * Θ + 2 * Real.pi * Θ ≤ (10 * b + 9) * Real.log 2 * 2 ^ (b + 2) := by
      have e0 : τ * Θ = (19 * b₀ + 19) * Real.log 2 * 2 ^ (b₀ + 2) := by
        rw [hτ]; unfold bτ; field_simp
      rw [e0, hb1, hpb, hpb2]
      have e2 : 0.69 * 2 ^ b * 36 ≤ Real.log 2 * 2 ^ b * (2 * b + 36) := by
        have : (36 : ℝ) ≤ 2 * b + 36 := by linarith
        have h1 : 0.69 * 2 ^ b ≤ Real.log 2 * 2 ^ b := mul_le_mul_of_nonneg_right hlog2.le h2b.le
        nlinarith
      have e3 : 2 * Real.pi * Θ ≤ 2 * 3.15 * 2 ^ b := by nlinarith
      nlinarith
    have : τ + 2 * Real.pi ≤ bσ Θ b := by
      unfold bσ
      rw [le_div_iff₀ hΘ]
      linarith
    linarith
  have ht0 : 0 ≤ t := le_trans hτ0 ht1
  have hlow : ∀ i < b, bτ Θ i ≤ t := fun i hi =>
    (bτ_mono Θ hΘ (show i ≤ b₀ by omega)).trans ht1
  have hup : t ≤ bσ Θ b := by linarith
  have h3 := tsum_amp_le_three Θ hΘ ht0 hlow hup
  have hspike : fej b t = bK b := by rw [ht]; exact fej_spike b n
  have hlagge : (bK b - 3) * amp Θ b t / 2 ≤ lag Θ t := by
    rw [lag_eq Θ hΘ ht0]
    have hsf := summable_amp_mul_fej Θ hΘ ht0
    have hge : amp Θ b t * fej b t ≤ ∑' i, amp Θ i t * fej i t :=
      hsf.le_tsum b fun j _ => mul_nonneg (amp_pos Θ j t).le (fej_nonneg j t)
    rw [hspike] at hge
    linarith
  have hamp : (2 : ℝ) ^ (b + 2) ≤ amp Θ b t := by
    unfold amp bc
    have hδ := half_lt_bδ Θ hΘ b
    have hexp : Real.exp (Θ / 2 * τ) ≤ Real.exp (bδ Θ b * t) :=
      Real.exp_le_exp.mpr (mul_le_mul hδ ht1 hτ0 (bδ_nonneg Θ hΘ b))
    have hval : Real.exp (Θ / 2 * τ) = (2 : ℝ) ^ ((19 * b₀ + 19) * 2 ^ (b₀ + 1)) := by
      rw [hτ]; unfold bτ
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ ((19 * b₀ + 19) * 2 ^ (b₀ + 1))),
        Real.log_pow]
      congr 1
      push_cast
      field_simp
      ring
    have hexpo : b + 2 + (5 * b * b + 5 * b) ≤ (19 * b₀ + 19) * 2 ^ (b₀ + 1) := by
      have h2 : b₀ + 1 ≤ 2 ^ b₀ := Nat.lt_two_pow_self
      have h3 : 2 ^ (b₀ + 1) = 2 * 2 ^ b₀ := by ring
      rw [h3, hb]
      nlinarith
    calc (2 : ℝ) ^ (b + 2) = (1 / 2 : ℝ) ^ (5 * b * b + 5 * b) * 2 ^ (b + 2 + (5 * b * b + 5 * b)) := by
          rw [pow_add (2 : ℝ) (b + 2), one_div_pow]; field_simp
      _ ≤ (1 / 2 : ℝ) ^ (5 * b * b + 5 * b) * 2 ^ ((19 * b₀ + 19) * 2 ^ (b₀ + 1)) := by
          gcongr; norm_num
      _ = (1 / 2 : ℝ) ^ (5 * b * b + 5 * b) * Real.exp (Θ / 2 * τ) := by rw [hval]
      _ ≤ (1 / 2 : ℝ) ^ (5 * b * b + 5 * b) * Real.exp (bδ Θ b * t) := by gcongr
  refine ⟨t, ?_, ?_⟩
  · have : s₀ < τ := by
      rw [hτ]; unfold bτ
      rw [lt_div_iff₀ hΘ]
      have hpb : (2 : ℝ) ^ (b₀ + 2) = 2 ^ b₀ * 4 := by rw [pow_add]; norm_num
      rw [hpb]
      have hb0 : (0 : ℝ) ≤ b₀ := Nat.cast_nonneg b₀
      have h2 : (0 : ℝ) < 2 ^ b₀ := by positivity
      have hs : s₀ * Θ ≤ |s₀| * Θ := mul_le_mul_of_nonneg_right (le_abs_self s₀) hΘ.le
      have e1 : 19 * 0.69 * (2 ^ b₀ * 4) ≤ (19 * b₀ + 19 : ℝ) * Real.log 2 * (2 ^ b₀ * 4) := by
        have h1 : (19 : ℝ) * 0.69 ≤ (19 * b₀ + 19) * Real.log 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      nlinarith
    linarith
  · have hK : (4 : ℝ) ≤ bK b := by
      unfold bK
      have : (4 : ℕ) ≤ 2 ^ (8 * b + 8) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (8 * b + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this
    have h4 : (2 : ℝ) ^ (b + 2) = 4 * 2 ^ b := by rw [pow_add]; ring
    have hpos := amp_pos Θ b t
    nlinarith

/-- **The good set of spacings is meagre.** -/
theorem isMeagre_goodSpacings (Θ : ℝ) (hΘ : 0 < Θ) :
    IsMeagre {ℓ : ℝ | 0 < ℓ ∧ BddAbove (range fun m : ℕ => lag Θ (m * ℓ))} := by
  set F : ℕ → Set ℝ := fun M => {ℓ | ∀ m : ℕ, lag Θ (m * ℓ) ≤ M} with hF
  have hclosed : ∀ M, IsClosed (F M) := by
    intro M
    have : F M = ⋂ m : ℕ, {ℓ | lag Θ (m * ℓ) ≤ M} := by ext ℓ; simp [hF]
    rw [this]
    exact isClosed_iInter fun m =>
      isClosed_le ((continuous_lag Θ hΘ).comp (continuous_const.mul continuous_id)) continuous_const
  have hsub : {ℓ : ℝ | 0 < ℓ ∧ BddAbove (range fun m : ℕ => lag Θ (m * ℓ))} ⊆
      ⋃ M : ℕ, (F M ∩ Ioi 0) := by
    rintro ℓ ⟨hℓ, C, hC⟩
    refine mem_iUnion.mpr ⟨⌈C⌉₊, fun m => ?_, hℓ⟩
    exact (hC ⟨m, rfl⟩).trans (Nat.le_ceil C)
  refine IsMeagre.mono hsub (isMeagre_iUnion fun M => IsNowhereDense.isMeagre ?_)
  rw [IsNowhereDense, Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hcl : closure (F M ∩ Ioi 0) ⊆ F M ∩ Ici 0 := by
    refine (closure_inter_subset_inter_closure _ _).trans ?_
    rw [(hclosed M).closure_eq, closure_Ioi]
  have hsubF : Metric.ball x ε ⊆ F M ∩ Ici 0 := hball.trans (interior_subset.trans hcl)
  have hx0 : 0 ≤ x := (hsubF (Metric.mem_ball_self hε)).2
  set a := x + ε / 4 with ha
  set c := x + ε / 2 with hc
  have ha0 : 0 < a := by rw [ha]; linarith
  have hac : a < c := by rw [ha, hc]; linarith
  have hIoo : ∀ ℓ ∈ Ioo a c, ∀ m : ℕ, lag Θ (m * ℓ) ≤ M := by
    intro ℓ hℓ m
    have hmem : ℓ ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hℓ.1, hℓ.2]
    exact (hsubF hmem).1 m
  obtain ⟨t, ht, hlt⟩ := exists_lag_gt Θ hΘ M (a * c / (c - a) + 1)
  have hts : a * c / (c - a) < t := by linarith
  obtain ⟨m, hm, ℓ, hℓ, rfl⟩ := RHTower.exists_nat_mul_mem_Ioo (s := t) ha0 hac hts
  have := hIoo ℓ hℓ m
  linarith

/-- **Almost every spacing is blind to a non-attained top.** -/
theorem exists_lag_configuration_ae_spacing_bddAbove {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ),
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧
      (∀ β < 1 / 2 + Θ, ∃ i, β < (ρ i).re) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧
      (∀ i, ∃ j, ρ j = starRingEnd ℂ (ρ i) ∧ c j = c i) ∧
      (∀ i, 0 < c i) ∧ Summable c ∧
      ∀ᵐ ℓ ∂volume, 0 < ℓ →
        BddAbove (range fun m : ℕ =>
          (∑' i, (c i : ℂ) * cexp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))).re) := by
  refine ⟨Cfg, inferInstance, cfgPoint Θ, cfgWeight, fun i => ?_, fun β hβ => ?_,
    finite_im_le Θ, fun i => ?_, cfgWeight_pos, summable_cfgWeight, ?_⟩
  · rw [cfgPoint_re]
    exact ⟨by linarith [half_lt_bδ Θ hΘ i.1], by linarith [bδ_lt Θ hΘ i.1]⟩
  · obtain ⟨b, hb⟩ := exists_pow_lt_of_lt_one (show 0 < (1 / 2 + Θ - β) / Θ by
      apply div_pos (by linarith) hΘ) (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨⟨b, ⟨(0, 1), zero_one_mem_offDiag b⟩⟩, ?_⟩
    rw [cfgPoint_re]
    unfold bδ
    have hb' : (1 / 2 : ℝ) ^ (b + 1) < (1 / 2 + Θ - β) / Θ := by
      calc (1 / 2 : ℝ) ^ (b + 1) ≤ (1 / 2) ^ b := pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (by omega)
        _ < _ := hb
    rw [lt_div_iff₀ hΘ] at hb'
    nlinarith
  · obtain ⟨b, p⟩ := i
    have hmem : ((p : ℕ × ℕ).2, (p : ℕ × ℕ).1) ∈ offDiag (bK b) := by
      have hp := Finset.mem_filter.mp p.2
      unfold offDiag
      simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, fun h => hp.2 h.symm⟩
    refine ⟨⟨b, ⟨((p : ℕ × ℕ).2, (p : ℕ × ℕ).1), hmem⟩⟩, ?_, rfl⟩
    apply Complex.ext
    · simp [cfgPoint]
    · simp only [cfgPoint_im, Complex.conj_im]
      ring
  · exact ae_cfg_bddAbove Θ hΘ

/-- **Measure versus category.** The same configuration has the good set of spacings
`{ℓ > 0 : sup_m Re Φ(mℓ) < ∞}` of full measure and meagre. -/
theorem exists_lag_configuration_goodSpacings_ae_and_meagre {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ),
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧
      (∀ β < 1 / 2 + Θ, ∃ i, β < (ρ i).re) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧
      (∀ i, 0 < c i) ∧ Summable c ∧
      (∀ᵐ ℓ ∂volume, 0 < ℓ →
        BddAbove (range fun m : ℕ =>
          (∑' i, (c i : ℂ) * cexp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))).re)) ∧
      IsMeagre {ℓ : ℝ | 0 < ℓ ∧ BddAbove (range fun m : ℕ =>
          (∑' i, (c i : ℂ) * cexp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))).re)} := by
  refine ⟨Cfg, inferInstance, cfgPoint Θ, cfgWeight, fun i => ?_, fun β hβ => ?_, finite_im_le Θ,
    cfgWeight_pos, summable_cfgWeight, ?_, ?_⟩
  · rw [cfgPoint_re]
    exact ⟨by linarith [half_lt_bδ Θ hΘ i.1], by linarith [bδ_lt Θ hΘ i.1]⟩
  · obtain ⟨b, hb⟩ := exists_pow_lt_of_lt_one (show 0 < (1 / 2 + Θ - β) / Θ by
      apply div_pos (by linarith) hΘ) (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨⟨b, ⟨(0, 1), zero_one_mem_offDiag b⟩⟩, ?_⟩
    rw [cfgPoint_re]
    unfold bδ
    have hb' : (1 / 2 : ℝ) ^ (b + 1) < (1 / 2 + Θ - β) / Θ := by
      calc (1 / 2 : ℝ) ^ (b + 1) ≤ (1 / 2) ^ b := pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (by omega)
        _ < _ := hb
    rw [lt_div_iff₀ hΘ] at hb'
    nlinarith
  · exact ae_cfg_bddAbove Θ hΘ
  · refine (isMeagre_goodSpacings Θ hΘ).mono ?_
    rintro ℓ ⟨hℓ, hb⟩
    refine ⟨hℓ, ?_⟩
    have heq : (fun m : ℕ => (∑' i, (cfgWeight i : ℂ) *
        cexp (((m : ℝ) * ℓ : ℝ) * (cfgPoint Θ i - 1 / 2))).re) = fun m : ℕ => lag Θ (m * ℓ) := by
      funext m
      rw [(hasSum_cfg Θ hΘ (by positivity : (0 : ℝ) ≤ m * ℓ)).tsum_eq, Complex.ofReal_re]
    rwa [heq] at hb

end RHTower.AlmostEverySpacing
