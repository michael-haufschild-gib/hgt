import GaloisForLFunctions.RHTower.Sieve.MultiEventual
import GaloisForLFunctions.RHTower.Sieve.ScaledBadStart

/-!
# The exceptional starts of the marker family are a vanishing fraction

Each block contributes `1024ε√y_k/ϱ² + √y_k/(log y_k)²` exceptional starts, and `√y_k = m/2^k ≤ m`.
Since the tolerance `ε` of the Möbius mean square is free and the number of blocks is fixed, the
whole family's exceptional set is below any prescribed fraction of `m`.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- Every block's cofactor scale grows. -/
theorem tendsto_multiBlockScale_block (K₀ : ℕ) {k : ℕ} (hk : k ≤ K₀) :
    Tendsto (fun v : ℕ => multiBlockScale K₀ v k) atTop atTop := by
  have hbase := tendsto_multiBlockScale K₀
  have h := Filter.Tendsto.atTop_div_const (show (0:ℝ) < (4:ℝ) ^ k by positivity) hbase
  exact h.congr fun v => (multiBlockScale_div K₀ v hk).symm

/-- **The exceptional starts of the family are below any fraction of `m`.** -/
theorem eventually_card_badStartUnion_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (K₀ : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v : ℕ in atTop,
      (((badStartUnion β K₀ v).card : ℕ) : ℝ) ≤ ε * ((multiScale K₀ v : ℕ) : ℝ) := by
  classical
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  set δ : ℝ := ε / (2 * ((K₀ : ℝ) + 1)) with hδ
  have hδ0 : (0 : ℝ) < δ := by
    rw [hδ]
    positivity
  set ε' : ℝ := δ * squarefreeDensity ^ 2 / 2048 with hε'
  have hε'0 : (0 : ℝ) < ε' := by
    rw [hε']
    positivity
  -- each block
  have hblock : ∀ k, k ≤ K₀ → ∀ᶠ v : ℕ in atTop,
      (((badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)).card : ℕ) : ℝ)
        ≤ δ * ((multiScale K₀ v : ℕ) : ℝ) := by
    intro k hk
    have hc0 : (0 : ℝ) < ((1 : ℝ) / 2) ^ k := by positivity
    have hc1 : ((1 : ℝ) / 2) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hev := eventually_card_badOuter_le (c := ((1 : ℝ) / 2) ^ k) (β := β) hc0 hc1 hβ0 hβ1
      hε'0
    have htail : ∀ᶠ y : ℝ in atTop,
        Real.sqrt y / (Real.log y) ^ 2 ≤ δ / 2 * Real.sqrt y := by
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.sqrt (2 / δ) + 1),
        eventually_gt_atTop (1 : ℝ)] with y hy hy1
      have hs0 : (0 : ℝ) ≤ Real.sqrt y := Real.sqrt_nonneg y
      have hd0 : (0 : ℝ) < Real.sqrt (2 / δ) := Real.sqrt_pos.2 (by positivity)
      have hlog0 : (0 : ℝ) < Real.log y := by linarith
      have hsq : 2 / δ ≤ (Real.log y) ^ 2 := by
        have hbase : Real.sqrt (2 / δ) ≤ Real.log y := by linarith
        nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 / δ), hbase, hd0]
      rw [div_le_iff₀ (by positivity)]
      have hkey : (1 : ℝ) ≤ δ / 2 * (Real.log y) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ δ / 2)
        have hval : δ / 2 * (2 / δ) = 1 := by field_simp
        linarith [hmul, hval]
      nlinarith [hkey, hs0]
    filter_upwards [(tendsto_multiBlockScale_block K₀ hk).eventually hev,
      (tendsto_multiBlockScale_block K₀ hk).eventually htail] with v hv htl
    have hsqrt : Real.sqrt (multiBlockScale K₀ v k) = ((multiBlockLen K₀ v k : ℕ) : ℝ) :=
      sqrt_multiBlockScale K₀ v k
    have hlen : ((multiBlockLen K₀ v k : ℕ) : ℝ) ≤ ((multiScale K₀ v : ℕ) : ℝ) := by
      have hle : multiBlockLen K₀ v k ≤ multiScale K₀ v := by
        rw [multiScale, multiBlockLen, multiBlockLen, multiHalf, multiHalf, Nat.sub_zero]
        have hpow : (2 : ℕ) ^ (K₀ - k) ≤ 2 ^ K₀ :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have hmul : 2 ^ (K₀ - k) * v ≤ 2 ^ K₀ * v := Nat.mul_le_mul_right v hpow
        omega
      exact_mod_cast hle
    have hcard := card_badStart_le_card_badOuter (multiBlockScale K₀ v k)
      (multiBlockWindow β K₀ v k)
    have hcardR : (((badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)).card : ℕ) : ℝ)
        ≤ (((badOuter (multiBlockScale K₀ v k)
            (scaledLength (((1:ℝ)/2) ^ k) β (multiBlockScale K₀ v k))).card : ℕ) : ℝ) := by
      rw [multiBlockWindow] at hcard ⊢
      exact_mod_cast hcard
    have hmain : (((badOuter (multiBlockScale K₀ v k)
          (scaledLength (((1:ℝ)/2) ^ k) β (multiBlockScale K₀ v k))).card : ℕ) : ℝ)
        ≤ 1024 * ε' * Real.sqrt (multiBlockScale K₀ v k) / squarefreeDensity ^ 2
          + Real.sqrt (multiBlockScale K₀ v k) / (Real.log (multiBlockScale K₀ v k)) ^ 2 := hv
    have hfirst : 1024 * ε' * Real.sqrt (multiBlockScale K₀ v k) / squarefreeDensity ^ 2
        = δ / 2 * Real.sqrt (multiBlockScale K₀ v k) := by
      rw [hε']
      field_simp
      ring
    have hs0 : (0 : ℝ) ≤ Real.sqrt (multiBlockScale K₀ v k) := Real.sqrt_nonneg _
    rw [hsqrt] at hfirst htl hs0
    have hlen0 : (0 : ℝ) ≤ ((multiBlockLen K₀ v k : ℕ) : ℝ) := Nat.cast_nonneg _
    have : (((badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)).card : ℕ) : ℝ)
        ≤ δ * ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
      rw [hsqrt] at hmain
      linarith [hcardR, hmain, hfirst, htl]
    calc (((badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)).card : ℕ) : ℝ)
        ≤ δ * ((multiBlockLen K₀ v k : ℕ) : ℝ) := this
      _ ≤ δ * ((multiScale K₀ v : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hlen hδ0.le
  have hall : ∀ᶠ v : ℕ in atTop, ∀ k ∈ Finset.range (K₀ + 1),
      (((badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)).card : ℕ) : ℝ)
        ≤ δ * ((multiScale K₀ v : ℕ) : ℝ) :=
    (Filter.eventually_all_finset (Finset.range (K₀ + 1))).2 fun k hk =>
      hblock k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
  filter_upwards [hall] with v hv
  refine (card_badStartUnion_le β K₀ v).trans ?_
  have hsum : ∑ k ∈ Finset.range (K₀ + 1),
      (((badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)).card : ℕ) : ℝ)
      ≤ ∑ _k ∈ Finset.range (K₀ + 1), δ * ((multiScale K₀ v : ℕ) : ℝ) :=
    Finset.sum_le_sum hv
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  have hm0 : (0 : ℝ) ≤ ((multiScale K₀ v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hK : (0 : ℝ) < (K₀ : ℝ) + 1 := by positivity
  have hval : ((K₀ + 1 : ℕ) : ℝ) * (δ * ((multiScale K₀ v : ℕ) : ℝ))
      = ε / 2 * ((multiScale K₀ v : ℕ) : ℝ) := by
    rw [hδ]
    push_cast
    field_simp
  rw [hval]
  nlinarith [hm0, hε]

end

end RHTower.Sieve
