import GaloisForLFunctions.RHTower.Sieve.FreeScaleWindowCount
import GaloisForLFunctions.RHTower.Sieve.ScaledBadStart

/-!
# The exceptional starts of a free-scale construction

The exceptional set depends only on the start scale `m`, not on the physical scale, so the estimate
of `Sieve/MultiBadStart` carries over verbatim: each block contributes `1024ε√y_k/ϱ² +
√y_k/(log y_k)²` with `√y_k = m/2^k ≤ m`, and the tolerance of the Möbius mean square is free.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- Each block's cofactor scale grows with the base. -/
theorem tendsto_freeScale (K₀ : ℕ) {k : ℕ} (hk : k ≤ K₀ + 1) :
    Tendsto (fun u : ℕ => freeScale (2 ^ (K₀ + 1) * u) k) atTop atTop := by
  have hval : ∀ u : ℕ, freeScale (2 ^ (K₀ + 1) * u) k
      = ((2 : ℝ) ^ (K₀ + 1 - k) * (u : ℝ)) ^ 2 := by
    intro u
    rw [freeScale, freeStart_pow_mul hk]
    push_cast
    ring
  have hlin : Tendsto (fun u : ℕ => (2 : ℝ) ^ (K₀ + 1 - k) * (u : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun u : ℕ => ((2 : ℝ) ^ (K₀ + 1 - k) * (u : ℝ)) ^ 2) atTop atTop := by
    have := hlin.atTop_mul_atTop₀ hlin
    exact this.congr fun u => (sq _).symm
  exact hsq.congr fun u => (hval u).symm

/-- The base start scale grows. -/
theorem tendsto_freeStart_zero (K₀ : ℕ) :
    Tendsto (fun u : ℕ => ((freeStart (2 ^ (K₀ + 1) * u) 0 : ℕ) : ℝ)) atTop atTop := by
  have hval : ∀ u : ℕ, ((freeStart (2 ^ (K₀ + 1) * u) 0 : ℕ) : ℝ)
      = (2 : ℝ) ^ (K₀ + 1) * (u : ℝ) := by
    intro u
    rw [freeStart_pow_mul (by omega)]
    push_cast
    rfl
  have hlin : Tendsto (fun u : ℕ => (2 : ℝ) ^ (K₀ + 1) * (u : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
  exact hlin.congr fun u => (hval u).symm

/-- **The exceptional starts of a free-scale construction are below any fraction of `m`.** -/
theorem eventually_card_freeBadStartUnion_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (K₀ : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      (((freeBadStartUnion β (2 ^ (K₀ + 1) * u) K₀).card : ℕ) : ℝ)
        ≤ ε * ((freeStart (2 ^ (K₀ + 1) * u) 0 : ℕ) : ℝ) := by
  classical
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  set δ : ℝ := ε / (2 * ((K₀ : ℝ) + 1)) with hδ
  have hδ0 : (0 : ℝ) < δ := by rw [hδ]; positivity
  set ε' : ℝ := δ * squarefreeDensity ^ 2 / 2048 with hε'
  have hε'0 : (0 : ℝ) < ε' := by rw [hε']; positivity
  have hblock : ∀ k, k ≤ K₀ → ∀ᶠ u : ℕ in atTop,
      (((badStart (freeScale (2 ^ (K₀ + 1) * u) k)
          (freeWindow β (2 ^ (K₀ + 1) * u) k)).card : ℕ) : ℝ)
        ≤ δ * ((freeStart (2 ^ (K₀ + 1) * u) 0 : ℕ) : ℝ) := by
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
    filter_upwards [(tendsto_freeScale K₀ (by omega : k ≤ K₀ + 1)).eventually hev,
      (tendsto_freeScale K₀ (by omega : k ≤ K₀ + 1)).eventually htail,
      Filter.eventually_gt_atTop 0] with u hv htl hu0
    set m : ℕ := 2 ^ (K₀ + 1) * u with hm
    have hsqrt : Real.sqrt (freeScale m k) = ((freeStart m k : ℕ) : ℝ) := sqrt_freeScale m k
    have hlen : ((freeStart m k : ℕ) : ℝ) ≤ ((freeStart m 0 : ℕ) : ℝ) := by
      exact_mod_cast freeStart_anti m (Nat.zero_le k)
    have hcard := card_badStart_le_card_badOuter (freeScale m k) (freeWindow β m k)
    have hcardR : (((badStart (freeScale m k) (freeWindow β m k)).card : ℕ) : ℝ)
        ≤ (((badOuter (freeScale m k)
            (scaledLength (((1:ℝ)/2) ^ k) β (freeScale m k))).card : ℕ) : ℝ) := by
      rw [freeWindow] at hcard ⊢
      exact_mod_cast hcard
    have hmain : (((badOuter (freeScale m k)
          (scaledLength (((1:ℝ)/2) ^ k) β (freeScale m k))).card : ℕ) : ℝ)
        ≤ 1024 * ε' * Real.sqrt (freeScale m k) / squarefreeDensity ^ 2
          + Real.sqrt (freeScale m k) / (Real.log (freeScale m k)) ^ 2 := hv
    have hfirst : 1024 * ε' * Real.sqrt (freeScale m k) / squarefreeDensity ^ 2
        = δ / 2 * Real.sqrt (freeScale m k) := by
      rw [hε']
      field_simp
      ring
    rw [hsqrt] at hfirst htl hmain
    have hlen0 : (0 : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep : (((badStart (freeScale m k) (freeWindow β m k)).card : ℕ) : ℝ)
        ≤ δ * ((freeStart m k : ℕ) : ℝ) := by
      linarith [hcardR, hmain, hfirst, htl]
    exact hstep.trans (mul_le_mul_of_nonneg_left hlen hδ0.le)
  have hall : ∀ᶠ u : ℕ in atTop, ∀ k ∈ Finset.range (K₀ + 1),
      (((badStart (freeScale (2 ^ (K₀ + 1) * u) k)
          (freeWindow β (2 ^ (K₀ + 1) * u) k)).card : ℕ) : ℝ)
        ≤ δ * ((freeStart (2 ^ (K₀ + 1) * u) 0 : ℕ) : ℝ) :=
    (Filter.eventually_all_finset (Finset.range (K₀ + 1))).2 fun k hk =>
      hblock k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
  filter_upwards [hall] with u hv
  refine (card_freeBadStartUnion_le β (2 ^ (K₀ + 1) * u) K₀).trans ?_
  have hsum := Finset.sum_le_sum hv
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  have hm0 : (0 : ℝ) ≤ ((freeStart (2 ^ (K₀ + 1) * u) 0 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hval : ((K₀ + 1 : ℕ) : ℝ) * (δ * ((freeStart (2 ^ (K₀ + 1) * u) 0 : ℕ) : ℝ))
      = ε / 2 * ((freeStart (2 ^ (K₀ + 1) * u) 0 : ℕ) : ℝ) := by
    rw [hδ]
    push_cast
    field_simp
  rw [hval]
  nlinarith [hm0, hε]

end

end RHTower.Sieve
