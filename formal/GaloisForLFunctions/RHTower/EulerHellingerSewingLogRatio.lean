import GaloisForLFunctions.RHTower.PrimeRecipBelowWindow
import GaloisForLFunctions.RHTower.EulerHellingerLocalGrowthBounds

/-!
# The logarithmic growth rate of the reflected sewing cost

For a fixed drift `0 < c < 1/2`,

```text
log L_N(c) / log N → 2c.
```

The upper bound compares every local term with `p^(2c-1) ≤ N^(2c)/p` and uses Mertens' bound on
`∑_{p<N} 1/p`.  The lower bound keeps the primes in a power window `[N^θ, N)` for a fixed `θ < 1`,
where Mertens' second theorem gives reciprocal mass `-log θ > 0`.
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The two finite bounds -/

theorem primeRecipBelow_le_primeRecipSum (N : ℕ) : primeRecipBelow N ≤ primeRecipSum N := by
  rw [primeRecipSum_eq_primeRecipBelow_add]
  linarith [primeRecipWeight_nonneg N]

theorem logReflectedSewingBelow_le {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) (N : ℕ) :
    logReflectedSewingBelow c N ≤
      sewingGrowthConst c * (N : ℝ) ^ (2 * c) * primeRecipBelow N := by
  have habs : |c| < 1 / 2 := by
    rw [abs_of_pos hc0]
    exact hc
  rw [logReflectedSewingBelow_eq_sum_localSewingLog habs N, primeRecipBelow,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hlt : p < N := (Nat.mem_primesBelow.mp hp).1
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hple : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hlt.le
  have hsplit : (p : ℝ) ^ (2 * c - 1) = (p : ℝ) ^ (2 * c) * ((p : ℝ))⁻¹ := by
    rw [show (2 : ℝ) * c - 1 = 2 * c + -1 by ring, Real.rpow_add hp0, Real.rpow_neg_one]
  have hmono : (p : ℝ) ^ (2 * c) ≤ (N : ℝ) ^ (2 * c) :=
    Real.rpow_le_rpow hp0.le hple (by linarith)
  have hinv : (0 : ℝ) < ((p : ℝ))⁻¹ := inv_pos.mpr hp0
  have hK : 0 < sewingGrowthConst c := sewingGrowthConst_pos hc
  refine le_trans (localSewingLog_le hprime hc0 hc) ?_
  rw [hsplit]
  calc sewingGrowthConst c * ((p : ℝ) ^ (2 * c) * ((p : ℝ))⁻¹)
      ≤ sewingGrowthConst c * ((N : ℝ) ^ (2 * c) * ((p : ℝ))⁻¹) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hinv.le) hK.le
    _ = sewingGrowthConst c * (N : ℝ) ^ (2 * c) * ((p : ℝ))⁻¹ := by ring

theorem primesBelow_subset {M N : ℕ} (h : M ≤ N) : Nat.primesBelow M ⊆ Nat.primesBelow N := by
  intro p hp
  rw [Nat.mem_primesBelow] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 h, hp.2⟩

theorem logReflectedSewingBelow_ge {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) {θ : ℝ} (_hθ0 : 0 < θ)
    {N : ℕ} (hMN : powerWindowIndex θ N ≤ N)
    (hact : (6 : ℝ) ≤ ((powerWindowIndex θ N : ℕ) : ℝ) ^ c) :
    (1 / 2) * ((N : ℝ) ^ θ) ^ (2 * c) *
        (primeRecipBelow N - primeRecipBelow (powerWindowIndex θ N))
      ≤ logReflectedSewingBelow c N := by
  have habs : |c| < 1 / 2 := by
    rw [abs_of_pos hc0]
    exact hc
  set M : ℕ := powerWindowIndex θ N with hMdef
  have hsub : Nat.primesBelow M ⊆ Nat.primesBelow N := primesBelow_subset hMN
  rw [logReflectedSewingBelow_eq_sum_localSewingLog habs N]
  have hdrop : ∑ p ∈ Nat.primesBelow N \ Nat.primesBelow M, localSewingLog p c ≤
      ∑ p ∈ Nat.primesBelow N, localSewingLog p c := by
    refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_
    exact fun p hp _ => (localSewingLog_pos (Nat.prime_of_mem_primesBelow hp) hc0 hc).le
  refine le_trans ?_ hdrop
  have hmass : (1 / 2) * ((N : ℝ) ^ θ) ^ (2 * c) *
      (primeRecipBelow N - primeRecipBelow M) =
      ∑ p ∈ Nat.primesBelow N \ Nat.primesBelow M,
        (1 / 2) * ((N : ℝ) ^ θ) ^ (2 * c) * ((p : ℝ))⁻¹ := by
    rw [← Finset.mul_sum, primeRecipBelow, primeRecipBelow,
      ← Finset.sum_sdiff_eq_sub hsub]
  rw [hmass]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_sdiff] at hp
  obtain ⟨hpN, hpM⟩ := hp
  have hprime := Nat.prime_of_mem_primesBelow hpN
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hMle : M ≤ p := by
    by_contra hcon
    exact hpM (Nat.mem_primesBelow.mpr ⟨not_le.mp hcon, hprime⟩)
  have hMler : ((M : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hMle
  have hM0 : (0 : ℝ) ≤ ((M : ℕ) : ℝ) := Nat.cast_nonneg M
  have hactp : (6 : ℝ) ≤ (p : ℝ) ^ c :=
    le_trans hact (Real.rpow_le_rpow hM0 hMler hc0.le)
  have hlow := localSewingLog_ge hprime hc0 hc hactp
  refine le_trans ?_ hlow
  have hsplit : (p : ℝ) ^ (2 * c - 1) = (p : ℝ) ^ (2 * c) * ((p : ℝ))⁻¹ := by
    rw [show (2 : ℝ) * c - 1 = 2 * c + -1 by ring, Real.rpow_add hp0, Real.rpow_neg_one]
  have hwin : ((N : ℝ) ^ θ) ^ (2 * c) ≤ (p : ℝ) ^ (2 * c) := by
    refine Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) θ) ?_ (by linarith)
    exact le_trans (rpow_le_powerWindowIndex θ N) hMler
  have hinv : (0 : ℝ) < ((p : ℝ))⁻¹ := inv_pos.mpr hp0
  rw [hsplit]
  calc (1 / 2) * ((N : ℝ) ^ θ) ^ (2 * c) * ((p : ℝ))⁻¹
      ≤ (1 / 2) * ((p : ℝ) ^ (2 * c)) * ((p : ℝ))⁻¹ := by
        have := mul_le_mul_of_nonneg_left hwin (by norm_num : (0 : ℝ) ≤ 1 / 2)
        exact mul_le_mul_of_nonneg_right this hinv.le
    _ = (1 / 2) * ((p : ℝ) ^ (2 * c) * ((p : ℝ))⁻¹) := by ring

/-! ## The logarithmic growth rate -/

private theorem tendsto_logShift_div (D : ℝ) :
    Tendsto (fun u : ℝ => (D + Real.log u) / u) atTop (nhds 0) := by
  have h1 : Tendsto (fun u : ℝ => D / u) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have h2 : Tendsto (fun u : ℝ => Real.log u / u) atTop (nhds 0) := by
    have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact this
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr fun u => ?_
  rw [add_div]

private theorem tendsto_logNat_atTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **The reflected sewing cost has logarithmic growth rate `2c`.** -/
theorem tendsto_log_logReflectedSewing_div_log {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    Tendsto (fun N : ℕ => Real.log (logReflectedSewingBelow c N) / Real.log N) atTop
      (nhds (2 * c)) := by
  have hK : 0 < sewingGrowthConst c := sewingGrowthConst_pos hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B : ℝ := mertensPrimeWindowBound with hB
  have hB0 : 0 ≤ B := mertensPrimeWindowBound_nonneg
  set C : ℝ := sewingGrowthConst c / Real.log 2 with hC
  have hC0 : 0 < C := div_pos hK hlog2
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · -- lower half: a fixed power window
    intro a ha
    set θ : ℝ := max (1 / 2) ((a + 2 * c) / (4 * c)) with hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hθ1 : θ < 1 := by
      refine max_lt (by norm_num) ?_
      rw [div_lt_one (by linarith)]
      linarith
    have hgoal : a < 2 * c * θ := by
      have h1 : (a + 2 * c) / (4 * c) ≤ θ := le_max_right _ _
      have h2 : 2 * c * ((a + 2 * c) / (4 * c)) = (a + 2 * c) / 2 := by
        field_simp
        ring
      have h3 : 2 * c * ((a + 2 * c) / (4 * c)) ≤ 2 * c * θ :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      rw [h2] at h3
      linarith
    have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
    set κ : ℝ := (1 / 2) * (-Real.log θ / 2) with hκ
    have hκ0 : 0 < κ := by
      rw [hκ]
      have : 0 < -Real.log θ := by linarith
      linarith
    have hwindow := tendsto_primeRecipBelow_window hθ0
    have hmass : ∀ᶠ N : ℕ in atTop,
        -Real.log θ / 2 ≤ primeRecipBelow N - primeRecipBelow (powerWindowIndex θ N) := by
      have hlt : -Real.log θ / 2 < -Real.log θ := by linarith
      exact (hwindow.eventually (eventually_gt_nhds hlt)).mono fun N hN => hN.le
    have hactivation : ∀ᶠ N : ℕ in atTop,
        (6 : ℝ) ≤ ((powerWindowIndex θ N : ℕ) : ℝ) ^ c := by
      have h : Tendsto (fun N : ℕ => ((powerWindowIndex θ N : ℕ) : ℝ) ^ c) atTop atTop :=
        (tendsto_rpow_atTop hc0).comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_powerWindowIndex hθ0))
      exact h.eventually_ge_atTop 6
    have hratio : Tendsto (fun N : ℕ => Real.log κ / Real.log (N : ℝ)) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds tendsto_logNat_atTop
    have hsmall : ∀ᶠ N : ℕ in atTop, a - 2 * c * θ < Real.log κ / Real.log (N : ℝ) :=
      hratio.eventually (eventually_gt_nhds (by linarith))
    filter_upwards [eventually_gt_atTop 2, hmass, hactivation, hsmall] with N hN hmassN hactN hsmallN
    have hNr : (2 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    have hMN : powerWindowIndex θ N ≤ N := by
      rw [powerWindowIndex]
      have hlt : (N : ℝ) ^ θ < (N : ℝ) := by
        have h1 : (N : ℝ) ^ θ < (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by linarith) hθ1
        rwa [Real.rpow_one] at h1
      have := (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) θ)).mpr
        (by exact_mod_cast hlt)
      omega
    have hlow := logReflectedSewingBelow_ge hc0 hc hθ0 hMN hactN
    have hpow : ((N : ℝ) ^ θ) ^ (2 * c) = (N : ℝ) ^ (2 * c * θ) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      ring
    have hpowpos : (0 : ℝ) < (N : ℝ) ^ (2 * c * θ) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hkey : κ * (N : ℝ) ^ (2 * c * θ) ≤ logReflectedSewingBelow c N := by
      refine le_trans ?_ hlow
      rw [hpow, hκ]
      have : (0 : ℝ) ≤ (1 / 2) * (N : ℝ) ^ (2 * c * θ) := by positivity
      nlinarith
    have hLpos : 0 < logReflectedSewingBelow c N :=
      logReflectedSewingBelow_pos hc0 hc hN
    have hlogL : Real.log κ + 2 * c * θ * Real.log (N : ℝ) ≤
        Real.log (logReflectedSewingBelow c N) := by
      have h1 : Real.log (κ * (N : ℝ) ^ (2 * c * θ)) ≤
          Real.log (logReflectedSewingBelow c N) :=
        Real.log_le_log (by positivity) hkey
      rwa [Real.log_mul (ne_of_gt hκ0) (ne_of_gt hpowpos),
        Real.log_rpow (by linarith)] at h1
    rw [lt_div_iff₀ hlogN]
    have hsm : (a - 2 * c * θ) * Real.log (N : ℝ) < Real.log κ := by
      rw [lt_div_iff₀ hlogN] at hsmallN
      linarith
    nlinarith
  · -- upper half: the Mertens bound on the prime reciprocal sum
    intro b hb
    have hshift := (tendsto_logShift_div (Real.log C + Real.log 2)).comp tendsto_logNat_atTop
    have hsmall : ∀ᶠ N : ℕ in atTop,
        (Real.log C + Real.log 2 + Real.log (Real.log (N : ℝ))) / Real.log (N : ℝ) < b - 2 * c :=
      hshift.eventually (eventually_lt_nhds (by linarith))
    have hbig : ∀ᶠ N : ℕ in atTop, B ≤ Real.log (N : ℝ) :=
      tendsto_logNat_atTop.eventually_ge_atTop B
    filter_upwards [eventually_gt_atTop 2, hsmall, hbig] with N hN hsmallN hbigN
    have hNr : (2 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    have hLpos : 0 < logReflectedSewingBelow c N :=
      logReflectedSewingBelow_pos hc0 hc hN
    have hAle : primeRecipBelow N ≤ (Real.log (N : ℝ) + B) / Real.log 2 :=
      le_trans (primeRecipBelow_le_primeRecipSum N)
        (primeRecipSum_le_log (by omega))
    have hpowpos : (0 : ℝ) < (N : ℝ) ^ (2 * c) := Real.rpow_pos_of_pos (by linarith) _
    have hupper : logReflectedSewingBelow c N ≤
        C * (N : ℝ) ^ (2 * c) * (Real.log (N : ℝ) + B) := by
      refine le_trans (logReflectedSewingBelow_le hc0 hc N) ?_
      have h1 : sewingGrowthConst c * (N : ℝ) ^ (2 * c) * primeRecipBelow N ≤
          sewingGrowthConst c * (N : ℝ) ^ (2 * c) * ((Real.log (N : ℝ) + B) / Real.log 2) :=
        mul_le_mul_of_nonneg_left hAle (by positivity)
      refine le_trans h1 (le_of_eq ?_)
      rw [hC]
      field_simp
    have hsumpos : (0 : ℝ) < Real.log (N : ℝ) + B := by linarith
    have hlogL : Real.log (logReflectedSewingBelow c N) ≤
        Real.log C + 2 * c * Real.log (N : ℝ) + Real.log (Real.log (N : ℝ) + B) := by
      have h1 := Real.log_le_log hLpos hupper
      rwa [Real.log_mul (by positivity) (ne_of_gt hsumpos),
        Real.log_mul (ne_of_gt hC0) (ne_of_gt hpowpos),
        Real.log_rpow (by linarith)] at h1
    have hlogsum : Real.log (Real.log (N : ℝ) + B) ≤
        Real.log 2 + Real.log (Real.log (N : ℝ)) := by
      have h1 : Real.log (Real.log (N : ℝ) + B) ≤ Real.log (2 * Real.log (N : ℝ)) :=
        Real.log_le_log hsumpos (by linarith)
      rwa [Real.log_mul (by norm_num) (ne_of_gt hlogN)] at h1
    rw [div_lt_iff₀ hlogN]
    rw [div_lt_iff₀ hlogN] at hsmallN
    linarith

end

end RHTower
