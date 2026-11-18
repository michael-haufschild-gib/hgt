import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount

/-!
# Merging balanced prime products in intervals with sharp endpoints

In a cell inside `[s²,2s²]`, consider products with a prime divisor in
`(s/K,Ks]` and prime quotient. Their count is smaller than the ordinary prime
supply by an arbitrarily large factor, uniformly down to each fixed
logarithmic relative width. Cutting the quotient interval separately at each
divisor retains both original endpoints.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Products in `(u,v]` with one balanced prime factor and a prime quotient. -/
def balancedProducts (K s u v : ℝ) : Finset ℕ :=
  (windowPrimes (s / K) (K * s)).biUnion fun q =>
    (windowPrimes (u / q) (v / q)).image (q * ·)

private theorem outer_count {K s : ℝ} (hK : 1 ≤ K) (hs : 1 < s)
    (hsep : 2 * Real.log K ≤ Real.log s) (hKs : K ≤ s) :
    ((windowPrimes (s / K) (K * s)).card : ℝ) * Real.log s ≤
      2 * Real.log 4 * K * s := by
  have hK0 : 0 < K := by linarith only [hK]
  have hs0 := lt_trans zero_lt_one hs
  have ha : 1 ≤ s / K := (le_div_iff₀ hK0).2 (by simpa using hKs)
  have hab : s / K ≤ K * s :=
    (div_le_self hs0.le hK).trans (le_mul_of_one_le_left hs0.le hK)
  have hlog : Real.log s ≤ 2 * Real.log (s / K) := by
    rw [Real.log_div hs0.ne' hK0.ne']; linarith only [hsep]
  have h := card_windowPrimes_mul_log_le ha hab
  have ht := Chebyshev.theta_le_log4_mul_x (mul_nonneg hK0.le hs0.le)
  have hz := Chebyshev.theta_nonneg (s / K)
  linarith only [mul_le_mul_of_nonneg_left hlog
    (Nat.cast_nonneg (windowPrimes (s / K) (K * s)).card : (0 : ℝ) ≤ _), h, ht, hz]

/-- At any prescribed log-power resolution, every balanced product can be
assigned arbitrarily many distinct prime slots in the same cell. -/
theorem eventually_balancedProducts_capacity (K : ℝ) (B D : ℕ) :
    ∀ᶠ s : ℝ in atTop, ∀ u v : ℝ, s ^ 2 ≤ u → u ≤ v → v ≤ 2 * s ^ 2 →
      s ^ 2 / Real.log s ^ B ≤ v - u →
      D * (balancedProducts K s u v).card ≤ (windowPrimes u v).card := by
  by_cases hK : 1 ≤ K
  · obtain ⟨A, hA, hupper⟩ := exists_card_windowPrimes_le (B + 1 : ℕ) zero_lt_one
    obtain ⟨H, hH, hlower⟩ := exists_card_windowPrimes_div_ge B (by norm_num : (0 : ℝ) < 1/2)
    have hK0 : 0 < K := by linarith only [hK]
    filter_upwards [eventually_ge_atTop (max 2 (max K (max (K * A) H))),
      Real.tendsto_log_atTop.eventually_ge_atTop
        (max (2 * Real.log K) (max (2 ^ (B+1)) (48 * D * Real.log 4 * K ^ 2)))] with s hs hL
    have hs2 := (le_max_left _ _).trans hs
    have hs0 : 0 < s := by linarith only [hs2]
    have hs1 : 1 < s := by linarith only [hs2]
    have hKs : K ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
    have hKA : K * A ≤ s := (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hs))
    have hHs : H ≤ s := (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hs))
    have hlog := Real.log_pos hs1
    have hsep := (le_max_left _ _).trans hL
    have hpow : (2 : ℝ) ^ (B+1) ≤ Real.log s :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hL)
    have hreserve : 48 * D * Real.log 4 * K ^ 2 ≤ Real.log s :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hL)
    intro u v hu huv hv hgap
    have ht : 0 < s ^ 2 := sq_pos_of_pos hs0
    have hlen := sub_nonneg.mpr huv
    -- Each prime quotient window has relative width at least one higher log power.
    have hrow (q : ℕ) (hq : q ∈ windowPrimes (s / K) (K * s)) :
        ((windowPrimes (u/q) (v/q)).card : ℝ) ≤
          4 * K * (v-u) / (s * Real.log s) := by
      obtain ⟨hp, hqlo, hqhi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
      have hscale : s / K ≤ s ^ 2 / q := by
        rw [div_le_div_iff₀ hK0 hq0]
        calc s * q ≤ s * (K * s) := by gcongr
             _ = s ^ 2 * K := by ring
      have hlarge : A ≤ s ^ 2 / q := ((le_div_iff₀ hK0).2
        (by simpa only [mul_comm A] using hKA)).trans hscale
      have hlog2 : Real.log s ≤ 2 * Real.log (s ^ 2 / q) := by
        have h := Real.log_le_log (div_pos hs0 hK0) hscale
        rw [Real.log_div hs0.ne' hK0.ne'] at h
        linarith only [h, hsep]
      have hlq : 0 < Real.log (s^2/q) := by linarith only [hlog, hlog2]
      have hexp : Real.log s ^ B ≤ Real.log (s^2/q) ^ (B+1) := by
        have ha := pow_le_pow_left₀ hlog.le hlog2 (B+1)
        rw [mul_pow, pow_succ (Real.log s)] at ha
        exact le_of_mul_le_mul_left
          (calc (2:ℝ)^(B+1) * Real.log s ^ B ≤ Real.log s ^ B * Real.log s := by
                  rw [mul_comm]; gcongr
                _ ≤ _ := ha) (by positivity)
      have hg : s^2/q / Real.log (s^2/q) ^ ((B+1:ℕ):ℝ) ≤ v/q-u/q := by
        rw [Real.rpow_natCast, ← sub_div, div_right_comm]
        exact div_le_div_of_nonneg_right
          ((div_le_div_of_nonneg_left ht.le (by positivity) hexp).trans hgap) hq0.le
      have h := hupper (s^2/q) hlarge (u/q) (v/q) (by gcongr) (by gcongr)
        (by rw [← mul_div_assoc]; gcongr) hg
      rw [← sub_div] at h
      have hden : s * Real.log s ≤ 2 * K * (q * Real.log (s^2/q)) := by
        have hq' := (div_lt_iff₀ hK0).1 hqlo
        calc s * Real.log s ≤ (q * K) * (2 * Real.log (s^2/q)) :=
                mul_le_mul hq'.le hlog2 hlog.le (by positivity)
             _ = _ := by ring
      refine h.trans ?_
      rw [show (1+1:ℝ) * ((v-u)/q) / Real.log (s^2/q) =
        (2*(v-u))/(q * Real.log (s^2/q)) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) hlen)]
    have hcnt : ((balancedProducts K s u v).card : ℝ) ≤
        (windowPrimes (s/K) (K*s)).card * (4*K*(v-u)/(s*Real.log s)) := by
      calc _ ≤ ∑ q ∈ windowPrimes (s/K) (K*s), ((windowPrimes (u/q) (v/q)).card : ℝ) := by
                  have hn : (balancedProducts K s u v).card ≤
                      ∑ q ∈ windowPrimes (s/K) (K*s), (windowPrimes (u/q) (v/q)).card :=
                    card_biUnion_le.trans (sum_le_sum (fun (q : ℕ) _ =>
                      card_image_le (s := windowPrimes (u/q) (v/q)) (f := (q*·))))
                  exact_mod_cast hn
           _ ≤ _ := (sum_le_sum hrow).trans_eq (by simp)
    have hlogbig : Real.log (2*s^2) = Real.log 2 + 2 * Real.log s := by
      rw [Real.log_mul (by norm_num) ht.ne', Real.log_pow]; norm_num
    have hbigpos : 0 < Real.log (2*s^2) := by rw [hlogbig]; positivity
    have hlow := hlower (2*s^2) (by nlinarith only [hHs, hs2, sq_nonneg (s-1)])
      2 (by norm_num) (by norm_num) (2*u) (2*v) (by linarith only [hu])
      (by linarith only [huv]) (by linarith only [hv]) (by
        rw [Real.rpow_natCast]
        have hle : Real.log s ≤ Real.log (2*s^2) := by rw [hlogbig]; linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
        have hh := (div_le_div_of_nonneg_left ht.le (pow_pos hlog B)
          (pow_le_pow_left₀ hlog.le hle B)).trans hgap
        rw [mul_div_assoc]; linarith only [hh])
    rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
        mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] at hlow
    have hout := outer_count hK hs1 hsep hKs
    have h3 : Real.log (2*s^2) ≤ 3 * Real.log s := by
      rw [hlogbig]; linarith only [Real.log_le_log (by norm_num : (0:ℝ)<2) hs2]
    have hcoef : (D:ℝ) * (windowPrimes (s/K) (K*s)).card * (24*K) ≤ s := by
      apply le_of_mul_le_mul_right _ hlog
      calc _ ≤ (D:ℝ) * (24*K) * (2 * Real.log 4 * K * s) := by
                  nlinarith only [mul_le_mul_of_nonneg_left hout (show 0 ≤ (D:ℝ)*(24*K) by positivity)]
           _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hreserve hs0.le]
    have hex := mul_le_mul_of_nonneg_left hcnt (Nat.cast_nonneg D)
    have hfinal : (D:ℝ) * (balancedProducts K s u v).card ≤ (v-u)/(6 * Real.log s) := by
      refine hex.trans ?_
      rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_right hcoef (mul_nonneg hlen hlog.le)]
    exact_mod_cast hfinal.trans (le_trans (by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_left h3 hlen]) hlow)
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with s hs u v _ _ _ _
    have he : windowPrimes (s/K) (K*s) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      by_cases hpos : 0 < K
      · obtain ⟨_, hl, hr⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hq
        have hleft := le_div_self (by linarith only [hs] : 0 ≤ s) hpos (le_of_not_ge hK)
        have hright := mul_le_of_le_one_left (by linarith only [hs] : 0 ≤ s) (le_of_not_ge hK)
        linarith only [hl, hr, hleft, hright]
      · have hz : K*s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos) (by linarith only [hs])
        have hq0 := (mem_Ioc.mp (mem_filter.mp hq).1).2
        rw [Nat.floor_of_nonpos hz] at hq0
        exact ((mem_filter.mp hq).2).ne_zero (by omega)
    simp [balancedProducts, he]

end GaloisForLFunctions.RestrictedFactorizationCalculus
