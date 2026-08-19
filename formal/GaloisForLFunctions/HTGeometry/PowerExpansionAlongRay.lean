import GaloisForLFunctions.HTGeometry.GammaLogPowerIndependence

/-!
# Reading an asymptotic expansion along an arbitrary escaping sequence

`power_expansion_eq_zero` and `log_power_expansion_eq_zero` read a finite expansion along the real
ray.  The boundary data of `archimedean-relative-prime-cocycle-curvature` and of
`finite-archimedean-gamma-product-boundary-law` live on *vertical* tubes, so the same reading is
needed along `σ + it` with `t → ∞`, and more generally along any sequence escaping to infinity.

Nothing in the argument uses the direction: peel the constant term, multiply by the variable, and
recurse.  The logarithm dies first because `‖log s‖ → ∞` while every power term stays bounded.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

theorem eq_zero_of_eventually_norm_le_div {c : ℂ} {K : ℝ} {S : ℕ → ℂ}
    (hS : Tendsto (fun n => ‖S n‖) atTop atTop)
    (h : ∀ᶠ n in atTop, ‖c‖ ≤ K / ‖S n‖) : c = 0 := by
  have hlim : Tendsto (fun n => K / ‖S n‖) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hS
  have hle : ‖c‖ ≤ 0 := ge_of_tendsto hlim h
  exact norm_le_zero_iff.mp hle

/-- **The descending powers are independent along any escaping sequence.** -/
theorem power_expansion_eq_zero_ray : ∀ (M : ℕ) (a : ℕ → ℂ) (K : ℝ) (S : ℕ → ℂ),
    Tendsto (fun n => ‖S n‖) atTop atTop →
    (∀ᶠ n in atTop, ‖∑ m ∈ Finset.range (M + 1), a m / (S n) ^ m‖ ≤ K / ‖S n‖ ^ (M + 1)) →
    ∀ m, m ≤ M → a m = 0 := by
  intro M
  induction M with
  | zero =>
      intro a K S hS h m hm
      have hm0 : m = 0 := by omega
      subst hm0
      refine eq_zero_of_eventually_norm_le_div (K := K) hS ?_
      filter_upwards [h] with n hn
      simpa using hn
  | succ M ih =>
      intro a K S hS h m hm
      have hge1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ‖S n‖ := hS.eventually_ge_atTop 1
      have hsplit : ∀ n : ℕ, ∑ j ∈ Finset.range (M + 2), a j / (S n) ^ j
          = a 0 + ∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ (j + 1) := by
        intro n
        rw [Finset.sum_range_succ']
        simp
        ring
      have htail : ∀ n : ℕ, (1 : ℝ) ≤ ‖S n‖ →
          ‖∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ (j + 1)‖
            ≤ (∑ j ∈ Finset.range (M + 1), ‖a (j + 1)‖) / ‖S n‖ := by
        intro n hn
        have hn0 : (0 : ℝ) < ‖S n‖ := by linarith
        refine le_trans (norm_sum_le _ _) ?_
        rw [Finset.sum_div]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_div, norm_pow]
        rw [div_le_div_iff₀ (by positivity) hn0]
        have hpow : ‖S n‖ ≤ ‖S n‖ ^ (j + 1) := by
          calc ‖S n‖ = ‖S n‖ ^ 1 := (pow_one _).symm
            _ ≤ ‖S n‖ ^ (j + 1) := pow_le_pow_right₀ hn (by omega)
        nlinarith [norm_nonneg (a (j + 1))]
      have hK0 : 0 ≤ K := by
        rcases (h.and hge1).exists with ⟨n, hn, hn1⟩
        have hn0 : (0 : ℝ) < ‖S n‖ := by linarith
        have hpos : (0 : ℝ) < ‖S n‖ ^ (M + 2) := by positivity
        have := le_trans (norm_nonneg _) hn
        rw [le_div_iff₀ hpos] at this
        nlinarith [this, hpos]
      have ha0 : a 0 = 0 := by
        refine eq_zero_of_eventually_norm_le_div
          (K := K + ∑ j ∈ Finset.range (M + 1), ‖a (j + 1)‖) hS ?_
        filter_upwards [h, hge1] with n hn hn1
        have hn0 : (0 : ℝ) < ‖S n‖ := by linarith
        rw [hsplit n] at hn
        have hstep : ‖a 0‖ ≤ ‖a 0 + ∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ (j + 1)‖
            + ‖∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ (j + 1)‖ := by
          have := norm_sub_le (a 0 + ∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ (j + 1))
            (∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ (j + 1))
          simpa using this
        have hbig : K / ‖S n‖ ^ (M + 2) ≤ K / ‖S n‖ := by
          have hpow : ‖S n‖ ≤ ‖S n‖ ^ (M + 2) := by
            calc ‖S n‖ = ‖S n‖ ^ 1 := (pow_one _).symm
              _ ≤ ‖S n‖ ^ (M + 2) := pow_le_pow_right₀ hn1 (by omega)
          have hp : (0 : ℝ) < ‖S n‖ ^ (M + 2) := by positivity
          rw [div_le_div_iff₀ hp hn0]
          nlinarith [hK0]
        have hsum : K / ‖S n‖ + (∑ j ∈ Finset.range (M + 1), ‖a (j + 1)‖) / ‖S n‖
            = (K + ∑ j ∈ Finset.range (M + 1), ‖a (j + 1)‖) / ‖S n‖ := by
          ring
        linarith [hstep, hn, hbig, htail n hn1, hsum.le, hsum.symm.le]
      have hrec : ∀ᶠ n in atTop,
          ‖∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ j‖ ≤ K / ‖S n‖ ^ (M + 1) := by
        filter_upwards [h, hge1] with n hn hn1
        have hn0 : (0 : ℝ) < ‖S n‖ := by linarith
        have hSne : S n ≠ 0 := by
          intro hz; rw [hz, norm_zero] at hn0; linarith
        have hid : ∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ (j + 1)
            = (∑ j ∈ Finset.range (M + 1), a (j + 1) / (S n) ^ j) / (S n) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [pow_succ]
          field_simp
        rw [hsplit n, ha0, zero_add, hid, norm_div] at hn
        rw [div_le_iff₀ hn0] at hn
        have hp : (0 : ℝ) < ‖S n‖ ^ (M + 2) := by positivity
        have hp1 : (0 : ℝ) < ‖S n‖ ^ (M + 1) := by positivity
        rw [le_div_iff₀ hp1]
        have hpowid : ‖S n‖ ^ (M + 2) = ‖S n‖ ^ (M + 1) * ‖S n‖ := by ring
        rw [hpowid] at hn
        have h2 := mul_le_mul_of_nonneg_right hn (le_of_lt hp1)
        have hfin : K / (‖S n‖ ^ (M + 1) * ‖S n‖) * ‖S n‖ * ‖S n‖ ^ (M + 1) = K := by
          field_simp
        rw [hfin] at h2
        exact h2
      have hrest := ih (fun j => a (j + 1)) K S hS hrec
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hm0]; exact ha0
      · obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        rw [hj]
        exact hrest j (by omega)

/-- **The logarithm and the descending powers are independent along any escaping sequence.** -/
theorem log_power_expansion_eq_zero_ray (M : ℕ) (b : ℂ) (a : ℕ → ℂ) (K : ℝ) (S : ℕ → ℂ)
    (hS : Tendsto (fun n => ‖S n‖) atTop atTop)
    (hlog : Tendsto (fun n => ‖Complex.log (S n)‖) atTop atTop)
    (h : ∀ᶠ n in atTop,
      ‖b * Complex.log (S n) + ∑ m ∈ Finset.range (M + 1), a m / (S n) ^ m‖
        ≤ K / ‖S n‖ ^ (M + 1)) :
    b = 0 ∧ ∀ m, m ≤ M → a m = 0 := by
  have hge1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ‖S n‖ := hS.eventually_ge_atTop 1
  have hK0 : 0 ≤ K := by
    rcases (h.and hge1).exists with ⟨n, hn, hn1⟩
    have hn0 : (0 : ℝ) < ‖S n‖ := by linarith
    have hpos : (0 : ℝ) < ‖S n‖ ^ (M + 1) := by positivity
    have := le_trans (norm_nonneg _) hn
    rw [le_div_iff₀ hpos] at this
    nlinarith [this, hpos]
  set T : ℝ := K + ∑ m ∈ Finset.range (M + 1), ‖a m‖ with hT
  have hbbound : ∀ᶠ n in atTop, ‖b‖ * ‖Complex.log (S n)‖ ≤ T := by
    filter_upwards [h, hge1] with n hn hn1
    have hn0 : (0 : ℝ) < ‖S n‖ := by linarith
    have hpow : ‖∑ m ∈ Finset.range (M + 1), a m / (S n) ^ m‖
        ≤ ∑ m ∈ Finset.range (M + 1), ‖a m‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      refine Finset.sum_le_sum fun m _ => ?_
      rw [norm_div, norm_pow]
      have hpm : (1 : ℝ) ≤ ‖S n‖ ^ m := one_le_pow₀ hn1
      rw [div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg (a m)]
    have hKle : K / ‖S n‖ ^ (M + 1) ≤ K := by
      have hpm : (1 : ℝ) ≤ ‖S n‖ ^ (M + 1) := one_le_pow₀ hn1
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hK0]
    have hid : b * Complex.log (S n)
        = (b * Complex.log (S n) + ∑ m ∈ Finset.range (M + 1), a m / (S n) ^ m)
          - ∑ m ∈ Finset.range (M + 1), a m / (S n) ^ m := by ring
    have hstep := norm_sub_le
      (b * Complex.log (S n) + ∑ m ∈ Finset.range (M + 1), a m / (S n) ^ m)
      (∑ m ∈ Finset.range (M + 1), a m / (S n) ^ m)
    rw [← hid, norm_mul] at hstep
    linarith [hstep, hn, hpow, hKle]
  have hb0 : b = 0 := by
    by_contra hb
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hdiv : Tendsto (fun n => ‖b‖ * ‖Complex.log (S n)‖) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hbpos hlog
    rcases (hdiv.eventually_gt_atTop T).and hbbound |>.exists with ⟨n, h1, h2⟩
    linarith
  refine ⟨hb0, ?_⟩
  refine power_expansion_eq_zero_ray M a K S hS ?_
  filter_upwards [h] with n hn
  rw [hb0, zero_mul, zero_add] at hn
  exact hn

end

end GaloisForLFunctions.HTGeometry
