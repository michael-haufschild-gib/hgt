import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZetaSamplingPoleCompression
import Zeta23.GammaFacts.Complete

/-!
# The archimedean density is constant on the sampled space up to a vanishing error

Stirling bounds the density error on the enlarged height window. Outside that
window every sampling center is far away; a quadratic spectral moment absorbs
the linear growth of the density. The full-line quadratic form therefore differs
from its constant-density baseline by `O(1/L)` in operator norm.
-/

open MeasureTheory Real Set Filter Topology Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Continuity near zero and Stirling away from zero give a global linear majorant. -/
theorem exists_mu_linear_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : ℝ, |mu τ| ≤ A + |τ| := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (gammaFacts.smooth.continuous.continuousOn : ContinuousOn mu (Icc (-1 : ℝ) 1))
  let A := |B| + |C| + Real.log (2 * π)
  have hp : 0 < 2 * π := by positivity
  have hp1 : 1 ≤ 2 * π := by linarith only [Real.pi_gt_three]
  have hlp : 0 ≤ Real.log (2 * π) := Real.log_nonneg hp1
  refine ⟨A, by dsimp [A]; positivity, fun τ => ?_⟩
  rcases le_or_gt |τ| 1 with hτ | hτ
  · have hh := hB τ (abs_le.mp hτ)
    rw [Real.norm_eq_abs] at hh
    dsimp [A]
    linarith only [hh, le_abs_self B, abs_nonneg C, hlp, abs_nonneg τ]
  · have hs := hC τ hτ.le
    have ht0 : 0 < |τ| := lt_trans zero_lt_one hτ
    have ht2 : 1 ≤ τ ^ 2 := by nlinarith only [hτ, sq_abs τ]
    have hCe : C / τ ^ 2 ≤ |C| := by
      rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one ht2)]
      nlinarith only [le_abs_self C, mul_le_mul_of_nonneg_left ht2 (abs_nonneg C)]
    have hlog : |Real.log (|τ| / (2 * π))| ≤ |τ| + Real.log (2 * π) := by
      rw [Real.log_div ht0.ne' hp.ne']
      have hlo := Real.log_nonneg hτ.le
      have hhi := Real.log_le_sub_one_of_pos ht0
      exact abs_le.mpr ⟨by linarith only [hlo, hlp, abs_nonneg τ],
        by linarith only [hhi, hlp]⟩
    have hfac : |(1 / (2 * π)) * Real.log (|τ| / (2 * π))| ≤
        |τ| + Real.log (2 * π) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * π))]
      exact (mul_le_mul_of_nonneg_right ((div_le_one hp).mpr hp1)
        (abs_nonneg _)).trans (by simpa using hlog)
    have hh := abs_sub_abs_le_abs_sub (mu τ)
      ((1 / (2 * π)) * Real.log (|τ| / (2 * π)))
    dsimp [A]
    linarith only [hs, hCe, hfac, hh, abs_nonneg B]

/-- Stirling gives a height-independent density error on the enlarged sampling window. -/
theorem exists_mu_sampling_window_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T τ : ℝ, 2 * π ≤ T → τ ∈ Icc (T/2) (3*T) →
      |mu τ - l T / (2 * π)| ≤ B := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  have hp : 0 < 2 * π := by positivity
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine ⟨|C| + (Real.log 2 + Real.log 3) / (2 * π), by positivity, ?_⟩
  intro T τ hT hτ
  have hT0 : 0 < T := hp.trans_le hT
  have hτ1 : 1 ≤ τ := by linarith only [hτ.1, hT, Real.pi_gt_three]
  have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one hτ1
  have hs := hC τ (by rw [abs_of_pos hτ0]; exact hτ1)
  rw [abs_of_pos hτ0] at hs
  have hτsq : 1 ≤ τ ^ 2 := by nlinarith only [hτ1]
  have hCe : C / τ ^ 2 ≤ |C| := by
    rw [div_le_iff₀ (sq_pos_of_pos hτ0)]
    have hh := mul_le_mul_of_nonneg_left hτsq (abs_nonneg C)
    linarith only [hh, le_abs_self C]
  have hlo := Real.log_le_log (by positivity : 0 < T / 2) hτ.1
  rw [Real.log_div hT0.ne' (by norm_num)] at hlo
  have hhi := Real.log_le_log hτ0 hτ.2
  rw [Real.log_mul (by norm_num) hT0.ne'] at hhi
  have hlogs : |Real.log τ - Real.log T| ≤ Real.log 2 + Real.log 3 := by
    apply abs_le.mpr
    constructor <;> linarith only [hlo, hhi, h2, h3]
  have he : (1 / (2 * π)) * Real.log (τ / (2 * π)) - l T / (2 * π) =
      (Real.log τ - Real.log T) / (2 * π) := by
    rw [l, Real.log_div hτ0.ne' hp.ne', Real.log_div hT0.ne' hp.ne']
    ring
  have hb : |(1 / (2 * π)) * Real.log (τ / (2 * π)) - l T / (2 * π)| ≤
      (Real.log 2 + Real.log 3) / (2 * π) := by
    rw [he, abs_div, abs_of_pos hp]
    exact div_le_div_of_nonneg_right hlogs hp.le
  exact (abs_sub_le (mu τ) ((1 / (2 * π)) * Real.log (τ / (2 * π)))
    (l T / (2 * π))).trans (add_le_add (hs.trans hCe) hb)

private theorem density_baseline_le_height {T : ℝ} (hT : 2 * π ≤ T) :
    0 ≤ l T / (2 * π) ∧ l T / (2 * π) ≤ T := by
  have hp : 0 < 2 * π := by positivity
  have hp1 : 1 ≤ 2 * π := by linarith only [Real.pi_gt_three]
  have hT0 : 0 < T := hp.trans_le hT
  have hratio : 1 ≤ T / (2 * π) := (le_div_iff₀ hp).mpr (by simpa using hT)
  have hl0 : 0 ≤ l T := Real.log_nonneg hratio
  have hl : l T ≤ T := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < T / (2 * π))
    have hd := div_le_self hT0.le hp1
    change Real.log (T / (2 * π)) ≤ T
    linarith only [hh, hd]
  exact ⟨div_nonneg hl0 hp.le, (div_le_self hl0 hp1).trans hl⟩

/-- Outside the enlarged window, the second spectral moment absorbs density growth. -/
private theorem density_error_le_quadratic_tail {A T τ t : ℝ}
    (hA : 0 ≤ A) (hmu : |mu τ| ≤ A + |τ|) (hT : 2 * π ≤ T)
    (ht : t ∈ Icc T (2*T)) (hτ : τ ∉ Icc (T/2) (3*T)) :
    |mu τ - l T / (2 * π)| ≤ (4 * A + 14) / T * (τ - t) ^ 2 := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hT1 : 1 ≤ T := by linarith only [hT, Real.pi_gt_three]
  have hr : T / 2 ≤ |τ - t| := by
    have hh : τ < T / 2 ∨ 3 * T < τ := by
      simpa only [mem_Icc, not_and_or, not_le] using hτ
    rcases hh with hh | hh
    · rw [abs_of_nonpos (by linarith only [ht.1, hh, hT0])]
      linarith only [ht.1, hh]
    · rw [abs_of_nonneg (by linarith only [ht.2, hh, hT0])]
      linarith only [ht.2, hh, hT0]
  have hτabs : |τ| ≤ |τ - t| + 2 * T := by
    have hh := abs_add_le (τ - t) t
    rw [sub_add_cancel, abs_of_nonneg (hT0.le.trans ht.1)] at hh
    linarith only [hh, ht.2]
  have hbase := density_baseline_le_height hT
  have he : |mu τ - l T / (2 * π)| ≤ (A + 3) * T + |τ - t| := by
    have hh := abs_sub_le (mu τ) 0 (l T / (2 * π))
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hbase.1] at hh
    have hAT := mul_le_mul_of_nonneg_left hT1 hA
    nlinarith only [hh, hmu, hτabs, hbase.2, hAT]
  have he' : |mu τ - l T / (2 * π)| ≤ (2 * A + 7) * |τ - t| := by
    have hh := mul_nonneg (show 0 ≤ A + 3 by linarith only [hA])
      (show 0 ≤ 2 * |τ - t| - T by linarith only [hr])
    nlinarith only [he, hh]
  have hm := mul_le_mul he' (show T ≤ 2 * |τ-t| by linarith only [hr])
    hT0.le (by positivity : 0 ≤ (2 * A + 7) * |τ-t|)
  rw [div_mul_eq_mul_div, le_div_iff₀ hT0]
  calc
    _ ≤ ((2 * A + 7) * |τ-t|) * (2 * |τ-t|) := hm
    _ = (4 * A + 14) * |τ-t| ^ 2 := by ring
    _ = _ := by rw [sq_abs]

/-- The quadratic form of the archimedean error relative to its constant density. -/
def normalizedArchimedeanDeviation (P : Params) (T : ℝ) (c : Fin (P.d T) → ℂ) : ℝ :=
  (∫ τ, (mu τ - l T / (2 * π)) * ‖zetaSamplingSynthesis P T c τ‖ ^ 2) /
    (P.a T * P.L T ^ 2)

/-- The actual archimedean density has a full-line `O(1/L)` compression error. -/
theorem exists_normalizedArchimedeanDeviation_le_inverse_bandwidth
    {P : Params} (hP : P.Valid) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 8 * P.w ≤ P.L T → 2 * π ≤ T →
      ∀ c : Fin (P.d T) → ℂ,
      |normalizedArchimedeanDeviation P T c| ≤
        K / (P.a T * P.L T) * ∑ k, ‖c k‖ ^ 2 := by
  obtain ⟨A, hA, hmu⟩ := exists_mu_linear_bound
  obtain ⟨B, hB, hwindow⟩ := exists_mu_sampling_window_bound
  let M : ℝ := 8 + 2 * (P.crho / P.w) ^ 2
  let K : ℝ := 2 * π * B + (4 * A + 14) * M / (2 * π)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro T hwL hT c
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hL : 0 < P.L T := by linarith only [hwL, hP.one_le_w]
  have ha : 0 < P.a T := by
    have hh := (Params.three_quarters_le_b hP hwL).trans (Params.b_le_a hP hwL)
    linarith only [hh]
  let E : ℝ := ∑ k, ‖c k‖ ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let F : ℝ → ℝ := fun τ => ‖zetaSamplingSynthesis P T c τ‖ ^ 2
  let R : ℝ → ℝ := fun τ => ∑ k : Fin (P.d T),
    P.phiHatR T (τ-P.tau T k) ^ 2 * (τ-P.tau T k) ^ 2
  have hFi : Integrable F := integrable_zetaSamplingSynthesis_sq hP hwL c
  have hRi (k : Fin (P.d T)) : Integrable (fun τ =>
      P.phiHatR T (τ-P.tau T k) ^ 2 * (τ-P.tau T k) ^ 2) :=
    (Params.integrable_phiHatR_sq_mul_sq hP hwL).comp_sub_right (P.tau T k)
  have hR : Integrable R := integrable_finsetSum _ fun k _ => hRi k
  have hdom : Integrable (fun τ => B * F τ + (4 * A + 14) / T * E * R τ) :=
    (hFi.const_mul B).add (hR.const_mul _)
  have hpoint (τ : ℝ) : ‖(mu τ - l T / (2 * π)) * F τ‖ ≤
      B * F τ + (4 * A + 14) / T * E * R τ := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ F τ from sq_nonneg _)]
    by_cases hτ : τ ∈ Icc (T/2) (3*T)
    · have hh := mul_le_mul_of_nonneg_right (hwindow T τ hT hτ)
        (show 0 ≤ F τ from sq_nonneg _)
      have hr : 0 ≤ (4 * A + 14) / T * E * R τ := by
        dsimp [R]
        positivity
      exact hh.trans (le_add_of_nonneg_right hr)
    · have hh := mul_le_mul_of_nonneg_left (zetaSamplingSynthesis_sq_le P T c τ)
        (abs_nonneg (mu τ - l T / (2 * π)))
      have ht (k : Fin (P.d T)) : P.tau T k ∈ Icc T (2*T) :=
        (P.toSetting T).tau_mem hL hT0.le (Finset.mem_range.mpr k.isLt)
      have hsum : (∑ k : Fin (P.d T),
          |mu τ - l T / (2 * π)| * P.phiHatR T (τ-P.tau T k) ^ 2) ≤
          (4 * A + 14) / T * R τ := by
        dsimp only [R]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k _
        have hz := mul_le_mul_of_nonneg_right
          (density_error_le_quadratic_tail hA (hmu τ) hT (ht k) hτ)
          (sq_nonneg (P.phiHatR T (τ-P.tau T k)))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hz
      have hh' : |mu τ - l T / (2 * π)| * F τ ≤
          (4 * A + 14) / T * E * R τ := by
        calc
          _ ≤ |mu τ - l T / (2 * π)| *
              (E * ∑ k : Fin (P.d T), P.phiHatR T (τ-P.tau T k) ^ 2) := hh
          _ = E * ∑ k : Fin (P.d T),
              |mu τ - l T / (2 * π)| * P.phiHatR T (τ-P.tau T k) ^ 2 := by
            rw [← Finset.mul_sum]
            ring
          _ ≤ E * ((4 * A + 14) / T * R τ) := mul_le_mul_of_nonneg_left hsum hE
          _ = _ := by ring
      have hbF : 0 ≤ B * F τ := mul_nonneg hB (sq_nonneg _)
      exact hh'.trans (le_add_of_nonneg_left hbF)
  have hmass : (∫ τ, R τ) ≤ (P.d T : ℝ) * M := by
    dsimp only [R]
    rw [integral_finsetSum _ (fun k _ => hRi k)]
    calc
      _ ≤ ∑ _k : Fin (P.d T), M := by
        apply Finset.sum_le_sum
        intro k _
        rw [integral_sub_right_eq_self (fun r => P.phiHatR T r ^ 2 * r ^ 2) (P.tau T k)]
        exact Params.integral_phiHatR_sq_mul_sq_le hP hwL
      _ = _ := by simp
  have hbound : |∫ τ, (mu τ - l T / (2 * π)) * F τ| ≤
      (B * (2 * π * P.L T) + (4 * A + 14) / T * (P.d T) * M) * E := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ∫ τ, B * F τ + (4 * A + 14) / T * E * R τ :=
        norm_integral_le_of_norm_le hdom (Eventually.of_forall hpoint)
      _ = B * (∫ τ, F τ) + (4 * A + 14) / T * E * (∫ τ, R τ) := by
        rw [integral_add (hFi.const_mul _) (hR.const_mul _), integral_const_mul,
          integral_const_mul]
      _ ≤ B * (2 * π * P.L T * E) + (4 * A + 14) / T * E * ((P.d T) * M) :=
        add_le_add (mul_le_mul_of_nonneg_left (integral_zetaSamplingSynthesis_sq_le hP hwL c) hB)
          (mul_le_mul_of_nonneg_left hmass (by positivity))
      _ = _ := by ring
  have hd : (P.d T : ℝ) ≤ P.L T * T / (2 * π) :=
    (P.toSetting T).d_le (mul_nonneg hL.le hT0.le)
  rw [normalizedArchimedeanDeviation, abs_div, abs_of_pos (mul_pos ha (sq_pos_of_pos hL))]
  calc
    _ ≤ ((B * (2 * π * P.L T) + (4 * A + 14) / T * (P.d T) * M) * E) /
        (P.a T * P.L T ^ 2) := div_le_div_of_nonneg_right hbound (by positivity)
    _ ≤ ((B * (2 * π * P.L T) + (4 * A + 14) / T *
        (P.L T * T / (2 * π)) * M) * E) / (P.a T * P.L T ^ 2) := by
      gcongr
    _ = _ := by dsimp [K, E]; field_simp <;> ring

/-- Every fixed bandwidth threshold is eventually attained. -/
theorem zetaSampling_bandwidth_eventually_ge {P : Params} (hP : P.Valid) (R : ℝ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → R ≤ P.L T := by
  refine ⟨2 * π * Real.exp (R / P.lam), fun T hT => ?_⟩
  have hp : 0 < 2 * π := by positivity
  have he : Real.exp (R / P.lam) ≤ T / (2 * π) :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hT)
  have hh := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hh
  have hm := mul_le_mul_of_nonneg_left hh hP.lam_pos.le
  change R ≤ P.lam * Real.log (T / (2 * π))
  simpa only [mul_div_cancel₀ _ hP.lam_pos.ne'] using hm

/-- A fixed multiple of the inverse tapered bandwidth tends to zero. -/
theorem zetaSampling_inverse_bandwidth_uniformly_small {P : Params} (hP : P.Valid)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      8 * P.w ≤ P.L T ∧ 2 * π ≤ T ∧ K / (P.a T * P.L T) ≤ ε := by
  obtain ⟨T₁, hT₁⟩ := zetaSampling_bandwidth_eventually_ge hP (max (8 * P.w) (2*K/ε))
  refine ⟨max T₁ (2 * π), fun T hT => ?_⟩
  have hLbound := hT₁ T ((le_max_left _ _).trans hT)
  have hwL : 8 * P.w ≤ P.L T := (le_max_left _ _).trans hLbound
  have hL : 0 < P.L T := by linarith only [hwL, hP.one_le_w]
  have ha := Params.half_le_a hP hwL
  have ha0 : 0 < P.a T := by linarith only [ha]
  have hAL : K / ε ≤ P.a T * P.L T := by
    calc
      _ = (1/2 : ℝ) * (2*K/ε) := by ring
      _ ≤ (1/2 : ℝ) * P.L T :=
        mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hLbound) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right ha hL.le
  refine ⟨hwL, (le_max_right _ _).trans hT, ?_⟩
  rw [div_le_iff₀ (mul_pos ha0 hL)]
  have hh := (div_le_iff₀ hε).mp hAL
  simpa only [mul_comm] using hh

/-- The actual archimedean error vanishes uniformly on unit coefficient vectors. -/
theorem normalizedArchimedeanDeviation_uniformly_small {P : Params} (hP : P.Valid)
    {ε : ℝ} (hε : 0 < ε) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ c : Fin (P.d T) → ℂ,
      |normalizedArchimedeanDeviation P T c| ≤ ε * ∑ k, ‖c k‖ ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_normalizedArchimedeanDeviation_le_inverse_bandwidth hP
  obtain ⟨T₀, hT₀⟩ := zetaSampling_inverse_bandwidth_uniformly_small hP hK hε
  refine ⟨T₀, fun T hT c => ?_⟩
  obtain ⟨hwL, htπ, he⟩ := hT₀ T hT
  exact (hbound T hwL htπ c).trans (mul_le_mul_of_nonneg_right he (by positivity))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_normalizedArchimedeanDeviation_le_inverse_bandwidth
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.normalizedArchimedeanDeviation_uniformly_small
