import GaloisForLFunctions.RHTower.SteinhausGaussianIndependentCutoffMean
import GaloisForLFunctions.RHTower.SteinhausFullGaussianEndpointEnvelope

open Complex Filter Topology Set Finset MeasureTheory
noncomputable section
namespace RHTower
open SteinhausModel

/-- Two endpoint limits bound the positive normalized Gaussian mass uniformly
throughout a closed abscissa band. -/
theorem exists_normalizedGaussianAbsoluteMass_band_bound
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop, 0 < R ∧
      ∀ σ ∈ Icc a b, normalizedGaussianAbsoluteMass σ R ≤ C := by
  let La := (Complex.exp ((a : ℂ) ^ 2) / (a : ℂ)).re
  let Lb := (Complex.exp ((b : ℂ) ^ 2) / (b : ℂ)).re
  have hA : ∀ᶠ R : ℝ in atTop, normalizedGaussianAbsoluteMass a R < La + 1 :=
    (tendsto_normalizedGaussianAbsoluteMass ha (hab.trans_lt hb)).eventually
      (gt_mem_nhds (by dsimp only [La]; linarith))
  have hB : ∀ᶠ R : ℝ in atTop, normalizedGaussianAbsoluteMass b R < Lb + 1 :=
    (tendsto_normalizedGaussianAbsoluteMass (ha.trans_le hab) hb).eventually
      (gt_mem_nhds (by dsimp only [Lb]; linarith))
  refine ⟨|La| + |Lb| + 2, by positivity, ?_⟩
  filter_upwards [hA, hB, eventually_gt_atTop (0 : ℝ)] with R hAR hBR hR
  refine ⟨hR, fun σ hσ => ?_⟩
  have h := normalizedGaussianAbsoluteMass_le_endpoints hR hσ.1 hσ.2
  linarith [le_abs_self La, le_abs_self Lb]

/-- The exact normalized Gaussian Abel cost is dominated by its actual positive
coefficient mass, uniformly over every independent polynomial cutoff. -/
theorem steinhausGaussianAbelSqrtCost_div_le_absoluteMass
    (β : ℝ) {N : ℕ} (hN : 0 < N) (L : ℕ) :
    (steinhausGaussianWeight β 1 N (L + 1) * Real.sqrt L +
      (∑ n ∈ Finset.Icc 1 L, (steinhausGaussianWeight β 1 N n -
        steinhausGaussianWeight β 1 N (n + 1)) * Real.sqrt n)) /
          (N : ℝ) ^ (1 / 2 - β) ≤ normalizedGaussianAbsoluteMass (1 / 2 - β) N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let d : ℝ := 1 / 2 - β
  let u : ℕ → ℝ := fun n =>
    ‖((n + 1 : ℕ) : ℂ) ^ ((d : ℂ) - 1) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / N)‖ * (N : ℝ) ^ (-d)
  have hu : Summable u := summable_normalizedGaussianAbsoluteTerms d hNR
  have heq : normalizedGaussianAbsoluteMass d N = ∑' n : ℕ, u n :=
    (tsum_mul_right).symm
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 L) :
      steinhausGaussianWeight β 1 N n * (Real.sqrt n - Real.sqrt (n - 1 : ℕ)) ≤
        ‖(n : ℂ) ^ ((d : ℂ) - 1) * smoothAFECutoff ((n : ℝ) / N)‖ := by
    have hn1 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    calc
      _ ≤ steinhausGaussianWeight β 1 N n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (steinhausSqrtIncrement_le n hn1)
          (steinhausGaussianWeight_nonneg β one_pos hN hn1)
      _ = (n : ℝ) ^ (d - 1) * (smoothAFECutoff ((n : ℝ) / N)).re := by
        simp only [steinhausGaussianWeight, one_mul]
        rw [mul_right_comm, ← Real.rpow_add hnR]
        congr 1
        dsimp only [d]
        ring_nf
      _ ≤ (n : ℝ) ^ (d - 1) * ‖smoothAFECutoff ((n : ℝ) / N)‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (Real.rpow_nonneg hnR.le _)
      _ = _ := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, Complex.sub_re,
          Complex.ofReal_re, Complex.one_re]
  rw [steinhausAbelSqrtCost_eq]
  change (∑ n ∈ Finset.Icc 1 L, _) / (N : ℝ) ^ d ≤ normalizedGaussianAbsoluteMass d N
  rw [div_eq_mul_inv, ← Real.rpow_neg hNR.le, heq]
  refine (mul_le_mul_of_nonneg_right (sum_le_sum hterm) (Real.rpow_nonneg hNR.le (-d))).trans ?_
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right, Finset.sum_mul]
  have hh := hu.sum_le_tsum (range L) (fun n _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hNR.le (-d)))
  simpa only [u, Nat.add_comm] using hh

/-- A single first-mean threshold works for every exponent in a compact
subcritical band and every independent polynomial cutoff. -/
theorem eventually_integral_norm_steinhausGaussianWeight_band_cutoff_le
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ β ∈ Icc a b, ∀ L : ℕ,
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 L, (steinhausGaussianWeight β 1 N n : ℂ) * X n ω‖ ∂steinhausMeasure) /
        (N : ℝ) ^ (1 / 2 - β) ≤ δ := by
  obtain ⟨K, hK, hmass⟩ := exists_normalizedGaussianAbsoluteMass_band_bound
    (a := 1 / 2 - b) (b := 1 / 2 - a) (by linarith) (by linarith) (by linarith)
  let ε : ℝ := δ / (2 * K)
  have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hK)
  obtain ⟨C, hC, hmean⟩ := exists_steinhausSummatoryMean_sqrt_envelope hε
  have htail : Tendsto (fun N : ℕ => C / (N : ℝ) ^ (1 / 2 - b)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop (by linarith : 0 < 1 / 2 - b)).comp tendsto_natCast_atTop_atTop)
  filter_upwards [htail.eventually (gt_mem_nhds (half_pos hδ)),
    tendsto_natCast_atTop_atTop.eventually hmass, eventually_ge_atTop (1 : ℕ)] with N htailN hmassN hN
  intro β hβ L
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR : (0 : ℝ) < N := zero_lt_one.trans_le hNR1
  have hp : 0 < (N : ℝ) ^ (1 / 2 - β) := Real.rpow_pos_of_pos hNR _
  have hcost : steinhausGaussianWeight β 1 N (L + 1) * Real.sqrt L +
      (∑ n ∈ Finset.Icc 1 L, (steinhausGaussianWeight β 1 N n -
        steinhausGaussianWeight β 1 N (n + 1)) * Real.sqrt n) ≤ K * (N : ℝ) ^ (1 / 2 - β) := by
    apply (div_le_iff₀ hp).mp
    exact (steinhausGaussianAbelSqrtCost_div_le_absoluteMass β hN L).trans
      (hmassN.2 _ ⟨by linarith [hβ.2], by linarith [hβ.1]⟩)
  have hw1 : steinhausGaussianWeight β 1 N 1 ≤ 1 := by
    simpa using steinhausGaussianWeight_le_rpow β one_pos hN (by norm_num : 0 < 1)
  have hupper : (∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
      (steinhausGaussianWeight β 1 N n : ℂ) * X n ω‖ ∂steinhausMeasure) ≤
      C + ε * (K * (N : ℝ) ^ (1 / 2 - β)) := by
    refine (integral_norm_steinhausWeightedSummatory_le_envelope
      (steinhausGaussianWeight β 1 N) L
      (fun n hn => steinhausGaussianWeight_nonneg β one_pos hN hn)
      (fun n hn => steinhausGaussianWeight_succ_le (ha.le.trans hβ.1) one_pos hN hn) hmean).trans ?_
    exact add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hcost hε.le)
  have hpow : (N : ℝ) ^ (1 / 2 - b) ≤ (N : ℝ) ^ (1 / 2 - β) :=
    Real.rpow_le_rpow_of_exponent_le hNR1 (by linarith [hβ.2])
  have htailβ : C / (N : ℝ) ^ (1 / 2 - β) ≤ C / (N : ℝ) ^ (1 / 2 - b) :=
    div_le_div_of_nonneg_left hC (Real.rpow_pos_of_pos hNR _) hpow
  have halgebra : (C + ε * (K * (N : ℝ) ^ (1 / 2 - β))) / (N : ℝ) ^ (1 / 2 - β) =
      C / (N : ℝ) ^ (1 / 2 - β) + δ / 2 := by
    dsimp only [ε]
    field_simp [hp.ne', hK.ne']
  have h := div_le_div_of_nonneg_right hupper hp.le
  rw [halgebra] at h
  linarith

end RHTower
