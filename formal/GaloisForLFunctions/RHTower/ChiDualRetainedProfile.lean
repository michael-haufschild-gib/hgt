import GaloisForLFunctions.RHTower.ChiDualMaskedMeanSquare

/-!
# Physical mean-square profile of the retained dual background

Subtract the exact complete free-prime mask from the full literal dual block.
The full-height spatial profile and sharp masked quadratic estimate control both
terms. This gives actual retained-background error with rate
m^-2 + (1+log H)/log(m^10), uniformly in each fixed-disc point and every eligible
block/cofactor budget. Source measurability and integrability are derived.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower



/-- The actual retained background inherits the scalar spatial profile after
charging the complete free-prime mask's physical quadratic energy. The estimate
is uniform in each compact-disc point, with no target or recurrence assumption. -/
theorem exists_chiDual_retained_block_mean_square_profile
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      ∀ H : ℕ, 1 ≤ H → H ^ 2 ≤ m ^ 10 →
      IntegrableOn (fun t => ‖(∑ n ∈ Finset.Icc A B \ primeWindowSupported (Finset.Icc A B) (m ^ 10) H,
        smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10) * zetaChiDualInteriorAtom s n t) -
          chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2)
        (Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10)) volume ∧
      ((∫ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10),
        ‖(∑ n ∈ Finset.Icc A B \ primeWindowSupported (Finset.Icc A B) (m ^ 10) H,
          smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10) * zetaChiDualInteriorAtom s n t) -
            chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2) / (m : ℝ) ^ 10) ≤
        C * (1 / (m : ℝ) ^ 2 + (1 + Real.log H) / Real.log ((m : ℝ) ^ 10)) := by
  obtain ⟨C₀, hC₀, hprofile⟩ := exists_chiDual_integer_block_mean_square_profile c hr hc0 hc1
  obtain ⟨C₁, hC₁, hmask⟩ := exists_chiDual_prime_mask_mean_square_log_bound c hr hc0 hc1
  refine ⟨2 * (C₀ + C₁), by positivity, ?_⟩
  have hp : Tendsto (fun m : ℕ => m ^ 10) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [hprofile, hp.eventually hmask, eventually_ge_atTop (2 : ℕ)] with m hprofile hmask hm2
  norm_num only [Nat.cast_pow] at hmask
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hm0 : (0 : ℝ) < m := by linarith only [hm2R]
  let N : ℝ := (m : ℝ) ^ 10
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hN1 : 1 < N := one_lt_pow₀ (by linarith only [hm2R] : (1 : ℝ) < m) (by decide)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  intro s hs A B hA hB hAB H hH hHN
  obtain ⟨hX, hXmean⟩ := hprofile s hs A B hA hB hAB
  let S := Finset.Icc A B
  let F := primeWindowSupported S (m ^ 10) H
  let R := S \ F
  let Y : ℝ → ℂ := fun t => ∑ n ∈ F, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t
  let V : ℝ → ℂ := fun t => ∑ n ∈ R, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t
  let P := chiDualSpatialStepProfile N A B
  let X : ℝ → ℂ := fun t => chiDualIntegerBlock s N A B t - P t
  let W := Icc N (2 * N)
  have hgeom (n : ℕ) (hn : n ∈ S) : (m : ℝ) ^ 10 / 5 ≤ n ∧ (n : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 := by
    obtain ⟨hnA, hnB⟩ := Finset.mem_Icc.mp hn
    have hlo : (A : ℝ) ≤ n := by exact_mod_cast hnA
    have hhi : (n : ℝ) ≤ B := by exact_mod_cast hnB
    exact ⟨hA.trans hlo, hhi.trans hB⟩
  have hy := hmask s hs S hgeom H hH hHN
  rw [intervalIntegral.integral_of_le (by linarith only [hN0]), ← integral_Icc_eq_integral_Ioc] at hy
  have hYmean : (∫ t in W, ‖Y t‖ ^ 2) / N ≤ C₁ * (1 + Real.log H) / Real.log N := by
    have h0 : (∫ t in W, ‖Y t‖ ^ 2) ≤ (C₁ * (1 + Real.log H) * N) / Real.log N :=
      (le_div_iff₀ hlog).mpr hy
    calc
      _ ≤ ((C₁ * (1 + Real.log H) * N) / Real.log N) / N :=
        div_le_div_of_nonneg_right h0 hN0.le
      _ = _ := by field_simp
  have hdist : dist s c ≤ r := Metric.mem_closedBall.mp hs
  have hre : |s.re - c.re| ≤ dist s c := by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
  have hs1 : s.re < 1 := by
    have hl := (abs_le.mp (hre.trans hdist)).2
    linarith only [hl, hc1]
  have hYcont : Continuous Y := continuous_chiDualMaskedBlock hs1 N F
  have hVcont : Continuous V := continuous_chiDualMaskedBlock hs1 N R
  have hY : IntegrableOn (fun t => ‖Y t‖ ^ 2) W volume := (hYcont.norm.pow 2).integrableOn_Icc
  have hPmeas : AEStronglyMeasurable P (volume.restrict W) := by
    have hc : ContinuousOn (fun t : ℝ => smoothAFECutoff ((t / (2 * Real.pi)) / N)) W := by
      intro t ht
      have ht0 : 0 < (t / (2 * Real.pi)) / N :=
        div_pos (div_pos (hN0.trans_le ht.1) (by positivity)) hN0
      exact (ContinuousAt.comp (f := fun u : ℝ => (u / (2 * Real.pi)) / N) (x := t)
        (hasDerivAt_smoothAFECutoff ht0).continuousAt (by fun_prop)).continuousWithinAt
    exact (hc.aestronglyMeasurable measurableSet_Icc).indicator measurableSet_Icc
  have hVmeas : AEStronglyMeasurable (fun t => ‖V t - P t‖ ^ 2) (volume.restrict W) :=
    ((hVcont.aestronglyMeasurable.sub hPmeas).norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hsum (t : ℝ) : V t + Y t = chiDualIntegerBlock s N A B t :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  have heq (t : ℝ) : V t - P t = X t - Y t := by
    dsimp only [X]
    rw [← hsum]
    ring
  have hpoint (t : ℝ) : ‖V t - P t‖ ^ 2 ≤ 2 * ‖X t‖ ^ 2 + 2 * ‖Y t‖ ^ 2 := by
    rw [heq]
    have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (X t) (Y t)) 2
    nlinarith only [hb, sq_nonneg (‖X t‖ - ‖Y t‖)]
  have hG : IntegrableOn (fun t => 2 * ‖X t‖ ^ 2 + 2 * ‖Y t‖ ^ 2) W volume :=
    Integrable.fun_add (hX.const_mul 2) (hY.const_mul 2)
  have hV : IntegrableOn (fun t => ‖V t - P t‖ ^ 2) W volume := by
    apply hG.mono' hVmeas
    exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint t)
  refine ⟨hV, ?_⟩
  have hb := setIntegral_mono hV hG hpoint
  rw [integral_add (hX.const_mul 2) (hY.const_mul 2), integral_const_mul, integral_const_mul] at hb
  have hi := div_le_div_of_nonneg_right hb hN0.le
  change (∫ t in W, ‖V t - P t‖ ^ 2) / N ≤ _
  apply hi.trans
  have hratio : 0 ≤ (1 + Real.log H) / Real.log N :=
    div_nonneg (by linarith only [Real.log_natCast_nonneg H]) hlog.le
  calc
    _ = 2 * ((∫ t in W, ‖X t‖ ^ 2) / N) + 2 * ((∫ t in W, ‖Y t‖ ^ 2) / N) := by ring
    _ ≤ 2 * (C₀ / (m : ℝ) ^ 2) + 2 * (C₁ * (1 + Real.log H) / Real.log N) :=
      add_le_add (mul_le_mul_of_nonneg_left hXmean (by norm_num))
        (mul_le_mul_of_nonneg_left hYmean (by norm_num))
    _ = (2 * C₀) * (1 / (m : ℝ) ^ 2) + (2 * C₁) * ((1 + Real.log H) / Real.log N) := by ring
    _ ≤ (2 * (C₀ + C₁)) * (1 / (m : ℝ) ^ 2) + (2 * (C₀ + C₁)) * ((1 + Real.log H) / Real.log N) :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith only [hC₁]) (by positivity))
        (mul_le_mul_of_nonneg_right (by linarith only [hC₀]) hratio)
    _ = _ := by ring


end RHTower
