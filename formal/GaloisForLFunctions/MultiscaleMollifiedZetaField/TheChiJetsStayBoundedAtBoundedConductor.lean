import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheChiTaperHasItsConductorJetLimits

/-!
# Uniform chi bounds at bounded normalized conductor

A bounded conductor rate bounds the exponential on a unit Cauchy circle.
The normalized Stirling error is uniformly bounded there once the scale
and height are large. This controls intermediate blocks without assuming
that their conductor ratios converge to the upper-height ratio.
-/

open Complex MeasureTheory Metric Set
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem normalized_stirling_exponent_le {R L t : ℝ}
    (hR : 0 ≤ R) (hL : R + 2 ≤ L) (ht : 4 ≤ t) :
    ((R + 1) / L) * (20 * ((R + 1) / L) / t + 52 / t ^ 2) ≤ 9 := by
  have hL0 : 0 < L := by linarith only [hR, hL]
  have ht0 : 0 < t := by linarith only [ht]
  have ha0 : 0 ≤ (R + 1) / L := by positivity
  have ha1 : (R + 1) / L ≤ 1 := (div_le_one hL0).mpr (by linarith only [hL])
  have h20 : 20 * ((R + 1) / L) / t ≤ 5 := by
    apply (div_le_iff₀ ht0).mpr
    linarith only [ha1, ht]
  have h52 : (52 : ℝ) / t ^ 2 ≤ 13 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    have hsq : (16 : ℝ) ≤ t ^ 2 := by nlinarith only [ht]
    linarith only [hsq]
  calc
    _ ≤ 1 * (20 * ((R + 1) / L) / t + 52 / t ^ 2) :=
      mul_le_mul_of_nonneg_right ha1 (by positivity)
    _ ≤ 9 := by linarith only [h20, h52]

/-- Every normalized chi jet is uniformly bounded when its centre and conductor rate are bounded. -/
theorem norm_scaled_holomorphicChiPair_jet_le {R K L t : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hL : R + 3 ≤ L) (ht : 4 ≤ t)
    {C : ℂ} (hC : ‖C‖ ≤ R) (hrate : ‖scaledChiConductorRate L t‖ ≤ K) (j : ℕ) :
    ‖iteratedDeriv j (fun z => holomorphicChiPair (z / (L : ℂ)) t) C‖ ≤
      (j.factorial : ℝ) * Real.exp (9 + K * (R + 1)) := by
  have hL0 : 0 < L := by linarith only [hR, hL]
  have ht0 : 0 < t := by linarith only [ht]
  have hzn {z : ℂ} {a : ℝ} (hz : ‖z - C‖ ≤ a) : ‖z‖ ≤ R + a := by
    have hh := norm_add_le (z - C) C
    rw [sub_add_cancel] at hh
    linarith only [hh, hz, hC]
  have hf : DifferentiableOn ℂ (fun z => holomorphicChiPair (z / (L : ℂ)) t) (ball C 2) := by
    intro z hz
    have hz2 : ‖z - C‖ ≤ 2 := (show ‖z - C‖ < 2 by simpa only [mem_ball, dist_eq_norm] using hz).le
    have hn : ‖z / (L : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hL0.le]
      exact (div_le_one hL0).mpr ((hzn hz2).trans (by linarith only [hL]))
    have him : 2 * |(z / (L : ℂ)).im| < t := by
      have hh := (Complex.abs_im_le_norm _).trans hn
      linarith only [hh, ht]
    have he : DifferentiableAt ℂ (scaledChiConductorError L t) z :=
      (analyticAt_scaledChiConductorError ht0 him).differentiableAt
    have hg : DifferentiableAt ℂ (fun w => Complex.exp (scaledChiConductorRate L t * w)) z := by fun_prop
    have hid : (fun w => holomorphicChiPair (w / (L : ℂ)) t) =
        fun w => Complex.exp (scaledChiConductorRate L t * w) +
          scaledChiConductorError L t w * Complex.exp (scaledChiConductorRate L t * w) :=
      funext (scaled_holomorphicChiPair_eq L ht0)
    rw [hid]
    exact (hg.add (he.mul hg)).differentiableWithinAt
  have hb : ∀ z ∈ sphere C 1,
      ‖holomorphicChiPair (z / (L : ℂ)) t‖ ≤ Real.exp (9 + K * (R + 1)) := by
    intro z hz
    have hz1 : ‖z - C‖ ≤ 1 := by simpa only [mem_sphere, dist_eq_norm] using (show dist z C = 1 from hz).le
    have hzR := hzn hz1
    have herror : ‖scaledChiConductorError L t z‖ ≤ Real.exp 9 - 1 := by
      have hh := norm_scaledChiConductorError_jet_le (R := R + 1) (L := L) (by positivity)
        (by linarith only [hL]) ht hzR 0
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hh
      exact hh.trans (sub_le_sub_right (Real.exp_le_exp.mpr
        (normalized_stirling_exponent_le (by positivity) (by linarith only [hL]) ht)) 1)
    have hexp : ‖Complex.exp (scaledChiConductorRate L t * z)‖ ≤ Real.exp (K * (R + 1)) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      exact (Complex.re_le_norm _).trans (by
        rw [norm_mul]
        exact mul_le_mul hrate hzR (norm_nonneg _) hK)
    rw [scaled_holomorphicChiPair_eq L ht0 z]
    calc
      _ ≤ ‖Complex.exp (scaledChiConductorRate L t * z)‖ +
          ‖scaledChiConductorError L t z * Complex.exp (scaledChiConductorRate L t * z)‖ := norm_add_le _ _
      _ ≤ Real.exp (K * (R + 1)) + (Real.exp 9 - 1) * Real.exp (K * (R + 1)) := by
        rw [norm_mul]
        exact add_le_add hexp (mul_le_mul herror hexp (norm_nonneg _)
          (sub_nonneg.mpr (Real.one_le_exp (by norm_num))))
      _ = _ := by rw [Real.exp_add]; ring
  have hsub : closedBall C 1 ⊆ ball C 2 := by
    intro z hz
    exact lt_of_le_of_lt hz (by norm_num : (1 : ℝ) < 2)
  simpa only [one_pow, div_one] using
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j zero_lt_one (hf.diffContOnCl_ball hsub) hb

/-- A bounded conductor rate gives the same uniform bound after taper integration. -/
theorem norm_normalizedChiTaperJet_le {R K L p q η u : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hL : R + 3 ≤ L) (hu : 0 < u) (huR : u ≤ R)
    (hη : 0 < η) (hp : 4 ≤ p - η) (hpq : p ≤ q) (hu20 : u / L ≤ 1 / 20)
    (hrate : ∀ t ∈ Icc (p - η) (q + η), ‖scaledChiConductorRate L t‖ ≤ K) (j : ℕ) :
    ‖normalizedChiTaperJet L p q η u j‖ ≤
      (q - p + 2 * η) * ((j.factorial : ℝ) * Real.exp (9 + K * (R + 1))) := by
  have hL0 : 0 < L := by linarith only [hR, hL]
  let D : ℝ := (j.factorial : ℝ) * Real.exp (9 + K * (R + 1))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hW : Integrable (blockWindow p q η) volume :=
    (contDiff_blockWindow p q η).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_blockWindow hη)
  rw [normalizedChiTaperJet_eq_integral hL0 hu hη hp hu20]
  calc
    _ ≤ ∫ t, blockWindow p q η t * D := by
      apply norm_integral_le_of_norm_le (hW.mul_const D)
      filter_upwards with t
      by_cases ht : t ∈ Icc (p - η) (q + η)
      · rw [norm_mul, norm_blockWindowC_eq]
        exact mul_le_mul_of_nonneg_left (norm_scaled_holomorphicChiPair_jet_le hR hK hL
          (hp.trans ht.1) (by simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using huR)
          (hrate t ht) j) (blockWindow_nonneg p q η t)
      · rw [blockWindowC_eq_zero hη ht, zero_mul, norm_zero]
        exact mul_nonneg (blockWindow_nonneg p q η t) hD
    _ = (∫ t, blockWindow p q η t) * D := integral_mul_const D _
    _ ≤ _ := mul_le_mul_of_nonneg_right (integral_blockWindow_le hη hpq) hD

end GaloisForLFunctions.MultiscaleMollifiedZetaField
