import GaloisForLFunctions.RHTower.CCM.CCMActualHeadExteriorCosineSuperoscillation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEnergyContinuity
import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Actual negative-energy escape for exterior packets

The literal zero-effective-frequency exterior packet converges locally to one
while its average against the normalized actual ground density is exactly zero.
The full corrected symbol therefore exports almost one unit of negative energy
beyond every fixed frequency window. No sign of the actual Weil ground energy
is assumed or concluded. Gamma, polar, and all visible prime terms are retained.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace RHTower

/-- Uniform-on-compacts control of the literal packet, independent of its degree. -/
theorem abs_exteriorSuperoscillationCosineSum_le_exp
    (H δ c x : ℝ) (N : ℕ) :
    |exteriorSuperoscillationCosineSum H δ c x N| ≤ Real.exp |c * δ * x| := by
  rw [exteriorSuperoscillationCosineSum_eq_re]
  apply (Complex.abs_re_le_norm _).trans
  unfold exteriorSuperoscillationPacket
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_pow]
  by_cases hN : N = 0
  · subst N
    simpa using Real.one_le_exp (abs_nonneg (c * δ * x))
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  let y : ℝ := -δ * x / N
  have harg : ((((-δ * x : ℝ) : ℂ) * I) / (N : ℂ)) = I * (y : ℂ) := by
    dsimp only [y]
    push_cast
    ring
  rw [harg]
  have hb : ‖((1 - c : ℝ) : ℂ) + (c : ℂ) * Complex.exp (I * (y : ℂ))‖ ≤
      Real.exp (|c| * |y|) := by
    have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := y)
    rw [Real.norm_eq_abs] at he
    calc
      _ = ‖1 + (c : ℂ) * (Complex.exp (I * (y : ℂ)) - 1)‖ := by
        congr 1
        push_cast
        ring
      _ ≤ ‖(1 : ℂ)‖ + ‖(c : ℂ) * (Complex.exp (I * (y : ℂ)) - 1)‖ := norm_add_le _ _
      _ = 1 + |c| * ‖Complex.exp (I * (y : ℂ)) - 1‖ := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 + |c| * |y| := by gcongr
      _ ≤ Real.exp (|c| * |y|) := by linarith [Real.add_one_le_exp (|c| * |y|)]
  calc
    _ ≤ (Real.exp (|c| * |y|)) ^ N := by gcongr
    _ = Real.exp |c * δ * x| := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp only [y]
      rw [abs_div, abs_mul, abs_neg, abs_of_pos hn, abs_mul, abs_mul]
      field_simp

private def groundFourier (a : SuzukiPositiveAperture) : SoninL2 :=
  ccmArchimedeanWeightedToL2 (ccmRestrictedWeilNormalizedGroundFormVector a).1

private theorem ground_fourier_eq (a : SuzukiPositiveAperture) :
    fourierUnitary (ccmArchimedeanFormToAperture a
      (ccmRestrictedWeilNormalizedGroundFormVector a) : SoninL2) = groundFourier a := by
  rw [ccmArchimedeanFormToAperture_val_eq_fourierUnitary_symm,
    fourierUnitary.apply_symm_apply]
  rfl

/-- Spectral density of the actual normalized restricted Weil ground. -/
def ccmExteriorEscapeGroundDensity (a : SuzukiPositiveAperture) (x : ℝ) : ℝ :=
  ‖groundFourier a x‖ ^ 2

private theorem density_nonneg (a : SuzukiPositiveAperture) (x : ℝ) :
    0 ≤ ccmExteriorEscapeGroundDensity a x := sq_nonneg _

private theorem density_integrable (a : SuzukiPositiveAperture) :
    Integrable (ccmExteriorEscapeGroundDensity a) := integrable_norm_sq _

theorem integral_ccmExteriorEscapeGroundDensity (a : SuzukiPositiveAperture) :
    (∫ x, ccmExteriorEscapeGroundDensity a x) = 1 := by
  change (∫ x, ‖groundFourier a x‖ ^ 2) = 1
  rw [← norm_sq_eq_integral, ← ground_fourier_eq, fourierUnitary.norm_map]
  have hn := norm_ccmRestrictedWeilNormalizedGroundFormVector_embedding a
  change ‖(ccmArchimedeanFormToAperture a
    (ccmRestrictedWeilNormalizedGroundFormVector a) : SoninL2)‖ = 1 at hn
  rw [hn, one_pow]

/-- The literal exterior packet whose effective frequency is zero. -/
def ccmExteriorEscapePacket (a : SuzukiPositiveAperture) (N : ℕ) (x : ℝ) : ℝ :=
  exteriorSuperoscillationCosineSum (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 x N

/-- Complete arithmetic symbol, with Gamma, polar term, and every visible prime power retained. -/
def ccmExteriorEscapeCorrectedSymbol (a : SuzukiPositiveAperture) (N : ℕ) (x : ℝ) : ℝ :=
  correctedCCMSymbol a.1 (2 * Real.pi * x) + ccmExteriorEscapePacket a N x

private theorem packet_integrable (a : SuzukiPositiveAperture) (N : ℕ) :
    Integrable (fun x => ccmExteriorEscapePacket a N x * ccmExteriorEscapeGroundDensity a x) := by
  let f := ccmArchimedeanFormToAperture a (ccmRestrictedWeilNormalizedGroundFormVector a)
  have hp := integrable_ccmActualHeadExteriorCosineMeasureGauge_mul_density (f : SoninL2)
    (exteriorSuperoscillationPositiveMeasure (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 N)
  have hn := integrable_ccmActualHeadExteriorCosineMeasureGauge_mul_density (f : SoninL2)
    (exteriorSuperoscillationNegativeMeasure (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 N)
  rw [show fourierUnitary (f : SoninL2) = groundFourier a from ground_fourier_eq a] at hp hn
  refine (hp.sub hn).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  rw [← sub_mul, exteriorCosineMeasureGauge_sub_eq_cosineSum]
  rfl

theorem integral_ccmExteriorEscapePacket_mul_groundDensity (a : SuzukiPositiveAperture) (N : ℕ) :
    (∫ x, ccmExteriorEscapePacket a N x * ccmExteriorEscapeGroundDensity a x) = 0 := by
  have h := integral_exteriorSuperoscillationCosineSum_mul_density_eq_zero a
    (ccmArchimedeanFormToAperture a (ccmRestrictedWeilNormalizedGroundFormVector a))
    (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 N
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) a.property.le)
    (by ring_nf; exact le_rfl)
  rw [ground_fourier_eq] at h
  exact h

private theorem base_integrable (a : SuzukiPositiveAperture) :
    Integrable (fun x => correctedCCMSymbol a.1 (2 * Real.pi * x) *
      ccmExteriorEscapeGroundDensity a x) :=
  integrable_correctedCCMSymbol_mul_actualHeadDensity a
    (ccmRestrictedWeilNormalizedGroundFormVector a)

private theorem corrected_integrable (a : SuzukiPositiveAperture) (N : ℕ) :
    Integrable (fun x => ccmExteriorEscapeCorrectedSymbol a N x *
      ccmExteriorEscapeGroundDensity a x) := by
  refine ((base_integrable a).add (packet_integrable a N)).congr
    (Eventually.of_forall fun x => ?_)
  change correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x +
    ccmExteriorEscapePacket a N x * ccmExteriorEscapeGroundDensity a x =
    (correctedCCMSymbol a.1 (2 * Real.pi * x) + ccmExteriorEscapePacket a N x) *
      ccmExteriorEscapeGroundDensity a x
  ring

private theorem corrected_average (a : SuzukiPositiveAperture) (N : ℕ) :
    (∫ x, ccmExteriorEscapeCorrectedSymbol a N x * ccmExteriorEscapeGroundDensity a x) =
      ∫ x, correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x := by
  simp_rw [ccmExteriorEscapeCorrectedSymbol, add_mul]
  rw [integral_add (base_integrable a) (packet_integrable a N),
    integral_ccmExteriorEscapePacket_mul_groundDensity, add_zero]

private theorem packet_limit (a : SuzukiPositiveAperture) (x : ℝ) :
    Tendsto (fun N => ccmExteriorEscapePacket a N x) atTop (𝓝 1) := by
  have h := tendsto_exteriorSuperoscillationCosineSum
    (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 x
  have he : 8 * Real.pi * a.1 - 2 * (4 * Real.pi * a.1) = 0 := by ring
  simpa only [ccmExteriorEscapePacket, he, zero_mul, Real.cos_zero] using h

private theorem packet_compact_limit (a : SuzukiPositiveAperture) (R : ℝ) :
    Tendsto (fun N => ∫ x in Icc (-R) R,
      ccmExteriorEscapePacket a N x * ccmExteriorEscapeGroundDensity a x)
      atTop (𝓝 (∫ x in Icc (-R) R, ccmExteriorEscapeGroundDensity a x)) := by
  let C := Real.exp (|2 * (4 * Real.pi * a.1)| * |R|)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (-R) R))
    (F := fun N x => ccmExteriorEscapePacket a N x * ccmExteriorEscapeGroundDensity a x)
    (f := ccmExteriorEscapeGroundDensity a)
    (fun x => C * ccmExteriorEscapeGroundDensity a x)
    (fun N => (packet_integrable a N).aestronglyMeasurable.restrict)
    ((density_integrable a).const_mul C).integrableOn
    (fun N => ?_) (Eventually.of_forall fun x => ?_)
  · exact hlim
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have habs : |x| ≤ |R| := abs_le.mpr
      ⟨(neg_le_neg (le_abs_self R)).trans hx.1, hx.2.trans (le_abs_self R)⟩
    have hp := abs_exteriorSuperoscillationCosineSum_le_exp
      (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 x N
    have hpc : |ccmExteriorEscapePacket a N x| ≤ C := by
      apply hp.trans
      apply Real.exp_le_exp.mpr
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg a x)]
    exact mul_le_mul_of_nonneg_right hpc (density_nonneg a x)
  · simpa only [one_mul] using (packet_limit a x).mul_const (ccmExteriorEscapeGroundDensity a x)

/-- Exact signed tail limit: every locally reproduced unit of mass is exported with negative sign. -/
theorem tendsto_ccmExteriorEscape_signed_tail (a : SuzukiPositiveAperture) (R : ℝ) :
    Tendsto (fun N => ∫ x in (Icc (-R) R)ᶜ,
      ccmExteriorEscapeCorrectedSymbol a N x * ccmExteriorEscapeGroundDensity a x)
      atTop (𝓝 ((∫ x in (Icc (-R) R)ᶜ,
        correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x) -
          ∫ x in Icc (-R) R, ccmExteriorEscapeGroundDensity a x)) := by
  have hB : Tendsto (fun _ : ℕ => ∫ x, correctedCCMSymbol a.1 (2 * Real.pi * x) *
      ccmExteriorEscapeGroundDensity a x) atTop
      (𝓝 (∫ x, correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x)) :=
    tendsto_const_nhds
  have hC : Tendsto (fun _ : ℕ => ∫ x in Icc (-R) R,
      correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x) atTop
      (𝓝 (∫ x in Icc (-R) R,
        correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x)) :=
    tendsto_const_nhds
  have h := hB.sub (hC.add (packet_compact_limit a R))
  have he (N : ℕ) :
      (∫ x in (Icc (-R) R)ᶜ, ccmExteriorEscapeCorrectedSymbol a N x *
        ccmExteriorEscapeGroundDensity a x) =
      (∫ x, correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x) -
        ((∫ x in Icc (-R) R, correctedCCMSymbol a.1 (2 * Real.pi * x) *
          ccmExteriorEscapeGroundDensity a x) +
        ∫ x in Icc (-R) R, ccmExteriorEscapePacket a N x * ccmExteriorEscapeGroundDensity a x) := by
    rw [setIntegral_compl measurableSet_Icc (corrected_integrable a N), corrected_average]
    simp_rw [ccmExteriorEscapeCorrectedSymbol, add_mul]
    rw [integral_add (base_integrable a).integrableOn (packet_integrable a N).integrableOn]
  simpa only [← he, setIntegral_compl measurableSet_Icc (base_integrable a), sub_add_eq_sub_sub] using h

/-- Negative part of the complete corrected symbol, measured by actual ground Fourier mass. -/
def ccmExteriorEscapeNegativeTailEnergy (a : SuzukiPositiveAperture) (R : ℝ) (N : ℕ) : ℝ :=
  ∫ x in (Icc (-R) R)ᶜ, max (-ccmExteriorEscapeCorrectedSymbol a N x) 0 *
    ccmExteriorEscapeGroundDensity a x

private theorem negative_density_integrable (a : SuzukiPositiveAperture) (N : ℕ) :
    Integrable (fun x => max (-ccmExteriorEscapeCorrectedSymbol a N x) 0 *
      ccmExteriorEscapeGroundDensity a x) := by
  have hi := ((corrected_integrable a N).norm.sub (corrected_integrable a N)).div_const 2
  refine hi.congr (Eventually.of_forall fun x => ?_)
  change (‖ccmExteriorEscapeCorrectedSymbol a N x * ccmExteriorEscapeGroundDensity a x‖ -
    ccmExteriorEscapeCorrectedSymbol a N x * ccmExteriorEscapeGroundDensity a x) / 2 =
    max (-ccmExteriorEscapeCorrectedSymbol a N x) 0 * ccmExteriorEscapeGroundDensity a x
  rw [Real.norm_eq_abs]
  by_cases h : 0 ≤ ccmExteriorEscapeCorrectedSymbol a N x
  · rw [abs_of_nonneg (mul_nonneg h (density_nonneg a x)), max_eq_right (neg_nonpos.mpr h)]
    ring
  · have hn := le_of_not_ge h
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hn (density_nonneg a x)),
      max_eq_left (neg_nonneg.mpr hn)]
    ring

private theorem neg_signed_tail_le (a : SuzukiPositiveAperture) (R : ℝ) (N : ℕ) :
    -(∫ x in (Icc (-R) R)ᶜ, ccmExteriorEscapeCorrectedSymbol a N x *
      ccmExteriorEscapeGroundDensity a x) ≤ ccmExteriorEscapeNegativeTailEnergy a R N := by
  rw [← integral_neg]
  apply integral_mono (corrected_integrable a N).neg.integrableOn
    (negative_density_integrable a N).integrableOn
  intro x
  change -(ccmExteriorEscapeCorrectedSymbol a N x * ccmExteriorEscapeGroundDensity a x) ≤ _
  rw [← neg_mul]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (density_nonneg a x)

private theorem interval_exhaustion {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun m : ℕ => ∫ x in Icc (-(m : ℝ)) m, f x) atTop (𝓝 (∫ x, f x)) := by
  have hcover : (⋃ m : ℕ, Icc (-(m : ℝ)) m) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨m, hm⟩ := exists_nat_gt |x|
    exact ⟨m, by constructor <;> linarith [neg_abs_le x, le_abs_self x]⟩
  have hmono : Monotone (fun m : ℕ => Icc (-(m : ℝ)) m) := by
    intro m n hmn
    apply Icc_subset_Icc
    · exact neg_le_neg (Nat.cast_le.mpr hmn)
    · exact_mod_cast hmn
  have h := tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) hmono
    (hf.integrableOn (s := ⋃ m : ℕ, Icc (-(m : ℝ)) m))
  simpa only [hcover, Measure.restrict_univ] using h

/-- Every fixed frequency window eventually misses almost one unit of negative corrected energy. -/
theorem eventually_lt_ccmExteriorEscapeNegativeTailEnergy
    (a : SuzukiPositiveAperture) (R c : ℝ) (hc : c < 1) :
    ∀ᶠ N in atTop, c < ccmExteriorEscapeNegativeTailEnergy a R N := by
  have hd := interval_exhaustion (density_integrable a)
  rw [integral_ccmExteriorEscapeGroundDensity] at hd
  have hb := interval_exhaustion (base_integrable a)
  have ht : Tendsto (fun m : ℕ =>
      (∫ x in Icc (-(m : ℝ)) m, ccmExteriorEscapeGroundDensity a x) -
      ∫ x in (Icc (-(m : ℝ)) m)ᶜ,
        correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x)
      atTop (𝓝 1) := by
    simpa only [setIntegral_compl measurableSet_Icc (base_integrable a), sub_self, sub_zero]
      using hd.sub ((show Tendsto (fun _ : ℕ => ∫ x,
        correctedCCMSymbol a.1 (2 * Real.pi * x) * ccmExteriorEscapeGroundDensity a x)
        atTop (𝓝 (∫ x, correctedCCMSymbol a.1 (2 * Real.pi * x) *
          ccmExteriorEscapeGroundDensity a x)) from tendsto_const_nhds).sub hb)
  have hmR : ∀ᶠ m : ℕ in atTop, R ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)
  obtain ⟨m, hmR, hmc⟩ := (hmR.and (ht.eventually (eventually_gt_nhds hc))).exists
  have hneg := (tendsto_ccmExteriorEscape_signed_tail a m).neg
  have hneg' : ∀ᶠ N in atTop,
      c < -(∫ x in (Icc (-(m : ℝ)) m)ᶜ, ccmExteriorEscapeCorrectedSymbol a N x *
        ccmExteriorEscapeGroundDensity a x) :=
    hneg.eventually (eventually_gt_nhds (by linarith : c < -_))
  filter_upwards [hneg'] with N hN
  apply hN.trans_le ((neg_signed_tail_le a m N).trans ?_)
  apply setIntegral_mono_set (negative_density_integrable a N).integrableOn
    (Eventually.of_forall (fun x => mul_nonneg (le_max_right _ _) (density_nonneg a x)))
  apply Eventually.of_forall
  intro x hx hsmall
  apply hx
  exact ⟨(neg_le_neg hmR).trans hsmall.1, hsmall.2.trans hmR⟩

/-- All sufficiently late degrees, even or odd, fail global positivity beyond any fixed window. -/
theorem eventually_exists_ccmExteriorEscapeCorrectedSymbol_negative
    (a : SuzukiPositiveAperture) (R : ℝ) :
    ∀ᶠ N in atTop, ∃ x ∉ Icc (-R) R, ccmExteriorEscapeCorrectedSymbol a N x < 0 := by
  filter_upwards [eventually_lt_ccmExteriorEscapeNegativeTailEnergy a R (1/2) (by norm_num)] with N hN
  by_contra hn
  push Not at hn
  have hz : ccmExteriorEscapeNegativeTailEnergy a R N = 0 := by
    unfold ccmExteriorEscapeNegativeTailEnergy
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
    rw [max_eq_right (neg_nonpos.mpr (hn x hx)), zero_mul]
    rfl
  rw [hz] at hN
  norm_num at hN

end RHTower
