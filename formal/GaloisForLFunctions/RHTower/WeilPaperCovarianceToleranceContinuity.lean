import GaloisForLFunctions.RHTower.WeilPaperCovarianceToleranceGeometry

/-!
# Continuity of covariance-window gamma certificates

The exact dual formula gives joint lower semicontinuity in observed law and
measurement tolerance. At a fixed law the certificate is continuous even at
zero tolerance, and has an explicit Lipschitz bound on every positive ray.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided
variable {ι : Type*}

/-- Each certified finite affine bound depends continuously on measured law
and error tolerance. -/
theorem continuous_paperCovarianceRobustAffineValue
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) (A : PaperCovarianceAffineMinorant c F G s) :
    Continuous (fun p : PaperObservedSpectralCompletion c F × ℝ≥0 =>
      paperCovarianceRobustAffineValue c F G p.1 s p.2 A) := by
  have hk (k : s) : Continuous (fun p : PaperObservedSpectralCompletion c F × ℝ≥0 =>
      paperObservedPhaseCovariances c F p.1 k.1) :=
    (continuous_apply k.1).comp ((paperObservedPhaseCovariances c F).continuous.comp continuous_fst)
  exact (continuous_const.add (continuous_finsetSum _ fun k _ => continuous_const.mul (hk k))).sub
    ((NNReal.continuous_coe.comp continuous_snd).mul continuous_const)

/-- The attained window minimum is jointly lower semicontinuous in the
completed spectral law and the nonnegative measurement tolerance. -/
theorem lowerSemicontinuous_paperCovarianceGammaCertificate_joint
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    LowerSemicontinuous (fun p : PaperObservedSpectralCompletion c F × ℝ≥0 =>
      paperCovarianceGammaCertificate c F G p.1 s p.2) := by
  have heq : (fun p : PaperObservedSpectralCompletion c F × ℝ≥0 =>
      paperCovarianceGammaCertificate c F G p.1 s p.2) =
      (fun p => ⨆ A : PaperCovarianceAffineMinorant c F G s,
        paperCovarianceRobustAffineValue c F G p.1 s p.2 A) := by
    funext p
    exact paperCovarianceGammaCertificate_eq_sSup_robustAffineValues c F G p.1 s p.2
  rw [heq]
  exact lowerSemicontinuous_ciSup
    (fun p => paperCovarianceRobustAffineValues_bddAbove c F G p.1 s p.2)
    (fun A => (continuous_paperCovarianceRobustAffineValue c F G s A).lowerSemicontinuous)

theorem lowerSemicontinuous_paperCovarianceGammaCertificate_tolerance
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    LowerSemicontinuous (paperCovarianceGammaCertificate c F G μ s) := by
  have hmap : Continuous (fun r : ℝ≥0 => (μ, r)) := continuous_const.prodMk continuous_id
  intro r b hb
  have h := lowerSemicontinuous_paperCovarianceGammaCertificate_joint c F G s (μ, r) b hb
  exact (hmap.tendsto r).eventually h

/-- Exact measurements are the continuous limit of measurements with vanishing
tolerance; there is no endpoint jump in the certified energy. -/
theorem continuousAt_zero_paperCovarianceGammaCertificate_tolerance
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    ContinuousAt (paperCovarianceGammaCertificate c F G μ s) 0 := by
  apply continuousAt_iff_lower_upperSemicontinuousAt.mpr
  refine ⟨lowerSemicontinuous_paperCovarianceGammaCertificate_tolerance c F G μ s 0, ?_⟩
  intro b hb
  exact Eventually.of_forall fun r =>
    (antitone_paperCovarianceGammaCertificate_tolerance c F G μ s (show 0 ≤ r from zero_le)).trans_lt hb

private theorem convex_nnreal_secant (f : ℝ≥0 → ℝ) (hc : ConvexOn ℝ≥0 univ f)
    (r q : ℝ≥0) (hq : 0 < q) (hrq : r ≤ q) :
    (q : ℝ) * (f r - f q) ≤ ((q : ℝ) - r) * (f 0 - f q) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let t : ℝ≥0 := r / q
  have ht : (t : ℝ) ≤ 1 := (div_le_one₀ hqR).mpr (by exact_mod_cast hrq)
  let u : ℝ≥0 := ⟨1 - t, sub_nonneg.mpr ht⟩
  have hsum : t + u = 1 := by
    apply NNReal.eq
    change (t : ℝ) + (1 - t) = 1
    ring
  have hpoint : t • q + u • 0 = r := by
    apply NNReal.eq
    change (r : ℝ) / q * q + (1 - t) * 0 = r
    field_simp
    ring
  have hh := hc.2 (mem_univ q) (mem_univ 0) (show 0 ≤ t from zero_le) (show 0 ≤ u from zero_le) hsum
  rw [hpoint] at hh
  change f r ≤ (r : ℝ) / q * f q + (1 - (r : ℝ) / q) * f 0 at hh
  have hm := mul_le_mul_of_nonneg_left hh hqR.le
  have he : (q : ℝ) * ((r : ℝ) / q * f q + (1 - (r : ℝ) / q) * f 0) =
      (r : ℝ) * f q + ((q : ℝ) - r) * f 0 := by
    field_simp
  rw [he] at hm
  nlinarith

/-- An explicit tolerance sensitivity bound above a positive precision floor. -/
def paperCovarianceToleranceSlopeBound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (a : {r : ℝ≥0 // 0 < r}) : ℝ≥0 :=
  ⟨(paperCovarianceGammaCertificate c F G μ s 0 - paperObservedGammaValue c F G) / a.1,
    div_nonneg (sub_nonneg.mpr (paperObservedGammaValue_le_covarianceCertificate c F G μ s 0)) a.1.2⟩

private theorem tolerance_gap_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (a : {r : ℝ≥0 // 0 < r})
    (r q : ℝ≥0) (har : a.1 ≤ r) (hrq : r ≤ q) :
    paperCovarianceGammaCertificate c F G μ s r - paperCovarianceGammaCertificate c F G μ s q ≤
      paperCovarianceToleranceSlopeBound c F G μ s a * ((q : ℝ) - r) := by
  let f := paperCovarianceGammaCertificate c F G μ s
  let B := f 0 - paperObservedGammaValue c F G
  have haR : 0 < (a.1 : ℝ) := by exact_mod_cast a.2
  have haq : (a.1 : ℝ) ≤ q := by exact_mod_cast har.trans hrq
  have hqr : (r : ℝ) ≤ q := by exact_mod_cast hrq
  have hanti := antitone_paperCovarianceGammaCertificate_tolerance c F G μ s
  have hd : 0 ≤ f r - f q := sub_nonneg.mpr (hanti hrq)
  have hsec := convex_nnreal_secant f (convexOn_paperCovarianceGammaCertificate_tolerance c F G μ s)
    r q (a.2.trans_le (har.trans hrq)) hrq
  have hB : f 0 - f q ≤ B := by
    dsimp [B, f]
    linarith [paperObservedGammaValue_le_covarianceCertificate c F G μ s q]
  have hbound : (f r - f q) * (a.1 : ℝ) ≤ ((q : ℝ) - r) * B := by
    calc
      _ ≤ (q : ℝ) * (f r - f q) := by nlinarith
      _ ≤ ((q : ℝ) - r) * (f 0 - f q) := hsec
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hqr)
  calc
    f r - f q ≤ (((q : ℝ) - r) * B) / a.1 := (le_div_iff₀ haR).mpr hbound
    _ = paperCovarianceToleranceSlopeBound c F G μ s a * ((q : ℝ) - r) := by
      change (((q : ℝ) - r) * B) / (a.1 : ℝ) = (B / (a.1 : ℝ)) * ((q : ℝ) - r)
      ring

/-- Every positive tolerance ray has an explicit global Lipschitz constant. -/
theorem lipschitzOnWith_paperCovarianceGammaCertificate_tolerance
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (a : {r : ℝ≥0 // 0 < r}) :
    LipschitzOnWith (paperCovarianceToleranceSlopeBound c F G μ s a)
      (paperCovarianceGammaCertificate c F G μ s) (Ici a.1) := by
  have hbound (r q : ℝ≥0) (har : a.1 ≤ r) (hrq : r ≤ q) :
      dist (paperCovarianceGammaCertificate c F G μ s r) (paperCovarianceGammaCertificate c F G μ s q) ≤
        paperCovarianceToleranceSlopeBound c F G μ s a * dist r q := by
    have hanti := antitone_paperCovarianceGammaCertificate_tolerance c F G μ s hrq
    have hqr : (r : ℝ) ≤ q := by exact_mod_cast hrq
    simpa only [Real.dist_eq, NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr hanti),
      abs_of_nonpos (sub_nonpos.mpr hqr), neg_sub] using tolerance_gap_bound c F G μ s a r q har hrq
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro r hr q hq
  rcases le_total r q with hrq | hqr
  · exact hbound r q hr hrq
  · simpa only [dist_comm] using hbound q r hq hqr

/-- Gamma certificates depend continuously on tolerance throughout the closed
nonnegative ray, including exact measurements at zero. -/
theorem continuous_paperCovarianceGammaCertificate_tolerance
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    Continuous (paperCovarianceGammaCertificate c F G μ s) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    exact continuousAt_zero_paperCovarianceGammaCertificate_tolerance c F G μ s
  · have hrp : 0 < r := lt_of_le_of_ne (show 0 ≤ r from zero_le) (Ne.symm hr)
    let a : {r : ℝ≥0 // 0 < r} := ⟨r / 2, by positivity⟩
    have har : a.1 < r := half_lt_self hrp
    exact ((lipschitzOnWith_paperCovarianceGammaCertificate_tolerance c F G μ s a).continuousOn r
      har.le).continuousAt (Ici_mem_nhds har)

end RHTower.WeilWorkPBAP
