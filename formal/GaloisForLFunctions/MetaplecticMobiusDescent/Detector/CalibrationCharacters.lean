/-
Calibration characters adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DetectorWitnessArithmetic

/-!
# Calibration characters

Calibration for a prime set and its residue monoid; the calibration character is the product of
local residue characters. Actual and bare congruence coefficients, element windows and the
Mellin summands of spectral rows.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace GammaDetectorExpansion
open GammaZeroDetector HeckeFamily

def line (t : ℝ) : ℂ := 2+t*I

@[simp] theorem line_re (t : ℝ) : (line t).re = 2 := by simp [line]
@[simp] theorem line_im (t : ℝ) : (line t).im = t := by simp [line]

theorem gamma_line_integrable : Integrable (fun t : ℝ => Gamma (line t)) := by
  obtain ⟨C,hC,hbound⟩ := gamma_rapid_bound 2 2 (by norm_num) 2
  apply (integrable_inv_one_add_sq.const_mul C).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    exact fun t => (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp
      (by unfold line; fun_prop)
  · filter_upwards [] with t
    have hb := hbound (line t) (by simp) (by simp)
    simp only [line_im] at hb
    have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [norm_nonneg (Gamma (line t))]

theorem gamma_mellin_inverse {x : ℝ} (hx : 0 < x) :
    ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t : ℝ, (x : ℂ)^(-line t)*Gamma (line t)) = Complex.exp (-(x : ℂ)) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ)
  have hm (s : ℂ) (hs : 0 < s.re) : mellin f s = Gamma s := by
    rw [Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  have hf : MellinConvergent f (2 : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (GammaIntegral_convergent (by norm_num : 0 < (2 : ℂ).re))
  have hline (t : ℝ) : mellin f (line t) = Gamma (line t) := hm _ (by simp)
  have hv : VerticalIntegrable (mellin f) 2 := by
    change Integrable (fun t : ℝ => mellin f (line t))
    simpa only [hline] using gamma_line_integrable
  have hi := mellinInv_mellin_eq 2 f hx hf hv (by unfold f; fun_prop)
  change (1/(2*Real.pi)) • (∫ t : ℝ, (x : ℂ)^(-line t) • mellin f (line t)) = f x at hi
  simp_rw [hline] at hi
  simp only [smul_eq_mul, f, ofReal_exp, ofReal_neg] at hi
  convert hi using 1; simp [one_div, Complex.real_smul]

def gammaTerm (a : ℂ) (N : ℝ) (ρ : ℂ) (Y : ℝ) (t : ℝ) : ℂ :=
  (Y : ℂ)^(line t)*Gamma (line t)*a*(N : ℂ)^(-(ρ+line t))

theorem gammaTerm_separate (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    gammaTerm a N ρ Y t = (a*(N : ℂ)^(-ρ))*
      (((N/Y : ℝ) : ℂ)^(-line t)*Gamma (line t)) := by
  rw [gammaTerm, neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hN.ne'),
    positive_quotient_cpow_neg N Y hN hY]
  ring

theorem gammaTerm_integral (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    ((2*Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, gammaTerm a N ρ Y t) =
      a*(N : ℂ)^(-ρ)*Complex.exp (-(N : ℂ)/(Y : ℂ)) := by
  simp_rw [gammaTerm_separate a hN hY ρ]
  rw [integral_const_mul]
  calc
    _ = (a*(N : ℂ)^(-ρ))*(((2*Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, ((N/Y : ℝ) : ℂ)^(-line t)*Gamma (line t)) := by ring
    _ = _ := by rw [gamma_mellin_inverse (div_pos hN hY)]; push_cast; rw [neg_div]

@[simp] theorem gammaTerm_zero (N : ℝ) (ρ : ℂ) (Y t : ℝ) : gammaTerm 0 N ρ Y t = 0 := by
  simp [gammaTerm]

theorem gammaTerm_norm (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    ‖gammaTerm a N ρ Y t‖ = (Y^2 * (‖a‖*N^(-(ρ.re+2)))) * ‖Gamma (line t)‖ := by
  simp only [gammaTerm, norm_mul, norm_cpow_eq_rpow_re_of_pos hY,
    norm_cpow_eq_rpow_re_of_pos hN, neg_re, add_re, line_re, Real.rpow_two]
  ring

theorem gammaTerm_integrable (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    Integrable (gammaTerm a N ρ Y) := by
  apply (gamma_line_integrable.norm.const_mul (Y^2*(‖a‖*N^(-(ρ.re+2))))).mono'
  · apply Continuous.aestronglyMeasurable
    have hl : Continuous line := by unfold line; fun_prop
    have hg : Continuous (fun t : ℝ => Gamma (line t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp hl.continuousAt
    have hy := (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hY.ne'))).continuous.comp hl
    have hn := (((differentiable_const ρ).add differentiable_id).neg.const_cpow
      (Or.inl (ofReal_ne_zero.mpr hN.ne'))).continuous.comp hl
    exact ((hy.mul hg).mul continuous_const).mul hn
  · exact ae_of_all _ (fun t => (gammaTerm_norm a hN hY ρ t).le)

theorem gamma_expansion {ι : Type*} [Countable ι] (a : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i, 0 ≤ N i) (hzero : ∀ i, N i = 0 → a i = 0)
    (ρ : ℂ) {Y : ℝ} (hY : 0 < Y)
    (hsum : Summable (fun i => ‖a i‖*(N i)^(-(ρ.re+2)))) :
    HasSum (fun i => a i*(N i : ℂ)^(-ρ)*Complex.exp (-(N i : ℂ)/(Y : ℂ)))
      (((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, ∑' i, gammaTerm (a i) (N i) ρ Y t) := by
  have hint (i : ι) : Integrable (gammaTerm (a i) (N i) ρ Y) := by
    by_cases hi : N i = 0
    · rw [hzero i hi]
      have he : gammaTerm 0 (N i) ρ Y = fun _ : ℝ => 0 := funext (gammaTerm_zero _ _ _)
      rw [he]
      exact integrable_zero ℝ ℂ volume
    · exact gammaTerm_integrable _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ
  have hnorm (i : ι) (t : ℝ) :
      ‖gammaTerm (a i) (N i) ρ Y t‖ =
        (Y^2*(‖a i‖*(N i)^(-(ρ.re+2))))*‖Gamma (line t)‖ := by
    by_cases hi : N i = 0
    · simp [hzero i hi]
    · exact gammaTerm_norm _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ t
  have hnormsum : Summable (fun i => ∫ t : ℝ, ‖gammaTerm (a i) (N i) ρ Y t‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact (hsum.mul_left (Y^2*(∫ t : ℝ, ‖Gamma (line t)‖))).congr
      (fun i => by ring)
  have hi := (hasSum_integral_of_summable_integral_norm hint hnormsum).mul_left
    (((2*Real.pi : ℝ) : ℂ)⁻¹)
  have he (i : ι) : (((2*Real.pi : ℝ) : ℂ)⁻¹) * (∫ t : ℝ, gammaTerm (a i) (N i) ρ Y t) =
      a i*(N i : ℂ)^(-ρ)*Complex.exp (-(N i : ℂ)/(Y : ℂ)) := by
    by_cases hn : N i = 0
    · simp [hzero i hn]
    · exact gammaTerm_integral _ (lt_of_le_of_ne (hN i) (Ne.symm hn)) hY ρ
  simpa only [he] using hi

private instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
private instance : Countable (Ideal O) := cubicIdealGenerator_injective.countable

theorem cutoffTerm_weighted (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      V ((J.absNorm : ℝ)/D) * IdealEuler.weighted (idealCoeff χ) s J := by
  simp only [cutoffTerm, HeckeDyadic.coefficient, ite_true,
    IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  ring

theorem cutoffTerm_outside (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (J : Ideal O)
    (hJ : J ∉ cutoffSet D) : cutoffTerm χ V D J s = 0 := by
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_hasSum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    HasSum (fun J : Ideal O => cutoffTerm χ V D J s) (cutoff χ V D s) :=
  hasSum_sum_of_ne_finset_zero (cutoffTerm_outside χ V hD hV s)

def pairCoefficient (χ : Character) (V : ℝ → ℂ) (D : ℝ) (p : Ideal O × Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((p.1.absNorm : ℝ)/D) *
    idealCoeff χ (p.1*p.2)

def pairNorm (p : Ideal O × Ideal O) : ℝ := (p.1*p.2).absNorm

theorem pairCoefficient_zero_norm (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (p : Ideal O × Ideal O) (hp : pairNorm p = 0) : pairCoefficient χ V D p = 0 := by
  have hn : (p.1*p.2).absNorm = 0 := by unfold pairNorm at hp; exact_mod_cast hp
  have hzero := Ideal.absNorm_eq_zero_iff.mp hn
  rw [pairCoefficient, hzero]
  rw [show (⊥ : Ideal O) = 0 from rfl, HeckeFamily.idealCoeff_zero, mul_zero]

theorem pairTerm_eq (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ)
    (p : Ideal O × Ideal O) :
    pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s) =
      cutoffTerm χ V D p.1 s * IdealEuler.weighted (idealCoeff χ) s p.2 := by
  rw [cutoffTerm_weighted]
  by_cases hp : p.1*p.2 = 0
  · have he : pairNorm p = 0 := by simp [pairNorm, hp]
    rw [pairCoefficient_zero_norm χ V D p he, zero_mul]
    rw [mul_assoc, ← map_mul, hp, map_zero, mul_zero]
  · rw [mul_assoc, ← map_mul]
    simp only [pairCoefficient, pairNorm, Complex.ofReal_natCast,
      IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      fullIdealWeight, if_neg hp]
    ring

theorem pairTerm_summable_norm (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)‖) := by
  simpa only [pairTerm_eq] using
    (cutoffTerm_hasSum χ V hD hV s).summable.norm.mul_norm
      (IdealEuler.weighted_summable_norm _ (idealCoeff_norm_le_one χ) s hs)

theorem pairSeries_eq (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    (∑' p : Ideal O × Ideal O, pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)) =
      cutoff χ V D s * LFunction χ s := by
  simp_rw [pairTerm_eq]
  rw [← tsum_mul_tsum_of_summable_norm (cutoffTerm_hasSum χ V hD hV s).summable.norm
    (IdealEuler.weighted_summable_norm _ (idealCoeff_norm_le_one χ) s hs)]
  rw [(cutoffTerm_hasSum χ V hD hV s).tsum_eq, LFunction_eq_series χ hs]
  rfl

theorem pairMajorant_summable (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖pairCoefficient χ V D p‖*(pairNorm p)^(-(ρ.re+2))) := by
  have h := pairTerm_summable_norm χ V hD hV (ρ+2) (by norm_num; linarith)
  apply h.congr
  intro p
  by_cases hp : pairNorm p = 0
  · simp [pairCoefficient_zero_norm χ V D p hp]
  · have hn : 0 < pairNorm p := lt_of_le_of_ne (by unfold pairNorm; positivity) (Ne.symm hp)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hn]
    simp only [neg_re, add_re]
    norm_num

theorem pairGamma_tsum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re)
    (Y t : ℝ) :
    (∑' p : Ideal O × Ideal O, gammaTerm (pairCoefficient χ V D p) (pairNorm p) ρ Y t) =
      detectorIntegrand χ V D Y ρ (line t) := by
  have hs : 1 < (ρ+line t).re := by simp only [add_re, line_re]; linarith
  calc
    _ = (Y : ℂ)^(line t)*Gamma (line t)*
        (∑' p : Ideal O × Ideal O, pairCoefficient χ V D p*(pairNorm p : ℂ)^(-(ρ+line t))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      unfold gammaTerm
      ring
    _ = _ := by rw [pairSeries_eq χ V hD hV _ hs]; unfold detectorIntegrand; ring

def pairExponential (χ : Character) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  pairCoefficient χ V D p*(pairNorm p : ℂ)^(-ρ)*Complex.exp (-(pairNorm p : ℂ)/(Y : ℂ))

theorem detector_hasSum_pairs (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairExponential χ V D ρ Y) (detectorIntegral χ V D Y ρ) := by
  have h := gamma_expansion (pairCoefficient χ V D) pairNorm
    (fun p => by unfold pairNorm; positivity) (pairCoefficient_zero_norm χ V D)
    ρ hY (pairMajorant_summable χ V hD hV hρ)
  unfold pairExponential detectorIntegral
  simpa only [pairGamma_tsum χ V hD hV hρ, line] using h

theorem detector_eq_double_sum (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    detectorIntegral χ V D Y ρ = ∑' J : Ideal O, ∑' K : Ideal O,
      (UniqueFactorizationMonoid.moebius J : ℂ) * V ((J.absNorm : ℝ)/D) *
      idealCoeff χ (J*K) * (((J*K).absNorm : ℝ) : ℂ)^(-ρ) *
        Complex.exp (-(((J*K).absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
  have h := detector_hasSum_pairs χ V hD hY hV hρ
  rw [← h.tsum_eq, h.summable.tsum_prod]
  rfl

theorem pairExponential_zero_left (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (K : Ideal O) : pairExponential χ V D ρ Y (0,K) = 0 := by
  unfold pairExponential
  rw [pairCoefficient_zero_norm χ V D _ (by simp [pairNorm]), zero_mul, zero_mul]

theorem pairExponential_zero_right (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) : pairExponential χ V D ρ Y (J,0) = 0 := by
  unfold pairExponential
  rw [pairCoefficient_zero_norm χ V D _ (by simp [pairNorm]), zero_mul, zero_mul]

theorem pairExponential_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : MulFiber J, pairExponential χ V D ρ Y p.val) =
      HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J := by
  have he (p : MulFiber J) :
      pairExponential χ V D ρ Y p.val =
        ((UniqueFactorizationMonoid.moebius p.val.1 : ℂ)*V ((p.val.1.absNorm : ℝ)/D)*
          IdealEuler.weighted (idealCoeff χ) ρ (p.val.1*p.val.2))*
          Complex.exp (-((J.absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
    rw [pairExponential, pairTerm_eq, cutoffTerm_weighted, mul_assoc _ _
      (IdealEuler.weighted (idealCoeff χ) ρ p.val.2), ← map_mul]
    congr 2
    rw [pairNorm, p.property]
  simp_rw [he]
  rw [tsum_mul_right, HeckeDetectorWitnessArithmetic.weighted_fiber]
  rfl

theorem detector_hasSum_convolution (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y)
      (detectorIntegral χ V D Y ρ) := by
  have h := (detector_hasSum_pairs χ V hD hY hV hρ).tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : MulFiber J,
    pairExponential χ V D ρ Y p.val) _ at h
  simpa only [pairExponential_fiber] using h

theorem detector_large_product_tail (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    (∑' J : Ideal O, HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J *
      (1-V (2*(J.absNorm : ℝ)/D))) =
      detectorIntegral χ V D Y ρ - Complex.exp (-1/(Y : ℂ)) := by
  have h := detector_hasSum_convolution χ V (by linarith : 0 < D) hY hVzero hρ
  rw [HeckeDetectorWitnessArithmetic.exponential_sum_tail χ V D hD hV hVzero ρ Y h.summable,
    h.tsum_eq]

theorem pairExponential_summable_norm (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O => ‖pairExponential χ V D ρ Y p‖) :=
  (detector_hasSum_pairs χ V hD hY hV hρ).summable.norm

def pairTail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  pairExponential χ V D ρ Y p * (1-V (2*pairNorm p/D))

theorem pairTail_summable (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (pairTail χ V D ρ Y) := by
  apply Summable.of_norm
  apply ((pairExponential_summable_norm χ V hD hY hVzero hρ).mul_right 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  rw [pairTail, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hn := norm_sub_le (1 : ℂ) (V (2*pairNorm p/D))
  rw [norm_one] at hn
  linarith [hV (2*pairNorm p/D)]

theorem pairTail_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : MulFiber J, pairTail χ V D ρ Y p.val) =
      HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J *
        (1-V (2*(J.absNorm : ℝ)/D)) := by
  have hn (p : MulFiber J) : pairNorm p.val = (J.absNorm : ℝ) := by
    rw [pairNorm, p.property]
  simp_rw [pairTail, hn]
  rw [tsum_mul_right, pairExponential_fiber]

theorem detector_eq_pair_tail (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hVone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairTail χ V D ρ Y)
      (detectorIntegral χ V D Y ρ - Complex.exp (-1/(Y : ℂ))) := by
  have hs := pairTail_summable χ V (by linarith : 0 < D) hY hVzero hV hρ
  have hf := hs.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : MulFiber J,
    pairTail χ V D ρ Y p.val) _ at hf
  simp_rw [pairTail_fiber] at hf
  have he := hf.tsum_eq
  rw [detector_large_product_tail χ V hD hY hVone hVzero hρ] at he
  exact he.symm ▸ hs.hasSum

end GammaDetectorExpansion

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace ProbePhysical
open Eisenstein CompletedGauss   CubicEisenstein
local notation "O" => Eisenstein.O

/-- The calibration character is the product of the local residue characters. -/
abbrev crtCharacter {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) : MulChar T ℂ :=
  CenteredMomentCorrelation.crtCharacter e χ

theorem crtCharacter_pow_six {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (hχ : ∀ i, χ i ^ 6 = 1) :
    crtCharacter R e χ ^ 6 = 1 := by
  apply MulChar.ext
  intro x
  rw [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply x.isUnit]
  change (∏ i, χ i (e x i)) ^ 6 = 1
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  have hu : IsUnit (e x i) := (Pi.isUnit_iff.mp (x.isUnit.map e.toMonoidHom)) i
  have he := congrArg (fun f : MulChar (R i) ℂ => f (e x i)) (hχ i)
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using he

theorem residue_char_ne_two_of_lambda_mem (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∈ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  intro hc
  have hd : lambda ∣ (3 : O) :=
    (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three
  obtain ⟨k, hk⟩ := hd
  have h3m : (3 : O) ∈ P := by rw [hk]; exact P.mul_mem_right k hg
  have h3 : (3 : O ⧸ P) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h3m
  have h2 : (2 : O ⧸ P) = 0 := by
    exact (ringChar.spec (O ⧸ P) 2).mpr (by rw [hc])
  have h1 : (1 : O ⧸ P) = 0 := by linear_combination h3 - h2
  exact one_ne_zero h1

theorem exists_local_calibration (P : Ideal O) [P.IsMaximal] :
    ∃ χ : MulChar (O ⧸ P) ℂ, χ ≠ 1 ∧ χ ^ 6 = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  by_cases hg : lambda ∉ P
  · refine ⟨Eisenstein.complexCubicChar P hg,
      Eisenstein.complexCubicChar_ne_one P hg, ?_⟩
    rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul,
      Eisenstein.complexCubicChar_pow_three, one_pow]
  · have hchar := residue_char_ne_two_of_lambda_mem P (not_not.mp hg)
    let χ : MulChar (O ⧸ P) ℂ := (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ)
    refine ⟨χ, ?_, ?_⟩
    · exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hchar)
    · have h2 : χ ^ 2 = 1 := by
        dsimp only [χ]
        rw [MulChar.ringHomComp_pow, (quadraticChar_isQuadratic (O ⧸ P)).sq_eq_one,
          MulChar.ringHomComp_one]
      rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, h2, one_pow]

def localCalibration (P : Ideal O) [P.IsMaximal] : MulChar (O ⧸ P) ℂ :=
  Classical.choose (exists_local_calibration P)

theorem localCalibration_nonprincipal (P : Ideal O) [P.IsMaximal] :
    localCalibration P ≠ 1 := (Classical.choose_spec (exists_local_calibration P)).1

theorem localCalibration_pow_six (P : Ideal O) [P.IsMaximal] :
    localCalibration P ^ 6 = 1 := (Classical.choose_spec (exists_local_calibration P)).2

def calibrationFromPrimes {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) : CalibrationData := by
  letI (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact {
    excluded := Finset.univ.image P
    generator := finitePrimeModulus P
    generator_ne_zero := finitePrimeModulus_ne_zero P
    residue := crtCharacter (fun i => O ⧸ P i)
      ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
        (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => localCalibration (P i)) }

theorem calibrationFromPrimes_pow_six {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).residue ^ 6 = 1 := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact crtCharacter_pow_six _ _ _ (fun i => localCalibration_pow_six (P i))

theorem calibrationFromPrimes_tau_norm {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    ‖(calibrationFromPrimes P hcop).tau‖ = 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := finiteEisensteinQuotientOfNonzero hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := residueTraceQuotientChar 1 b hb
  have hψ : ψ.IsPrimitive := residueTraceQuotientChar_primitive b hb
  have hg := finite_crt_gauss_norm_sq (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) (fun i => localCalibration_nonprincipal (P i)) ψ hψ
  have hcard : (Fintype.card (O ⧸ Ideal.span {b}) : ℝ) = elementNorm b := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard] at hg
  have hQ : 0 < elementNorm b := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hb))
  have hn : ‖∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x‖ =
      Real.sqrt (elementNorm b) := by
    have hs := Real.sq_sqrt hQ.le
    have hs0 := Real.sqrt_nonneg (elementNorm b)
    have hn0 := norm_nonneg (∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x)
    nlinarith
  change ‖(∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) * ψ d) /
    (Real.sqrt (elementNorm b) : ℂ)‖ = 1
  rw [tsum_fintype, norm_div, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hQ).ne']

theorem calibrationFromPrimes_tau_ne_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationFromPrimes_tau_norm]; norm_num)

def calibrationForSet (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) : CalibrationData := by
  letI (P : S) : P.val.IsMaximal := hS P.val P.property
  exact calibrationFromPrimes (fun P : S => P.val)
    (fun P Q hPQ => Ideal.isCoprime_of_isMaximal (fun h => hPQ (Subtype.ext h)))

theorem calibrationForSet_excluded (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).excluded = S := by
  change Finset.univ.image (fun P : S => P.val) = S
  ext P
  simp

theorem calibrationForSet_span (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    Ideal.span {(calibrationForSet S hS).generator} = ∏ P ∈ S, P := by
  change Ideal.span {finitePrimeModulus (fun P : S => P.val)} = _
  rw [span_finitePrimeModulus]
  exact Finset.prod_coe_sort S (fun P : Ideal O => P)

theorem calibrationForSet_pow_six (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).residue ^ 6 = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_pow_six

theorem calibrationForSet_tau_norm (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    ‖(calibrationForSet S hS).tau‖ = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_tau_norm

theorem calibrationForSet_tau_ne_zero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationForSet_tau_norm]; norm_num)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace ProbePhysical
open Eisenstein  CubicEisenstein
local notation "O" => Eisenstein.O

def calibrationGauss (C : CalibrationData) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    residueTraceQuotientChar 1 C.generator C.generator_ne_zero
      (Ideal.Quotient.mk (Ideal.span {C.generator}) h * d)

theorem calibrationGauss_one (C : CalibrationData) :
    calibrationGauss C 1 = (Real.sqrt (elementNorm C.generator) : ℂ) * C.tau := by
  have hn : 0 < elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hc : (Real.sqrt (elementNorm C.generator) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  simp only [calibrationGauss, map_one, one_mul, CalibrationData.tau]
  field_simp

theorem calibrationFromPrimes_gauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (h : O) :
    calibrationGauss (calibrationFromPrimes P hcop) h =
      ((calibrationFromPrimes P hcop).residueMonoid h)⁻¹ *
        calibrationGauss (calibrationFromPrimes P hcop) 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := finiteEisensteinQuotientOfNonzero hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := residueTraceQuotientChar 1 b hb
  have ht := finite_crt_gauss_transform (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) (fun i => localCalibration_nonprincipal (P i)) ψ
    (Ideal.Quotient.mk (Ideal.span {b}) h)
  change (∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
      ψ (Ideal.Quotient.mk (Ideal.span {b}) h * d)) =
    (∏ i, localCalibration (P i) (e (Ideal.Quotient.mk (Ideal.span {b}) h) i))⁻¹ *
      ∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
        ψ (Ideal.Quotient.mk (Ideal.span {b}) 1 * d)
  simpa [MulChar.inv_apply_eq_inv'] using ht

theorem calibrationForSet_gauss (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (h : O) :
    calibrationGauss (calibrationForSet S hS) h =
      star ((calibrationForSet S hS).residueMonoid h) *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    finiteEisensteinQuotientOfNonzero C.generator_ne_zero
  have hc : star (C.residueMonoid h) = (C.residueMonoid h)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ h)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have he : calibrationGauss C h = (C.residueMonoid h)⁻¹ * calibrationGauss C 1 := by
    let (P : S) : P.val.IsMaximal := hS P.val P.property
    unfold C calibrationForSet
    apply calibrationFromPrimes_gauss
  rw [he, calibrationGauss_one, ← hc]
  ring

theorem calibrationForSet_residue_sixth (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) (ha : IsCoprime (calibrationForSet S hS).generator a) :
    (calibrationForSet S hS).residueMonoid a ^ 6 = 1 := by
  let C := calibrationForSet S hS
  have hu := (isUnit_quotient_span_iff C.generator a).mpr ha
  have h6 := congrArg (fun χ : MulChar (O ⧸ Ideal.span {C.generator}) ℂ =>
    χ (Ideal.Quotient.mk _ a)) (calibrationForSet_pow_six S hS)
  change C.residue (Ideal.Quotient.mk _ a) ^ 6 = 1
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using h6

theorem calibrationForSet_quotient_conjugate (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (s k u a : O)
    (hs : IsCoprime (calibrationForSet S hS).generator s)
    (ha : IsCoprime (calibrationForSet S hS).generator a)
    (hrel : s * k = u * a ^ 6) :
    star ((calibrationForSet S hS).residueMonoid k) =
      star ((calibrationForSet S hS).residueMonoid u) *
        (calibrationForSet S hS).residueMonoid s := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    finiteEisensteinQuotientOfNonzero C.generator_ne_zero
  have hc (x : O) : star (C.residueMonoid x) = (C.residueMonoid x)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ x)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have hu := (isUnit_quotient_span_iff C.generator s).mpr hs
  have hsn : C.residueMonoid s ≠ 0 := C.residue.apply_ne_zero_iff.mpr hu
  have he := congrArg C.residueMonoid hrel
  simp only [map_mul, map_pow] at he
  have h6 : C.residueMonoid a ^ 6 = 1 := calibrationForSet_residue_sixth S hS a ha
  rw [h6, mul_one] at he
  have hk : C.residueMonoid k = (C.residueMonoid s)⁻¹ * C.residueMonoid u := by
    rw [← he, ← mul_assoc, inv_mul_cancel₀ hsn, one_mul]
  change star (C.residueMonoid k) = star (C.residueMonoid u) * C.residueMonoid s
  rw [hc k, hc u, hk, mul_inv_rev, inv_inv]

theorem calibrationForSet_gauss_sixth_row (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (s k u a : O)
    (hs : IsCoprime (calibrationForSet S hS).generator s)
    (ha : IsCoprime (calibrationForSet S hS).generator a)
    (hrel : s * k = u * a ^ 6) :
    calibrationGauss (calibrationForSet S hS) k =
      star ((calibrationForSet S hS).residueMonoid u) *
        (calibrationForSet S hS).residueMonoid s *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  rw [calibrationForSet_gauss,
    calibrationForSet_quotient_conjugate S hS s k u a hs ha hrel]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace ProbeRow
open Eisenstein CompletedGauss CubicEisenstein
local notation "O" => Eisenstein.O

theorem fullIdealWeight_norm_eq_of_re (s t : ℂ) (h : s.re = t.re) (I : Ideal O) :
    ‖fullIdealWeight s I‖ = ‖fullIdealWeight t I‖ := by
  by_cases hI : I = 0
  · simp [hI, fullIdealWeight]
  · exact (norm_fullIdealWeight s ⟨I, hI⟩).trans
      ((by rw [h] : _ = _).trans (norm_fullIdealWeight t ⟨I, hI⟩).symm)

theorem fullIdealWeight_continuous (I : Ideal O) : Continuous (fun t => fullIdealWeight t I) := by
  by_cases hI : I = 0
  · simp only [hI, fullIdealWeight]
    exact continuous_const
  · have hn : (Ideal.absNorm I : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_ne_zero_iff I).mpr
        (Ring.HasFiniteQuotients.finiteQuotient hI)
    simp only [fullIdealWeight, if_neg hI]
    exact continuous_id.neg.const_cpow (Or.inl hn)

def rowMajorant (σ : ℝ) (p : Ideal O × Ideal O) : ℝ :=
  2 * (‖fullIdealWeight (σ : ℂ) p.1‖ * ‖fullIdealWeight (3 * (σ : ℂ)) p.2‖)

theorem rowMajorant_summable (σ : ℝ) (hσ : 1 < σ) : Summable (rowMajorant σ) := by
  have h3 : 1 < (3 * (σ : ℂ)).re := by norm_num; linarith
  exact ((fullIdealWeight_summable_norm (σ : ℂ) hσ).mul_of_nonneg
    (fullIdealWeight_summable_norm (3 * (σ : ℂ)) h3)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2

theorem spectralSummand_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ y : ℝ) (p : Ideal O × Ideal O) :
    ‖spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2‖ ≤ rowMajorant σ p := by
  have h1 : ((σ : ℂ) + y * Complex.I).re = (σ : ℂ).re := by simp
  have h3 : (3 * ((σ : ℂ) + y * Complex.I)).re = (3 * (σ : ℂ)).re := by simp
  simpa only [rowMajorant, fullIdealWeight_norm_eq_of_re _ _ h1,
    fullIdealWeight_norm_eq_of_re _ _ h3] using
    spectralSummand_norm_le S D Ψ hΨ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem spectralRow_continuous_vertical (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) :
    Continuous (fun y : ℝ => spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  apply continuous_tsum _ (rowMajorant_summable σ hσ)
    (fun p y => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
  intro p
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  exact continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
    ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))

theorem spectralRow_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) (y : ℝ) :
    ‖spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)‖ ≤ ∑' p, rowMajorant σ p := by
  have hs := spectralRow_summable S D Ψ hΨ ((σ : ℂ) + y * Complex.I) (by simpa using hσ)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum (fun p => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
      (rowMajorant_summable σ hσ))

theorem verticalKernel_norm (Z : ℝ) (hZ : 0 < Z) (σ y : ℝ) :
    ‖(Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2)‖ =
      Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : (((σ : ℂ) + y * Complex.I) ^ 2).re = σ ^ 2 + (-1 * y ^ 2) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [hre, Real.exp_add]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

theorem spectralRow_vertical_integrable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  let B : ℝ := ∑' p, rowMajorant σ p
  have hg := (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * B)
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply hg.mono' (hk.mul (spectralRow_continuous_vertical S D Ψ hΨ σ hσ)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply, Pi.pow_apply]
  rw [norm_mul, verticalKernel_norm Z hZ σ y]
  calc
    _ ≤ (Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2)) * B :=
      mul_le_mul_of_nonneg_left (spectralRow_vertical_bound S D Ψ hΨ σ hσ y)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le) (Real.exp_pos _).le)
    _ = _ := by ring

end ProbeRow
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

lemma elementNorm_pos (a : O) (ha : a ≠ 0) : 0 < elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

theorem CalibrationData.residueMonoid_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    finiteEisensteinQuotientOfNonzero C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

theorem CalibrationData.Xi_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.Xi a‖ ≤ 1 := by
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans
    (idealRowHom_norm _ _)

theorem CalibrationData.Xi_norm_one (C : CalibrationData) (a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    ‖C.Xi a‖ = 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    finiteEisensteinQuotientOfNonzero C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hu := (CubicEisenstein.isUnit_quotient_span_iff C.generator a).mpr hcop
  have hξ : ‖C.residueMonoid a‖ = 1 := by
    change ‖C.residue (Ideal.Quotient.mk _ a)‖ = 1
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    have hp : C.residue (u : O ⧸ Ideal.span {C.generator}) ^
        Fintype.card (O ⧸ Ideal.span {C.generator})ˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one hp Fintype.card_pos.ne'
  have hc : IsCoprime (Ideal.span {a} : Ideal O) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff a C.generator).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask C.generator (Ideal.span {a}) ((supported_iff_native _).mp ha)
  rw [idealRowHom_argument_pow _ _ _ ((supported_iff_native _).mp ha).1, if_pos hc] at h6
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ = 1
  rw [norm_mul, hξ, Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0), mul_one]

theorem calibrated_rowCoefficient_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    rowCoefficient η C.Xi s hs m a = HeckeFamily.elementCoeff η a * (C.Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  rowCoefficient_apply_unit η C.Xi s hs m a (C.Xi_norm_one a ha hcop)

theorem physicalRow_integrable (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s})) (m : O)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((4 : ℂ) + y * Complex.I) *
      Complex.exp (((4 : ℂ) + y * Complex.I) ^ 2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) ((4 : ℂ) + y * Complex.I)) := by
  exact spectralRow_vertical_integrable C.excluded D (rowCoefficient η C.Xi s hs m)
    (fun a => rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m a)
    4 (by norm_num) Z hZ

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve ProbeRow
local notation "O" => Eisenstein.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (CanonicalRowCompletion.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (CanonicalRowCompletion.prime_coprime_span_iff P a).mpr (h P hP)

theorem calibrationForSet_coprime_of_excluded (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (a : O)
    (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    IsCoprime (calibrationForSet S hS).generator a := by
  apply (calibrationForSet_coprime_iff S hS a).mpr
  intro P hP ha
  apply hmask P hP
  exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

theorem source_rowCoefficient_apply (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    rowCoefficient η (calibrationForSet S hS).Xi s hs m a =
      HeckeFamily.elementCoeff η a * ((calibrationForSet S hS).Xi a)⁻¹ *
        sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  calibrated_rowCoefficient_apply η (calibrationForSet S hS) s hs m a ha
    (calibrationForSet_coprime_of_excluded S hS a hmask)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePrimePower
open Eisenstein GaussianShiftedPartition
local notation "O" => Eisenstein.O

def exactQuotient (a b : O) (h : b ∣ a) : O := Classical.choose h

lemma exactQuotient_spec (a b : O) (h : b ∣ a) : a = b * exactQuotient a b h :=
  Classical.choose_spec h

lemma exactQuotient_eq (a b c : O) (h : b ∣ a) (hb : b ≠ 0) (he : a = b*c) :
    exactQuotient a b h = c := by
  apply mul_left_cancel₀ hb
  exact (exactQuotient_spec a b h).symm.trans he


end ProbePrimePower
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein  CubicEisenstein GaussianShiftedPartition ProbePrimePower
open CenteredMomentFourier CenteredMomentCommonSupport
local notation "O" => Eisenstein.O

def rawFourier (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a}, F m * primitiveTrace a ha (Ideal.Quotient.mk _ H * m)

theorem rawFourier_exactQuotient (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) :
    conductorFourier a s ha hs F H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) *
        (if h : s∣H then rawFourier a ha F (exactQuotient H s h) else 0) := by
  by_cases h : s∣H
  · rw [dif_pos h]
    conv_lhs => rw [exactQuotient_spec H s h]
    exact conductorFourier_lift a s ha hs F _
  · rw [dif_neg h, mul_zero]
    by_contra hn
    exact h (conductorFourier_support a s ha hs F H hn)

def congruenceCoefficient (a s : O) (ha : a≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s}, χ d *
    (if h : s ∣ H-a*representative s d then
      rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)

lemma trace_split_product (a s : O) (ha : a≠0) (hs : s≠0) (H m d : O) :
    primitiveTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ (H*m)) *
      primitiveTrace s hs (Ideal.Quotient.mk _ ((-m)*d)) =
    primitiveTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ ((H-a*d)*m)) := by
  have hscale := primitiveTrace_scaled s a (a*s) (mul_comm a s)
    hs ha (mul_ne_zero ha hs) 1 (Ideal.Quotient.mk _ ((-m)*d))
  simp only [one_mul, map_one, CenteredMomentCorrelation.scaledResidue_mk] at hscale
  calc
    _ = primitiveTrace (a*s) (mul_ne_zero ha hs)
        (Ideal.Quotient.mk _ (H*m+a*((-m)*d))) := by
      rw [map_add, AddChar.map_add_eq_mul, hscale]
    _ = _ := by congr 2; ring

def fullFourier (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a*s}, F (conductorReduction a s m) *
    rawFourier s hs χ (-representative (a*s) m) *
    primitiveTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ H*m)

theorem fullFourier_eq_congruence (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) :
    fullFourier a s ha hs F χ H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * congruenceCoefficient a s ha F χ H := by
  let : Finite (O ⧸ Ideal.span {a*s}) := finiteEisensteinQuotientOfNonzero (mul_ne_zero ha hs)
  let : Finite (O ⧸ Ideal.span {s}) := finiteEisensteinQuotientOfNonzero hs
  let : Fintype (O ⧸ Ideal.span {a*s}) := Fintype.ofFinite _
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold fullFourier rawFourier
  simp_rw [tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold congruenceCoefficient
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = χ d * conductorFourier a s ha hs F (H-a*representative s d) := by
      rw [conductorFourier, tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have ht := trace_split_product a s ha hs H (representative (a*s) m) (representative s d)
      simp only [map_mul, representative_spec] at ht
      rw [← ht]
      ring
    _ = _ := by rw [rawFourier_exactQuotient]; ring

theorem rawFourier_norm_le (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (H : O) :
    ‖rawFourier a ha F H‖ ≤ (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finiteEisensteinQuotientOfNonzero ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  rw [rawFourier, tsum_fintype]
  calc
    _ ≤ ∑ m : O ⧸ Ideal.span {a}, ‖F m * primitiveTrace a ha (Ideal.Quotient.mk _ H*m)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m : O ⧸ Ideal.span {a}, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact hF m
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem congruenceCoefficient_norm_le (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (hχ : ∀ d, ‖χ d‖≤1) (H : O) :
    ‖congruenceCoefficient a s ha F χ H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) * (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finiteEisensteinQuotientOfNonzero hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold congruenceCoefficient
  rw [tsum_fintype]
  calc
    _ ≤ ∑ d : O ⧸ Ideal.span {s}, ‖χ d *
        (if h : s ∣ H-a*representative s d then
          rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _d : O ⧸ Ideal.span {s}, (Ideal.absNorm (Ideal.span {a}):ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · rw [norm_mul]
        exact (mul_le_mul (hχ d) (rawFourier_norm_le a ha F hF _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · simp only [mul_zero, norm_zero]
        positivity
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein GaussianShiftedPartition CanonicalRowCompletion
open CenteredMomentFourier
local notation "O" => Eisenstein.O

def calibratedNumerator (C : CalibrationData) (A m : O) : ℂ :=
  C.residueMonoid m * idealRowHom m (Ideal.span {A})

lemma calibratedNumerator_congr (C : CalibrationData) (A m n : O)
    (h : m-n ∈ (Ideal.span {C.generator*A} : Ideal O)) :
    calibratedNumerator C A m = calibratedNumerator C A n := by
  have hd : C.generator*A ∣ m-n := Ideal.mem_span_singleton.mp h
  have hb : Ideal.Quotient.mk (Ideal.span {C.generator}) m =
      Ideal.Quotient.mk (Ideal.span {C.generator}) n := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_right C.generator A).trans hd)
  have hA : m-n ∈ (Ideal.span {A} : Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_left A C.generator).trans hd)
  unfold calibratedNumerator CalibrationData.residueMonoid
  simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, hb, idealRowHom_congr_mod (Ideal.span {A}) m n hA]

def calibratedQuotient (C : CalibrationData) (A : O)
    (m : O ⧸ Ideal.span {C.generator*A}) : ℂ :=
  calibratedNumerator C A (representative (C.generator*A) m)

lemma calibratedQuotient_mk (C : CalibrationData) (A m : O) :
    calibratedQuotient C A (Ideal.Quotient.mk _ m) = calibratedNumerator C A m := by
  apply calibratedNumerator_congr
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

def outerQuotient (s : O) (d : O ⧸ Ideal.span {s}) : ℂ :=
  idealRowHom (representative s d) (Ideal.span {s})

lemma rawFourier_outer (s : O) (hs : s≠0) (h : O) :
    rawFourier s hs (outerQuotient s) h = sexticGauss s hs h := by
  unfold rawFourier outerQuotient sexticGauss
  apply tsum_congr
  intro x
  congr 1

lemma outerQuotient_mk (s a : O) :
    outerQuotient s (Ideal.Quotient.mk _ a) = idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  exact Ideal.Quotient.eq.mp (representative_spec s (Ideal.Quotient.mk _ a))

def actualCongruenceCoefficient (C : CalibrationData) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA)
    (calibratedQuotient C A) (outerQuotient s) H

def actualPhysicalFourier (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {(C.generator*A)*s},
    calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m) *
    primitiveTrace ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
      (Ideal.Quotient.mk _ H*m)

theorem actualPhysicalFourier_eq (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
  unfold actualCongruenceCoefficient
  rw [← fullFourier_eq_congruence (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA) hs]
  unfold actualPhysicalFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction (C.generator*A) s m =
      Ideal.Quotient.mk (Ideal.span {C.generator*A}) (representative ((C.generator*A)*s) m) := by
    conv_lhs => rw [← representative_spec ((C.generator*A)*s) m]
    rfl
  rw [he, calibratedQuotient_mk]

lemma calibratedNumerator_norm_le (C : CalibrationData) (A m : O) :
    ‖calibratedNumerator C A m‖≤1 := by
  let := finiteEisensteinQuotientOfNonzero C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hC : ‖C.residueMonoid m‖≤1 :=
    FiniteRayExpansion.norm_char_le_one C.residue _
  rw [calibratedNumerator, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hC).trans (idealRowHom_norm _ _)

theorem actualCongruenceCoefficient_norm_le (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (H : O) :
    ‖actualCongruenceCoefficient C A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) *
        (Ideal.absNorm (Ideal.span {C.generator*A}):ℝ) := by
  apply congruenceCoefficient_norm_le _ _ _ hs
  · intro m
    exact calibratedNumerator_norm_le C A _
  · intro d
    exact idealRowHom_norm _ _

theorem normalizedPhysicalFourier_eq (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (H : O) :
    (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ)⁻¹ * actualPhysicalFourier C A s hA hs H =
      (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ) * actualCongruenceCoefficient C A s hA H := by
  have hQ : 0<(Ideal.absNorm (Ideal.span {s}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hs))
  have hroot : (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  have he : (Ideal.absNorm (Ideal.span {s}):ℂ) =
      (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ)^2 := by
    exact_mod_cast (Real.sq_sqrt hQ.le).symm
  rw [actualPhysicalFourier_eq, he]
  field_simp

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
namespace ProbePhysical
open Eisenstein GaussianShiftedPartition 
open SchwartzPlanePoisson CenteredMomentFourier
local notation "O" => Eisenstein.O

lemma sexticGauss_frequency_congr (s : O) (hs : s≠0) (h k : O)
    (he : h-k ∈ (Ideal.span {s}:Ideal O)) : sexticGauss s hs h = sexticGauss s hs k := by
  have hmk := Ideal.Quotient.eq.mpr he
  simp only [sexticGauss, hmk]

def physicalQuotient (C : CalibrationData) (A s : O) (hs : s≠0)
    (m : O ⧸ Ideal.span {(C.generator*A)*s}) : ℂ :=
  calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m)

lemma physicalQuotient_mk (C : CalibrationData) (A s : O) (hs : s≠0) (m : O) :
    physicalQuotient C A s hs (Ideal.Quotient.mk _ m) =
      calibratedNumerator C A m * sexticGauss s hs (-m) := by
  have hd : (C.generator*A)*s ∣ representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m ∈
      (Ideal.span {C.generator*A}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right (C.generator*A) s).trans hd)
  have hs' : -representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-(-m) ∈
      (Ideal.span {s}:Ideal O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s (C.generator*A)).trans hd)
  unfold physicalQuotient
  rw [calibratedNumerator_congr C A _ m hA, sexticGauss_frequency_congr s hs _ (-m) hs']

theorem physical_row_poisson (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0< K) :
    (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) * W (elementNorm m/K)) =
      ((K / elementNorm (C.generator*A) : ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C A s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)) := by
  let c := (C.generator*A)*s
  have hc : c≠0 := mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs
  let := finiteEisensteinQuotientOfNonzero hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have ht := actual_radial_poisson_trace (hWc.toSchwartzMap hWs) K hK c hc
    (physicalQuotient C A s hs)
  change (∑' m : O, physicalQuotient C A s hs (Ideal.Quotient.mk _ m) *
    W (‖ringComplex m‖^2/K)) =
    (K/‖ringComplex c‖^2:ℝ) • ∑' H : O,
      (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
        primitiveTrace c hc (Ideal.Quotient.mk _ H*r)) *
        paperRadialFourier W (K*‖ringComplex H‖^2/‖ringComplex c‖^2) at ht
  have hf (H : O) : (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
      primitiveTrace c hc (Ideal.Quotient.mk _ H*r)) =
        (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
    rw [← actualPhysicalFourier_eq C A s hA hs H]
    exact (tsum_fintype _).symm
  simp_rw [physicalQuotient_mk, ringComplex_norm_sq_eq_absNorm_span, hf] at ht
  change (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) * W (elementNorm m/K)) =
    (K/elementNorm c:ℝ) • ∑' H : O,
      ((Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H) *
        paperRadialFourier W (K*elementNorm H/elementNorm c) at ht
  rw [ht]
  simp only [mul_assoc, tsum_mul_left, Complex.real_smul, Complex.ofReal_div]
  have hn : (elementNorm s:ℂ)≠0 := by
    simp only [elementNorm, Complex.ofReal_natCast]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  have hnorm : elementNorm c = elementNorm (C.generator*A) * elementNorm s := by
    dsimp only [elementNorm, c]
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul]
  simp only [← mul_assoc C.generator A s]
  rw [hnorm, Complex.ofReal_mul]
  simp only [elementNorm, Complex.ofReal_natCast] at hn ⊢
  field_simp

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein  CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstPoisson
local notation "O" => Eisenstein.O

theorem calibration_mixed_fourier (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        primitiveTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) =
      C.residueMonoid b * star (C.residueMonoid H) * (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        (∑' y : Residue b, F (Ideal.Quotient.mk _ C.generator*y) *
          primitiveTrace b hb (Ideal.Quotient.mk _ H*y)) := by
  dsimp only
  let C := calibrationForSet S hS
  let := finiteEisensteinQuotientOfNonzero C.generator_ne_zero
  let := finiteEisensteinQuotientOfNonzero hb
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero C.generator_ne_zero hb)
  let : Fintype (Residue C.generator) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (C.generator*b)) := Fintype.ofFinite _
  rw [tsum_fintype, coprime_mixed_fourier _ _ C.generator_ne_zero hb hcop]
  change C.residueMonoid b * calibrationGauss C H * _ = _
  rw [calibrationForSet_gauss]
  rw [tsum_fintype]
  dsimp only [C]
  simp only [frequencyReduction_mk]
  ring

theorem calibration_mixed_fourier_zero (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        primitiveTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) = 0 := by
  dsimp only
  rw [calibration_mixed_fourier S hS b hb hcop F H]
  have hz : (calibrationForSet S hS).residueMonoid H=0 := by
    change (calibrationForSet S hS).residue (Ideal.Quotient.mk _ H)=0
    apply MulChar.map_nonunit
    exact fun h => hH ((isUnit_quotient_span_iff _ _).mp h)
  rw [hz, star_zero]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein GaussianShiftedPartition CanonicalRowCompletion
open CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => Eisenstein.O

def elementFourier (c : O) (hc : c≠0) (f : O → ℂ) (H : O) : ℂ :=
  ∑' x : Residue c, f (representative c x) * primitiveTrace c hc (Ideal.Quotient.mk _ H*x)

lemma elementFourier_congr (c d : O) (hc : c≠0) (hd : d≠0) (f : O → ℂ) (H : O)
    (he : c=d) : elementFourier c hc f H = elementFourier d hd f H := by
  subst d
  rfl

def movingQuotient (A s : O) (hs : s≠0) (x : Residue (A*s)) : ℂ :=
  idealRowHom (representative (A*s) x) (Ideal.span {A}) *
    sexticGauss s hs (-representative (A*s) x)

lemma movingQuotient_mk (A s : O) (hs : s≠0) (m : O) :
    movingQuotient A s hs (Ideal.Quotient.mk _ m) =
      idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m) := by
  have hd : A*s ∣ representative (A*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative (A*s) (Ideal.Quotient.mk _ m)-m ∈ (Ideal.span {A}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right A s).trans hd)
  have hs' : -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) ∈ (Ideal.span {s}:Ideal O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative (A*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s A).trans hd)
  unfold movingQuotient
  rw [idealRowHom_congr_mod _ _ _ hA, sexticGauss_frequency_congr s hs _ (-m) hs']

lemma physicalFourier_eq_element (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      elementFourier (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
        (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H := by
  change elementFourier ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
    (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H = _
  apply elementFourier_congr
  exact mul_assoc _ _ _

lemma physicalFourier_eq_mixed (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      ∑' x : Residue (C.generator*(A*s)),
        C.residue (frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x) *
          movingQuotient A s hs (frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x) *
          primitiveTrace (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
            (Ideal.Quotient.mk _ H*x) := by
  rw [physicalFourier_eq_element]
  unfold elementFourier
  apply tsum_congr
  intro x
  have he : Ideal.Quotient.mk (Ideal.span {C.generator*(A*s)})
      (representative (C.generator*(A*s)) x) = x := representative_spec _ _
  have hrA : frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  have hrB : frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  rw [hrA, hrB, movingQuotient_mk]
  change _ = (C.residueMonoid _ * (_ * _)) * _

  ring

theorem actualPhysicalFourier_zero_off_calibration (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    actualPhysicalFourier (calibrationForSet S hS) A s hA hs H=0 := by
  rw [physicalFourier_eq_mixed]
  exact calibration_mixed_fourier_zero S hS (A*s) (mul_ne_zero hA hs) hcop (movingQuotient A s hs) H hH

theorem actualCongruenceCoefficient_zero_off_calibration (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA H=0 := by
  have he := actualPhysicalFourier_zero_off_calibration S hS A s hA hs hcop H hH
  rw [actualPhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  exact (mul_eq_zero.mp he).resolve_left hn

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein GaussianShiftedPartition CanonicalRowCompletion
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve 
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

lemma movingQuotient_unit_scale (A s : O) (hs : Supported (Ideal.span {s}))
    (b : O) (hcop : IsCoprime b s) (x : Residue (A*s)) :
    movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (Ideal.Quotient.mk _ b*x) =
      idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹ *
        movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) x := by
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, movingQuotient_mk, movingQuotient_mk, idealRowHom_argument_mul]
  rw [show -(b*m)=b*(-m) by ring, sexticGauss_unit_scale s hs b (-m) hcop]
  ring

def barePhysicalFourier (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  elementFourier (A*s) (mul_ne_zero hA hs)
    (fun m => idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H

theorem actualPhysicalFourier_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualPhysicalFourier C A s hA (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      barePhysicalFourier A s hA (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  rw [physicalFourier_eq_mixed, calibration_mixed_fourier S hS (A*s)
    (mul_ne_zero hA (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs)) hcop]
  dsimp only [C] at hcs ⊢
  simp_rw [movingQuotient_unit_scale A s hs (calibrationForSet S hS).generator hcs]
  simp only [mul_assoc, tsum_mul_left]
  rfl

def bareCongruenceCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient A s hA (outerQuotient A) (outerQuotient s) H

lemma barePhysicalFourier_eq (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    barePhysicalFourier A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ)*bareCongruenceCoefficient A s hA H := by
  unfold bareCongruenceCoefficient
  rw [← fullFourier_eq_congruence A s hA hs]
  unfold barePhysicalFourier elementFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction A s m = Ideal.Quotient.mk (Ideal.span {A}) (representative (A*s) m) := by
    conv_lhs => rw [← representative_spec (A*s) m]
    rfl
  rw [he]
  rw [outerQuotient_mk]

theorem actualCongruenceCoefficient_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s hA H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      bareCongruenceCoefficient A s hA H := by
  dsimp only
  have he := actualPhysicalFourier_calibration_factor S hS A s hA hs hcop H
  dsimp only at he
  rw [actualPhysicalFourier_eq, barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CubicEisenstein
local notation "O" => Eisenstein.O

lemma Xi_apply (C : CalibrationData) (a : O) :
    C.Xi a = C.residueMonoid a * idealRowHom C.generator (Ideal.span {a}) := rfl

theorem calibration_coefficient_cancel (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H *
      idealRowHom C.generator (Ideal.span {s}) /
        ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid H)) *
      (C.Xi A)⁻¹ = bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcA : IsCoprime C.generator A := hcop.of_mul_right_left
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  have hXA : C.Xi A≠0 := by
    intro h
    have hn := C.Xi_norm_one A hA hcA
    rw [h, norm_zero] at hn
    norm_num at hn
  have hXs : C.Xi s≠0 := by
    intro h
    have hn := C.Xi_norm_one s hs hcs
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [Xi_apply] at hXA hXs
  have hηA := left_ne_zero_of_mul hXA
  have hκA := right_ne_zero_of_mul hXA
  have hηs := left_ne_zero_of_mul hXs
  have hκs := right_ne_zero_of_mul hXs
  have hηH : C.residueMonoid H≠0 :=
    C.residue.apply_ne_zero_iff.mpr ((isUnit_quotient_span_iff C.generator H).mpr hH)
  have hηHstar : star (C.residueMonoid H)≠0 := star_ne_zero.mpr hηH
  have hτ : C.tau≠0 := calibrationForSet_tau_ne_zero S hS
  have hq : 0< elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hroot : (Real.sqrt (elementNorm C.generator):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have he := actualCongruenceCoefficient_calibration_factor S hS A s
    (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) hs hcop H
  dsimp only at he
  rw [he, Xi_apply, map_mul]
  change _ = bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H
  dsimp only [C] at hηA hκA hηs hκs hηHstar hτ hroot
  field_simp

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeRow
open Eisenstein CompletedGauss CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve
open ProbeCompleted
local notation "O" => Eisenstein.O

def baseRowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O →* ℂ :=
  targetMonoid η * ProbeRow.conjugateMonoid Xi * reciprocityPhaseMonoid s ((supported_iff_native _).mp hs)

lemma spectralSummand_mul_fixed_twist (S : Finset (Ideal O)) (D I J : Ideal O)
    (φ Ψ : O →* ℂ) (t : ℂ) :
    spectralSummand S D (φ*Ψ) t I J =
      φ (completedIndex I J) * spectralSummand S D Ψ t I J := by
  have hc (η : O →* ℂ) : cubeWeight η J =
      star (CompletedGauss.angularFactor (primaryIdealGenerator J))^3 *
        η (primaryIdealGenerator J)^3 / (Ideal.absNorm J:ℂ) := rfl
  unfold spectralSummand
  rw [hc, hc]
  simp only [columnWeight, MonoidHom.mul_apply, map_mul, map_pow, mul_pow, completedIndex]
  ring

theorem spectralSummand_row_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (Xi : O →* ℂ) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    spectralSummand S D (rowCoefficient η Xi s hs m) t I J =
      idealRowHom m (Ideal.span {completedIndex I J}) *
        spectralSummand S D (baseRowCoefficient η Xi s hs) t I J := by
  have hr : rowCoefficient η Xi s hs m =
      ((idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom) *
        baseRowCoefficient η Xi s hs := by
    change _ * _ = _ * _
    exact mul_comm _ _
  rw [hr, spectralSummand_mul_fixed_twist]
  rfl

theorem calibrated_spectralSummand_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : ProbePhysical.CalibrationData) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    C.residueMonoid m * spectralSummand S D (rowCoefficient η C.Xi s hs m) t I J =
      ProbePhysical.calibratedNumerator C (completedIndex I J) m *
        spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J := by
  rw [spectralSummand_row_separation]
  unfold ProbePhysical.calibratedNumerator
  ring

theorem spectralSummand_zero_completedIndex (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (t : ℂ) (hz : completedIndex I J=0) :
    spectralSummand S D Ψ t I J=0 := by
  rcases mul_eq_zero.mp hz with hI | hJ
  · have hg : squarefreeGaussCoefficient I=0 := by
      exact squarefreeGaussCoefficient_of_primary_zero I hI
    simp only [spectralSummand, columnWeight, hg, zero_mul, zero_div, mul_zero]
  · have hJ' : primaryIdealGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (CompletedGauss.angularFactor (primaryIdealGenerator J))^3 *
        Ψ (primaryIdealGenerator J)^3 / (Ideal.absNorm J:ℂ)=0
      simp [hJ', CompletedGauss.angularFactor]
    simp only [spectralSummand, hc, mul_zero, zero_mul]

end ProbeRow
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein CompletedGauss
local notation "O" => Eisenstein.O

theorem elementWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun m : O => W (elementNorm m / R))).Finite := by
  obtain ⟨B, _hB, hbound⟩ := compact_window_bound W hW
  apply (Eisenstein.finite_norm_sublevel (Real.sqrt (B*R))).subset
  intro m hm
  have hnorm : ‖ringComplex m‖^2 ≤ B*R := by
    rw [ringComplex_norm_sq_eq_absNorm_span]
    exact (div_le_iff₀ hR).mp (hbound _ hm)
  calc
    _ = Real.sqrt (‖ringComplex m‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hnorm

theorem idealWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (Ideal.finite_setOf_absNorm_le M).subset
  intro I hI
  have hnorm : (Ideal.absNorm I : ℝ) ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hI)
  exact_mod_cast hnorm.trans hM.le

theorem elementWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : O → ℂ) :
    Summable (fun m : O => W (elementNorm m / R) * F m) := by
  apply summable_of_hasFiniteSupport
  apply (elementWindow_finite_support W hW R hR).subset
  intro m hm hzero
  exact hm (by simp only [hzero, zero_mul])

theorem idealWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : Ideal O → ℂ) :
    Summable (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R) * F I) := by
  apply summable_of_hasFiniteSupport
  apply (idealWindow_finite_support W hW R hR).subset
  intro I hI hzero
  exact hI (by simp only [hzero, zero_mul])

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CompletedGauss ProbeCompleted ProbeRow _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => Eisenstein.O

lemma finite_support_tsum_comm {α β : Type*} (f : α → β → ℂ) (S : Finset α)
    (hz : ∀ a, a∉S → ∀ b, f a b=0) (hs : ∀ a∈S, Summable (f a)) :
    (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b := by
  calc
    _ = ∑ a∈S, ∑' b, f a b := tsum_eq_sum (fun a ha => by simp only [hz a ha, tsum_zero])
    _ = ∑' b, ∑ a∈S, f a b := (Summable.tsum_finsetSum hs).symm
    _ = _ := by
      apply tsum_congr
      intro b
      exact (tsum_eq_sum (fun a ha => hz a ha b)).symm

theorem physical_spectral_reopen (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O)
    (hs : Supported (Ideal.span {s})) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (K : ℝ) (hK : 0< K) (t : ℂ) (ht : 1< t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, spectralSummand S D (baseRowCoefficient η C.Xi s hs) t p.1 p.2 *
      ∑' m : O, calibratedNumerator C (completedIndex p.1 p.2) m *
        sexticGauss s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (-m) * W (elementNorm m/K) := by
  let F (m : O) (p : Ideal O × Ideal O) : ℂ :=
    C.residueMonoid m * sexticGauss s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (-m) * W (elementNorm m/K) *
      spectralSummand S D (rowCoefficient η C.Xi s hs m) t p.1 p.2
  have hfin := elementWindow_finite_support W hW K hK
  have hzero : ∀ m, m∉hfin.toFinset → ∀ p, F m p=0 := by
    intro m hm p
    have hz : W (elementNorm m/K)=0 := by simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hm
    simp only [F, hz, mul_zero, zero_mul]
  have hsum (m : O) : Summable (F m) :=
    (spectralRow_summable S D (rowCoefficient η C.Xi s hs m)
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m) t ht).mul_left _
  have he := finite_support_tsum_comm F hfin.toFinset hzero (fun m _ => hsum m)
  calc
    _ = ∑' m : O, ∑' p : Ideal O × Ideal O, F m p := by
      simp only [F, spectralRow, tsum_mul_left]
    _ = ∑' p : Ideal O × Ideal O, ∑' m : O, F m p := he
    _ = _ := by
      apply tsum_congr
      intro p
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      unfold F
      rw [spectralSummand_row_separation]
      unfold calibratedNumerator
      ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace ProbeRow
open Eisenstein CompletedGauss CubicEisenstein
local notation "O" => Eisenstein.O

theorem spectralSummand_norm_eq_of_re (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (s t : ℂ) (h : s.re = t.re) (I J : Ideal O) :
    ‖spectralSummand S D Ψ s I J‖ = ‖spectralSummand S D Ψ t I J‖ := by
  have h3 : (3 * s).re = (3 * t).re := by simp [Complex.mul_re, h]
  simp only [spectralSummand, norm_mul, fullIdealWeight_norm_eq_of_re _ _ h,
    fullIdealWeight_norm_eq_of_re _ _ h3]

def mellinSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (p : Ideal O × Ideal O) (y : ℝ) : ℂ :=
  (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) * Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
    spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem mellinSummand_norm (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) (y : ℝ) :
    ‖mellinSummand S D Ψ σ Z p y‖ =
      (Z ^ σ * Real.exp (σ ^ 2) * ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖) *
        Real.exp (-1 * y ^ 2) := by
  unfold mellinSummand
  rw [norm_mul, verticalKernel_norm Z hZ σ y,
    spectralSummand_norm_eq_of_re S D Ψ _ (σ : ℂ) (by simp)]
  ring

theorem mellinSummand_integrable (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) :
    Integrable (mellinSummand S D Ψ σ Z p) := by
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have ht : Continuous (fun y : ℝ => spectralSummand S D Ψ
      ((σ : ℂ) + y * Complex.I) p.1 p.2) :=
    continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
      ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply ((integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖)).mono'
    (hk.mul ht).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => (mellinSummand_norm S D Ψ σ Z hZ p y).le)

theorem mellinSummand_integral_norm (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) :
    (∫ y : ℝ, ‖mellinSummand S D Ψ σ Z p y‖) =
      ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖ *
        (Z ^ σ * Real.exp (σ ^ 2) * ∫ y : ℝ, Real.exp (-1 * y ^ 2)) := by
  simp only [mellinSummand_norm S D Ψ σ Z hZ, integral_const_mul]
  ring

/-- Absolute Gaussian domination permits termwise Mellin integration. -/
theorem spectralRow_integral_eq_tsum (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    (∫ y : ℝ, (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) =
      ∑' p, ∫ y : ℝ, mellinSummand S D Ψ σ Z p y := by
  let : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
  let : Countable (Ideal O) := cubicIdealGenerator_injective.countable
  have hs : Summable (fun p => ∫ y : ℝ, ‖mellinSummand S D Ψ σ Z p y‖) := by
    simp only [mellinSummand_integral_norm S D Ψ σ Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (σ : ℂ) hσ).norm.mul_right _
  rw [integral_tsum_of_summable_integral_norm
    (fun p => mellinSummand_integrable S D Ψ σ Z hZ p) hs]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [mellinSummand, tsum_mul_left, spectralRow]

end ProbeRow
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
