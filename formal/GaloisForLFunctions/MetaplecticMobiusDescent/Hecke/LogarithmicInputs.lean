/-
Logarithmic inputs adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DyadicHeckePolynomials

/-!
# Logarithmic inputs

Radicals of deletion bounds, presentation complexity and uniform constants of the logarithmic
inputs; central loss parameters and squared dyadic bounds.
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
open scoped Classical Topology
open Set
namespace HeckeLogarithmicInput
open HeckeFamily

def regular (η : Character) (s : ℂ) : ℂ :=
  if η.residue = 1 then HeckePrincipalStrip.sourceNormalized η s else LFunction η s

theorem regular_eq_nonprincipal (η : Character) (hη : η.residue ≠ 1) :
    regular η = LFunction η := by funext s; simp [regular, hη]

theorem regular_differentiableAt (η : Character) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regular η) s := by
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · have he : regular η = HeckePrincipalStrip.sourceNormalized η := by
      funext z; simp [regular, hη]
    rw [he]
    exact (HeckeOrigin.poleRemoved_entire η s).div (differentiableAt_id.add_const 1) hplus
  · rw [regular_eq_nonprincipal η hη]
    exact LFunction_entire_nonprincipal η hη s

theorem regular_ne_zero (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regular η s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith [HeckeZeroSupremum.half_le_beta]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · simp only [regular, if_pos hη, HeckePrincipalStrip.sourceNormalized]
    apply div_ne_zero _ hplus
    by_cases h1 : s = 1
    · subst s; exact HeckeOrigin.poleRemoved_one_ne_zero η hη
    · rw [HeckeOrigin.poleRemoved_eq η h0 h1]
      exact mul_ne_zero (sub_ne_zero.mpr h1)
        (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inl h1))
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inr hη)

theorem regular_inverse_differentiableAt (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) :
    DifferentiableAt ℂ (fun z => (regular η z)⁻¹) s :=
  (regular_differentiableAt η (by linarith [HeckeZeroSupremum.half_le_beta])).inv
    (regular_ne_zero η hs)

theorem principal_regular_factor_bound {s : ℂ} (hs : 0 ≤ s.re) :
    ‖s-1‖ ≤ ‖s+1‖ := by
  have he : ‖s+1‖^2 - ‖s-1‖^2 = 4*s.re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  nlinarith [norm_nonneg (s-1), norm_nonneg (s+1)]

theorem regular_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖regular η s‖ ≤ HeckeReciprocalBound.bound σ := by
  by_cases hη : η.residue = 1
  · have h0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
    have h1 : s ≠ 1 := by intro h; simp [h] at hs; linarith
    have hp : 0 < ‖s+1‖ := by
      have hr := Complex.re_le_norm (s+1)
      simp only [Complex.add_re, Complex.one_re] at hr
      linarith
    simp only [regular, if_pos hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, norm_div, norm_mul]
    apply le_trans _ (HeckeStripActual.LFunction_norm_le η hσ hs)
    apply (div_le_iff₀ hp).mpr
    nlinarith [principal_regular_factor_bound (s := s) (by linarith), norm_nonneg (LFunction η s)]
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeStripActual.LFunction_norm_le η hσ hs

theorem regular_inverse_norm_le (η : Character) {s : ℂ} (hs : (3/2 : ℝ) ≤ s.re) :
    ‖(regular η s)⁻¹‖ ≤ 5 * HeckeReciprocalBound.bound (3/2) := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hL := HeckeReciprocalBound.reciprocal_norm_le η (by norm_num : (1 : ℝ)<3/2) hs
  rw [HeckeReciprocal.reciprocal_eq_inv η h0 h1] at hL
  have hB : 0 ≤ HeckeReciprocalBound.bound (3/2) := tsum_nonneg (fun _ => norm_nonneg _)
  by_cases hη : η.residue = 1
  · have hlow : (1/2 : ℝ) ≤ ‖s-1‖ := by
      have hr := Complex.re_le_norm (s-1)
      simp only [Complex.sub_re, Complex.one_re] at hr
      linarith
    have hratio : ‖s+1‖ / ‖s-1‖ ≤ 5 := by
      apply (div_le_iff₀ (by linarith : 0 < ‖s-1‖)).mpr
      have hr := norm_add_le (s-1) (2 : ℂ)
      norm_num only [Complex.norm_ofNat] at hr
      rw [show s-1+2=s+1 by ring] at hr
      linarith
    simp only [regular, if_pos hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, inv_div, norm_div, norm_mul]
    calc
      _ = (‖s+1‖ / ‖s-1‖) * ‖(LFunction η s)⁻¹‖ := by rw [norm_inv]; ring
      _ ≤ _ := mul_le_mul hratio hL (norm_nonneg _) (by norm_num)
  · rw [regular_eq_nonprincipal η hη]
    linarith

def uniformConstant : ℝ :=
  108*((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10))

theorem uniformConstant_nonneg : 0 ≤ uniformConstant := by
  have hc := HeckeStrip.leftConstant_pos
  have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
  unfold uniformConstant
  positivity

theorem modulus_norm_ge_one (η : Character) : 1 ≤ (η.modulus.absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

theorem regular_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (z : ℂ)
    (hz : z ∈ HeckeStrip.closedStrip) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hη : η.residue = 1
  · simpa only [regular, if_pos hη, uniformConstant] using
      HeckePrincipalStrip.uniform_source_normalized_strip_bound η hp z hz
  · rw [regular_eq_nonprincipal η hη]
    apply (HeckePresentation.uniform_strip_bound η hp hη z hz).trans
    have hc := HeckeStrip.leftConstant_pos
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    unfold uniformConstant
    gcongr ; norm_num

theorem regular_right_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) {z : ℂ}
    (hz : -(1/10 : ℝ) ≤ z.re) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hright : z.re ≤ 11/10
  · exact regular_strip_bound η hp z ⟨hz, hright⟩
  · apply (regular_norm_le η (by norm_num : (1 : ℝ)<11/10) (le_of_not_ge hright)).trans
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    have hc := HeckeStrip.leftConstant_pos
    have hC : HeckeReciprocalBound.bound (11/10) ≤ uniformConstant := by
      unfold uniformConstant; nlinarith
    have hQ : 1 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
      Real.one_le_rpow (modulus_norm_ge_one η) (by norm_num)
    have hT : 1 ≤ (3+|z.im|)^2 := by nlinarith [abs_nonneg z.im]
    exact hC.trans ((le_mul_of_one_le_right uniformConstant_nonneg hQ).trans
      (le_mul_of_one_le_right (mul_nonneg uniformConstant_nonneg (by linarith : 0 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ))) hT))

theorem regular_ne_zero_on_disk (η : Character) (a e t : ℝ)
    (ha : HeckeZeroSupremum.beta ≤ a) (he : 0 < e) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    regular η z ≠ 0 := by
  apply regular_ne_zero η
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ < 2-a-2*e := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hrl := neg_abs_le (z-((2 : ℂ)+t*Complex.I)).re
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re] at hr hrl
  linarith

theorem reciprocal_norm_le_regular_inverse (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) :
    ‖HeckeReciprocal.reciprocal η s‖ ≤ ‖(regular η s)⁻¹‖ := by
  have hs0 : 0 < s.re := by linarith [HeckeZeroSupremum.half_le_beta]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  by_cases hη : η.residue = 1
  · by_cases h1 : s = 1
    · subst s
      rw [HeckeReciprocal.reciprocal_principal_one η hη, norm_zero]
      exact norm_nonneg _
    have hp : s+1 ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
      linarith
    have hL := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inl h1)
    have he : HeckeReciprocal.reciprocal η s =
        ((s-1)/(s+1))*(regular η s)⁻¹ := by
      rw [HeckeReciprocal.reciprocal_eq_inv η h0 h1]
      simp only [regular, if_pos hη, HeckePrincipalStrip.sourceNormalized,
        HeckeOrigin.poleRemoved_eq η h0 h1]
      field_simp
    rw [he, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hp)).mpr (principal_regular_factor_bound hs0.le)
  · simp only [HeckeReciprocal.reciprocal, regular, if_neg hη, le_refl]

theorem regular_disk_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (a e t : ℝ)
    (ha : (1/2 : ℝ) ≤ a) (he : 0 ≤ e) {z : ℂ}
    (hz : z ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    ‖regular η z‖ ≤ (4*uniformConstant) * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|t|)^2 := by
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (z-((2 : ℂ)+t*Complex.I))
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.sub_im, Complex.add_im, Complex.mul_im] at hr hi
  have hzre : -(1/10 : ℝ) ≤ z.re := by
    have hh := neg_abs_le (z.re-2)
    linarith
  have hheight : 3+|z.im| ≤ 2*(3+|t|) := by
    have hab := abs_add_le (z.im-t) t
    rw [sub_add_cancel] at hab
    linarith [abs_nonneg t]
  apply (regular_right_growth η hp hzre).trans
  have hsq : (3+|z.im|)^2 ≤ 4*(3+|t|)^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|)
      (by positivity : 0 ≤ 2*(3+|t|))).mpr hheight
    nlinarith
  calc
    _ ≤ uniformConstant*(η.modulus.absNorm : ℝ)^(3/5 : ℝ)*(4*(3+|t|)^2) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg uniformConstant_nonneg (Real.rpow_nonneg (by positivity) _))
    _ = _ := by ring

end HeckeLogarithmicInput

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Set Metric
namespace HeckeLogarithmic
open HeckeFamily HeckeLogarithmicInput

def complexity (η : Character) (t : ℝ) : ℝ :=
  2*(η.modulus.absNorm : ℝ)*(3+|t|)^2

theorem complexity_ge_exp (η : Character) (t : ℝ) : Real.exp 1 ≤ complexity η t :=
  LogarithmicControl.conductor_height_scale_ge_exp _ t (modulus_norm_ge_one η)

theorem regular_disk_differentiable (η : Character) {a e t : ℝ}
    (ha : (1/2 : ℝ) ≤ a) (he : 0 < e) :
    DifferentiableOn ℂ (regular η) (ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) := by
  intro z hz
  exact (regular_differentiableAt η (by
    have hr := LogarithmicControl.disk_re_gt hz
    linarith)).differentiableWithinAt

theorem exists_uniform_polynomial_exponent :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ a e t : ℝ, 1/2 ≤ a → 0 < e → ∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-3*e),
        ‖regular η z‖ ≤ (complexity η t)^M := by
  obtain ⟨M, hM, hb⟩ := LogarithmicControl.absorb_polynomial_constant
    (K := 2*uniformConstant) (p := 1) (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro η hp a e t ha he z hz
  have hz2 : z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz
  have h := regular_disk_growth η hp a e t ha he.le hz2
  have hQ : (η.modulus.absNorm : ℝ)^(3/5 : ℝ) ≤ (η.modulus.absNorm : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (modulus_norm_ge_one η)
      (show (3/5 : ℝ)≤1 by norm_num)
  apply h.trans
  calc
    _ ≤ (4*uniformConstant)*(η.modulus.absNorm : ℝ)*(3+|t|)^2 := by
      gcongr
      exact mul_nonneg (by norm_num) uniformConstant_nonneg
    _ = (2*uniformConstant)*complexity η t := by unfold complexity; ring
    _ ≤ (complexity η t)^M := by simpa only [Real.rpow_one] using hb _ (complexity_ge_exp η t)

theorem disk_control_of_euler_log (e A ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ D B : ℝ, 0 < D ∧ 0 ≤ B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ (a t : ℝ) (E : ℂ → ℂ),
      1/2 ≤ a → a ≤ 1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      DifferentiableOn ℂ E (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      EqOn (Complex.exp ∘ E) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨M,hM,hpoly⟩ := exists_uniform_polynomial_exponent
  obtain ⟨D,hD,hb⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, LogarithmicControl.outerConstant e A M/(2*e), hD, ?_, ?_⟩
  · have hB := LogarithmicControl.outerConstant_ge_one he he' hA hM
    positivity
  · intro η hp a t E ha ha' hzero hE hEL hEb
    exact hb a (complexity η t) (regular η) E ((2 : ℂ)+t*Complex.I) ha ha'
      (complexity_ge_exp η t) (regular_disk_differentiable η ha he) hzero
      (hpoly η hp a e t ha he) hE hEL hEb

end HeckeLogarithmic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology BigOperators
open Set Metric Filter Complex Eisenstein
open IdealEuler IdealCharacter
open HeckeIdealSeries (PrimeIdeal)

namespace HeckeIdealSeries

lemma prime_norm_series_summable (σ : ℝ) (hσ : 0 < σ) :
    Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val : ℝ)^(-(1+σ))) := by
  have ht := (fullIdealWeight_summable_norm (1+(σ : ℂ))
    (by simp; linarith)).comp_injective
      (i := fun P : PrimeIdeal => P.val) Subtype.val_injective
  apply ht.congr
  intro P
  simp only [Function.comp_def, fullIdealWeight, if_neg P.property.ne_zero]
  simpa only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-(1+(σ : ℂ))))

lemma prod_primeSet {M : Type*} [CommMonoid M] (I : Ideal O) (f : Ideal O → M) :
    (∏ P ∈ primeSet I, f P.val) = ∏ P ∈ primeSupport I, f P := by
  unfold primeSet
  rw [Finset.prod_image]
  · exact Finset.prod_attach (primeSupport I) f
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

end HeckeIdealSeries

namespace HeckeEulerLog

def eulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' P : PrimeIdeal, -Complex.log (1 - weighted a s P.val)

def majorant (σ : ℝ) (P : PrimeIdeal) : ℝ :=
  (3 / 2) * (Ideal.absNorm P.val : ℝ) ^ (-σ)

theorem majorant_summable {σ : ℝ} (hσ : 1 < σ) : Summable (majorant σ) := by
  have h := (HeckeIdealSeries.prime_norm_series_summable (σ - 1)
    (by linarith)).mul_left (3 / 2)
  have he : -(1+(σ-1)) = -σ := by ring
  simp only [he] at h
  convert h using 1 <;> (ext x y <;> rfl)

theorem weighted_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) :
    ‖weighted a s P.val‖ ≤ (Ideal.absNorm P.val : ℝ) ^ (-σ) := by
  change ‖a P.val * fullIdealWeight s P.val‖ ≤ _
  simp only [fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖HeckeIdealSeries.primeNormPower P s‖ ≤ _
  rw [HeckeIdealSeries.norm_primeNormPower]
  have hn : (1 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast (show 1 ≤ Ideal.absNorm P.val from
      (by have := HeckeIdealSeries.prime_norm_two_le P; omega))
  exact (mul_le_of_le_one_left (by positivity) (ha _)).trans
    (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))

theorem weighted_norm_le_half (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} (hs : 1 ≤ s.re) : ‖weighted a s P.val‖ ≤ 1 / 2 := by
  refine (weighted_norm_le a ha P hs).trans ?_
  rw [Real.rpow_neg_one]
  have hn : (2 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast HeckeIdealSeries.prime_norm_two_le P
  exact inv_le_of_inv_le₀ (by norm_num) (by norm_num at *; exact hn)

theorem log_factor_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant σ P := by
  have hhalf := weighted_norm_le_half a ha P (hσ.trans hs)
  have h := Complex.norm_log_one_add_half_le_self
    (z := -weighted a s P.val) (by simpa using hhalf)
  simp only [norm_neg, ← sub_eq_add_neg] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left (weighted_norm_le a ha P hs) (by norm_num))

theorem weighted_differentiable (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    Differentiable ℂ (fun s ↦ weighted a s P.val) := by
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (HeckeIdealSeries.prime_norm_pos P).ne'
  change Differentiable ℂ (fun s ↦ a P.val * fullIdealWeight s P.val)
  simp only [fullIdealWeight, P.property.ne_zero, ite_false]
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem log_factor_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) :
    DifferentiableOn ℂ (fun s ↦ -Complex.log (1 - weighted a s P.val)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hn := prime_norm_lt_one a ha s (by linarith : 0 < s.re) P
  have hslit : 1 - weighted a s P.val ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -weighted a s P.val) (by simpa using hn)
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub (weighted_differentiable a P s))).neg.differentiableWithinAt

theorem eulerLog_differentiableOn_halfplane (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) : DifferentiableOn ℂ (eulerLog a) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (majorant_summable hσ)
  · intro P
    exact (log_factor_differentiableOn a ha P).mono (fun s hs ↦ hσ.trans hs)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro P s hs
    exact log_factor_norm_le a ha P hσ.le hs.le

theorem eulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (eulerLog a) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hσ : 1 < (1 + s.re) / 2 := by linarith
  have hmem : s ∈ {w : ℂ | (1 + s.re) / 2 < w.re} := by dsimp; linarith
  exact ((eulerLog_differentiableOn_halfplane a ha hσ s hmem).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem exp_eulerLog_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Complex.exp (eulerLog a s) = series a s :=
  HeckeBoundary.exp_log_euler_eq_series a ha s hs

def eulerLogBound : ℝ := 1 + ∑' P : PrimeIdeal, majorant (3 / 2) P

theorem eulerLogBound_ge_one : 1 ≤ eulerLogBound := by
  unfold eulerLogBound
  have h : 0 ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P :=
    tsum_nonneg (fun P ↦ by unfold majorant; positivity)
  linarith

theorem eulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hb : ∀ P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant (3 / 2) P :=
    fun P ↦ log_factor_norm_le a ha P (by norm_num) hs
  have hsum := majorant_summable (by norm_num : (1 : ℝ) < 3 / 2)
  have hnorm : Summable (fun P : PrimeIdeal ↦ ‖-Complex.log (1 - weighted a s P.val)‖) :=
    hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc
    ‖eulerLog a s‖ ≤ ∑' P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P := hnorm.tsum_le_tsum hb hsum
    _ ≤ eulerLogBound := by unfold eulerLogBound; linarith

theorem inner_disk_re {t : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (2 + (t : ℂ) * Complex.I) (1 / 2)) : 3 / 2 ≤ s.re := by
  have hn : ‖(2 + (t : ℂ) * Complex.I) - s‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs
  have hr := Complex.re_le_norm ((2 + (t : ℂ) * Complex.I) - s)
  norm_num at hr
  linarith

theorem eulerLog_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) (series a)
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(eulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact exp_eulerLog_eq_series a ha s (hsub hs)
  · intro s hs
    exact eulerLog_norm_le a ha (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ) (hL : ∀ s : ℂ, 1 < s.re → L s = series a s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) L (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  obtain ⟨hd, he, hb⟩ := eulerLog_inner_disk a ha t
  refine ⟨hd, ?_, hb⟩
  intro s hs
  have hr := inner_disk_re (ball_subset_closedBall hs)
  exact (he hs).trans (hL s (by linarith)).symm

def principalLog (s : ℂ) : ℂ := Complex.log (1 - 2 / (s + 1))

theorem norm_two_div_add_one_lt_one {s : ℂ} (hs : 1 < s.re) :
    ‖(2 : ℂ) / (s + 1)‖ < 1 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_lt_one hn).mpr (by linarith)

theorem norm_two_div_add_one_le {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖(2 : ℂ) / (s + 1)‖ ≤ 4 / 5 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ hn).mpr (by linarith)

theorem principalLog_differentiableOn :
    DifferentiableOn ℂ principalLog {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hnorm := norm_two_div_add_one_lt_one hs
  have hslit : 1 - (2 : ℂ) / (s + 1) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, neg_div] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -(2 : ℂ) / (s + 1)) (by simpa using hnorm)
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (2 : ℂ)).div
      (differentiableAt_id.add_const 1) hs1))).differentiableWithinAt

theorem exp_principalLog {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalLog s) = (s - 1) / (s + 1) := by
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [principalLog, Complex.exp_log (HeckeIdealSeries.one_sub_ne_zero
    (norm_two_div_add_one_lt_one hs))]
  field_simp
  ring

theorem principalLog_norm_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalLog s‖ ≤ 3 := by
  have hb := norm_two_div_add_one_le hs
  have hlt : ‖-(2 : ℂ) / (s + 1)‖ < 1 := by simpa using hb.trans_lt (by norm_num : (4 : ℝ) / 5 < 1)
  have h := Complex.norm_log_one_add_le hlt
  have hn : ‖-(2 : ℂ) / (s + 1)‖ = ‖(2 : ℂ) / (s + 1)‖ := by simp
  rw [hn] at h
  have heq : 1 + -(2 : ℂ) / (s + 1) = 1 - 2 / (s + 1) := by ring
  rw [heq] at h
  change ‖principalLog s‖ ≤ _ at h
  have hden : 0 < 1 - ‖(2 : ℂ) / (s + 1)‖ := by linarith
  have hinv : (1 - ‖(2 : ℂ) / (s + 1)‖)⁻¹ ≤ 5 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hnorm := norm_nonneg ((2 : ℂ) / (s + 1))
  have hsq : ‖(2 : ℂ) / (s + 1)‖ ^ 2 ≤ 16 / 25 := by nlinarith
  have hmul := mul_le_mul hsq hinv (inv_nonneg.mpr hden.le) (by norm_num : (0 : ℝ) ≤ 16 / 25)
  nlinarith

def principalEulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := principalLog s + eulerLog a s

theorem principalEulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (principalEulerLog a) {s : ℂ | 1 < s.re} :=
  principalLog_differentiableOn.add (eulerLog_differentiableOn a ha)

theorem exp_principalEulerLog (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalEulerLog a s) = ((s - 1) / (s + 1)) * series a s := by
  rw [principalEulerLog, Complex.exp_add, exp_principalLog hs, exp_eulerLog_eq_series a ha s hs]

theorem principalEulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound :=
  (norm_add_le _ _).trans (add_le_add (principalLog_norm_le hs) (eulerLog_norm_le a ha hs))

theorem principal_continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) (t : ℝ) :
    DifferentiableOn ℂ (principalEulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ principalEulerLog a) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(principalEulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact (exp_principalEulerLog a ha (hsub hs)).trans (hL s (hsub hs)).symm
  · intro s hs
    exact principalEulerLog_norm_le a ha
      (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem residue_continued_inner_disk (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog (ofResidue M χ hχ))
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog (ofResidue M χ hχ)) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog (ofResidue M χ hχ) s‖ ≤ eulerLogBound :=
  continued_inner_disk _ (norm_ofResidue_le_one M χ hχ) L hL t

theorem continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e eulerLogBound M / (2 * e)) * Real.log C) := by
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he'
    eulerLogBound_ge_one hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := continued_inner_disk a ha L hEq t
  exact hbound b C L (eulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

theorem principal_continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e (3 + eulerLogBound) M / (2 * e)) * Real.log C) := by
  have hA : 1 ≤ 3 + eulerLogBound := by linarith [eulerLogBound_ge_one]
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := principal_continued_inner_disk a ha L hEq t
  exact hbound b C L (principalEulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

end HeckeEulerLog

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDeletionBounds
open HeckeFamily

theorem constant_pow_primeSupport_bound (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Ideal O, M ≠ ⊥ →
      K^(primeSupport M).card ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 1)
  have hn0 : 0 < (n : ℝ) := by linarith [le_max_right K 1]
  have hKpow : K ≤ (2 : ℝ)^n := by
    have hn2 : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self).le
    linarith [le_max_left K 1]
  obtain ⟨C, hC, hbound⟩ := CompletedGauss.prime_support_subsets_bound
    (ε/(n : ℝ)) (div_pos hε hn0)
  refine ⟨C ^ n, by positivity, ?_⟩
  intro M hM
  calc
    _ ≤ ((2 : ℝ)^n)^(primeSupport M).card :=
      pow_le_pow_left₀ hK hKpow _
    _ = ((2 : ℝ)^(primeSupport M).card)^n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (C*(M.absNorm : ℝ)^(ε/(n : ℝ)))^n :=
      pow_le_pow_left₀ (by positivity) (hbound M hM) n
    _ = C ^ n*(M.absNorm : ℝ)^ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), div_mul_cancel₀ _ hn0.ne']

def localBound (σ : ℝ) : ℝ := (1-(2 : ℝ)^(-σ))⁻¹

theorem localBound_pos {σ : ℝ} (hσ : 0 < σ) : 0 < localBound σ := by
  unfold localBound
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

theorem term_bound {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖a*(N : ℂ)^(-s)‖ ≤ (2 : ℝ)^(-σ) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha).trans
  apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by linarith : -s.re ≤ -σ)).trans
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)

theorem factor_bounds {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖EulerFactors.factor N a s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor N a s)⁻¹‖ ≤ localBound σ := by
  have hδ : (2 : ℝ)^(-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hδ0 : 0 ≤ (2 : ℝ)^(-σ) := Real.rpow_nonneg (by norm_num) _
  have ht := term_bound hσ hN ha hs
  have hl : 1-(2 : ℝ)^(-σ) ≤ ‖EulerFactors.factor N a s‖ := by
    have hh := norm_sub_le (1-a*(N : ℂ)^(-s)) (-a*(N : ℂ)^(-s))
    have he : (1-a*(N : ℂ)^(-s))-(-a*(N : ℂ)^(-s)) = 1 := by ring
    rw [he, norm_one, neg_mul, norm_neg] at hh
    change 1-(2 : ℝ)^(-σ) ≤ ‖1-a*(N : ℂ)^(-s)‖
    linarith
  constructor
  · apply (norm_sub_le _ _).trans
    rw [norm_one]
    apply (add_le_add (le_refl 1) ht).trans
    unfold localBound
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr
    nlinarith [sq_nonneg ((2 : ℝ)^(-σ))]
  · rw [norm_inv]
    exact (inv_le_inv₀ (by linarith : 0 < ‖EulerFactors.factor N a s‖)
      (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr hl

theorem factors_bound_pow (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (localBound σ)^(primeSupport M).card ∧
    ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤
      (localBound σ)^(primeSupport M).card := by
  have hfactor (P : HeckeIdealSeries.PrimeIdeal) :
      ‖EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s)⁻¹‖ ≤ localBound σ :=
    factor_bounds hσ (by exact_mod_cast HeckeIdealSeries.prime_norm_two_le P)
      (idealCoeff_norm_le_one ψ P.val) hs
  have he : (∏ P ∈ HeckeIdealSeries.primeSet M, localBound σ) =
      (localBound σ)^(primeSupport M).card := by
    rw [HeckeIdealSeries.prod_primeSet M (fun _ => localBound σ)]
    simp
  constructor
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [norm_prod, ← he]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).1)
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [← Finset.prod_inv_distrib, norm_prod, ← he]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).2)

theorem factors_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O), M ≠ ⊥ → ∀ (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := constant_pow_primeSupport_bound (localBound σ) ε
    (localBound_pos hσ).le hε
  refine ⟨2*C, by positivity, ?_⟩
  intro M hM ψ s hs
  obtain ⟨h1, h2⟩ := factors_bound_pow σ hσ M ψ hs
  have h := hb M hM
  nlinarith

def radical (M : Ideal O) : Ideal O :=
  HeckeIdealSeries.primeProduct (HeckeIdealSeries.primeSet M)

theorem radical_ne_zero (M : Ideal O) : HeckeDeletionBounds.radical M ≠ 0 :=
  HeckeIdealSeries.primeProduct_ne_zero _

theorem factors_radical (M : Ideal O) (ψ : Character) (s : ℂ) :
    HeckeFiniteDeletion.factors (HeckeDeletionBounds.radical M) ψ s = HeckeFiniteDeletion.factors M ψ s := by
  unfold HeckeFiniteDeletion.factors HeckeDeletionBounds.radical
  rw [HeckeIdealSeries.primeSet_primeProduct]

theorem factors_radical_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*((HeckeDeletionBounds.radical M).absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := factors_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s hs
  simpa only [factors_radical] using hb (HeckeDeletionBounds.radical M) (radical_ne_zero M) ψ s hs

theorem factor_bound_any_re {N : ℝ} (hN : 2 ≤ N) {a s : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖EulerFactors.factor N a s‖ ≤ 2*N^(max (-s.re) 0) := by
  have hn : 1 ≤ N := by linarith
  have ht : ‖a*(N : ℂ)^(-s)‖ ≤ N^(-s.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha
  have hpow : N^(-s.re) ≤ N^(max (-s.re) 0) :=
    Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _)
  have h1 : 1 ≤ N^(max (-s.re) 0) := Real.one_le_rpow hn (le_max_right _ _)
  have hb := norm_sub_le (1 : ℂ) (a*(N : ℂ)^(-s))
  rw [norm_one] at hb
  change ‖1-a*(N : ℂ)^(-s)‖ ≤ _
  linarith

theorem factors_bound_any_re (M : Ideal O) (ψ : Character) (s : ℂ) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (2 : ℝ)^(HeckeIdealSeries.primeSet M).card *
        ((HeckeDeletionBounds.radical M).absNorm : ℝ)^(max (-s.re) 0) := by
  unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ P ∈ HeckeIdealSeries.primeSet M,
        2*(P.val.absNorm : ℝ)^(max (-s.re) 0) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro P _
      exact factor_bound_any_re (show (2 : ℝ) ≤ (P.val.absNorm : ℝ) by exact_mod_cast HeckeIdealSeries.prime_norm_two_le P)
        (idealCoeff_norm_le_one ψ P.val)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      simp only [HeckeDeletionBounds.radical, HeckeIdealSeries.primeProduct, map_prod, Nat.cast_prod]

theorem primeSet_card (M : Ideal O) :
    (HeckeIdealSeries.primeSet M).card =
      (primeSupport M).card := by
  unfold HeckeIdealSeries.primeSet
  rw [Finset.card_image_iff.mpr ?_, Finset.card_attach]
  intro P hP Q hQ h
  exact Subtype.ext (congrArg (fun R : HeckeIdealSeries.PrimeIdeal => R.val) h)

theorem factors_any_re_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
        C*((HeckeDeletionBounds.radical M).absNorm : ℝ)^(max (-s.re) 0 + ε) := by
  obtain ⟨C, hC, hb⟩ := CompletedGauss.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s
  have hR : 0 < ((HeckeDeletionBounds.radical M).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))
  have hc : (2 : ℝ)^(HeckeIdealSeries.primeSet M).card ≤ C*((HeckeDeletionBounds.radical M).absNorm : ℝ)^ε := by
    have h := hb (HeckeDeletionBounds.radical M) (radical_ne_zero M)
    rw [← primeSet_card, HeckeDeletionBounds.radical, HeckeIdealSeries.primeSet_primeProduct] at h
    exact h
  apply (factors_bound_any_re M ψ s).trans
  calc
    _ ≤ (C*((HeckeDeletionBounds.radical M).absNorm : ℝ)^ε)*((HeckeDeletionBounds.radical M).absNorm : ℝ)^(max (-s.re) 0) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [Real.rpow_add hR]; ring

end HeckeDeletionBounds

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeDeletionReciprocal
open HeckeFamily HeckeFiniteDeletion HeckeReciprocal HeckeDeletionBounds

theorem reciprocal_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    reciprocal χ s = reciprocal ψ s * (factors χ.modulus ψ s)⁻¹ := by
  by_cases hχ : χ.residue = 1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [reciprocal, if_pos hχ, if_pos hψ]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    simp only [reciprocal, if_neg hχ, if_neg hψ]
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs, mul_inv]

theorem exists_primitive_reciprocal_reduction (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : Character,
      ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
        (∀ I : Ideal O, idealCoeff χ I =
          if IsCoprime I χ.modulus then idealCoeff ψ I else 0) ∧
        ∀ s : ℂ, σ ≤ s.re →
          ‖reciprocal χ s‖ ≤ C*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε * ‖reciprocal ψ s‖ := by
  obtain ⟨C, hC, hb⟩ := factors_radical_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro χ
  obtain ⟨ψ, _, hp, hn, hm⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, hn, hm, ?_⟩
  intro s hs
  rw [reciprocal_eq_of_mask χ ψ hm (hσ.trans_le hs), norm_mul]
  have hf := hb χ.modulus ψ s hs
  have hfb : ‖(factors χ.modulus ψ s)⁻¹‖ ≤ C*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ s)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfb (norm_nonneg (reciprocal ψ s))

end HeckeDeletionReciprocal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Set Metric
namespace HeckeLogarithmicActual
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic

def eulerLog (η : Character) : ℂ → ℂ :=
  if η.residue = 1 then HeckeEulerLog.principalEulerLog (idealCoeff η)
  else HeckeEulerLog.eulerLog (idealCoeff η)

def innerBound : ℝ := 3+HeckeEulerLog.eulerLogBound

theorem innerBound_ge_one : 1 ≤ innerBound := by
  unfold innerBound
  linarith [HeckeEulerLog.eulerLogBound_ge_one]

theorem actual_inner_log (η : Character) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) ∧
    EqOn (Complex.exp ∘ eulerLog η) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) ∧
    ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖eulerLog η z‖ ≤ innerBound := by
  by_cases hη : η.residue = 1
  · have hright (s : ℂ) (hs : 1< s.re) : regular η s =
        ((s-1)/(s+1))*IdealEuler.series (idealCoeff η) s := by
      have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
      have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
      simp only [regular, if_pos hη, HeckePrincipalStrip.sourceNormalized]
      rw [HeckeOrigin.poleRemoved_eq η h0 h1, LFunction_eq_series η hs]
      ring
    simpa only [eulerLog, if_pos hη, innerBound] using
      HeckeEulerLog.principal_continued_inner_disk (idealCoeff η) (idealCoeff_norm_le_one η)
        (regular η) hright t
  · have hright (s : ℂ) (hs : 1< s.re) : regular η s = IdealEuler.series (idealCoeff η) s := by
      rw [regular_eq_nonprincipal η hη]
      exact LFunction_eq_series η hs
    obtain ⟨hd,he,hb⟩ := HeckeEulerLog.continued_inner_disk (idealCoeff η)
      (idealCoeff_norm_le_one η) (regular η) hright t
    simp only [eulerLog, if_neg hη]
    refine ⟨hd,he,?_⟩
    intro z hz
    have h := hb z hz
    unfold innerBound
    linarith

theorem disk_control (e ε : ℝ) (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D B : ℝ, 0< D ∧ 0≤ B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ a t : ℝ,
      1/2≤ a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨D,B,hD,hB,hb⟩ := disk_control_of_euler_log e innerBound ε he he' innerBound_ge_one hε
  refine ⟨D,B,hD,hB,?_⟩
  intro η hp a t ha ha' hzero
  obtain ⟨hE,hEL,hEb⟩ := actual_inner_log η t
  exact hb η hp a t (eulerLog η) ha ha' hzero hE hEL hEb

theorem primitive_reciprocal_subpower (e ε : ℝ)
    (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D : ℝ, 0< D ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ s : ℂ, HeckeZeroSupremum.beta+8*e ≤ s.re →
        ‖HeckeReciprocal.reciprocal η s‖ ≤ D*(complexity η s.im)^ε := by
  obtain ⟨D,B,hD,_,hb⟩ := disk_control e ε he he' hε
  have hEuler : 0 ≤ HeckeReciprocalBound.bound 2 := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨D+HeckeReciprocalBound.bound 2, by linarith, ?_⟩
  intro η hp s hs
  have hcomp : 1 ≤ (complexity η s.im)^ε := Real.one_le_rpow
    ((Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp η s.im)) hε.le
  by_cases hs2 : s.re ≤ 2
  · have hbound := (hb η hp HeckeZeroSupremum.beta s.im HeckeZeroSupremum.half_le_beta
      HeckeZeroSupremum.beta_le_one (fun z hz => regular_ne_zero_on_disk η HeckeZeroSupremum.beta e s.im le_rfl he hz)).1
    have hmem : s ∈ closedBall ((2 : ℂ)+s.im*Complex.I) (2-HeckeZeroSupremum.beta-6*e) := by
      have h := LogarithmicControl.same_height_mem_disk (a := HeckeZeroSupremum.beta)
        (e := e) (t := s.im) (v := 8*e) le_rfl hs hs2
      rw [Complex.re_add_im] at h
      exact closedBall_subset_closedBall (by linarith) h
    have hz := hbound s hmem
    have hr := reciprocal_norm_le_regular_inverse η (by linarith : HeckeZeroSupremum.beta< s.re)
    have hcp : 0 ≤ (complexity η s.im)^ε := by linarith
    nlinarith [norm_nonneg (regular η s)]
  · have hr := HeckeReciprocalBound.reciprocal_norm_le η (by norm_num : (1 : ℝ)<2)
      (le_of_not_ge hs2)
    have hp0 : 0 ≤ D+HeckeReciprocalBound.bound 2 := by linarith
    exact hr.trans ((by linarith : HeckeReciprocalBound.bound 2 ≤ D+HeckeReciprocalBound.bound 2).trans
      (le_mul_of_one_le_right hp0 hcomp))

end HeckeLogarithmicActual

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeReciprocalGrowth
open HeckeFamily HeckeLogarithmic HeckeDeletionBounds

def presentationComplexity (χ : Character) (t : ℝ) : ℝ :=
  ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)*complexity χ t

theorem reciprocal_subpower (e ε : ℝ)
    (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D : ℝ, 0< D ∧ ∀ (χ : Character) (s : ℂ),
      HeckeZeroSupremum.beta+8*e ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ D*(presentationComplexity χ s.im)^ε := by
  obtain ⟨Dp,hDp,hpbound⟩ := HeckeLogarithmicActual.primitive_reciprocal_subpower e ε he he' hε
  obtain ⟨Cd,hCd,hreduce⟩ := HeckeDeletionReciprocal.exists_primitive_reciprocal_reduction
    (HeckeZeroSupremum.beta+8*e) ε (by linarith [HeckeZeroSupremum.half_le_beta]) hε
  refine ⟨Cd*Dp, mul_pos hCd hDp, ?_⟩
  intro χ s hs
  obtain ⟨ψ,hp,hn,_,hr⟩ := hreduce χ
  have hc : complexity ψ s.im ≤ complexity χ s.im := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ s.im :=
    (Real.exp_pos 1).le.trans (complexity_ge_exp ψ s.im)
  have hr0 : 0 ≤ ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by positivity
  apply (hr s hs).trans
  calc
    _ ≤ Cd*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε * (Dp*(complexity ψ s.im)^ε) :=
      mul_le_mul_of_nonneg_left (hpbound ψ hp s hs) (by positivity)
    _ = (Cd*Dp)*(((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)*complexity ψ s.im)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hc hr0) hε.le)
      (mul_pos hCd hDp).le

theorem polynomial_reciprocal_bound (χ : Character) (a : ℝ)
    (hβ : HeckeZeroSupremum.beta < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2) := by
  let e : ℝ := min (1/2000) ((a-HeckeZeroSupremum.beta)/16)
  have he : 0< e := lt_min (by norm_num) (by linarith)
  have he' : e<1/1000 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hmargin : HeckeZeroSupremum.beta+8*e ≤ a := by
    have hh := min_le_right (1/2000 : ℝ) ((a-HeckeZeroSupremum.beta)/16)
    change e ≤ (a-HeckeZeroSupremum.beta)/16 at hh
    linarith
  obtain ⟨C,hC,hbound⟩ := reciprocal_subpower e 1 he he' (by norm_num)
  let K : ℝ := C*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)*(2*(χ.modulus.absNorm : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨18*K, by positivity, ?_⟩
  intro s hs
  have h := hbound χ s (hmargin.trans hs)
  have hheight : (3+|s.im|)^2 ≤ 18*(1+|s.im|^2) := by
    nlinarith [sq_nonneg (|s.im|-1), sq_nonneg |s.im|]
  rw [Real.rpow_one] at h
  calc
    _ ≤ K*(3+|s.im|)^2 := by
      convert h using 1 ; unfold K presentationComplexity complexity ; ring
    _ ≤ K*(18*(1+|s.im|^2)) := mul_le_mul_of_nonneg_left hheight hK
    _ = _ := by ring

end HeckeReciprocalGrowth

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace HeckeDyadic
open HeckeFamily

theorem horizontal_join_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤ D) (hlr : l≤ r) (hC : 0≤ C) (_hK : 0≤ K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤ C)
    (hs : ∀ x ∈ Icc l r, ‖series χ inverse ((x : ℂ)+y*I+shift σ freq)‖≤ K) :
    ‖∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤ C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤ D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ inverse W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem profile_strip_decay (a b : ℝ) (ha : 0< a) (l r : ℝ) (n : ℕ) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0< C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ)⊆Icc a b →
      ∀ x ∈ Icc l r, ∀ y : ℝ,
      (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  CompletedHeight.mellin_strip_source_bound a b ha l r n

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeDyadic
open HeckeFamily HeckeDeletionBounds HeckeReciprocalGrowth HeckeLogarithmic

theorem radical_dvd (M : Ideal O) (hM : M≠0) : HeckeDeletionBounds.radical M∣M := by
  unfold HeckeDeletionBounds.radical HeckeIdealSeries.primeProduct
  rw [HeckeIdealSeries.prod_primeSet M (fun J : Ideal O => J)]
  exact support_product_dvd hM (Finset.Subset.refl _)

theorem radical_norm_le_modulus (χ : Character) :
    ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)≤χ.modulus.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
    (map_dvd Ideal.absNorm (radical_dvd χ.modulus χ.modulus_ne_bot))

theorem presentationComplexity_le_of_modulus_le (χ : Character) (U H : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤ U) :
    presentationComplexity χ H≤2*U^2*(3+|H|)^2 := by
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hU : 0≤ U := (Nat.cast_nonneg χ.modulus.absNorm).trans hQ
  unfold presentationComplexity complexity
  calc
    _ ≤ U*(2*U*(3+|H|)^2) := by gcongr
    _ = _ := by ring

theorem reflected_conductor_cost (χ : Character) (U a e ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤ U) (ha : 1/2≤ a) (he : 0≤ e) (hε : 0≤ε) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)≤ U^(a-1/2+12*e+2*ε) := by
  have hU : 0< U := lt_of_lt_of_le zero_lt_one
    ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hR := (radical_norm_le_modulus χ).trans hQ
  calc
    _ ≤ U^(a-1/2+6*e)*U^(6*e+2*ε) :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) hQ (by linarith))
        (Real.rpow_le_rpow (by positivity) hR (by positivity))
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hU.le _)
    _ = _ := by
      rw [←Real.rpow_add hU]
      congr 1
      ring

theorem positive_scale_exponent (U a e r : ℝ) (hU : 0< U) :
    (U^r)^(a+6*e-1/2)=U^((a-1/2+6*e)*r) := by
  rw [←Real.rpow_mul hU.le]
  congr 1
  ring

theorem reflected_scale_exponent (U a e ε m : ℝ) (hU : 0< U) :
    U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e)=
      U^((a-1/2)*(1-m)+6*e*(2-m)+2*ε) := by
  rw [←Real.rpow_mul hU.le,←Real.rpow_add hU]
  congr 1
  ring

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckeDyadic

theorem exists_external_tail_order (τ B p : ℝ) (hτ : 0<τ) :
    ∃ n : ℕ, ∀ Z : ℝ, 1≤ Z → Z^B/(1+Z^τ)^n≤ Z^p := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((B-p)/τ)
  refine ⟨n,?_⟩
  intro Z hZ
  have hZp : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hn' : B≤ p+τ*(n : ℝ) := by
    have h := (div_lt_iff₀ hτ).mp hn
    nlinarith
  have hden : 0<(1+Z^τ)^n := by positivity
  apply (div_le_iff₀ hden).mpr
  calc
    Z^B ≤ Z^(p+τ*(n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hn'
    _ = Z^p*(Z^τ)^n := by
      rw [Real.rpow_add hZp,Real.rpow_mul hZp.le,Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hZp.le _) (by linarith) n)
      (Real.rpow_nonneg hZp.le _)

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤ Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

theorem uniform_external_tail_order (τ dmax B R : ℝ)
    (hτ : 0<τ) (_hdmax : 0≤ dmax) (hB : 0≤ B) (hR : 0≤ R) :
    ∃ n : ℕ, ∀ Z d p : ℝ, 1≤ Z → 0≤ d → d≤ dmax → -R≤ p →
      (Z^d)^B/(1+Z^τ/2)^n≤(2 : ℝ)^n*(Z^d)^p := by
  obtain ⟨n,hn⟩ := exists_external_tail_order τ (dmax*B) (-dmax*R) hτ
  refine ⟨n,?_⟩
  intro Z d p hZ hd hd' hp
  have hZp : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hnum : (Z^d)^B≤ Z^(dmax*B) := by
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd' hB)
  have htarget : Z^(-dmax*R)≤(Z^d)^p := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    nlinarith [mul_nonneg hd (show 0≤ p+R by linarith),
      mul_nonneg (show 0≤ dmax-d by linarith) hR]
  have hden : ((1+Z^τ)/2)^n≤(1+Z^τ/2)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ (Z^(dmax*B))/((1+Z^τ)/2)^n :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (2 : ℝ)^n*(Z^(dmax*B)/(1+Z^τ)^n) := by
      rw [div_pow]
      field_simp
    _ ≤ (2 : ℝ)^n*Z^(-dmax*R) := mul_le_mul_of_nonneg_left (hn Z hZ) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left htarget (by positivity)

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckeDyadic

theorem central_squared_exponents (R a e κ η ε r m : ℝ)
    (hR : 0≤ R) (he : 0≤ e) (hκ : 0≤κ) (_hη : 0≤η)
    (hr : r≤ R) (hm : 0≤ m)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    2*((a-1/2+6*e)*r+2*κ+η)≤(2*a-1)*r+ε ∧
    2*((a-1/2)*(1-m)+6*e*(2-m)+4*κ+η)≤(2*a-1)*(1-m)+ε := by
  have hEr : e*r≤ e*R := mul_le_mul_of_nonneg_left hr he
  have hEm : 0≤ e*m := mul_nonneg he hm
  have hER : 0≤ e*R := mul_nonneg he hR
  constructor <;> nlinarith

theorem exists_central_loss_parameters (R ε : ℝ) (hR : 0≤ R) (hε : 0<ε) :
    ∃ e₀ κ η : ℝ, 0< e₀ ∧ e₀≤1/1000 ∧ 0<κ ∧ κ≤1 ∧ 0<η ∧
      ∀ e : ℝ, 0< e → e< e₀ → 12*e*(R+2)+8*κ+2*η≤ε/2 := by
  let e₀ : ℝ := min (1/1000) (ε/(96*(R+2)))
  let κ : ℝ := min (1/2) (ε/64)
  let η : ℝ := ε/16
  have hRp : 0< R+2 := by linarith
  have he₀ : 0< e₀ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hκ : 0<κ := lt_min (by norm_num) (div_pos hε (by norm_num))
  refine ⟨e₀,κ,η,he₀,min_le_left _ _,hκ,(min_le_left _ _).trans (by norm_num),
    div_pos hε (by norm_num),?_⟩
  intro e he he'
  have heb : e≤ε/(96*(R+2)) := he'.le.trans (min_le_right _ _)
  have heb' := (le_div_iff₀ (by positivity : 0<96*(R+2))).mp heb
  have hκb : κ≤ε/64 := min_le_right _ _
  dsimp only [η]
  nlinarith

theorem indexed_height_bound (i I : ℕ) (hi : i≤ I) (T : ℝ) (hT : 0≤ T) :
    (3+(3*i+2 : ℕ)*T)^4≤(3*(I : ℝ)+5)^4*(1+T)^4 := by
  have hi' : (i : ℝ)≤ I := by exact_mod_cast hi
  have hlin : 3+(3*i+2 : ℕ)*T≤(3*(I : ℝ)+5)*(1+T) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hi' hT,Nat.cast_nonneg (α:=ℝ) I]
  calc
    _ ≤ ((3*(I : ℝ)+5)*(1+T))^4 := pow_le_pow_left₀ (by positivity) hlin 4
    _ = _ := mul_pow _ _ _

theorem min_plain_bound (X C U δ m ε : ℝ)
    (h₁ : X≤ C*U^(δ*m+ε)) (h₂ : X≤ C*U^(δ*(1-m)+ε)) :
    X≤ C*U^(δ*min m (1-m)+ε) := by
  rcases le_total m (1-m) with h | h
  · simpa only [min_eq_left h] using h₁
  · simpa only [min_eq_right h] using h₂

theorem squared_bound_of_central_and_error (z : ℂ) (U C E p b ε : ℝ)
    (hU : 1≤ U) (hC : 0≤ C) (hE : 0≤ E) (hε : 0≤ε)
    (hb : 2*b≤ε)
    (hz : ‖z‖≤ C*U^(p+b)+E*U^p) :
    ‖z‖^2≤(C+E)^2*U^(2*p+ε) := by
  have hUp : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hp₁ : U^(p+b)≤ U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hp₂ : U^p≤ U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hn : ‖z‖≤(C+E)*U^(p+ε/2) := by
    calc
      _ ≤ C*U^(p+b)+E*U^p := hz
      _ ≤ C*U^(p+ε/2)+E*U^(p+ε/2) := add_le_add
        (mul_le_mul_of_nonneg_left hp₁ hC) (mul_le_mul_of_nonneg_left hp₂ hE)
      _ = _ := by ring
  calc
    _ ≤ ((C+E)*U^(p+ε/2))^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by
      have hp : (U^(p+ε/2))^2=U^(2*p+ε) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
        congr 1
        norm_num
        ring
      rw [mul_pow,hp]

end HeckeDyadic

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
