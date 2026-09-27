import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The cubic Gamma norm of Route L

For a real parameter `δ` the Route L source atoms `f_x(t) = x² exp(-x t)` live in the weighted
half-line space with inner product

`⟨F, G⟩_δ = Γ(5+δ)⁻¹ ∫_0^∞ t^(4+δ) F(t) G(t) dt`.

This module fixes that inner product on real functions, the finiteness class on which it is a
genuine Hilbert inner product, and the embedding into `L²(0,∞)` through the half-density
`t^((4+δ)/2) F(t)`.  The embedding delivers the triangle inequality, Cauchy--Schwarz and
polarization for the literal function-level norm.  The monomial--exponential Gram law

`⟨t^j e^{-a t}, t^k e^{-b t}⟩_δ = Γ(5+δ+j+k) / (Γ(5+δ) (a+b)^(5+δ+j+k))`

gives the source Gram `⟨f_x, f_y⟩_δ = x² y² / (x+y)^(5+δ)` and its dilation homogeneity.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace

noncomputable section

namespace RHTower.CubicGamma

/-- The half-line on which the cubic Gamma weight lives. -/
abbrev halfLine : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-- The normalized cubic Gamma inner product `Γ(5+δ)⁻¹ ∫_0^∞ t^(4+δ) F G`. -/
def gammaInner (δ : ℝ) (F G : ℝ → ℝ) : ℝ :=
  (Real.Gamma (5 + δ))⁻¹ * ∫ t in Ioi (0 : ℝ), t ^ (4 + δ) * (F t * G t)

/-- The cubic Gamma energy `‖F‖_δ²`. -/
def gammaEnergy (δ : ℝ) (F : ℝ → ℝ) : ℝ := gammaInner δ F F

/-- The cubic Gamma norm `‖F‖_δ`. -/
def gammaNorm (δ : ℝ) (F : ℝ → ℝ) : ℝ := Real.sqrt (gammaEnergy δ F)

/-- Finite cubic Gamma energy: measurability on the half-line and integrability of
`t^(4+δ) F(t)²`. -/
def GammaFinite (δ : ℝ) (F : ℝ → ℝ) : Prop :=
  AEStronglyMeasurable F halfLine ∧
    IntegrableOn (fun t => t ^ (4 + δ) * F t ^ 2) (Ioi (0 : ℝ))

/-- The half-density feature `Γ(5+δ)^(-1/2) t^((4+δ)/2) F(t)`. -/
def feature (δ : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Real.sqrt (Real.Gamma (5 + δ)))⁻¹ * (t ^ ((4 + δ) / 2) * F t)

theorem gamma_pos {δ : ℝ} (hδ : 0 < 5 + δ) : 0 < Real.Gamma (5 + δ) :=
  Real.Gamma_pos_of_pos hδ

private theorem rpow_half_sq {t c : ℝ} (ht : 0 < t) : (t ^ (c / 2)) ^ 2 = t ^ c := by
  rw [pow_two, ← Real.rpow_add ht]
  congr 1
  ring

theorem feature_mul_feature {δ : ℝ} (hδ : 0 < 5 + δ) (F G : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    feature δ F t * feature δ G t =
      (Real.Gamma (5 + δ))⁻¹ * (t ^ (4 + δ) * (F t * G t)) := by
  have hg := gamma_pos hδ
  have hs : (Real.sqrt (Real.Gamma (5 + δ)))⁻¹ * (Real.sqrt (Real.Gamma (5 + δ)))⁻¹ =
      (Real.Gamma (5 + δ))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hg.le]
  have hp := rpow_half_sq (c := 4 + δ) ht
  unfold feature
  calc
    _ = ((Real.sqrt (Real.Gamma (5 + δ)))⁻¹ * (Real.sqrt (Real.Gamma (5 + δ)))⁻¹) *
          ((t ^ ((4 + δ) / 2)) ^ 2 * (F t * G t)) := by ring
    _ = _ := by rw [hs, hp]

theorem feature_sq {δ : ℝ} (hδ : 0 < 5 + δ) (F : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    feature δ F t ^ 2 = (Real.Gamma (5 + δ))⁻¹ * (t ^ (4 + δ) * F t ^ 2) := by
  rw [pow_two, feature_mul_feature hδ F F ht, pow_two]

theorem aestronglyMeasurable_feature {δ : ℝ} {F : ℝ → ℝ}
    (hF : AEStronglyMeasurable F halfLine) :
    AEStronglyMeasurable (feature δ F) halfLine := by
  unfold feature
  exact aestronglyMeasurable_const.mul
    (((measurable_id.pow_const ((4 + δ) / 2)).aestronglyMeasurable).mul hF)

theorem GammaFinite.memLp {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    MemLp (feature δ F) 2 halfLine := by
  refine (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_feature hF.1)).mpr ?_
  have h := hF.2.const_mul (Real.Gamma (5 + δ))⁻¹
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, sq_abs, feature_sq hδ F ht]

open Classical in
/-- The embedding of the cubic Gamma space into `L²(0,∞)`. -/
def toL2 (δ : ℝ) (F : ℝ → ℝ) : Lp ℝ 2 halfLine :=
  if h : MemLp (feature δ F) 2 halfLine then h.toLp _ else 0

theorem toL2_eq {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    toL2 δ F = (hF.memLp hδ).toLp _ := by
  unfold toL2
  rw [dif_pos (hF.memLp hδ)]

theorem toL2_ae {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    (toL2 δ F : ℝ → ℝ) =ᵐ[halfLine] feature δ F := by
  rw [toL2_eq hδ hF]
  exact (hF.memLp hδ).coeFn_toLp

/-- The embedding realizes the cubic Gamma inner product. -/
theorem inner_toL2 {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    ⟪toL2 δ F, toL2 δ G⟫_ℝ = gammaInner δ F G := by
  rw [L2.inner_def, gammaInner, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [toL2_ae hδ hF, toL2_ae hδ hG, ae_restrict_mem measurableSet_Ioi]
    with t h1 h2 ht
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [mul_comm, feature_mul_feature hδ F G ht]

theorem gammaInner_comm (δ : ℝ) (F G : ℝ → ℝ) : gammaInner δ F G = gammaInner δ G F := by
  unfold gammaInner
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem gammaEnergy_eq_norm_sq {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    gammaEnergy δ F = ‖toL2 δ F‖ ^ 2 := by
  rw [gammaEnergy, ← inner_toL2 hδ hF hF, real_inner_self_eq_norm_sq]

theorem gammaEnergy_nonneg {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    0 ≤ gammaEnergy δ F := by
  rw [gammaEnergy_eq_norm_sq hδ hF]
  positivity

theorem norm_toL2 {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    ‖toL2 δ F‖ = gammaNorm δ F := by
  rw [gammaNorm, gammaEnergy_eq_norm_sq hδ hF, Real.sqrt_sq (norm_nonneg _)]

theorem gammaNorm_nonneg (δ : ℝ) (F : ℝ → ℝ) : 0 ≤ gammaNorm δ F := Real.sqrt_nonneg _

theorem gammaNorm_sq {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    gammaNorm δ F ^ 2 = gammaEnergy δ F := by
  rw [← norm_toL2 hδ hF, gammaEnergy_eq_norm_sq hδ hF]

/-! ### The finiteness class -/

theorem GammaFinite.zero (δ : ℝ) : GammaFinite δ (fun _ => 0) := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
  exact integrableOn_zero

/-- Domination by a finite function. -/
theorem GammaFinite.of_abs_le {δ : ℝ} {F G : ℝ → ℝ} (hG : GammaFinite δ G)
    (hF : AEStronglyMeasurable F halfLine) (hle : ∀ t ∈ Ioi (0 : ℝ), |F t| ≤ |G t|) :
    GammaFinite δ F := by
  refine ⟨hF, ?_⟩
  refine hG.2.mono' ?_ ?_
  · exact ((measurable_id.pow_const (4 + δ)).aestronglyMeasurable).mul (hF.pow 2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw : 0 ≤ t ^ (4 + δ) := Real.rpow_nonneg (le_of_lt ht) _
    have hsq : F t ^ 2 ≤ G t ^ 2 := by
      have := hle t ht
      nlinarith [abs_nonneg (F t), sq_abs (F t), sq_abs (G t)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hsq hw

theorem GammaFinite.smul {δ : ℝ} {F : ℝ → ℝ} (hF : GammaFinite δ F) (c : ℝ) :
    GammaFinite δ (fun t => c * F t) := by
  refine ⟨aestronglyMeasurable_const.mul hF.1, ?_⟩
  exact IntegrableOn.congr_fun (hF.2.const_mul (c ^ 2)) (fun t _ => by ring) measurableSet_Ioi

theorem GammaFinite.neg {δ : ℝ} {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    GammaFinite δ (fun t => -F t) := by
  refine ⟨hF.1.neg, ?_⟩
  exact IntegrableOn.congr_fun hF.2 (fun t _ => by ring) measurableSet_Ioi

theorem GammaFinite.add {δ : ℝ} {F G : ℝ → ℝ} (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    GammaFinite δ (fun t => F t + G t) := by
  have hmeas : AEStronglyMeasurable (fun t => F t + G t) halfLine := hF.1.add hG.1
  refine ⟨hmeas, ?_⟩
  have hsum := (hF.2.add hG.2).const_mul 2
  refine hsum.mono' ?_ ?_
  · exact ((measurable_id.pow_const (4 + δ)).aestronglyMeasurable).mul (hmeas.pow 2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw : 0 ≤ t ^ (4 + δ) := Real.rpow_nonneg (le_of_lt ht) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    have hq : (F t + G t) ^ 2 ≤ 2 * (F t ^ 2 + G t ^ 2) := by
      nlinarith [sq_nonneg (F t - G t)]
    calc t ^ (4 + δ) * (F t + G t) ^ 2 ≤ t ^ (4 + δ) * (2 * (F t ^ 2 + G t ^ 2)) :=
          mul_le_mul_of_nonneg_left hq hw
      _ = 2 * (t ^ (4 + δ) * F t ^ 2 + t ^ (4 + δ) * G t ^ 2) := by ring

theorem GammaFinite.sub {δ : ℝ} {F G : ℝ → ℝ} (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    GammaFinite δ (fun t => F t - G t) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem GammaFinite.sum {δ : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, GammaFinite δ (F i)) :
    GammaFinite δ (fun t => ∑ i ∈ s, F i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GammaFinite.zero δ
  | insert j s hj ih =>
      have hj' := hF j (Finset.mem_insert_self j s)
      have hs := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.sum_insert hj] using hj'.add hs

theorem GammaFinite.congr {δ : ℝ} {F G : ℝ → ℝ} (hF : GammaFinite δ F) (h : F = G) :
    GammaFinite δ G := h ▸ hF

/-! ### Linearity of the embedding -/

theorem toL2_add {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    toL2 δ (fun t => F t + G t) = toL2 δ F + toL2 δ G := by
  rw [toL2_eq hδ hF, toL2_eq hδ hG, toL2_eq hδ (hF.add hG), ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards with t
  simp only [feature, Pi.add_apply]
  ring

theorem toL2_smul {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) (c : ℝ) :
    toL2 δ (fun t => c * F t) = c • toL2 δ F := by
  rw [toL2_eq hδ hF, toL2_eq hδ (hF.smul c), ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards with t
  simp only [feature, Pi.smul_apply, smul_eq_mul]
  ring

theorem toL2_neg {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    toL2 δ (fun t => -F t) = -toL2 δ F := by
  rw [toL2_eq hδ hF, toL2_eq hδ hF.neg, ← MemLp.toLp_neg]
  apply MemLp.toLp_congr
  filter_upwards with t
  simp only [feature, Pi.neg_apply]
  ring

theorem toL2_sub {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    toL2 δ (fun t => F t - G t) = toL2 δ F - toL2 δ G := by
  rw [toL2_eq hδ hF, toL2_eq hδ hG, toL2_eq hδ (hF.sub hG), ← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  filter_upwards with t
  simp only [feature, Pi.sub_apply]
  ring

theorem toL2_zero {δ : ℝ} (hδ : 0 < 5 + δ) : toL2 δ (fun _ => 0) = 0 := by
  have h := toL2_smul hδ (GammaFinite.zero δ) 0
  simpa only [mul_zero, zero_smul] using h

theorem toL2_sum {δ : ℝ} (hδ : 0 < 5 + δ) {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, GammaFinite δ (F i)) :
    toL2 δ (fun t => ∑ i ∈ s, F i t) = ∑ i ∈ s, toL2 δ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using toL2_zero hδ
  | insert j s hj ih =>
      have hj' := hF j (Finset.mem_insert_self j s)
      have hs' : ∀ i ∈ s, GammaFinite δ (F i) := fun i hi => hF i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert hj, ← ih hs', ← toL2_add hδ hj' (GammaFinite.sum s hs')]
      simp only [Finset.sum_insert hj]

/-! ### Hilbert inequalities for the literal norm -/

theorem gammaNorm_add_le {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    gammaNorm δ (fun t => F t + G t) ≤ gammaNorm δ F + gammaNorm δ G := by
  rw [← norm_toL2 hδ hF, ← norm_toL2 hδ hG, ← norm_toL2 hδ (hF.add hG), toL2_add hδ hF hG]
  exact norm_add_le _ _

theorem gammaNorm_sub_le {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    gammaNorm δ (fun t => F t - G t) ≤ gammaNorm δ F + gammaNorm δ G := by
  rw [← norm_toL2 hδ hF, ← norm_toL2 hδ hG, ← norm_toL2 hδ (hF.sub hG), toL2_sub hδ hF hG]
  exact norm_sub_le _ _

theorem gammaNorm_smul {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) (c : ℝ) :
    gammaNorm δ (fun t => c * F t) = |c| * gammaNorm δ F := by
  rw [← norm_toL2 hδ hF, ← norm_toL2 hδ (hF.smul c), toL2_smul hδ hF, norm_smul,
    Real.norm_eq_abs]

theorem gammaNorm_neg {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    gammaNorm δ (fun t => -F t) = gammaNorm δ F := by
  rw [← norm_toL2 hδ hF, ← norm_toL2 hδ hF.neg, toL2_neg hδ hF, norm_neg]

theorem gammaNorm_sum_le {δ : ℝ} (hδ : 0 < 5 + δ) {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → ℝ} (hF : ∀ i ∈ s, GammaFinite δ (F i)) :
    gammaNorm δ (fun t => ∑ i ∈ s, F i t) ≤ ∑ i ∈ s, gammaNorm δ (F i) := by
  rw [← norm_toL2 hδ (GammaFinite.sum s hF), toL2_sum hδ s hF]
  calc ‖∑ i ∈ s, toL2 δ (F i)‖ ≤ ∑ i ∈ s, ‖toL2 δ (F i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, gammaNorm δ (F i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact norm_toL2 hδ (hF i hi)

/-- Reverse triangle inequality for the literal norm. -/
theorem abs_gammaNorm_sub_le {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    |gammaNorm δ F - gammaNorm δ G| ≤ gammaNorm δ (fun t => F t - G t) := by
  rw [← norm_toL2 hδ hF, ← norm_toL2 hδ hG, ← norm_toL2 hδ (hF.sub hG), toL2_sub hδ hF hG]
  exact abs_norm_sub_norm_le _ _

/-- Cauchy--Schwarz for the cubic Gamma inner product. -/
theorem abs_gammaInner_le {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    |gammaInner δ F G| ≤ gammaNorm δ F * gammaNorm δ G := by
  rw [← inner_toL2 hδ hF hG, ← norm_toL2 hδ hF, ← norm_toL2 hδ hG]
  exact abs_real_inner_le_norm _ _

theorem gammaInner_add_left {δ : ℝ} (hδ : 0 < 5 + δ) {F G H : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) (hH : GammaFinite δ H) :
    gammaInner δ (fun t => F t + G t) H = gammaInner δ F H + gammaInner δ G H := by
  rw [← inner_toL2 hδ (hF.add hG) hH, toL2_add hδ hF hG, inner_add_left,
    inner_toL2 hδ hF hH, inner_toL2 hδ hG hH]

theorem gammaInner_smul_left {δ : ℝ} (hδ : 0 < 5 + δ) {F H : ℝ → ℝ}
    (hF : GammaFinite δ F) (hH : GammaFinite δ H) (c : ℝ) :
    gammaInner δ (fun t => c * F t) H = c * gammaInner δ F H := by
  rw [← inner_toL2 hδ (hF.smul c) hH, toL2_smul hδ hF, real_inner_smul_left,
    inner_toL2 hδ hF hH]

theorem gammaInner_smul_right {δ : ℝ} (hδ : 0 < 5 + δ) {F H : ℝ → ℝ}
    (hF : GammaFinite δ F) (hH : GammaFinite δ H) (c : ℝ) :
    gammaInner δ H (fun t => c * F t) = c * gammaInner δ H F := by
  rw [gammaInner_comm, gammaInner_smul_left hδ hF hH, gammaInner_comm]

theorem gammaInner_sum_left {δ : ℝ} (hδ : 0 < 5 + δ) {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → ℝ} (hF : ∀ i ∈ s, GammaFinite δ (F i)) {H : ℝ → ℝ} (hH : GammaFinite δ H) :
    gammaInner δ (fun t => ∑ i ∈ s, F i t) H = ∑ i ∈ s, gammaInner δ (F i) H := by
  rw [← inner_toL2 hδ (GammaFinite.sum s hF) hH, toL2_sum hδ s hF, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  exact inner_toL2 hδ (hF i hi) hH

/-- The energy of a finite combination is its full Gram quadratic form. -/
theorem gammaEnergy_sum {δ : ℝ} (hδ : 0 < 5 + δ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) {F : ι → ℝ → ℝ} (hF : ∀ i ∈ s, GammaFinite δ (F i)) :
    gammaEnergy δ (fun t => ∑ i ∈ s, c i * F i t) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * gammaInner δ (F i) (F j) := by
  have hc : ∀ i ∈ s, GammaFinite δ (fun t => c i * F i t) := fun i hi => (hF i hi).smul (c i)
  rw [gammaEnergy, ← inner_toL2 hδ (GammaFinite.sum s hc) (GammaFinite.sum s hc),
    toL2_sum hδ s hc, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [toL2_smul hδ (hF i hi), toL2_smul hδ (hF j hj), real_inner_smul_left,
    real_inner_smul_right, inner_toL2 hδ (hF i hi) (hF j hj)]
  ring

/-- Polarization of the energy of a sum. -/
theorem gammaEnergy_add {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    gammaEnergy δ (fun t => F t + G t) =
      gammaEnergy δ F + 2 * gammaInner δ F G + gammaEnergy δ G := by
  rw [gammaEnergy, gammaEnergy, gammaEnergy, ← inner_toL2 hδ (hF.add hG) (hF.add hG),
    toL2_add hδ hF hG, ← inner_toL2 hδ hF hG, ← inner_toL2 hδ hF hF, ← inner_toL2 hδ hG hG,
    inner_add_left, inner_add_right, inner_add_right, real_inner_comm (toL2 δ G) (toL2 δ F)]
  ring

theorem gammaEnergy_sub {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) :
    gammaEnergy δ (fun t => F t - G t) =
      gammaEnergy δ F - 2 * gammaInner δ F G + gammaEnergy δ G := by
  rw [gammaEnergy, gammaEnergy, gammaEnergy, ← inner_toL2 hδ (hF.sub hG) (hF.sub hG),
    toL2_sub hδ hF hG, ← inner_toL2 hδ hF hG, ← inner_toL2 hδ hF hF, ← inner_toL2 hδ hG hG,
    inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm (toL2 δ G) (toL2 δ F)]
  ring

/-- Pointwise domination on the half-line bounds the norm. -/
theorem gammaNorm_le_of_abs_le {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ} (hG : GammaFinite δ G)
    (hF : AEStronglyMeasurable F halfLine) (hle : ∀ t ∈ Ioi (0 : ℝ), |F t| ≤ |G t|) :
    gammaNorm δ F ≤ gammaNorm δ G := by
  have hF' := GammaFinite.of_abs_le hG hF hle
  rw [← norm_toL2 hδ hF', ← norm_toL2 hδ hG]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [toL2_ae hδ hF', toL2_ae hδ hG, ae_restrict_mem measurableSet_Ioi]
    with t h1 h2 ht
  rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs]
  unfold feature
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle t ht) (abs_nonneg _))
    (abs_nonneg _)

/-- A pointwise bound by a sum of finite majorants. -/
theorem gammaNorm_le_of_abs_le_sum {δ : ℝ} (hδ : 0 < 5 + δ) {ι : Type*} (s : Finset ι)
    {F : ℝ → ℝ} {G : ι → ℝ → ℝ} (hG : ∀ i ∈ s, GammaFinite δ (G i))
    (hF : AEStronglyMeasurable F halfLine)
    (hle : ∀ t ∈ Ioi (0 : ℝ), |F t| ≤ ∑ i ∈ s, G i t) :
    gammaNorm δ F ≤ ∑ i ∈ s, gammaNorm δ (G i) := by
  refine (gammaNorm_le_of_abs_le hδ (GammaFinite.sum s hG) hF ?_).trans
    (gammaNorm_sum_le hδ s hG)
  intro t ht
  refine (hle t ht).trans (le_abs_self _)

/-! ### Monomial--exponential Gram law -/

/-- The Mellin moment behind every Gram entry. -/
theorem integral_rpow_mul_exp {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-(c * t))) = Real.Gamma s / c ^ s := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := s - 1) (b := c)
    (by norm_num) (by linarith) hc
  have hfun : (fun t : ℝ => t ^ (s - 1) * Real.exp (-(c * t))) =
      fun t : ℝ => t ^ (s - 1) * Real.exp (-c * t ^ (1 : ℝ)) := by
    funext t
    rw [Real.rpow_one, neg_mul]
  rw [hfun, h, show -(s - 1 + 1) / (1 : ℝ) = -s by ring, show (s - 1 + 1) / (1 : ℝ) = s by ring,
    Real.rpow_neg hc.le]
  ring

theorem integrableOn_rpow_mul_exp {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-(c * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := s - 1) (b := c)
    (by linarith) le_rfl hc
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

/-- The monomial--exponential profile `t^j e^{-a t}`. -/
def expMono (j : ℕ) (a t : ℝ) : ℝ := t ^ j * Real.exp (-(a * t))

theorem continuous_expMono (j : ℕ) (a : ℝ) : Continuous (expMono j a) := by
  unfold expMono
  fun_prop

private theorem weight_mul_mono {δ t : ℝ} (ht : 0 < t) (j : ℕ) :
    t ^ (4 + δ) * t ^ j = t ^ (5 + δ + j - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add ht]
  congr 1
  ring

theorem expMono_gram_integrand {δ a b t : ℝ} (ht : 0 < t) (j k : ℕ) :
    t ^ (4 + δ) * (expMono j a t * expMono k b t) =
      t ^ (5 + δ + (j + k : ℕ) - 1) * Real.exp (-((a + b) * t)) := by
  unfold expMono
  rw [← weight_mul_mono ht (j + k), pow_add]
  have he : Real.exp (-(a * t)) * Real.exp (-(b * t)) = Real.exp (-((a + b) * t)) := by
    rw [← Real.exp_add]
    ring_nf
  calc
    _ = t ^ (4 + δ) * (t ^ j * t ^ k) * (Real.exp (-(a * t)) * Real.exp (-(b * t))) := by ring
    _ = _ := by rw [he]

theorem gammaFinite_expMono {δ : ℝ} (hδ : 0 < 5 + δ) (j : ℕ) {a : ℝ} (ha : 0 < a) :
    GammaFinite δ (expMono j a) := by
  refine ⟨(continuous_expMono j a).aestronglyMeasurable, ?_⟩
  have h := integrableOn_rpow_mul_exp (s := 5 + δ + ((j + j : ℕ) : ℝ))
    (c := a + a) (by positivity) (by linarith)
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  rw [pow_two, expMono_gram_integrand ht]

/-- **Monomial--exponential Gram law.** -/
theorem gammaInner_expMono {δ : ℝ} (hδ : 0 < 5 + δ) (j k : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    gammaInner δ (expMono j a) (expMono k b) =
      Real.Gamma (5 + δ + (j + k : ℕ)) /
        (Real.Gamma (5 + δ) * (a + b) ^ (5 + δ + (j + k : ℕ))) := by
  unfold gammaInner
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => expMono_gram_integrand ht j k),
    integral_rpow_mul_exp (by positivity) (by linarith)]
  field_simp

theorem gammaEnergy_expMono {δ : ℝ} (hδ : 0 < 5 + δ) (j : ℕ) {a : ℝ} (ha : 0 < a) :
    gammaEnergy δ (expMono j a) =
      Real.Gamma (5 + δ + 2 * j) / (Real.Gamma (5 + δ) * (2 * a) ^ (5 + δ + 2 * j)) := by
  rw [gammaEnergy, gammaInner_expMono hδ j j ha ha]
  push_cast
  ring_nf

/-! ### The Route L source atom -/

/-- The cubic source atom `f_x(t) = x² e^{-x t}`. -/
def atom (x t : ℝ) : ℝ := x ^ 2 * Real.exp (-(x * t))

theorem atom_eq_expMono (x : ℝ) : atom x = fun t => x ^ 2 * expMono 0 x t := by
  funext t
  simp [atom, expMono]

theorem continuous_atom (x : ℝ) : Continuous (atom x) := by
  unfold atom
  fun_prop

theorem gammaFinite_atom {δ : ℝ} (hδ : 0 < 5 + δ) {x : ℝ} (hx : 0 < x) :
    GammaFinite δ (atom x) := by
  rw [atom_eq_expMono]
  exact (gammaFinite_expMono hδ 0 hx).smul _

/-- The source Gram kernel `K_δ(x,y) = x² y² / (x+y)^(5+δ)`. -/
def sourceKernel (δ x y : ℝ) : ℝ := x ^ 2 * y ^ 2 / (x + y) ^ (5 + δ)

/-- **Source Gram law.** `⟨f_x, f_y⟩_δ = K_δ(x,y)`. -/
theorem gammaInner_atom {δ : ℝ} (hδ : 0 < 5 + δ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    gammaInner δ (atom x) (atom y) = sourceKernel δ x y := by
  rw [atom_eq_expMono, atom_eq_expMono,
    gammaInner_smul_left hδ (gammaFinite_expMono hδ 0 hx) ((gammaFinite_expMono hδ 0 hy).smul _),
    gammaInner_comm,
    gammaInner_smul_left hδ (gammaFinite_expMono hδ 0 hy) (gammaFinite_expMono hδ 0 hx),
    gammaInner_comm, gammaInner_expMono hδ 0 0 hx hy]
  have hg := gamma_pos hδ
  unfold sourceKernel
  simp only [add_zero, Nat.cast_zero]
  field_simp

theorem sourceKernel_pos {δ x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < sourceKernel δ x y := by
  unfold sourceKernel
  have : 0 < (x + y) ^ (5 + δ) := Real.rpow_pos_of_pos (by linarith) _
  positivity

/-- Dilation homogeneity of the source kernel: `K_δ(q x, q y) = q^(-1-δ) K_δ(x,y)`. -/
theorem sourceKernel_dilate {δ q x y : ℝ} (hq : 0 < q) (hx : 0 < x) (hy : 0 < y) :
    sourceKernel δ (q * x) (q * y) = q ^ (-1 - δ) * sourceKernel δ x y := by
  unfold sourceKernel
  have hxy : 0 < x + y := by linarith
  rw [show q * x + q * y = q * (x + y) by ring, Real.mul_rpow hq.le hxy.le,
    show (-1 - δ : ℝ) = 4 - (5 + δ) by ring, Real.rpow_sub hq, Real.rpow_ofNat]
  have h1 : 0 < q ^ (5 + δ) := Real.rpow_pos_of_pos hq _
  have h2 : 0 < (x + y) ^ (5 + δ) := Real.rpow_pos_of_pos hxy _
  field_simp

/-! ### Dilation -/

/-- The dilation `U_q F(t) = q² F(q t)`; on atoms `U_q f_x = f_(q x)`. -/
def dilate (q : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ := q ^ 2 * F (q * t)

theorem dilate_atom (q x : ℝ) : dilate q (atom x) = atom (q * x) := by
  funext t
  unfold dilate atom
  rw [mul_pow, show x * (q * t) = q * x * t by ring]
  ring

/-- The dilation energy law `‖U_q F‖_δ² = q^(-1-δ) ‖F‖_δ²`, valid for every real function. -/
theorem gammaEnergy_dilate {δ q : ℝ} (hq : 0 < q) (F : ℝ → ℝ) :
    gammaEnergy δ (dilate q F) = q ^ (-1 - δ) * gammaEnergy δ F := by
  unfold gammaEnergy gammaInner dilate
  have hcomp := integral_comp_mul_left_Ioi
    (fun u : ℝ => q ^ (-δ) * (u ^ (4 + δ) * (F u * F u))) 0 hq
  have hleft : (∫ t in Ioi (0 : ℝ), t ^ (4 + δ) * (q ^ 2 * F (q * t) * (q ^ 2 * F (q * t)))) =
      ∫ t in Ioi (0 : ℝ), q ^ (-δ) * ((q * t) ^ (4 + δ) * (F (q * t) * F (q * t))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    simp only
    rw [Real.mul_rpow hq.le ht'.le]
    have h4 : q ^ (-δ) * q ^ (4 + δ) = q ^ 4 := by
      rw [← Real.rpow_add hq, show -δ + (4 + δ) = (4 : ℝ) by ring, Real.rpow_ofNat]
    calc _ = q ^ 4 * (t ^ (4 + δ) * (F (q * t) * F (q * t))) := by ring
      _ = _ := by rw [← h4]; ring
  rw [hleft, hcomp, mul_zero, smul_eq_mul, integral_const_mul,
    show (-1 - δ : ℝ) = -1 + -δ by ring, Real.rpow_add hq, Real.rpow_neg_one]
  ring

theorem quasiMeasurePreserving_mul_left_halfLine {q : ℝ} (hq : 0 < q) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => q * t) halfLine halfLine := by
  refine ⟨measurable_const_mul q, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply (measurable_const_mul q) hs,
    Measure.restrict_apply (measurable_const_mul q hs)]
  rw [Measure.restrict_apply hs] at h0
  have hsub : (fun t => q * t) ⁻¹' s ∩ Ioi 0 ⊆ (fun t => q * t) ⁻¹' (s ∩ Ioi 0) := by
    rintro t ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    simp only [mem_Ioi] at h2 ⊢
    positivity
  refine measure_mono_null hsub ?_
  rw [Real.volume_preimage_mul_left hq.ne', h0, mul_zero]

theorem GammaFinite.dilate {δ q : ℝ} (hq : 0 < q) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    GammaFinite δ (dilate q F) := by
  refine ⟨aestronglyMeasurable_const.mul
    (hF.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_mul_left_halfLine hq)), ?_⟩
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => q ^ (-δ) * (u ^ (4 + δ) * F u ^ 2)) 0 hq).mpr
    (by rw [mul_zero]; exact hF.2.const_mul _)
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  show q ^ (-δ) * ((q * t) ^ (4 + δ) * F (q * t) ^ 2) = t ^ (4 + δ) * (q ^ 2 * F (q * t)) ^ 2
  rw [Real.mul_rpow hq.le ht'.le]
  have h4 : q ^ (-δ) * q ^ (4 + δ) = q ^ 4 := by
    rw [← Real.rpow_add hq, show -δ + (4 + δ) = (4 : ℝ) by ring, Real.rpow_ofNat]
  calc _ = (q ^ (-δ) * q ^ (4 + δ)) * (t ^ (4 + δ) * F (q * t) ^ 2) := by ring
    _ = _ := by rw [h4]; ring

theorem gammaNorm_dilate {δ q : ℝ} (hq : 0 < q) (F : ℝ → ℝ) :
    gammaNorm δ (dilate q F) = q ^ (-(1 + δ) / 2) * gammaNorm δ F := by
  rw [gammaNorm, gammaNorm, gammaEnergy_dilate hq, Real.sqrt_mul (Real.rpow_nonneg hq.le _),
    Real.sqrt_eq_rpow, ← Real.rpow_mul hq.le]
  congr 2
  ring

/-- The insertion `D_q = I - U_q` has norm at most `1 + q^(-(1+δ)/2)`. -/
theorem gammaNorm_sub_dilate_le {δ q : ℝ} (hδ : 0 < 5 + δ) (hq : 0 < q) {F : ℝ → ℝ}
    (hF : GammaFinite δ F) :
    gammaNorm δ (fun t => F t - dilate q F t) ≤ (1 + q ^ (-(1 + δ) / 2)) * gammaNorm δ F := by
  refine (gammaNorm_sub_le hδ hF (hF.dilate hq)).trans (le_of_eq ?_)
  rw [gammaNorm_dilate hq]
  ring

end RHTower.CubicGamma
