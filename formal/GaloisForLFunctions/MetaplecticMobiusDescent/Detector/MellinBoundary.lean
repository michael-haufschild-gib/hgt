/-
The Mellin boundary adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.MarkedIdealSeries

/-!
# The Mellin boundary

Profiles, height spaces and height measures of the Mellin boundary, joint heights and scale
bounds; analyticity and strip differentiability of the continued source (`ProbeFiniteProductX`).
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

open MeasureTheory Set Filter Complex
open scoped Topology
namespace ProbeMellinBoundary
open PrincipalMellinResidues HeckeFamily SchwartzPlanePoisson

def height (t : ℝ) : ℝ := 1+|t|
lemma height_pos (t : ℝ) : 0< height t := by unfold height; positivity
lemma height_one_le (t : ℝ) : 1≤ height t := by simp [height]

def cauchy (t : ℝ) : ℝ := (1+t^2)⁻¹
lemma cauchy_nonneg (t : ℝ) : 0≤ cauchy t := by unfold cauchy; positivity
lemma cauchy_integrable : Integrable cauchy := integrable_inv_one_add_sq
lemma cauchy_tendsto : Tendsto cauchy atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop (1:ℝ) (tendsto_pow_atTop (by decide : 2≠0)))

theorem boundaryControl_of_cauchy (F : ℂ → ℂ) {a b C : ℝ}
    (ha : Continuous (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Continuous (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hla : ∀t : ℝ, ‖F ((a:ℂ)+t*I)‖≤ C*cauchy t)
    (hlb : ∀t : ℝ, ‖F ((b:ℂ)+t*I)‖≤ C*cauchy t)
    (hjoin : ∀x∈uIcc a b, ∀t : ℝ, 1≤|t| → ‖F ((x:ℂ)+t*I)‖≤ C*cauchy t) :
    BoundaryControl F a b := by
  have hi (h : Continuous (fun t : ℝ => F ((a:ℂ)+t*I))) :=
    (cauchy_integrable.const_mul C).mono' h.aestronglyMeasurable (Eventually.of_forall hla)
  have hj (ε : ℝ) (hε : |ε|=1) :
      Tendsto (fun T : ℝ => ∫x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      (by simpa using (cauchy_tendsto.const_mul C).mul_const |b-a|)
    filter_upwards [eventually_ge_atTop 1] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have ht : |ε*T|=T := by rw [abs_mul,hε,one_mul,abs_of_nonneg (by linarith)]
    have hh := hjoin x (uIoc_subset_uIcc hx) (ε*T) (by simpa [ht] using hT)
    have he : cauchy (ε*T)=cauchy T := by
      unfold cauchy
      have hs : (ε*T)^2=T^2 := by nlinarith [sq_abs (ε*T)]
      rw [hs]
    simpa [he] using hh
  refine ⟨hi ha, (cauchy_integrable.const_mul C).mono' hb.aestronglyMeasurable
    (Eventually.of_forall hlb), ?_, ?_⟩
  · simpa using hj (-1) (by norm_num)
  · simpa using hj 1 (by norm_num)

lemma pole_distance_vertical (p x t : ℝ) : |x-p|≤‖(x:ℂ)+t*I-p‖ := by
  simpa using Complex.abs_re_le_norm ((x:ℂ)+t*I-p)
lemma pole_distance_horizontal (p x t : ℝ) : |t|≤‖(x:ℂ)+t*I-p‖ := by
  simpa using Complex.abs_im_le_norm ((x:ℂ)+t*I-p)

theorem boundaryControl_of_pole_product (F V G : ℂ → ℂ) {a b p C D δ : ℝ} (J : ℕ)
    (hδ : 0<δ) (hδ1 : δ≤1) (hpa : δ≤|a-p|) (hpb : δ≤|b-p|)
    (hF : ∀x∈uIcc a b, ∀t : ℝ, (x:ℂ)+t*I≠p →
      F ((x:ℂ)+t*I)=V ((x:ℂ)+t*I)*G ((x:ℂ)+t*I)/((x:ℂ)+t*I-p))
    (hV : ContinuousOn V {z : ℂ | z.re∈uIcc a b})
    (hG : ContinuousOn G {z : ℂ | z.re∈uIcc a b})
    (_hC : 0≤ C) (hD : 0≤ D)
    (hVbd : ∀x∈uIcc a b, ∀t : ℝ, height t^(J+2)*‖V ((x:ℂ)+t*I)‖≤ C)
    (hGbd : ∀x∈uIcc a b, ∀t : ℝ, (x=a ∨ x=b ∨ 1≤|t|) →
      ‖G ((x:ℂ)+t*I)‖≤ D*height t^J) :
    BoundaryControl F a b := by
  have hne (x t : ℝ) (hd : δ≤‖(x:ℂ)+t*I-p‖) : (x:ℂ)+t*I≠p := by
    intro h
    rw [h, sub_self, norm_zero] at hd
    linarith
  have hc (x : ℝ) (hx : x∈uIcc a b) (hd : δ≤|x-p|) :
      Continuous (fun t : ℝ => F ((x:ℂ)+t*I)) := by
    have hn (t : ℝ) : (x:ℂ)+t*I≠p := hne x t (hd.trans (pole_distance_vertical p x t))
    have hv := hV.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (x:ℂ)+t*I))
      (by intro t; simpa using hx)
    have hg := hG.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (x:ℂ)+t*I))
      (by intro t; simpa using hx)
    exact ((hv.mul hg).div (by fun_prop) (fun t => sub_ne_zero.mpr (hn t))).congr
      (fun t => (hF x hx t (hn t)).symm)
  have hbound (x : ℝ) (hx : x∈uIcc a b) (t : ℝ)
      (hd : δ≤‖(x:ℂ)+t*I-p‖) (hboundary : x=a ∨ x=b ∨ 1≤|t|) : ‖F ((x:ℂ)+t*I)‖≤(C*D/δ)*cauchy t := by
    have hn := hne x t hd
    have hv : height t^2 * (height t^J*‖V ((x:ℂ)+t*I)‖)≤ C := by
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hVbd x hx t
    have hv' := weighted_two_to_cauchy
      (mul_nonneg (pow_nonneg (height_pos t).le _) (norm_nonneg _)) t hv
    change height t^J*‖V ((x:ℂ)+t*I)‖≤ C*cauchy t at hv'
    rw [hF x hx t hn, norm_div, norm_mul]
    apply (div_le_div₀ (mul_nonneg (norm_nonneg _) (mul_nonneg hD (pow_nonneg (height_pos t).le _)))
      (mul_le_mul_of_nonneg_left (hGbd x hx t hboundary) (norm_nonneg _)) hδ hd).trans
    calc
      ‖V ((x:ℂ)+t*I)‖*(D*height t^J)/δ = D/δ*(height t^J*‖V ((x:ℂ)+t*I)‖) := by ring
      _ ≤ D/δ*(C*cauchy t) := mul_le_mul_of_nonneg_left hv' (div_nonneg hD hδ.le)
      _ = _ := by ring
  apply boundaryControl_of_cauchy F (hc a (left_mem_uIcc) hpa) (hc b (right_mem_uIcc) hpb)
  · intro t
    exact hbound a left_mem_uIcc t (hpa.trans (pole_distance_vertical p a t)) (Or.inl rfl)
  · intro t
    exact hbound b right_mem_uIcc t (hpb.trans (pole_distance_vertical p b t)) (Or.inr (Or.inl rfl))
  · intro x hx t ht
    exact hbound x hx t ((hδ1.trans ht).trans (pole_distance_horizontal p x t)) (Or.inr (Or.inr ht))

def scaleBound (q lo hi : ℝ) : ℝ := Real.exp (max (Real.log q*lo) (Real.log q*hi))
lemma scaleBound_pos (q lo hi : ℝ) : 0< scaleBound q lo hi := Real.exp_pos _
lemma rpow_le_scaleBound {q lo hi x : ℝ} (hq : 0< q) (hx : x∈Icc lo hi) :
    q^x≤ scaleBound q lo hi := by
  rw [Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  by_cases hl : 0≤ Real.log q
  · exact (mul_le_mul_of_nonneg_left hx.2 hl).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hl)).trans (le_max_left _ _)
lemma cpow_le_scaleBound {q lo hi : ℝ} (hq : 0< q) (z : ℂ) (hz : z.re∈Icc lo hi) :
    ‖(q:ℂ)^z‖≤ scaleBound q lo hi := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
  exact rpow_le_scaleBound hq hz

def wScalar (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
    mellin (paperRadialFourier W0) z / LFunction eta s

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0< a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH AL : ℝ}
    (hcw : 1< cw) (hAH : 0≤ AH) (hAL : 0≤ AL) (JH JL : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤ w.re ∧ w.re≤ cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤ AH*height t^JH)
    (hLbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤ AL*height t^JL) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  let δ : ℝ := min (1/20) (cw-1)
  have hδ : 0<δ := lt_min (by norm_num) (sub_pos.mpr hcw)
  have hab : (19/20:ℝ)≤ cw := by linarith
  have hu : uIcc (19/20:ℝ) cw=Icc (19/20:ℝ) cw := uIcc_of_le hab
  obtain ⟨C,hC,hV⟩ := compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) (19/20) cw (JH+JL+2)
  let G (w : ℂ) := wScalar W0 X Z eta s z * (Y:ℂ)^(w-1) *
    (H w z*B w z) * HeckeOrigin.poleRemoved (fixedPrincipal M) w
  have hGc : ContinuousOn G {w : ℂ | w.re∈uIcc (19/20:ℝ) cw} := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact (continuous_const.mul ((continuous_id.sub continuous_const).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne')))).continuousOn
      · rw [hu]; exact hHB
    · exact (HeckeOrigin.poleRemoved_entire (fixedPrincipal M)).continuous.continuousOn
  apply boundaryControl_of_pole_product _ (mellin W1) G (p:=1) (δ:=δ) (C:=C)
    (D:=‖wScalar W0 X Z eta s z‖*scaleBound Y (19/20-1) (cw-1)*AH*AL) (JH+JL)
    hδ (by dsimp [δ]; exact (min_le_left _ _).trans (by norm_num))
    (by dsimp [δ]; norm_num)
    (by dsimp [δ]; rw [abs_of_pos (sub_pos.mpr hcw)]; exact min_le_right _ _) ?_
    (compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
      (W1.smooth ⊤)).continuous.continuousOn hGc hC.le
    (by unfold scaleBound; positivity) (by intro x hx t; exact hV x (hu ▸ hx) t) ?_
  · intro x hx t hn
    have hxp := (hu ▸ hx).1
    have h0 : (x:ℂ)+t*I≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : (x:ℂ)+t*I≠1 := by simpa using hn
    dsimp only [G]
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1]
    norm_num only [Complex.ofReal_one]
    apply (eq_div_iff (sub_ne_zero.mpr h1)).mpr
    unfold sourceMultiplier wScalar
    ring
  · intro x hx t hboundary
    have hv := cpow_le_scaleBound hY (((x:ℂ)+t*I)-1)
      (show (((x:ℂ)+t*I)-1).re∈Icc (19/20-1) (cw-1) by
        simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,zero_mul,
          sub_zero,add_zero,one_re]
        exact ⟨sub_le_sub_right (hu ▸ hx).1 1, sub_le_sub_right (hu ▸ hx).2 1⟩)
    dsimp only [G]
    rw [norm_mul,norm_mul,norm_mul]
    calc
      _ ≤ ‖wScalar W0 X Z eta s z‖ * scaleBound Y (19/20-1) (cw-1) *
          (AH*height t^JH) * (AL*height t^JL) := by
        have hscale := (scaleBound_pos Y (19/20-1) (cw-1)).le
        have hp := (height_pos t).le
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
            (hHBbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity))
          (hLbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

lemma gaussian_strip_norm_le (s : ℂ) {a b x : ℝ} (ha : 0< a) (hx : x∈Icc a b) (t : ℝ) :
    ‖Complex.exp ((s+((x:ℂ)+t*I)-1)^2)‖≤ Real.exp ((|s.re|+b+1)^2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hr : ((s+((x:ℂ)+t*I)-1)^2).re = (s.re+x-1)^2-(s.im+t)^2 := by simp [pow_two]
  rw [hr]
  have hxb : 0< x := ha.trans_le hx.1
  have hK : 0≤|s.re|+b+1 := by linarith [abs_nonneg s.re, hx.2]
  have hA : |s.re+x-1|≤|s.re|+b+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le s.re, le_abs_self s.re, hx.2]
  have hsq := pow_le_pow_left₀ (abs_nonneg (s.re+x-1)) hA 2
  rw [sq_abs] at hsq
  nlinarith [sq_nonneg (s.im+t)]

def zScalar (W1 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*mellin W1 1 / LFunction eta s

def zScaleBound (W1 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s : ℂ) (a b : ℝ) : ℝ :=
  scaleBound X (1/2-b) (1/2-a) * scaleBound Z (s.re+a-1) (s.re+b-1) *
    Real.exp ((|s.re|+b+1)^2) * ‖mellin W1 1‖ / ‖LFunction eta s‖

lemma zScalar_continuous (W1 : SchwartzMap ℝ ℂ) {X Z : ℝ} (hX : 0< X) (hZ : 0< Z)
    (eta : Character) (s : ℂ) : Continuous (zScalar W1 X Z eta s) := by
  unfold zScalar
  apply Continuous.div_const
  apply Continuous.mul_const
  apply Continuous.mul
  · exact (((continuous_const.sub continuous_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (((continuous_const.add continuous_id).sub continuous_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))))
  · fun_prop

lemma zScalar_norm_le (W1 : SchwartzMap ℝ ℂ) {X Z a b x : ℝ}
    (hX : 0< X) (hZ : 0< Z) (ha : 0< a) (hx : x∈Icc a b)
    (eta : Character) (s : ℂ) (t : ℝ) :
    ‖zScalar W1 X Z eta s ((x:ℂ)+t*I)‖≤ zScaleBound W1 X Z eta s a b := by
  unfold zScalar zScaleBound
  simp only [norm_div,norm_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul
  · apply mul_le_mul
    · apply cpow_le_scaleBound hX
      simpa using And.intro (sub_le_sub_left hx.2 (1/2)) (sub_le_sub_left hx.1 (1/2))
    · apply cpow_le_scaleBound hZ
      simpa using And.intro (by linarith [hx.1] : s.re+a-1≤ s.re+x-1)
        (by linarith [hx.2] : s.re+x-1≤ s.re+b-1)
    · exact norm_nonneg _
    · exact (scaleBound_pos _ _ _).le
  · exact gaussian_strip_norm_le s ha hx t
  · exact norm_nonneg _
  · exact mul_nonneg (scaleBound_pos _ _ _).le (scaleBound_pos _ _ _).le

theorem source_z_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0< a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (eta : Character) (s : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {e AH AL : ℝ}
    (he : 0< e) (hAH : 0≤ AH) (hAL : 0≤ AL) (JH JL : ℕ)
    (hHB : ContinuousOn (fun z => H 1 z*B 1 z)
      {z : ℂ | (33/200:ℝ)≤ z.re ∧ z.re≤1/6+e})
    (hHBbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖H 1 ((x:ℂ)+t*I) * B 1 ((x:ℂ)+t*I)‖≤ AH*height t^JH)
    (hLbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤ AL*height t^JL) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z eta s H B 1 z *
      LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  let δ : ℝ := min (1/600) e
  have hδ : 0<δ := lt_min (by norm_num) he
  have hab : (33/200:ℝ)≤1/6+e := by linarith
  have hu : uIcc (33/200:ℝ) (1/6+e)=Icc (33/200:ℝ) (1/6+e) := uIcc_of_le hab
  obtain ⟨C,hC,hV⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    (33/200) (1/6+e) (by norm_num) (JH+JL+2)
  let G (z : ℂ) := zScalar W1 X Z eta s z * (H 1 z*B 1 z) *
    HeckeOrigin.poleRemoved (fixedPrincipal M) (6*z) / 6
  have hGc : ContinuousOn G {z : ℂ | z.re∈uIcc (33/200:ℝ) (1/6+e)} := by
    apply ContinuousOn.div_const
    apply ContinuousOn.mul
    · exact (zScalar_continuous W1 hX hZ eta s).continuousOn.mul (by rw [hu]; exact hHB)
    · exact ((HeckeOrigin.poleRemoved_entire (fixedPrincipal M)).continuous.comp
        (continuous_const.mul continuous_id)).continuousOn
  apply boundaryControl_of_pole_product _ (mellin (paperRadialFourier W0)) G
    (p:=1/6) (δ:=δ) (C:=C)
    (D:=zScaleBound W1 X Z eta s (33/200) (1/6+e)*AH*AL/6) (JH+JL)
    hδ (by dsimp [δ]; exact (min_le_left _ _).trans (by norm_num))
    (by dsimp [δ]; norm_num)
    (by dsimp [δ]; rw [show (1/6+e:ℝ)-1/6=e by ring, abs_of_pos he]; exact min_le_right _ _)
    ?_ ?_ hGc hC.le (by unfold zScaleBound scaleBound; positivity) (by intro x hx t; exact hV x (hu ▸ hx) t) ?_
  · intro x hx t hn
    have hxp := (hu ▸ hx).1
    have h0 : 6*((x:ℂ)+t*I)≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : 6*((x:ℂ)+t*I)≠1 := by
      intro h
      apply hn
      push_cast
      linear_combination h/6
    have hd : (x:ℂ)+t*I-(1/6:ℂ)≠0 := sub_ne_zero.mpr (by simpa using hn)
    dsimp only [G]
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1]
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    apply (eq_div_iff hd).mpr
    unfold sourceMultiplier zScalar
    norm_num only [sub_self,Complex.cpow_zero,mul_one]
    ring
  · apply (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.mono
    intro z hz
    have := (hu ▸ hz).1
    change 0< z.re
    linarith
  · intro x hx t hboundary
    dsimp only [G]
    rw [norm_div,norm_mul,norm_mul]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ (zScaleBound W1 X Z eta s (33/200) (1/6+e) *
          (AH*height t^JH) * (AL*height t^JL))/6 := by
        have hS : 0≤ zScaleBound W1 X Z eta s (33/200) (1/6+e) := by
          unfold zScaleBound scaleBound
          positivity
        have hp := (height_pos t).le
        apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤6)
        exact mul_le_mul
          (mul_le_mul (zScalar_norm_le W1 hX hZ (by norm_num) (hu ▸ hx) eta s t)
            (hHBbd x (hu ▸ hx) t hboundary) (norm_nonneg _) hS)
          (hLbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

def profile (W0 W1 : SchwartzMap ℝ ℂ) (s w z : ℂ) : ℂ :=
  Complex.exp ((s+z-1)^2) * mellin (paperRadialFourier W0) z * mellin W1 w

def jointHeight (t v w : ℝ) : ℝ := 1+|t|+|v|+|w|
lemma jointHeight_pos (t v w : ℝ) : 0< jointHeight t v w := by unfold jointHeight; positivity

def gaussianMoment (n : ℕ) (u : ℝ) : ℝ := height u^n*Real.exp (-(u^2))
lemma gaussianMoment_nonneg (n : ℕ) (u : ℝ) : 0≤ gaussianMoment n u := by
  unfold gaussianMoment height
  positivity
lemma gaussianMoment_integrable (n : ℕ) : Integrable (gaussianMoment n) := by
  apply ((Continuation.polynomialGaussian_integrable n).const_mul ((2:ℝ)^(n-1))).mono'
  · unfold gaussianMoment height
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · apply Eventually.of_forall
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianMoment_nonneg n u)]
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg u) n
    simpa [gaussianMoment,height,Continuation.polynomialGaussian,mul_assoc] using
      mul_le_mul_of_nonneg_right h (Real.exp_pos (-(u^2))).le

lemma height_sub_le (t v : ℝ) : height t≤ height (t+v)*height v := by
  have ht : |t|≤|t+v|+|v| := by
    simpa using (abs_sub_le (t+v) 0 v)
  unfold height
  nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v), abs_nonneg (t+v),abs_nonneg v]

lemma jointHeight_le_shear (t v w : ℝ) :
    jointHeight t v w≤2*height (t+v)*height v*height w := by
  have ht : |t|≤|t+v|+|v| := by simpa using (abs_sub_le (t+v) 0 v)
  have huv : 1≤ height (t+v)*height v := one_le_mul_of_one_le_of_one_le (height_one_le _) (height_one_le _)
  have h1 : 1+|t|+|v|≤2*height (t+v)*height v := by
    unfold height
    nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v), abs_nonneg (t+v),abs_nonneg v]
  unfold jointHeight
  change 1+|t|+|v|+|w|≤2*height (t+v)*height v*(1+|w|)
  calc
    _ ≤ 2*height (t+v)*height v+|w| := by linarith [h1]
    _ ≤ 2*height (t+v)*height v+(2*height (t+v)*height v)*|w| := by
      have hh : 1≤2*height (t+v)*height v := by nlinarith
      have hhh := mul_le_mul_of_nonneg_right hh (abs_nonneg w)
      linarith
    _ = _ := by ring

lemma weighted_to_cauchy {f C : ℝ} (J : ℕ) (t : ℝ) (hf : 0≤ f)
    (h : height t^(J+2)*f≤ C) : height t^J*f≤ C*cauchy t := by
  have hh : (1+|t|)^2*(height t^J*f)≤ C := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using h
  exact weighted_two_to_cauchy
    (mul_nonneg (pow_nonneg (height_pos t).le _) hf) t hh

lemma weighted_coupled_cauchy (J : ℕ) (t v w A B C D : ℝ)
    (hA : 0≤ A) (hB : 0≤ B) (hC : 0≤ C) (_hD : 0≤ D)
    (ha : height v^(J+2)*A≤ C) (hb : height w^(J+2)*B≤ D) :
    jointHeight t v w^J * Real.exp (-((t+v)^2))*A*B ≤
      (2:ℝ)^J*C*D*(gaussianMoment J (t+v)*cauchy v*cauchy w) := by
  have hpow := pow_le_pow_left₀ (jointHeight_pos t v w).le (jointHeight_le_shear t v w) J
  have ha' := weighted_to_cauchy J v hA ha
  have hb' := weighted_to_cauchy J w hB hb
  calc
    _ ≤ (2*height (t+v)*height v*height w)^J * Real.exp (-((t+v)^2))*A*B := by gcongr
    _ = (2:ℝ)^J * gaussianMoment J (t+v) * (height v^J*A)*(height w^J*B) := by
      simp only [mul_pow,gaussianMoment]
      ring
    _ ≤ (2:ℝ)^J * gaussianMoment J (t+v) * (C*cauchy v)*(D*cauchy w) := by
      have hg := gaussianMoment_nonneg J (t+v)
      have hc := cauchy_nonneg v
      have hd := cauchy_nonneg w
      have hw := (height_pos w).le
      have hv := (height_pos v).le
      gcongr
    _ = _ := by ring

abbrev HeightSpace := (ℝ×ℝ)×ℝ
abbrev heightMeasure : Measure HeightSpace := (volume.prod volume).prod volume

def jointEnvelope (J : ℕ) (p : HeightSpace) : ℝ :=
  gaussianMoment J (p.1.1+p.1.2)*cauchy p.1.2*cauchy p.2

lemma jointEnvelope_nonneg (J : ℕ) (p : HeightSpace) : 0≤ jointEnvelope J p := by
  exact mul_nonneg (mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _)) (cauchy_nonneg _)

lemma jointEnvelope_integrable (J : ℕ) : Integrable (jointEnvelope J) heightMeasure := by
  have hp : MeasurePreserving (fun p : ℝ×ℝ => (p.1+p.2,p.2))
      (volume.prod volume) (volume.prod volume) := by
    have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
        (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
    have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
    simpa only [Function.comp_def,Prod.swap,add_comm] using! hp1
  have ht := hp.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hi := ((gaussianMoment_integrable J).mul_prod cauchy_integrable).mul_prod cauchy_integrable
  exact ht.integrable_comp_of_integrable hi

def onLines (W0 W1 : SchwartzMap ℝ ℂ) (σ ξ υ : ℝ) (p : HeightSpace) : ℂ :=
  profile W0 W1 ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)

lemma onLines_norm (W0 W1 : SchwartzMap ℝ ℂ) (σ ξ υ : ℝ) (p : HeightSpace) :
    ‖onLines W0 W1 σ ξ υ p‖ = Real.exp ((σ+ξ-1)^2)*Real.exp (-((p.1.1+p.1.2)^2))*
      ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ *
      ‖mellin W1 ((υ:ℂ)+p.2*I)‖ := by
  unfold onLines profile
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have hr : ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)^2).re =
      (σ+ξ-1)^2+(-((p.1.1+p.1.2)^2)) := by simp [pow_two]; ring
  rw [hr,Real.exp_add]

lemma onLines_continuous (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0< a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (σ ξ υ : ℝ) (hξ : 0<ξ) : Continuous (onLines W0 W1 σ ξ υ) := by
  have hR : Continuous (fun t : ℝ => mellin (paperRadialFourier W0) ((ξ:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t; simpa using hξ)
  have hW := (compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
    (W1.smooth ⊤)).continuous
  unfold onLines profile
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · exact hR.comp (continuous_snd.comp continuous_fst)
  · exact hW.comp (by fun_prop)

def realGaussianBound (slo shi zlo zhi : ℝ) : ℝ :=
  Real.exp ((|slo|+|shi|+|zlo|+|zhi|+1)^2)
lemma realGaussianBound_pos (slo shi zlo zhi : ℝ) : 0< realGaussianBound slo shi zlo zhi :=
  Real.exp_pos _
lemma realGaussian_le {slo shi zlo zhi σ ξ : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi) :
    Real.exp ((σ+ξ-1)^2)≤ realGaussianBound slo shi zlo zhi := by
  have hs : |σ|≤|slo|+|shi| := by
    rw [abs_le]
    constructor <;> linarith [hσ.1,hσ.2,neg_abs_le slo,le_abs_self shi,abs_nonneg slo,abs_nonneg shi]
  have hz : |ξ|≤|zlo|+|zhi| := by
    rw [abs_le]
    constructor <;> linarith [hξ.1,hξ.2,neg_abs_le zlo,le_abs_self zhi,abs_nonneg zlo,abs_nonneg zhi]
  have hh : |σ+ξ-1|≤|slo|+|shi|+|zlo|+|zhi|+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le σ,le_abs_self σ,neg_abs_le ξ,le_abs_self ξ]
  apply Real.exp_le_exp.mpr
  have hp := pow_le_pow_left₀ (abs_nonneg (σ+ξ-1)) hh 2
  simpa [sq_abs] using hp

lemma profile_moment_majorant (W0 W1 : SchwartzMap ℝ ℂ) (J : ℕ)
    {slo shi zlo zhi σ ξ υ C D : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi)
    (hC : 0≤ C) (hD : 0≤ D)
    (hR : ∀v : ℝ, height v^(J+2)*‖mellin (paperRadialFourier W0) ((ξ:ℂ)+v*I)‖≤ C)
    (hW : ∀w : ℝ, height w^(J+2)*‖mellin W1 ((υ:ℂ)+w*I)‖≤ D) (p : HeightSpace) :
    jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ≤
      (realGaussianBound slo shi zlo zhi*2^J*C*D)*jointEnvelope J p := by
  have hb := weighted_coupled_cauchy J p.1.1 p.1.2 p.2
    ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ ‖mellin W1 ((υ:ℂ)+p.2*I)‖ C D
    (norm_nonneg _) (norm_nonneg _) hC hD (hR _) (hW _)
  rw [onLines_norm]
  calc
    _ = Real.exp ((σ+ξ-1)^2) * (jointHeight p.1.1 p.1.2 p.2^J*
        Real.exp (-((p.1.1+p.1.2)^2))*
        ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖*‖mellin W1 ((υ:ℂ)+p.2*I)‖) := by ring
    _ ≤ realGaussianBound slo shi zlo zhi *
        ((2:ℝ)^J*C*D*(gaussianMoment J (p.1.1+p.1.2)*cauchy p.1.2*cauchy p.2)) :=
      mul_le_mul (realGaussian_le hσ hξ) hb
        (by have := (jointHeight_pos p.1.1 p.1.2 p.2).le; positivity)
        (realGaussianBound_pos _ _ _ _).le
    _ = _ := by unfold jointEnvelope; ring

theorem profile_uniform_moments (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0< zlo) (J : ℕ) :
    ∃ K : ℝ, 0< K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖) heightMeasure ∧
      (∫p : HeightSpace, jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤ K := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 zlo zhi hzlo (J+2)
  obtain ⟨D,hD,hW⟩ := compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+2)
  let A := realGaussianBound slo shi zlo zhi*2^J*C*D
  have hA : 0< A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|∫p, jointEnvelope J p ∂heightMeasure|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ
  have hbound := profile_moment_majorant W0 W1 J hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  have hc := onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ (hzlo.trans_le hξ.1)
  have hf : Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
      ‖onLines W0 W1 σ ξ υ p‖) heightMeasure := by
    apply ((jointEnvelope_integrable J).const_mul A).mono'
    · exact ((by unfold jointHeight; fun_prop : Continuous (fun p : HeightSpace =>
        jointHeight p.1.1 p.1.2 p.2^J)).mul hc.norm).aestronglyMeasurable
    · apply Eventually.of_forall
      intro p
      have hn : 0≤ jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ :=
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
      rw [Real.norm_eq_abs,abs_of_nonneg hn]
      exact hbound p
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫p, A*jointEnvelope J p ∂heightMeasure := integral_mono hf
      ((jointEnvelope_integrable J).const_mul A) hbound
    _ = A*(∫p, jointEnvelope J p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := le_abs_self (∫p, jointEnvelope J p ∂heightMeasure)
      exact mul_le_mul_of_nonneg_left (by linarith) hA.le

def outsideBox (T : ℝ) : Set HeightSpace :=
  {p | T < |p.1.1| ∨ T < |p.1.2| ∨ T < |p.2|}
lemma outsideBox_measurable (T : ℝ) : MeasurableSet (outsideBox T) := by
  unfold outsideBox
  measurability
lemma height_le_joint_on_tail {T : ℝ} {p : HeightSpace} (hp : p∈outsideBox T) :
    1+T≤ jointHeight p.1.1 p.1.2 p.2 := by
  rcases hp with h|h|h <;> unfold jointHeight <;>
    linarith [abs_nonneg p.1.1,abs_nonneg p.1.2,abs_nonneg p.2]

lemma weighted_tail_pointwise (f : HeightSpace → ℂ) (J N : ℕ) {T : ℝ} (hT : 0≤ T)
    {p : HeightSpace} (hp : p∈outsideBox T) :
    jointHeight p.1.1 p.1.2 p.2^J*‖f p‖ ≤
      (jointHeight p.1.1 p.1.2 p.2^(J+N)*‖f p‖)/(1+T)^N := by
  apply (le_div_iff₀ (by positivity)).mpr
  have hn := pow_le_pow_left₀ (by linarith : 0≤1+T) (height_le_joint_on_tail hp) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos p.1.1 p.1.2 p.2).le J) (norm_nonneg (f p)))
  convert hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0< zlo) (J N : ℕ) :
    ∃ K : ℝ, 0< K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi, ∀T : ℝ, 0≤ T →
      (∫p : HeightSpace in outsideBox T, jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤ K/(1+T)^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo (J+N)
  obtain ⟨K0,hK0,hM0⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ T hT
  obtain ⟨hi,hb⟩ := hM σ hσ ξ hξ υ hυ
  have hi0 := (hM0 σ hσ ξ hξ υ hυ).1
  calc
    _ ≤ ∫p : HeightSpace in outsideBox T,
        (jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖)/(1+T)^N ∂heightMeasure := by
      apply setIntegral_mono_on hi0.integrableOn (hi.div_const _).integrableOn (outsideBox_measurable T)
      intro p hp
      exact weighted_tail_pointwise _ J N hT hp
    _ = (∫p : HeightSpace in outsideBox T,
        jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)/(1+T)^N :=
      integral_div _ _
    _ ≤ (∫p : HeightSpace,
        jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)/(1+T)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply setIntegral_le_integral hi
      exact Eventually.of_forall (fun p => mul_nonneg
        (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

theorem profile_arithmetic_integrable (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ)
    (G : HeightSpace → ℂ) (hG : AEStronglyMeasurable G heightMeasure) (A : ℝ) (J : ℕ)
    (hbound : ∀p, ‖G p‖≤ A*jointHeight p.1.1 p.1.2 p.2^J) :
    Integrable (fun p => G p*onLines W0 W1 σ ξ υ p) heightMeasure := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ ξ ξ υ υ hξ J
  have hi := (hM σ ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩).1
  apply (hi.const_mul A).mono'
  · exact hG.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)

inductive SliceAxis where
  | s | z | w

def sliceMap (axis : SliceAxis) (T : ℝ) (q : ℝ×ℝ) : HeightSpace :=
  match axis with
  | .s => ((T,q.1),q.2)
  | .z => ((q.1,T),q.2)
  | .w => ((q.1,q.2),T)

lemma sliceMap_continuous (axis : SliceAxis) (T : ℝ) : Continuous (sliceMap axis T) := by
  cases axis <;> unfold sliceMap <;> fun_prop

lemma slice_height_le (axis : SliceAxis) (T : ℝ) (q : ℝ×ℝ) :
    height T≤ jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2 := by
  cases axis <;> unfold sliceMap height jointHeight <;>
    linarith [abs_nonneg q.1,abs_nonneg q.2]

lemma cauchy_le_one (t : ℝ) : cauchy t≤1 := by
  simpa [cauchy] using inv_anti₀ (by norm_num : (0:ℝ)<1)
    (show 1≤1+t^2 by nlinarith [sq_nonneg t])

def sliceEnvelope (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) : ℝ :=
  match axis with
  | .s | .z => gaussianMoment J (T+q.1)*cauchy q.2
  | .w => gaussianMoment J (q.1+q.2)*cauchy q.2

def sliceMass (J : ℕ) : ℝ := (∫u : ℝ, gaussianMoment J u)*(∫v : ℝ, cauchy v)

lemma sliceEnvelope_nonneg (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    0≤ sliceEnvelope axis J T q := by
  cases axis <;> exact mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _)

lemma jointEnvelope_slice_le (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointEnvelope J (sliceMap axis T q)≤ sliceEnvelope axis J T q := by
  cases axis
  · change gaussianMoment J (T+q.1)*cauchy q.1*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one q.1) (gaussianMoment_nonneg J (T+q.1))) (cauchy_nonneg q.2)
    simpa using hh
  · change gaussianMoment J (q.1+T)*cauchy T*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one T) (gaussianMoment_nonneg J (q.1+T))) (cauchy_nonneg q.2)
    simpa [add_comm] using hh
  · change gaussianMoment J (q.1+q.2)*cauchy q.2*cauchy T ≤ gaussianMoment J (q.1+q.2)*cauchy q.2
    simpa using mul_le_mul_of_nonneg_left (cauchy_le_one T)
      (mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _))

lemma pairEnvelope_integrable (J : ℕ) :
    Integrable (fun q : ℝ×ℝ => gaussianMoment J (q.1+q.2)*cauchy q.2) (volume.prod volume) := by
  have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
      (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
  have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
  have hi := hp1.integrable_comp_of_integrable ((gaussianMoment_integrable J).mul_prod cauchy_integrable)
  simpa only [Function.comp_def,Prod.swap,add_comm] using! hi

lemma sliceEnvelope_integrable (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    Integrable (sliceEnvelope axis J T) (volume.prod volume) := by
  cases axis
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact pairEnvelope_integrable J

lemma sliceEnvelope_integral (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    (∫q : ℝ×ℝ, sliceEnvelope axis J T q ∂volume.prod volume)=sliceMass J := by
  cases axis
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (q.1+q.2)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_symm _ (pairEnvelope_integrable J)]
    simp_rw [integral_mul_const,integral_add_right_eq_self]
    exact integral_const_mul _ _

lemma weighted_slice_pointwise (f : HeightSpace → ℂ) (axis : SliceAxis) (J N : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
      ‖f (sliceMap axis T q)‖ ≤
    (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
      ‖f (sliceMap axis T q)‖)/height T^N := by
  apply (le_div_iff₀ (pow_pos (height_pos T) N)).mpr
  have hn := pow_le_pow_left₀ (height_pos T).le (slice_height_le axis T q) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos (sliceMap axis T q).1.1
      (sliceMap axis T q).1.2 (sliceMap axis T q).2).le J) (norm_nonneg (f (sliceMap axis T q))))
  convert hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0< zlo) (J N : ℕ) :
    ∃ K : ℝ, 0< K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T : ℝ,
      Integrable (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)≤ K/height T^N := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    zlo zhi hzlo (J+N+2)
  obtain ⟨D,hD,hW⟩ := compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+N+2)
  let A := realGaussianBound slo shi zlo zhi*2^(J+N)*C*D
  have hA : 0< A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|sliceMass (J+N)|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ axis T
  have hb := profile_moment_majorant W0 W1 (J+N) hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  let f (q : ℝ×ℝ) := jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
    (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖
  have hbound (q : ℝ×ℝ) : f q≤(A/height T^N)*sliceEnvelope axis (J+N) T q := by
    calc
      _ ≤ (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
          ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖)/height T^N :=
        weighted_slice_pointwise _ axis J N T q
      _ ≤ (A*jointEnvelope (J+N) (sliceMap axis T q))/height T^N :=
        div_le_div_of_nonneg_right (hb _) (pow_nonneg (height_pos T).le N)
      _ ≤ (A*sliceEnvelope axis (J+N) T q)/height T^N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (jointEnvelope_slice_le _ _ _ _) hA.le)
          (pow_nonneg (height_pos T).le N)
      _ = _ := by ring
  have hfnonneg (q : ℝ×ℝ) : 0≤ f q := mul_nonneg
    (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
  have hf : Integrable f (volume.prod volume) := by
    apply ((sliceEnvelope_integrable axis (J+N) T).const_mul (A/height T^N)).mono'
    · have hc := (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)
      exact ((by cases axis <;> unfold sliceMap jointHeight <;> fun_prop : Continuous (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J)).mul hc.norm).aestronglyMeasurable
    · exact Eventually.of_forall (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (hfnonneg q)]; exact hbound q)
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ, (A/height T^N)*sliceEnvelope axis (J+N) T q ∂volume.prod volume :=
      integral_mono hf ((sliceEnvelope_integrable axis (J+N) T).const_mul _) hbound
    _ = (A/height T^N)*sliceMass (J+N) := by rw [integral_const_mul,sliceEnvelope_integral]
    _ ≤ (A/height T^N)*(1+|sliceMass (J+N)|) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hA.le (pow_nonneg (height_pos T).le N))
      linarith [le_abs_self (sliceMass (J+N))]
    _ = _ := by ring

theorem profile_arithmetic_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0< zlo) (J N : ℕ) :
    ∃ K : ℝ, 0< K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀A : ℝ, 0≤ A → ∀G : HeightSpace → ℂ,
      AEStronglyMeasurable G heightMeasure →
      (∀p, ‖G p‖≤ A*jointHeight p.1.1 p.1.2 p.2^J) →
      Integrable (fun p => G p*onLines W0 W1 σ ξ υ p) heightMeasure ∧
      ∀T : ℝ, 0≤ T →
      (∫p : HeightSpace in outsideBox T, ‖G p*onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)
        ≤ A*K/(1+T)^N := by
  obtain ⟨K,hK,hT⟩ := profile_uniform_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  obtain ⟨K0,hK0,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ A hA G hG hbound
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ (hzlo.trans_le hξ.1) G hG A J hbound
  refine ⟨hi,?_⟩
  intro T hT0
  calc
    _ ≤ ∫p : HeightSpace in outsideBox T,
        A*(jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure := by
      apply setIntegral_mono_on hi.norm.integrableOn
        (((hM σ hσ ξ hξ υ hυ).1).const_mul A).integrableOn (outsideBox_measurable T)
      intro p hp
      rw [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)
    _ = A*(∫p : HeightSpace in outsideBox T,
        jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) :=
      integral_const_mul _ _
    _ ≤ A*(K/(1+T)^N) := mul_le_mul_of_nonneg_left (hT σ hσ ξ hξ υ hυ T hT0) hA
    _ = _ := by ring

theorem profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0< zlo) (J N : ℕ) :
    ∃ K : ℝ, 0< K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T A : ℝ, 0≤ A → ∀G : ℝ×ℝ → ℂ,
      AEStronglyMeasurable G (volume.prod volume) →
      (∀q, ‖G q‖≤ A*jointHeight (sliceMap axis T q).1.1
        (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ, ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)
        ≤ A*K/height T^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA G hG hbound
  obtain ⟨hm,hmb⟩ := hM σ hσ ξ hξ υ hυ axis T
  have hdom (q : ℝ×ℝ) : ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖≤
      A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
        (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) := by
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg _)
  have hi : Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q))
      (volume.prod volume) := by
    apply (hm.const_mul A).mono'
    · exact hG.mul (((onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)).aestronglyMeasurable)
    · exact Eventually.of_forall hdom
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ,
        A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) ∂volume.prod volume :=
      integral_mono hi.norm (hm.const_mul A) hdom
    _ = A*(∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume) :=
      integral_const_mul _ _
    _ ≤ A*(K/height T^N) := mul_le_mul_of_nonneg_left hmb hA
    _ = _ := by ring

theorem profile_arithmetic_fubini (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ)
    (G : HeightSpace → ℂ) (hG : AEStronglyMeasurable G heightMeasure) (A : ℝ) (J : ℕ)
    (hbound : ∀p, ‖G p‖≤ A*jointHeight p.1.1 p.1.2 p.2^J) :
    ((∫p : HeightSpace, G p*onLines W0 W1 σ ξ υ p ∂heightMeasure) =
      ∫r : ℝ, ∫s : ℝ, ∫t : ℝ, G ((r,s),t)*onLines W0 W1 σ ξ υ ((r,s),t)) ∧
    ((∫p : HeightSpace, G p*onLines W0 W1 σ ξ υ p ∂heightMeasure) =
      ∫t : ℝ, ∫s : ℝ, ∫r : ℝ, G ((r,s),t)*onLines W0 W1 σ ξ υ ((r,s),t)) := by
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ hξ G hG A J hbound
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with t ht
    exact integral_prod_symm _ ht

end ProbeMellinBoundary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Complex Set
namespace PrincipalMellinGrowth
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

def principalConstant (M : Ideal Eisenstein.O) : ℝ :=
  (1+HeckeLogarithmicInput.uniformConstant)*(M.absNorm : ℝ)^(3/5 : ℝ)*
    HeckeDeletionBounds.localBound (19/20)^(primeSupport M).card

theorem principalConstant_pos (M : Ideal Eisenstein.O) [NeZero M] :
    0< principalConstant M := by
  have hQ : 0<(M.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  exact mul_pos (mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg])
    (Real.rpow_pos_of_pos hQ _)) (pow_pos (HeckeDeletionBounds.localBound_pos (by norm_num)) _)

lemma poleRemoved_eq_mul_regular (χ : Character) (hχ : χ.residue=1)
    {s : ℂ} (hs : s+1≠0) :
    HeckeOrigin.poleRemoved χ s=(s+1)*HeckeLogarithmicInput.regular χ s := by
  simp only [HeckeLogarithmicInput.regular,if_pos hχ,HeckePrincipalStrip.sourceNormalized]
  field_simp

theorem principal_poleRemoved_growth (χ : Character) (hχ : χ.residue=1)
    {s : ℂ} (hs : (19/20 : ℝ)≤ s.re) :
    ‖HeckeOrigin.poleRemoved χ s‖≤ principalConstant χ.modulus*‖s+1‖*(3+|s.im|)^2 := by
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue=1 := (HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mp hχ
  have hs0 : 0< s.re := by linarith
  have h0 : s≠0 := by intro hh; norm_num [hh] at hs
  have hplus : s+1≠0 := by
    intro hh
    have hr := congrArg Complex.re hh
    simp only [add_re,one_re,zero_re] at hr
    linarith
  have heq : HeckeOrigin.poleRemoved χ s=
      ((s+1)*HeckeLogarithmicInput.regular ψ s)*HeckeFiniteDeletion.factors χ.modulus ψ s := by
    rw [← poleRemoved_eq_mul_regular ψ hψ hplus]
    by_cases h1 : s=1
    · subst s
      rw [HeckeOrigin.poleRemoved_one,HeckeOrigin.poleRemoved_one]
      exact HeckeFiniteDeletion.regularizedL_eq_of_mask χ ψ hmask (by norm_num)
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1,HeckeOrigin.poleRemoved_eq ψ h0 h1,
        HeckeFiniteDeletion.LFunction_eq_of_mask χ ψ hmask hs0 h1]
      ring
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10 : ℝ)≤ s.re)
  have hd := (HeckeDeletionBounds.factors_bound_pow (19/20) (by norm_num)
    χ.modulus ψ hs).1
  have hQ' : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)≤(χ.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hC := HeckeLogarithmicInput.uniformConstant_nonneg
  have hD := (HeckeDeletionBounds.localBound_pos (by norm_num : (0 : ℝ)<19/20)).le
  rw [heq,norm_mul,norm_mul]
  calc
    _ ≤ (‖s+1‖*(HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
          (3+|s.im|)^2))*
        HeckeDeletionBounds.localBound (19/20)^(primeSupport χ.modulus).card := by
      gcongr
    _ ≤ (‖s+1‖*((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
          (3+|s.im|)^2))*
        HeckeDeletionBounds.localBound (19/20)^(primeSupport χ.modulus).card := by
      gcongr
      linarith
    _ = _ := by unfold principalConstant; ring

def wAmplitude (M : Ideal Eisenstein.O) (cw : ℝ) : ℝ := 9*(cw+2)*principalConstant M

def zAmplitude (M : Ideal Eisenstein.O) : ℝ := 216*principalConstant M

theorem wAmplitude_pos (M : Ideal Eisenstein.O) [NeZero M] {cw : ℝ} (hcw : 1< cw) :
    0< wAmplitude M cw := by
  unfold wAmplitude
  exact mul_pos (mul_pos (by norm_num) (by linarith)) (principalConstant_pos M)

theorem zAmplitude_pos (M : Ideal Eisenstein.O) [NeZero M] : 0< zAmplitude M := by
  unfold zAmplitude
  exact mul_pos (by norm_num) (principalConstant_pos M)

theorem fixed_principal_w_growth (M : Ideal Eisenstein.O) [NeZero M]
    {cw : ℝ} (hcw : 1< cw) {x : ℝ} (hx : x∈Icc (19/20 : ℝ) cw) (t : ℝ) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤ wAmplitude M cw*height t^3 := by
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(((x:ℂ)+t*I) : ℂ).re by simpa using hx.1)
  have hn : ‖((x:ℂ)+t*I)+1‖≤(cw+2)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
      mul_zero,sub_zero,add_zero,zero_add,mul_one,one_re,one_im]
    rw [abs_of_pos (by linarith [hx.1] : 0< x+1)]
    unfold height
    have hmul : 0≤(cw+1)*|t| := mul_nonneg (by linarith) (abs_nonneg t)
    nlinarith [hx.2]
  have hheight : (3+|t|)^2≤9*height t^2 := by
    have hh : 3+|t|≤3*height t := by unfold height; linarith [abs_nonneg t]
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+|t|) hh 2
    simpa only [mul_pow,show (3:ℝ)^2=9 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have ht0 := (height_pos t).le
  change ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤
    principalConstant M*‖((x:ℂ)+t*I)+1‖*(3+|(((x:ℂ)+t*I) : ℂ).im|)^2 at hb
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  calc
    _ ≤ principalConstant M*‖((x:ℂ)+t*I)+1‖*(3+|t|)^2 := hb
    _ ≤ principalConstant M*((cw+2)*height t)*(9*height t^2) := by
      have hc2 : 0≤ cw+2 := by linarith
      gcongr
    _ = _ := by unfold wAmplitude; ring

theorem fixed_principal_z_growth (M : Ideal Eisenstein.O) [NeZero M]
    {e : ℝ} (he : 0< e) (he' : e≤2/3) {x : ℝ}
    (hx : x∈Icc (33/200 : ℝ) (1/6+e)) (t : ℝ) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤ zAmplitude M*height t^3 := by
  have hre : (6*((x:ℂ)+t*I) : ℂ).re=6*x := by simp
  have him : (6*((x:ℂ)+t*I) : ℂ).im=6*t := by simp
  have habs : |(6*((x:ℂ)+t*I) : ℂ).im|=6*|t| := by rw [him,abs_mul]; norm_num
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(6*((x:ℂ)+t*I) : ℂ).re by rw [hre]; linarith [hx.1])
  have hn : ‖(6*((x:ℂ)+t*I) : ℂ)+1‖≤6*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp only [add_re,add_im,one_re,one_im,add_zero,hre,him]
    rw [abs_of_pos (by linarith [hx.1] : 0<6*x+1),abs_mul]
    rw [abs_of_pos (by norm_num : (0:ℝ)<6)]
    unfold height
    linarith [hx.2]
  have hheight : (3+6*|t|)^2≤36*height t^2 := by
    have hh : 3+6*|t|≤6*height t := by unfold height; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+6*|t|) hh 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have ht0 := (height_pos t).le
  change ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤
    principalConstant M*‖(6*((x:ℂ)+t*I) : ℂ)+1‖*(3+|(6*((x:ℂ)+t*I) : ℂ).im|)^2 at hb
  rw [habs] at hb
  calc
    _ ≤ principalConstant M*‖(6*((x:ℂ)+t*I) : ℂ)+1‖*(3+6*|t|)^2 := hb
    _ ≤ principalConstant M*(6*height t)*(36*height t^2) := by gcongr
    _ = _ := by unfold zAmplitude; ring

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0< a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH : ℝ}
    (hcw : 1< cw) (hAH : 0≤ AH) (JH : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤ w.re ∧ w.re≤ cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤ AH*height t^JH) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply ProbeMellinBoundary.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY eta s z hEta H B
    (AL:=wAmplitude M cw) hcw hAH (wAmplitude_pos M hcw).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_w_growth M hcw hx t

theorem source_z_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0< a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (eta : Character) (s : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {e AH : ℝ}
    (he : 0< e) (he' : e≤2/3) (hAH : 0≤ AH) (JH : ℕ)
    (hHB : ContinuousOn (fun z => H 1 z*B 1 z)
      {z : ℂ | (33/200:ℝ)≤ z.re ∧ z.re≤1/6+e})
    (hHBbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖H 1 ((x:ℂ)+t*I) * B 1 ((x:ℂ)+t*I)‖≤ AH*height t^JH) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z eta s H B 1 z *
      LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ eta s hEta H B
    (AL:=zAmplitude M) he hAH (zAmplitude_pos M).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_z_growth M he he' hx t

end PrincipalMellinGrowth

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def spectralCompensatedHigh (S : Finset Id) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η 1 x w z

theorem spectralCompensatedHigh_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    spectralCompensatedHigh S T η x w z B q=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedIdealHighSeries_eq_product S hS (T\J)
    (fun P hP=> hT P (Finset.mem_sdiff.mp hP).1) η x w z hx hw hz]
  simp only [mul_div_assoc,Finset.prod_mul_distrib]
  ring

theorem spectralCompensatedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh_eq_product S hS T hT η x w z B q hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein ProbeEuler ProbeLocal
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma initialPrime_denominators (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 0< x.re) (hw : 0< w.re) (hz : 0< z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    (1-coordV Q z≠0) ∧ (1-coordW Q 1 w≠0) ∧
      (1-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x≠0) := by
  dsimp only
  have hQ : (1:ℝ)< Ideal.absNorm P.val := by
    have hh := HeckeIdealSeries.prime_norm_two_le P
    exact_mod_cast (by omega : 1< Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)< Ideal.absNorm P.val := by linarith
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordD_norm_le _ hQ0 _ 1 x (HeckeFamily.idealCoeff_norm_le_one η P.val) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

lemma idealClosedCorrection_eq_continued (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm P.val
    idealClosedCorrection η P x w z=continuedCorrection (coordV Q z) (coordW Q 1 w)
      (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) := rfl

lemma standardFactor_times_continued (V W D M : ℂ)
    (hV : 1-V≠0) (hW : 1-W≠0) (hD : 1-D≠0) :
    (1-D)/((1-V)*(1-W))*continuedCorrection V W D M=localFactor V W M := by
  unfold continuedCorrection localFactor
  field_simp
  ring

lemma idealHighLocalFactor_eq_raw (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : CanonicalQuadraticSieve.Supported P.val) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z=
      localFactor (coordV Q z) (coordW Q 1 w) (idealMarkedClosed η P x w z) := by
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have he := idealHighLocalFactor_rational η P hs x w z hx hw hz
  have hc := standardFactor_times_continued (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) hd.1 hd.2.1 hd.2.2
  rw [←idealClosedCorrection_eq_continued] at hc
  dsimp only at he hc ⊢
  rw [he]
  simpa only [coordV,coordW,coordD,star_one,mul_one,one_mul] using hc

theorem idealCompensatedRatio_eq_continued (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z B q : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    B*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q=
      compensatedReplacement (coordV Q z) (coordW Q 1 w)
        (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) B q /
          idealClosedCorrection η P x w z := by
  have hs := outside_prime_supported S hS.bad P hP
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have hraw := idealHighLocalFactor_eq_raw η P hs x w z hx hw hz
  have hn := source_idealHighLocalFactor_ne_zero S hS η P hP x w z hx hw hz
  rw [hraw] at hn
  have hH : idealClosedCorrection η P x w z≠0 :=
    factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))
  have he := compensatedReplacement_eq_raw (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) B q hd.1 hd.2.1 hd.2.2 hn
  rw [←continuedCorrection_eq_raw _ _ _ _ hd.1 hd.2.1 hd.2.2,
    ←idealClosedCorrection_eq_continued] at he
  dsimp only at hraw he ⊢
  rw [idealMarkedLocalFactor_rational η P hs x w z hx hz,hraw,he]
  exact (mul_div_cancel_left₀ _ hH).symm

theorem spectralCompensatedHigh_continued (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(compensatedReplacement (coordV (Ideal.absNorm P.val) z)
          (coordW (Ideal.absNorm P.val) 1 w)
          (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
          (idealMarkedClosed η P x w z) (B P) (q P) / idealClosedCorrection η P x w z) := by
  rw [spectralCompensatedHigh_L_factorization S hS T hT η x w z B q hx hw hz]
  congr 1
  apply Finset.prod_congr rfl
  intro P hP
  exact idealCompensatedRatio_eq_continued S hS η P (hT P hP) x w z (B P) (q P) hx hw hz

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace ProbeFiniteProductBounds
open Eisenstein CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal Eisenstein.O

def localMultiplier (η : Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  (Q : ℂ)^(z-1) *
    (compensatedReplacement (coordV Q z) (coordW Q 1 w)
      (coordD Q (idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z)
      (star (idealCoeff η P.val)*(Q : ℂ)^x) ((Q : ℂ)^(-w)) /
      idealClosedCorrection η P x w z)

def selectedMultiplier (η : Character) (T : Finset PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∏ P ∈ T, localMultiplier η P x w z

def slotMultiplier {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (x w z : ℂ) : ℂ :=
  ∏ j ∈ J, ∑ P ∈ T j, b j P * localMultiplier η P x w z

theorem correction_lower_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hb := (idealClosedCorrection_bound η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem correction_ne_zero (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (correction_lower_bound η S hS P hP x w z hx hw hz))

theorem correction_inverse_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hh := correction_lower_bound η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma marked_differentiableAt_w (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma marked_differentiableAt_z (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryIdealGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro w hw
  have hmc := marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem local_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : 7/8 ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12*‖coordR Q A x z‖*(1+‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12*(1/2:ℝ)*(1+1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4*‖coordK Q η x w‖*‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4*1*(1/2:ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

lemma replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
  have hV1 : ‖1-V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have hW1 : ‖1-W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have hBq : ‖B-q‖ ≤ R+1 := (norm_sub_le B q).trans (add_le_add hB hq)
  have hVW : ‖1-V*W‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (V*W)
    rw [norm_one,norm_mul] at hn
    have hm : ‖V‖*‖W‖ ≤ 1/2 := by
      calc
        _ ≤ (1/2:ℝ)*1 := by gcongr
        _ = _ := by ring
    linarith
  have hi := inv_one_sub_norm_le_two D hD
  unfold compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (‖B-q‖*‖1-V‖*‖1-W‖*‖P‖ + ‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*P) (q*(1-V*W))
    _ ≤ ((R+1)*2*2*16+1*2)*2 := by gcongr
    _ ≤ 200*(1+R) := by linarith

def localBound (Bx Bz : ℝ) (P : PrimeIdeal) : ℝ :=
  (Ideal.absNorm P.val : ℝ)^(Bz-1) * (400*(1+(Ideal.absNorm P.val : ℝ)^Bx))

lemma localBound_nonneg (Bx Bz : ℝ) (P : PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  unfold localBound
  positivity

theorem local_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    marked_bound Q (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := correction_inverse_bound η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
  have hp : ‖(Q : ℂ)^(z-1)‖ ≤ Q^(Bz-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re,Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  change _ ≤ Q^(Bz-1)*(400*(1+Q^Bx))
  calc
    _ ≤ Q^(Bz-1)*(200*(1+Q^Bx)*2) := by gcongr
    _ = _ := by ring

def selectedBound (T : Finset PrimeIdeal) (Bx Bz : ℝ) : ℝ :=
  ∏ P ∈ T, localBound Bx Bz P

def slotBound {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : ℝ :=
  ∏ j ∈ J, ∑ P ∈ T j, ‖b j P‖ * localBound Bx Bz P

lemma selectedBound_nonneg (T : Finset PrimeIdeal) (Bx Bz : ℝ) :
    0 ≤ selectedBound T Bx Bz := Finset.prod_nonneg (fun P _ => localBound_nonneg Bx Bz P)

lemma slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (localBound_nonneg Bx Bz P))

theorem selected_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => selectedMultiplier η T x w z) {w : ℂ | 9/10 < w.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_w η S hS P (hT P hp) x z hx hz)

theorem selected_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => selectedMultiplier η T x w z) {z : ℂ | 4/25 < z.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_z η S hS P (hT P hp) x w hx hw)

theorem slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem selected_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖selectedMultiplier η T x w z‖ ≤ selectedBound T Bx Bz := by
  simp only [selectedMultiplier,selectedBound,norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun P hp => local_norm_bound η S hS P (hT P hp) x w z Bx Bz hx hw hz)

theorem slot_norm_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma global_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hb := globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem combined_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (globalClosedCorrection_analytic_w η S hS x z hx hz).mul (slot_analytic_w η S hS J T b hT x z hx hz)

theorem combined_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (globalClosedCorrection_analytic_z η S hS x w hx hw).mul (slot_analytic_z η S hS J T b hT x w hx hw)

theorem combined_slot_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem selected_initial_identity (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ)
    (hx : 3/2 < x.re) (hw : 2 < w.re) (hz : 1/6 < z.re) :
    (∏ P ∈ T, (Ideal.absNorm P.val : ℂ)^(z-1)) *
      spectralCompensatedHigh S T η x w z
        (fun P => star (idealCoeff η P.val)*(Ideal.absNorm P.val : ℂ)^x)
        (fun P => (Ideal.absNorm P.val : ℂ)^(-w)) =
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w /
        LFunction (η.excludePrimes S hS.prime) x) *
        (globalClosedCorrection η S x w z * selectedMultiplier η T x w z) := by
  rw [spectralCompensatedHigh_continued S hS T hT η x w z _ _ hx hw hz]
  simp only [selectedMultiplier,localMultiplier,Finset.prod_mul_distrib,Complex.ofReal_natCast]
  ring_nf

theorem source_w_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1< cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_w η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem source_z_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : 7/8 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0< e) (he' : e≤2/3) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
        LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply PrincipalMellinGrowth.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ
    (η.excludePrimes S hS.prime) s hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) he he'
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      1 ((x : ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)

theorem source_multiplier_differentiable_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hM := compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (combined_slot_analytic_w η S hS.tail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he : (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun w => ((X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (SchwartzPlanePoisson.paperRadialFourier W0) z /
      LFunction (η.excludePrimes S hS.prime) s) * (Y:ℂ)^(w-1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem source_multiplier_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : 7/8 ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (SchwartzPlanePoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)< z.re at hz; linarith)
  have hH := (combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he : (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w / LFunction (η.excludePrimes S hS.prime) s) *
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (SchwartzPlanePoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

theorem source_w_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0) {cw : ℝ} (hcw : 1< cw) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral cw (fun w => K w z * LFunction (fixedPrincipal M) w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction (fixedPrincipal M) w) +
        K 1 z * fixedPrincipalResidue M := by
  dsimp only
  apply PrincipalMellinResidues.source_w_shift (fixedPrincipal M) _ z hcw
  · exact (source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY s z hs (by linarith)).mono (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · exact source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1 M X Y Z hY s z hs hz hEta hcw

theorem source_residue_z_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : 7/8 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0< e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral (1/6+e) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) =
      verticalIntegral (33/200) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) +
        K 1 (1/6) * fixedPrincipalResidue M / 6 := by
  dsimp only
  apply PrincipalMellinResidues.source_residue_z_shift (fixedPrincipal M) _ he
  · exact (source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s 1 hs
      (by norm_num)).mono (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · exact source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ s hs hEta he he'

theorem local_eq_regionSlot (η : Character) (P : PrimeIdeal) (s w z : ℂ) :
    localMultiplier η P s w z = (Ideal.absNorm P.val : ℂ)^(z-1) *
      PrincipalSlotEstimate.regionSlot (Ideal.absNorm P.val)
        (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) s w z := by
  simp only [localMultiplier,PrincipalSlotEstimate.regionSlot,PrincipalSlotEstimate.regionReplacement,
    PrincipalSlotEstimate.regionMarked,idealMarkedClosed,idealClosedCorrection,Complex.ofReal_natCast]

def windowMultiplier {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (W : ι → ℝ → ℂ) (scale : ι → ℝ) (s w z : ℂ) : ℂ :=
  slotMultiplier η J T (fun j P => W j ((Ideal.absNorm P.val : ℝ)/scale j)) s w z

theorem window_at_residue {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (W : ι → ℝ → ℝ) (scale : ι → ℝ) (s : ℂ) :
    windowMultiplier η J T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      ∏ j ∈ J, ∑ P ∈ T j,
        ((W j ((Ideal.absNorm P.val : ℝ)/scale j) *
          (Ideal.absNorm P.val : ℝ)^(-(5/6 : ℝ)) : ℝ) : ℂ) *
        PrincipalSlotEstimate.principalSlot (Ideal.absNorm P.val)
          (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) s := by
  unfold windowMultiplier slotMultiplier
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro P hp
  rw [local_eq_regionSlot,PrincipalSlotEstimate.region_slot_at_residue]
  have hQ : 0 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  rw [Complex.ofReal_mul,Complex.ofReal_cpow hQ.le]
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  norm_num
  ring_nf

theorem slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 7/8≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(7/8 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using PrincipalSlotEstimate.weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryIdealGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 7/8≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(7/8 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)

@[simp] theorem slotMultiplier_empty {ι : Type*} (η : Character) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (s w z : ℂ) : slotMultiplier η ∅ T b s w z = 1 := by
  simp [slotMultiplier]

theorem selected_as_slots (η : Character) (T : Finset PrimeIdeal) (s w z : ℂ) :
    selectedMultiplier η T s w z = slotMultiplier η T (fun P => {P}) (fun _ _ => 1) s w z := by
  simp [selectedMultiplier,slotMultiplier]

theorem fixed_source_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (η : Character) (s : ℂ) (hs : 7/8 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e) (he' : e≤2/3) :
    let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  constructor
  · intro z hz
    exact source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY s z hs (by rw [hz]; linarith) hEta hcw
  · exact source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0
      (∏ P ∈ S, P) X Y Z hX hZ s hs hEta he he'

lemma boundary_mul_const (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

theorem fixed_source_ordered_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (η : Character) (s : ℂ) (hs : 7/8 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hh := fixed_source_boundaries S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ η s hs hEta hcw he he'
  dsimp only at hh ⊢
  refine ⟨?_,hh.2⟩
  intro z hz
  convert boundary_mul_const _ _ _ (hh.1 z hz) (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1 <;> first | rfl | (funext w; ring)

theorem uniform_closed_box_bound {ι : Type*} (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (Bx Bw Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Character) (s w z : ℂ),
      s.re ∈ Icc (7/8) Bx → w.re ∈ Icc (19/20) Bw → z.re ∈ Icc (33/200) Bz →
      ‖globalClosedCorrection η S s w z * slotMultiplier η J T b s w z‖ ≤ C :=
  ⟨(3/2)*slotBound J T b Bx Bz,
    mul_nonneg (by norm_num) (slotBound_nonneg J T b Bx Bz),
    fun η s w z hs hw hz => combined_slot_bound η S hS J T b hT s w z Bx Bz hs hw.1 hz⟩

end ProbeFiniteProductBounds
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace ProbeFiniteProductX
open Eisenstein CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds
local notation "Id" => Ideal Eisenstein.O

lemma marked_differentiableAt_x (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryIdealGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | 7/8 < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | 7/8 < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_x η S hS P (hT P hp) w z hw hz)

theorem slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | 7/8 < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem window_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | 7/8 < x.re} :=
  slot_analytic_x η S hS J T _ hT w z hw hz

theorem combined_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | 7/8 < x.re} :=
  (globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (selected_analytic_x η S hS T hT w z hw hz)

theorem combined_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | 7/8 < x.re} :=
  (globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (slot_analytic_x η S hS J T b hT w z hw hz)

def continuedSourceMultiplier {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(x+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((x+z-1)^2) *
    mellin (SchwartzPlanePoisson.paperRadialFourier W0) z * mellin W1 w *
      HeckeReciprocal.reciprocal (η.excludePrimes S hS) x *
      globalClosedCorrection η S x w z * slotMultiplier η J T b x w z

theorem continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (7/8 : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hx' : (7/8 : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem continued_source_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a : ℝ) (w z : ℂ) :
    (fun t : ℝ => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z ((a:ℂ)+t*I) w z)
      =ᵐ[volume] (fun t : ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
        ((a:ℂ)+t*I) (globalClosedCorrection η S ((a:ℂ)+t*I))
          (slotMultiplier η J T b ((a:ℂ)+t*I)) w z) := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply continued_source_eq_raw
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem source_analytic_x_off_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (7/8 : ℝ) HeckeZeroSupremum.beta < x.re ∧ x≠1} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((isOpen_lt continuous_const Complex.continuous_re).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (7/8 : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; norm_num at hx'
  have hL := LFunction_differentiableAt (η.excludePrimes S hS.prime) hx0 (Or.inl hx.2)
  have hLn := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime) hβ (Or.inl hx.2)
  have hH := (globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : 7/8< a) (hβ : HeckeZeroSupremum.beta< a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤ x.re ∧ x.re≤ c} := by
  apply (continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

theorem continued_source_principal_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (w z : ℂ)
    (hχ : (η.excludePrimes S hS).residue=1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z 1 w z=0 := by
  simp only [continuedSourceMultiplier,HeckeReciprocal.reciprocal_principal_one _ hχ,mul_zero,zero_mul]

end ProbeFiniteProductX
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
