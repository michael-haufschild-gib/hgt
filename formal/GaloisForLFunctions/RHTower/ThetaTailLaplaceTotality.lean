import GaloisForLFunctions.RHTower.ThetaTailAnalyticLocality
import GaloisForLFunctions.RHTower.ThetaTailFirstMomentDoubleLaplace
import GaloisForLFunctions.HTGeometry.ExpRayL2
import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier–Laplace totality of the complete theta sections

Absolute scalar Fubini identifies the Laplace transforms of both theta source
channels with explicit half-line exponential sections. Fourier inversion
identifies their annihilators on every positive vertical line. Analytic
uniqueness identifies the original section span on every real tail.
The transformed difference form is twice the literal bilateral Bezoutian.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace FourierTransform
noncomputable section
namespace RHTower.ThetaTailSignature
open DominatedL2Sections GaloisForLFunctions.HTGeometry

lemma channel_continuous (d : ℝ) (w : ℂ) :
    Continuous (fun p : ℝ × ℝ => thetaTailChannelIntegrand d w p.1 p.2) := by
  unfold thetaTailChannelIntegrand
  exact ((by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.2+p.1+d:ℝ):ℂ))).mul
    (Complex.continuous_ofReal.comp
      (contDiff_thetaCuspFullSource.continuous.comp (by fun_prop)))).mul (by fun_prop)

lemma pairing_integrable (v : SourceL2) (d : ℝ) {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun p : ℝ × ℝ => star (v p.1) * thetaTailChannelIntegrand d w p.1 p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => star (v p.1) * thetaTailChannelIntegrand d w p.1 p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) :=
    ((Lp.aestronglyMeasurable v).restrict.star.comp_fst).mul
      (channel_continuous d w).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with s
    exact (integrable_thetaTailChannelIntegrand d w s).const_mul (star (v s))
  · have hb := (((Lp.memLp v).restrict (Ioi (0:ℝ))).norm.integrable_mul
      (memLp_two_expRay_restrict hw 0).norm).mul_const
        (∫ x : ℝ, ‖thetaTailChannelIntegrand d w 0 x‖)
    apply hb.congr
    filter_upwards with s
    simp only [norm_expRay, norm_mul, norm_star, integral_const_mul]
    rw [integral_norm_thetaTailChannelIntegrand_eq d w s]
    simp only [Pi.mul_apply]
    ring

lemma pairing_swap (v : SourceL2) (d : ℝ) {w : ℂ} (hw : 0 < w.re) :
    (∫ x : ℝ, ∫ s in Ioi (0:ℝ),
      star (v s) * thetaTailChannelIntegrand d w s x) =
    ∫ s in Ioi (0:ℝ), star (v s) * thetaTailKreinPlusTransform d w s := by
  rw [← integral_integral_swap (pairing_integrable v d hw)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  exact integral_const_mul (star (v s)) (thetaTailChannelIntegrand d w s)

lemma real_mem_strip (x : ℝ) : (x:ℂ) ∈ thetaCuspStrip := by
  simp only [thetaCuspStrip, mem_setOf_eq, Complex.ofReal_im, abs_zero]
  exact div_pos Real.pi_pos (by norm_num)

lemma channel_inner_real (v : SourceL2) (d x : ℝ) :
    inner ℂ v ((completeThetaSource.family d).section (x:ℂ)) =
      ∫ s in Ioi (0:ℝ), star (v s) *
        (((x+s+d:ℝ):ℂ) * (thetaCuspFullSource (x+s):ℂ)) := by
  rw [Family.inner_section _ _ (real_mem_strip x)]
  change (∫ s, star (v s) * completeThetaSource.channel d (x:ℂ) s) = _
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ Ioi (0:ℝ)
  · simp only [StripSource.channel, indicator_of_mem hs]
    rw [show (x:ℂ)+(s:ℂ) = ((x+s:ℝ):ℂ) by push_cast; rfl,
      completeThetaSource.ofReal]
    simp only [completeThetaSource, Complex.ofReal_add]
  · simp [StripSource.channel, hs]

lemma weighted_inner_integrable (v : SourceL2) (d : ℝ) {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun x : ℝ => Complex.exp (w*(x:ℂ)) *
      inner ℂ v ((completeThetaSource.family d).section (x:ℂ))) := by
  have hi := (pairing_integrable v d hw).integral_prod_right
  apply hi.congr
  filter_upwards with x
  rw [channel_inner_real, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  unfold thetaTailChannelIntegrand
  ring

lemma weighted_inner_continuous (v : SourceL2) (d : ℝ) (w : ℂ) :
    Continuous (fun x : ℝ => Complex.exp (w*(x:ℂ)) *
      inner ℂ v ((completeThetaSource.family d).section (x:ℂ))) := by
  apply Continuous.mul (by fun_prop)
  exact ((completeThetaSource.family d).analytic_inner v).continuousOn.comp_continuous
    Complex.continuous_ofReal real_mem_strip



def laplaceChannelValue (d : ℝ) (w : ℂ) : ℝ → ℂ :=
  (Ioi (0:ℝ)).indicator (thetaTailKreinPlusTransform d w)

lemma memLp_kreinPlusTransform (d : ℝ) {w : ℂ} (hw : 0 < w.re) :
    MemLp (thetaTailKreinPlusTransform d w) 2 (volume.restrict (Ioi (0:ℝ))) := by
  change MemLp (fun s => thetaTailKreinPlusTransform d w s) 2 (volume.restrict (Ioi 0))
  simpa only [thetaTailKreinPlusTransform_eq, expRay] using
    (memLp_two_expRay_restrict hw 0).mul_const
      (thetaBilateralLaplaceMoment w + (d:ℂ)*thetaBilateralLaplace w)

lemma memLp_laplaceChannelValue (d : ℝ) {w : ℂ} (hw : 0 < w.re) :
    MemLp (laplaceChannelValue d w) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioi).mpr (memLp_kreinPlusTransform d hw)

def laplaceChannel (d : ℝ) (w : ℂ) (hw : 0 < w.re) : SourceL2 :=
  (memLp_laplaceChannelValue d hw).toLp (laplaceChannelValue d w)

lemma inner_laplaceChannel (v : SourceL2) (d : ℝ) {w : ℂ} (hw : 0 < w.re) :
    inner ℂ v (laplaceChannel d w hw) =
      ∫ s in Ioi (0:ℝ), star (v s) * thetaTailKreinPlusTransform d w s := by
  rw [L2.inner_def, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [(memLp_laplaceChannelValue d hw).coeFn_toLp] with s hs
  change inner ℂ (v s) (((memLp_laplaceChannelValue d hw).toLp (laplaceChannelValue d w)) s) = _
  rw [hs, RCLike.inner_apply]
  by_cases h : s ∈ Ioi (0:ℝ) <;> simp [laplaceChannelValue, h, mul_comm]

lemma laplace_channel_identity (v : SourceL2) (d : ℝ) {w : ℂ} (hw : 0 < w.re) :
    (∫ x : ℝ, Complex.exp (w*(x:ℂ)) *
      inner ℂ v ((completeThetaSource.family d).section (x:ℂ))) =
      inner ℂ v (laplaceChannel d w hw) := by
  rw [inner_laplaceChannel, ← pairing_swap v d hw]
  apply integral_congr_ae
  filter_upwards with x
  rw [channel_inner_real, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  unfold thetaTailChannelIntegrand
  ring

def laplaceSection (w : ℂ) (hw : 0 < w.re) : SourceDouble :=
  WithLp.toLp 2 (laplaceChannel 1 w hw, laplaceChannel (-1) w hw)

lemma weighted_section_inner_integrable (v : SourceDouble) {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun x : ℝ => Complex.exp (w*(x:ℂ)) *
      inner ℂ v (completeThetaSource.section (x:ℂ))) := by
  simp only [StripSource.section, WithLp.prod_inner_apply, WithLp.ofLp_fst,
    WithLp.ofLp_snd, mul_add]
  exact (weighted_inner_integrable v.fst 1 hw).fun_add
    (weighted_inner_integrable v.snd (-1) hw)

lemma weighted_section_inner_continuous (v : SourceDouble) (w : ℂ) :
    Continuous (fun x : ℝ => Complex.exp (w*(x:ℂ)) *
      inner ℂ v (completeThetaSource.section (x:ℂ))) := by
  convert (weighted_inner_continuous v.fst 1 w).add
    (weighted_inner_continuous v.snd (-1) w) using 1
  ext x
  simp only [StripSource.section, WithLp.prod_inner_apply, WithLp.ofLp_fst,
    WithLp.ofLp_snd, mul_add, Pi.add_apply]

lemma laplace_section_identity (v : SourceDouble) {w : ℂ} (hw : 0 < w.re) :
    (∫ x : ℝ, Complex.exp (w*(x:ℂ)) *
      inner ℂ v (completeThetaSource.section (x:ℂ))) =
      inner ℂ v (laplaceSection w hw) := by
  simp only [StripSource.section, laplaceSection, WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, mul_add]
  rw [integral_add (weighted_inner_integrable v.fst 1 hw)
    (weighted_inner_integrable v.snd (-1) hw), laplace_channel_identity v.fst 1 hw,
    laplace_channel_identity v.snd (-1) hw]

lemma fourier_weighted_section_inner (v : SourceDouble) {σ : ℝ} (hσ : 0 < σ)
    (t : ℝ) :
    𝓕 (fun x : ℝ => Complex.exp ((σ:ℂ)*(x:ℂ)) *
      inner ℂ v (completeThetaSource.section (x:ℂ))) t =
    inner ℂ v (laplaceSection ((σ:ℂ) + (-2*Real.pi*t:ℝ)*Complex.I) (by simpa using hσ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← laplace_section_identity]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma laplace_annihilator_iff (v : SourceDouble) {σ : ℝ} (hσ : 0 < σ) :
    (∀ t : ℝ, inner ℂ v
      (laplaceSection ((σ:ℂ)+(t:ℂ)*Complex.I) (by simpa using hσ)) = 0) ↔
    (∀ x : ℝ, inner ℂ v (completeThetaSource.section (x:ℂ)) = 0) := by
  constructor
  · intro h
    let f : ℝ → ℂ := fun x => Complex.exp ((σ:ℂ)*(x:ℂ)) *
      inner ℂ v (completeThetaSource.section (x:ℂ))
    have hz : 𝓕 f = 0 := by
      funext t
      exact (fourier_weighted_section_inner v hσ t).trans (h (-2*Real.pi*t))
    have hfi : Integrable (𝓕 f) := by rw [hz]; exact integrable_zero _ _ _
    have hinv := (weighted_section_inner_continuous v (σ:ℂ)).fourierInv_fourier_eq
      (weighted_section_inner_integrable v (by simpa using hσ)) hfi
    intro x
    have hzero : f x = 0 := by
      rw [hz] at hinv
      exact (congrFun hinv.symm x).trans (by simp [Real.fourierInv_eq])
    exact (mul_eq_zero.mp hzero).resolve_left (Complex.exp_ne_zero _)
  · intro h t
    rw [← laplace_section_identity]
    simp [h]

lemma laplace_closedSpan_eq {σ : ℝ} (hσ : 0 < σ) :
    (Submodule.span ℂ (range (fun t : ℝ =>
      laplaceSection ((σ:ℂ)+(t:ℂ)*Complex.I) (by simpa using hσ)))).topologicalClosure =
    (Submodule.span ℂ (range (fun x : ℝ => completeThetaSource.section (x:ℂ)))).topologicalClosure := by
  ext v
  rw [RHTower.mem_topologicalClosure_span_iff, RHTower.mem_topologicalClosure_span_iff]
  simp only [forall_mem_range]
  exact forall_congr' fun u => by rw [laplace_annihilator_iff u hσ]



lemma inner_laplaceChannels (d : ℝ) {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    inner ℂ (laplaceChannel d v hv) (laplaceChannel d w hw) =
      ∫ s in Ioi (0:ℝ), star (thetaTailKreinPlusTransform d v s) *
        thetaTailKreinPlusTransform d w s := by
  rw [inner_laplaceChannel]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (memLp_laplaceChannelValue d hv).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with s hs hpos
  change star (((memLp_laplaceChannelValue d hv).toLp (laplaceChannelValue d v)) s) * _ = _
  rw [hs, laplaceChannelValue, indicator_of_mem hpos]

lemma laplace_section_kernel {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    inner ℂ (laplaceSection v hv) (differenceForm (laplaceSection w hw)) =
      2 * thetaBilateralLaplaceBezoutian w v := by
  rw [differenceForm_apply, WithLp.prod_inner_apply]
  change inner ℂ (laplaceChannel 1 v hv) (laplaceChannel 1 w hw) +
    inner ℂ (laplaceChannel (-1) v hv) (-(laplaceChannel (-1) w hw)) = _
  rw [inner_neg_right, ← sub_eq_add_neg, inner_laplaceChannels, inner_laplaceChannels]
  have hp : Integrable (fun s => star (thetaTailKreinPlusTransform 1 v s) *
      thetaTailKreinPlusTransform 1 w s) (volume.restrict (Ioi (0:ℝ))) := by
    exact ((memLp_kreinPlusTransform 1 hv).star.integrable_mul
      (memLp_kreinPlusTransform 1 hw)).congr (Eventually.of_forall fun s => rfl)
  have hm : Integrable (fun s => star (thetaTailKreinPlusTransform (-1) v s) *
      thetaTailKreinPlusTransform (-1) w s) (volume.restrict (Ioi (0:ℝ))) := by
    exact ((memLp_kreinPlusTransform (-1) hv).star.integrable_mul
      (memLp_kreinPlusTransform (-1) hw)).congr (Eventually.of_forall fun s => rfl)
  rw [← integral_sub hp hm]
  have hi := integral_thetaTailKreinDifference_eq_bilateralLaplaceBezoutian
    (c := 1) (by norm_num) (w := w) (v := v) (by simpa using add_pos hw hv)
  have heq : (∫ s in Ioi (0:ℝ), star (thetaTailKreinPlusTransform 1 v s) *
      thetaTailKreinPlusTransform 1 w s - star (thetaTailKreinPlusTransform (-1) v s) *
      thetaTailKreinPlusTransform (-1) w s) =
    ∫ s in Ioi (0:ℝ), thetaTailKreinPlusTransform 1 w s *
      (starRingEnd ℂ) (thetaTailKreinPlusTransform 1 v s) -
      thetaTailKreinMinusTransform 1 w s *
      (starRingEnd ℂ) (thetaTailKreinMinusTransform 1 v s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    have hm (z : ℂ) : thetaTailKreinPlusTransform (-1) z s =
        thetaTailKreinMinusTransform 1 z s := by
      simp only [thetaTailKreinPlusTransform, thetaTailKreinMinusTransform, sub_eq_add_neg]
    dsimp only
    rw [hm w, hm v]
    simp only [Complex.star_def]
    ring
  rw [heq]
  norm_num only [Complex.ofReal_one, mul_one] at hi
  linear_combination 2 * hi

lemma real_tail_annihilator_iff (v : SourceDouble) (a : ℝ) :
    (∀ x : Ioi a, inner ℂ v (completeThetaSource.section (x:ℂ)) = 0) ↔
    (∀ x : ℝ, inner ℂ v (completeThetaSource.section (x:ℂ)) = 0) := by
  constructor
  · intro h
    let D := completeThetaSource.tailAccumulationSet a
    have hfreq : ∃ᶠ z in nhdsWithin D.point ({D.point}ᶜ),
        inner ℂ v (completeThetaSource.section z) = 0 := by
      apply D.frequently_nodes.mono
      rintro z ⟨x, hx, rfl⟩
      exact h ⟨x, hx⟩
    have hz := (completeThetaSource.analytic_inner v).eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_thetaCuspStrip D.point_mem_domain hfreq
    exact fun x => hz (real_mem_strip x)
  · exact fun h x => h x

lemma real_tail_closedSpan_eq (a : ℝ) :
    (Submodule.span ℂ (range (fun x : Ioi a => completeThetaSource.section (x:ℂ)))).topologicalClosure =
    (Submodule.span ℂ (range (fun x : ℝ => completeThetaSource.section (x:ℂ)))).topologicalClosure := by
  ext v
  rw [RHTower.mem_topologicalClosure_span_iff, RHTower.mem_topologicalClosure_span_iff]
  simp only [forall_mem_range]
  exact forall_congr' fun u => by rw [real_tail_annihilator_iff u a]

lemma real_section_kernel (x y : ℝ) :
    inner ℂ (completeThetaSource.section (y:ℂ))
      (differenceForm (completeThetaSource.section (x:ℂ))) =
      2 * (thetaTailFirstMomentKernel x y : ℂ) := by
  rw [← completeThetaSource.realization_kernel (real_mem_strip x) (real_mem_strip y),
    completeThetaSource_realization_kernel]
  push_cast
  rfl

end RHTower.ThetaTailSignature
