import GaloisForLFunctions.HTGeometry.ComplexSquareRootEnvelope
import GaloisForLFunctions.RHTower.ThetaTailAnalyticLocality
import GaloisForLFunctions.RHTower.ThetaTailKernelGeometricDeficitSplit
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Analytic locality of the geometric theta comparison

The square-root source feature is analytic on the right half-strip and has
the existing polynomial source envelope. Its augmented Hermitian realization
retains every finite negative dimension on every positive real tail.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry.ComplexSquareRootEnvelope
namespace RHTower.ThetaGeometricBoundaryAudit
open DominatedL2Sections Metric

def geometricStrip : Set ℂ := thetaCuspStrip ∩ {z : ℂ | 0 < z.re}

lemma isOpen_geometricStrip : IsOpen geometricStrip :=
  isOpen_thetaCuspStrip.inter (isOpen_lt continuous_const Complex.continuous_re)

lemma isPreconnected_geometricStrip : IsPreconnected geometricStrip :=
  (convex_thetaCuspStrip.inter (convex_halfSpace_re_gt 0)).isPreconnected

def geometricChannel (P : StripSource) (z : ℂ) : ℝ → ℂ :=
  (Ioi (0:ℝ)).indicator (fun s => Complex.sqrt (z+(s:ℂ))*P.phi (z+(s:ℂ)))

lemma geometricChannel_measurable (P : StripSource) {z : ℂ} (hz : z ∈ geometricStrip) :
    AEStronglyMeasurable (geometricChannel P z) volume := by
  have hphi : Continuous (fun s : ℝ => P.phi (z+(s:ℂ))) :=
    P.holomorphic.continuousOn.comp_continuous
      (continuous_const.add Complex.continuous_ofReal) (fun s => by
        simpa only [thetaCuspStrip, mem_setOf_eq, Complex.add_im, Complex.ofReal_im, add_zero]
          using hz.1)
  have hsqrt : ContinuousOn (fun s : ℝ => Complex.sqrt (z+(s:ℂ))) (Ioi 0) := by
    intro s hs
    have hr : 0 ≤ (z+(s:ℂ)).re := by
      change 0 ≤ z.re+s
      exact add_nonneg hz.2.le hs.le
    have hshift : ContinuousAt (fun t : ℝ => z+(t:ℂ)) s := by fun_prop
    exact (ContinuousAt.comp (f := fun t : ℝ => z+(t:ℂ))
      (Complex.continuousAt_sqrt (Or.inl hr)) hshift).continuousWithinAt
  exact (aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr
    ((hsqrt.mul hphi.continuousOn).aestronglyMeasurable measurableSet_Ioi)

lemma geometricChannel_holomorphic (P : StripSource) (s : ℝ) :
    DifferentiableOn ℂ (fun z => geometricChannel P z s) geometricStrip := by
  by_cases hs : 0 < s
  · simp only [geometricChannel, indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs)]
    apply (Complex.differentiableOn_sqrt.comp
      (differentiableOn_id.add_const (s:ℂ)) ?_).mul
      (P.holomorphic.comp (differentiableOn_id.add_const (s:ℂ)) ?_)
    · intro z hz
      exact Or.inl (show 0 < (z+(s:ℂ)).re from add_pos hz.2 hs)
    · intro z hz
      simpa only [thetaCuspStrip, mem_setOf_eq, Complex.add_im, Complex.ofReal_im, add_zero, id_eq]
        using hz.1
  · simp only [geometricChannel, indicator_of_notMem (show s ∉ Ioi (0:ℝ) from hs)]
    exact differentiableOn_const (0:ℂ)

lemma geometricChannel_le_channel (P : StripSource) {z : ℂ} (hz : 0 ≤ z.re) (s : ℝ) :
    ‖geometricChannel P z s‖ ≤ ‖P.channel 1 z s‖ := by
  by_cases hs : 0 < s
  · simp only [geometricChannel, StripSource.channel,
      indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs), norm_mul, Complex.ofReal_one]
    exact mul_le_mul_of_nonneg_right
      (sqrt_norm_le_add_one (show 0 ≤ (z+(s:ℂ)).re from add_nonneg hz hs.le)) (norm_nonneg _)
  · simp only [geometricChannel, StripSource.channel,
      indicator_of_notMem (show s ∉ Ioi (0:ℝ) from hs), le_refl]

lemma geometricChannel_local_bound (P : StripSource) {z : ℂ} (hz : z ∈ geometricStrip) :
    ∃ R : ℝ, 0 < R ∧ ball z R ⊆ geometricStrip ∧
      ∃ B : ℝ → ℝ, MemLp B 2 volume ∧
        ∀ s w, w ∈ ball z R → ‖geometricChannel P w s‖ ≤ B s := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_geometricStrip z hz
  obtain ⟨R, hR, _, B, hB, hbound⟩ := P.channel_local_bound 1 hz.1
  refine ⟨min r R, lt_min hr hR, ?_, B, hB, ?_⟩
  · intro w hw
    exact hsub (ball_subset_ball (min_le_left r R) hw)
  · intro s w hw
    have hwg := hsub (ball_subset_ball (min_le_left r R) hw)
    exact (geometricChannel_le_channel P hwg.2.le s).trans
      (hbound s w (ball_subset_ball (min_le_right r R) hw))

def geometricFamily (P : StripSource) : Family (volume : Measure ℝ) where
  domain := geometricStrip
  isOpen_domain := isOpen_geometricStrip
  value := geometricChannel P
  measurable := fun _ hz => geometricChannel_measurable P hz
  holomorphic := geometricChannel_holomorphic P
  local_bound := fun _ hz => geometricChannel_local_bound P hz

end RHTower.ThetaGeometricBoundaryAudit

namespace RHTower.ThetaGeometricBoundaryAudit
open DominatedL2Sections
open scoped InnerProductSpace ComplexOrder

abbrev GeometricAugmented := WithLp 2 (SourceDouble × SourceL2)

def geometricDifferenceForm (ε : ℝ) : GeometricAugmented →L[ℂ] GeometricAugmented :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceDouble SourceL2).symm ∘L
    ((differenceForm.comp (ContinuousLinearMap.fst ℂ SourceDouble SourceL2)).prod
      ((-(2*ε:ℂ)) • (ContinuousLinearMap.snd ℂ SourceDouble SourceL2))) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ SourceDouble SourceL2)

lemma geometricDifferenceForm_apply (ε : ℝ) (v : GeometricAugmented) :
    geometricDifferenceForm ε v = WithLp.toLp 2 (differenceForm v.fst, -(2*ε:ℂ) • v.snd) := rfl

lemma geometricDifferenceForm_hermitian (ε : ℝ) (v w : GeometricAugmented) :
    inner ℂ v (geometricDifferenceForm ε w) = inner ℂ (geometricDifferenceForm ε v) w := by
  rw [geometricDifferenceForm_apply, geometricDifferenceForm_apply,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change inner ℂ v.fst (differenceForm w.fst)+inner ℂ v.snd (-(2*ε:ℂ) • w.snd) =
    inner ℂ (differenceForm v.fst) w.fst+inner ℂ (-(2*ε:ℂ) • v.snd) w.snd
  rw [differenceForm_hermitian, inner_smul_left, inner_smul_right]
  simp [map_ofNat]

def geometricAugmentedSection (P : StripSource) (z : ℂ) : GeometricAugmented :=
  WithLp.toLp 2 (P.section z, (geometricFamily P).section z)

lemma geometricAugmentedSection_analytic_inner (P : StripSource) (v : GeometricAugmented) :
    AnalyticOnNhd ℂ (fun z => inner ℂ v (geometricAugmentedSection P z)) geometricStrip := by
  have hp : AnalyticOnNhd ℂ (fun z => inner ℂ v.fst (P.section z)) geometricStrip :=
    (P.analytic_inner v.fst).mono inter_subset_left
  have hg := (geometricFamily P).analytic_inner v.snd
  apply AnalyticOnNhd.congr isOpen_geometricStrip (hp.add hg)
  intro z _
  change inner ℂ v.fst (P.section z)+inner ℂ v.snd ((geometricFamily P).section z) =
    inner ℂ v (geometricAugmentedSection P z)
  rw [WithLp.prod_inner_apply]
  rfl

def geometricRealization (P : StripSource) (ε : ℝ) :=
  compressedClosedSpanRealization geometricStrip (geometricAugmentedSection P)
    (geometricDifferenceForm ε) isPreconnected_geometricStrip isOpen_geometricStrip
    (geometricAugmentedSection_analytic_inner P) (geometricDifferenceForm_hermitian ε)

lemma geometricRealization_kernel (P : StripSource) (ε : ℝ) {z w : ℂ}
    (hz : z ∈ geometricStrip) (hw : w ∈ geometricStrip) :
    (geometricRealization P ε).kernel z w =
      inner ℂ (P.section w) (differenceForm (P.section z))-
        (2*ε:ℂ)*inner ℂ ((geometricFamily P).section w) ((geometricFamily P).section z) := by
  rw [geometricRealization, compressedClosedSpanRealization_kernel_eq _ _ _ _ _ _ _ hz hw,
    geometricDifferenceForm_apply, WithLp.prod_inner_apply]
  change inner ℂ (P.section w) (differenceForm (P.section z))+
    inner ℂ ((geometricFamily P).section w) (-(2*ε:ℂ) • ((geometricFamily P).section z)) = _
  rw [inner_smul_right, neg_mul, sub_eq_add_neg]

lemma ofReal_mem_geometricStrip {x : ℝ} (hx : 0 < x) : (x:ℂ) ∈ geometricStrip := by
  constructor
  · simp only [thetaCuspStrip, mem_setOf_eq, Complex.ofReal_im, abs_zero]
    positivity
  · exact hx

lemma geometricChannel_real {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    geometricChannel completeThetaSource (x:ℂ) s =
      ((Real.sqrt (x+s)*thetaCuspFullSource (x+s):ℝ):ℂ) := by
  rw [geometricChannel, indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs)]
  change Complex.sqrt ((x:ℂ)+(s:ℂ))*thetaCuspStripSource ((x:ℂ)+(s:ℂ)) = _
  rw [← Complex.ofReal_add, thetaCuspStripSource_ofReal,
    Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr (add_nonneg hx.le hs.le)),
    Complex.ofReal_re, Complex.ofReal_mul]

lemma geometric_inner_real {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    inner ℂ ((geometricFamily completeThetaSource).section (y:ℂ))
      ((geometricFamily completeThetaSource).section (x:ℂ)) =
        (thetaTailGeometricKernel x y:ℂ) := by
  rw [(geometricFamily completeThetaSource).inner_sections
    (ofReal_mem_geometricStrip hx) (ofReal_mem_geometricStrip hy)]
  have hpoint (s : ℝ) :
      star (geometricChannel completeThetaSource (y:ℂ) s)*
          geometricChannel completeThetaSource (x:ℂ) s =
        (Ioi (0:ℝ)).indicator (fun s => ((Real.sqrt ((x+s)*(y+s))*
          (thetaCuspFullSource (x+s)*thetaCuspFullSource (y+s)):ℝ):ℂ)) s := by
    by_cases hs : 0 < s
    · rw [geometricChannel_real hy hs, geometricChannel_real hx hs,
        indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs)]
      have he : (Real.sqrt (y+s)*thetaCuspFullSource (y+s))*
          (Real.sqrt (x+s)*thetaCuspFullSource (x+s)) =
          Real.sqrt ((x+s)*(y+s))*(thetaCuspFullSource (x+s)*thetaCuspFullSource (y+s)) := by
        rw [Real.sqrt_mul (add_nonneg hx.le hs.le)]
        ring
      simpa only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul] using
        congrArg Complex.ofReal he
    · simp only [geometricChannel, indicator_of_notMem (show s ∉ Ioi (0:ℝ) from hs),
        star_zero, zero_mul]
  change (∫ s, star (geometricChannel completeThetaSource (y:ℂ) s)*
    geometricChannel completeThetaSource (x:ℂ) s) = _
  rw [show (fun s => star (geometricChannel completeThetaSource (y:ℂ) s)*
    geometricChannel completeThetaSource (x:ℂ) s) = _ from funext hpoint,
    integral_indicator measurableSet_Ioi, integral_complex_ofReal]
  rfl

lemma geometricRealization_kernel_real (ε : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (geometricRealization completeThetaSource ε).kernel (x:ℂ) (y:ℂ) =
      ((2*(thetaTailFirstMomentKernel x y-ε*thetaTailGeometricKernel x y):ℝ):ℂ) := by
  rw [geometricRealization_kernel _ _ (ofReal_mem_geometricStrip hx) (ofReal_mem_geometricStrip hy),
    ← completeThetaSource.realization_kernel (ofReal_mem_geometricStrip hx).1
      (ofReal_mem_geometricStrip hy).1,
    completeThetaSource_realization_kernel, geometric_inner_real hx hy]
  push_cast
  ring

end RHTower.ThetaGeometricBoundaryAudit

namespace RHTower.ThetaGeometricBoundaryAudit
open DominatedL2Sections
open scoped InnerProductSpace

def geometricTailAccumulationSet (P : StripSource) (ε a : ℝ) :
    (geometricRealization P ε).toAnalyticTotalSectionFamily.AccumulationSet where
  nodes := Complex.ofReal '' Ioi (max a 0)
  nodes_subset := by
    rintro z ⟨x, hx, rfl⟩
    exact ofReal_mem_geometricStrip ((le_max_right a 0).trans_lt hx)
  point := (((max a 0)+1:ℝ):ℂ)
  point_mem_domain := by
    apply ofReal_mem_geometricStrip
    have hm := le_max_right a (0:ℝ)
    linarith
  frequently_nodes := (P.tailAccumulationSet (max a 0)).frequently_nodes

lemma geometric_negative_dimensions_tail_iff (P : StripSource) (ε a : ℝ) (r : ℕ) :
    (geometricRealization P ε).HasFiniteGramNegativeDimensionOn
        (Complex.ofReal '' Ioi (max a 0)) r ↔
      (geometricRealization P ε).HasFiniteGramNegativeDimensionOn geometricStrip r :=
  (geometricRealization P ε).hasFiniteGramNegativeDimensionOn_accumulationSet_iff
    (geometricTailAccumulationSet P ε a) r


end RHTower.ThetaGeometricBoundaryAudit
