import GaloisForLFunctions.RHTower.AnalyticDominatedL2Sections
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.ThetaTailFirstMomentKernel
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Analytic locality for the literal theta tail kernel

The complete source and any strip source satisfying the displayed exponential
bounds have a total analytic L2 realization of twice their first-moment tail
kernel. Every finite negative dimension survives on every real tail. A negative
diagonal anywhere gives a finite real negative packet beyond any threshold.
This proves no sign for the complete theta kernel.
-/

noncomputable section
namespace RHTower.DominatedL2Sections
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace

/-- Source data needed by the tail Krein sections. Both the complete source and
the exact first atom have this analytic strip and exponential envelope. -/
structure StripSource where
  phi : ℂ → ℂ
  realValue : ℝ → ℝ
  ofReal : ∀ x : ℝ, phi (x:ℂ) = (realValue x:ℂ)
  holomorphic : DifferentiableOn ℂ phi thetaCuspStrip
  decay : ∀ δ : ℝ, 0≤δ → 2*δ<Real.pi/2 → ∃ C : ℝ, 0≤C ∧
    ∀ z : ℂ, |z.im|≤δ → ‖phi z‖ ≤ C*Real.exp (-|z.re|)

def StripSource.channel (P : StripSource) (c : ℝ) (z : ℂ) : ℝ → ℂ :=
  (Ioi (0:ℝ)).indicator (fun s => (z+(s:ℂ)+(c:ℂ))*P.phi (z+(s:ℂ)))

private theorem shifted_weight_bound {N c s : ℝ} (hN : 0≤N) (hs : 0 ≤ s) :
    (N+s+|c|)*Real.exp (-s) ≤ (N+|c|+2)*Real.exp (-(s/2)) := by
  have h0 : Real.exp (-s) ≤ Real.exp (-(s/2)) := Real.exp_le_exp.mpr (by linarith)
  have h1 : s*Real.exp (-s) ≤ 2*Real.exp (-(s/2)) := by
    have hs' : s ≤ 2*Real.exp (s/2) := by linarith [Real.add_one_le_exp (s/2)]
    calc
      _ ≤ (2*Real.exp (s/2))*Real.exp (-s) :=
        mul_le_mul_of_nonneg_right hs' (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring
  have h2 := mul_le_mul_of_nonneg_left h0 (show 0≤N+|c| by positivity)
  nlinarith

theorem StripSource.channel_bound (P : StripSource) {δ C N : ℝ} (hC : 0≤C)
    (hdec : ∀ z : ℂ, |z.im|≤δ → ‖P.phi z‖ ≤ C*Real.exp (-|z.re|))
    (hN : 0≤N) (c : ℝ) {z : ℂ} (hz : ‖z‖≤N) (him : |z.im|≤δ) (s : ℝ) :
    ‖P.channel c z s‖ ≤ C*Real.exp N*(N+|c|+2)*Real.exp (-(|s|/2)) := by
  by_cases hs : 0<s
  · rw [StripSource.channel, Set.indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs), norm_mul]
    have hphi := hdec (z+(s:ℂ)) (by simpa using him)
    have he : Real.exp (-|(z+(s:ℂ)).re|) ≤ Real.exp N*Real.exp (-s) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [Complex.add_re, Complex.ofReal_re]
      have hzre := Complex.abs_re_le_norm z
      linarith [le_abs_self (z.re+s), neg_le_abs z.re]
    have hphi' : ‖P.phi (z+(s:ℂ))‖ ≤ C*Real.exp N*Real.exp (-s) := by
      calc
        _ ≤ C*Real.exp (-|(z+(s:ℂ)).re|) := hphi
        _ ≤ C*(Real.exp N*Real.exp (-s)) := mul_le_mul_of_nonneg_left he hC
        _ = _ := by ring
    have hn : ‖z+(s:ℂ)+(c:ℂ)‖ ≤ N+s+|c| := by
      calc
        _ ≤ ‖z‖+‖(s:ℂ)‖+‖(c:ℂ)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ _ := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using
          _root_.add_le_add_right (_root_.add_le_add_right hz s) |c|
    have hp := mul_le_mul hn hphi' (norm_nonneg _) (by positivity : 0≤N+s+|c|)
    have hw := shifted_weight_bound (c := c) hN hs.le
    rw [abs_of_pos hs]
    nlinarith [mul_le_mul_of_nonneg_left hw (show 0≤C*Real.exp N by positivity)]
  · rw [StripSource.channel, Set.indicator_of_notMem (by simpa using hs), norm_zero]
    positivity

theorem StripSource.channel_measurable (P : StripSource) (c : ℝ)
    {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    AEStronglyMeasurable (P.channel c z) volume := by
  have hphi : Continuous (fun s : ℝ => P.phi (z+(s:ℂ))) :=
    P.holomorphic.continuousOn.comp_continuous
      (continuous_const.add Complex.continuous_ofReal) (fun s => by simpa only [thetaCuspStrip, Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, add_zero] using hz)
  exact ((show Continuous (fun s : ℝ => z+(s:ℂ)+(c:ℂ)) by fun_prop).mul hphi).aestronglyMeasurable.indicator
    measurableSet_Ioi

theorem StripSource.channel_holomorphic (P : StripSource) (c s : ℝ) :
    DifferentiableOn ℂ (fun z => P.channel c z s) thetaCuspStrip := by
  by_cases hs : 0<s
  · simp only [StripSource.channel, Set.indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs)]
    exact ((differentiableOn_id.add_const (s:ℂ)).add_const (c:ℂ)).mul
      (P.holomorphic.comp (differentiableOn_id.add_const (s:ℂ))
        (fun z hz => by simpa only [thetaCuspStrip, Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, add_zero] using hz))
  · simp only [StripSource.channel, Set.indicator_of_notMem (show s ∉ Ioi (0:ℝ) by exact hs)]
    exact differentiableOn_const (0:ℂ)

end RHTower.DominatedL2Sections

noncomputable section
namespace RHTower.DominatedL2Sections
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace

theorem StripSource.channel_local_bound (P : StripSource) (c : ℝ)
    {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    ∃ R : ℝ, 0<R ∧ ball z R ⊆ thetaCuspStrip ∧
      ∃ B : ℝ → ℝ, MemLp B 2 volume ∧ ∀ s w, w ∈ ball z R → ‖P.channel c w s‖ ≤ B s := by
  change |z.im|<Real.pi/4 at hz
  obtain ⟨δ, hzδ, hδ⟩ := exists_between hz
  have hδ0 : 0≤δ := le_trans (abs_nonneg _) hzδ.le
  have hopen : IsOpen {w : ℂ | |w.im|<δ} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hopen z hzδ
  obtain ⟨C, hC, hdec⟩ := P.decay δ hδ0 (by linarith)
  let N := ‖z‖+R
  let K := C*Real.exp N*(N+|c|+2)
  have hN : 0≤N := by dsimp [N]; positivity
  refine ⟨R, hR, fun w hw => lt_trans (hball hw) hδ,
    fun s => K*Real.exp (-(|s|/2)), ?_, ?_⟩
  · simpa [div_eq_mul_inv, mul_comm] using
      (memLp_two_exp_neg_mul_abs (b := (1/2:ℝ)) (by norm_num)).const_mul K
  · intro s w hw
    have hn : ‖w‖≤N := by
      have hd : ‖w-z‖<R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      calc
        ‖w‖ = ‖(w-z)+z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w-z‖+‖z‖ := norm_add_le _ _
        _ ≤ N := by dsimp [N]; linarith
    exact P.channel_bound hC hdec hN c hn (hball hw).le s

def StripSource.family (P : StripSource) (c : ℝ) : Family (volume : Measure ℝ) where
  domain := thetaCuspStrip
  isOpen_domain := isOpen_thetaCuspStrip
  value := P.channel c
  measurable := fun _ hz => P.channel_measurable c hz
  holomorphic := P.channel_holomorphic c
  local_bound := fun _ hz => P.channel_local_bound c hz

abbrev SourceL2 := Lp ℂ 2 (volume : Measure ℝ)
abbrev SourceDouble := WithLp 2 (SourceL2 × SourceL2)

def differenceForm : SourceDouble →L[ℂ] SourceDouble :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceL2 SourceL2).symm ∘L
    ((ContinuousLinearMap.fst ℂ SourceL2 SourceL2).prod
      (-(ContinuousLinearMap.snd ℂ SourceL2 SourceL2))) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ SourceL2 SourceL2)

theorem differenceForm_apply (v : SourceDouble) :
    differenceForm v = WithLp.toLp 2 (v.fst, -v.snd) := rfl

theorem differenceForm_hermitian (v w : SourceDouble) :
    inner ℂ v (differenceForm w) = inner ℂ (differenceForm v) w := by
  change inner ℂ v.fst w.fst+inner ℂ v.snd (-w.snd) =
    inner ℂ v.fst w.fst+inner ℂ (-v.snd) w.snd
  simp

/-- The source realization with one scalar comparison channel. -/
abbrev SourceAugmented := WithLp 2 (SourceDouble × ℂ)

def scalarDifferenceForm (c : ℝ) : SourceAugmented →L[ℂ] SourceAugmented :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceDouble ℂ).symm ∘L
    ((differenceForm.comp (ContinuousLinearMap.fst ℂ SourceDouble ℂ)).prod
      ((-(2*c:ℂ)) • (ContinuousLinearMap.snd ℂ SourceDouble ℂ))) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ SourceDouble ℂ)

theorem scalarDifferenceForm_apply (c : ℝ) (v : SourceAugmented) :
    scalarDifferenceForm c v = WithLp.toLp 2 (differenceForm v.fst, -(2*c:ℂ)*v.snd) := rfl

theorem scalarDifferenceForm_hermitian (c : ℝ) (v w : SourceAugmented) :
    inner ℂ v (scalarDifferenceForm c w) = inner ℂ (scalarDifferenceForm c v) w := by
  rw [scalarDifferenceForm_apply, scalarDifferenceForm_apply, WithLp.prod_inner_apply,
    WithLp.prod_inner_apply]
  change inner ℂ v.fst (differenceForm w.fst)+inner ℂ v.snd (-(2*c:ℂ)*w.snd) =
    inner ℂ (differenceForm v.fst) w.fst+inner ℂ (-(2*c:ℂ)*v.snd) w.snd
  rw [differenceForm_hermitian]
  simp only [RCLike.inner_apply, map_mul, map_neg, Complex.conj_ofReal, map_ofNat]
  ring

def StripSource.section (P : StripSource) (z : ℂ) : SourceDouble :=
  WithLp.toLp 2 ((P.family 1).section z, (P.family (-1)).section z)

theorem StripSource.analytic_inner (P : StripSource) (v : SourceDouble) :
    AnalyticOnNhd ℂ (fun z => inner ℂ v (P.section z)) thetaCuspStrip := by
  have hp := (P.family 1).analytic_inner v.fst
  have hm := (P.family (-1)).analytic_inner v.snd
  apply AnalyticOnNhd.congr isOpen_thetaCuspStrip (hp.add hm)
  intro z _
  change inner ℂ v.fst ((P.family 1).section z)+inner ℂ v.snd ((P.family (-1)).section z) = inner ℂ v (P.section z)
  rw [WithLp.prod_inner_apply]
  rfl

def StripSource.realization (P : StripSource) :=
  compressedClosedSpanRealization thetaCuspStrip P.section differenceForm
    isPreconnected_thetaCuspStrip isOpen_thetaCuspStrip P.analytic_inner differenceForm_hermitian

theorem StripSource.realization_kernel (P : StripSource) {z w : ℂ}
    (hz : z ∈ thetaCuspStrip) (hw : w ∈ thetaCuspStrip) :
    P.realization.kernel z w = inner ℂ (P.section w) (differenceForm (P.section z)) :=
  compressedClosedSpanRealization_kernel_eq thetaCuspStrip P.section differenceForm
    isPreconnected_thetaCuspStrip isOpen_thetaCuspStrip P.analytic_inner differenceForm_hermitian hz hw

end RHTower.DominatedL2Sections

noncomputable section
namespace RHTower.DominatedL2Sections
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace

theorem StripSource.inner_difference (P : StripSource) {z w : ℂ}
    (hz : z ∈ thetaCuspStrip) (hw : w ∈ thetaCuspStrip) :
    inner ℂ (P.section w) (differenceForm (P.section z)) =
      ∫ s : ℝ, star (P.channel 1 w s)*P.channel 1 z s-
        star (P.channel (-1) w s)*P.channel (-1) z s := by
  rw [differenceForm_apply, WithLp.prod_inner_apply]
  change inner ℂ ((P.family 1).section w) ((P.family 1).section z)+
    inner ℂ ((P.family (-1)).section w) (-((P.family (-1)).section z)) = _
  rw [inner_neg_right, ← sub_eq_add_neg, (P.family 1).inner_sections hz hw,
    (P.family (-1)).inner_sections hz hw]
  exact (integral_sub
    (((P.family 1).memLp hw).star.integrable_mul ((P.family 1).memLp hz))
    (((P.family (-1)).memLp hw).star.integrable_mul ((P.family (-1)).memLp hz))).symm

def StripSource.realKernel (P : StripSource) (x y : ℝ) : ℝ :=
  ∫ s in Ioi 0, (x+y+2*s)*P.realValue (x+s)*P.realValue (y+s)

private theorem ofReal_mem_strip (x : ℝ) : (x:ℂ) ∈ thetaCuspStrip := by
  simp only [thetaCuspStrip, mem_setOf_eq, Complex.ofReal_im, abs_zero]
  positivity

theorem StripSource.realization_kernel_real (P : StripSource) (x y : ℝ) :
    P.realization.kernel (x:ℂ) (y:ℂ) = ((2*P.realKernel x y:ℝ):ℂ) := by
  rw [P.realization_kernel (ofReal_mem_strip x) (ofReal_mem_strip y),
    P.inner_difference (ofReal_mem_strip x) (ofReal_mem_strip y)]
  have hpoint (s : ℝ) :
      star (P.channel 1 (y:ℂ) s)*P.channel 1 (x:ℂ) s-
        star (P.channel (-1) (y:ℂ) s)*P.channel (-1) (x:ℂ) s =
      (Ioi (0:ℝ)).indicator
        (fun s => ((2*((x+y+2*s)*P.realValue (x+s)*P.realValue (y+s)):ℝ):ℂ)) s := by
    by_cases hs : s ∈ Ioi (0:ℝ)
    · simp only [StripSource.channel, Set.indicator_of_mem hs, ← Complex.ofReal_add, P.ofReal]
      push_cast
      simp only [Complex.star_def, map_add, map_mul, map_neg, map_one, Complex.conj_ofReal]
      ring
    · simp only [StripSource.channel, Set.indicator_of_notMem hs, star_zero, zero_mul, sub_self]
  rw [show (fun s => star (P.channel 1 (y:ℂ) s)*P.channel 1 (x:ℂ) s-
      star (P.channel (-1) (y:ℂ) s)*P.channel (-1) (x:ℂ) s) =
    (Ioi (0:ℝ)).indicator
      (fun s => ((2*((x+y+2*s)*P.realValue (x+s)*P.realValue (y+s)):ℝ):ℂ)) from funext hpoint,
    integral_indicator measurableSet_Ioi, _root_.integral_complex_ofReal, integral_const_mul]
  rfl

def completeThetaSource : StripSource where
  phi := thetaCuspStripSource
  realValue := thetaCuspFullSource
  ofReal := thetaCuspStripSource_ofReal
  holomorphic := differentiableOn_thetaCuspStripSource
  decay := fun _ h0 h4 => exists_norm_thetaCuspStripSource_le h0 h4

end RHTower.DominatedL2Sections

noncomputable section
namespace RHTower
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace

namespace DominatedL2Sections

def StripSource.tailAccumulationSet (P : StripSource) (a : ℝ) :
    P.realization.toAnalyticTotalSectionFamily.AccumulationSet where
  nodes := Complex.ofReal '' Ioi a
  nodes_subset := by rintro z ⟨x, _, rfl⟩; exact ofReal_mem_strip x
  point := ((a+1:ℝ):ℂ)
  point_mem_domain := ofReal_mem_strip _
  frequently_nodes := by
    let u : ℕ → ℂ := fun n => ((a+1+1/((n:ℝ)+1):ℝ):ℂ)
    have ht : Tendsto u atTop (𝓝 ((a+1:ℝ):ℂ)) := by
      apply (Complex.continuous_ofReal.tendsto (a+1)).comp
      simpa [u] using (tendsto_const_nhds (x := a+1)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hn : ∀ n, u n ∈ ({((a+1:ℝ):ℂ)}ᶜ : Set ℂ) := by
      intro n
      simp only [u, mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
      have hp : 0 < 1/((n:ℝ)+1) := by positivity
      linarith
    have htw := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u ht
      (Eventually.of_forall hn)
    apply htw.frequently (Frequently.of_forall fun n => ?_)
    refine ⟨a+1+1/((n:ℝ)+1), ?_, rfl⟩
    change a < a+1+1/((n:ℝ)+1)
    have hp : 0 < 1/((n:ℝ)+1) := by positivity
    linarith

end DominatedL2Sections
end RHTower

noncomputable section
namespace RHTower.DominatedL2Sections
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace

/-- A real kernel's complex packet energy splits into two real packet energies. -/
theorem real_packet_of_negative_complex_packet {ι : Type*}
    (S : Finset ι) (K : ι → ι → ℝ) (d : ι → ℂ)
    (hd : (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*((2*K i j:ℝ):ℂ)).re < 0) :
    ∃ b : ι → ℝ, ∑ i ∈ S, ∑ j ∈ S, b i*b j*K i j < 0 := by
  have hsplit :
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*((2*K i j:ℝ):ℂ)).re =
      2*((∑ i ∈ S, ∑ j ∈ S, (d i).re*(d j).re*K i j)+
        (∑ i ∈ S, ∑ j ∈ S, (d i).im*(d j).im*K i j)) := by
    simp only [Complex.re_sum]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  rw [hsplit] at hd
  by_cases hr : (∑ i ∈ S, ∑ j ∈ S, (d i).re*(d j).re*K i j)<0
  · exact ⟨fun i => (d i).re, hr⟩
  · exact ⟨fun i => (d i).im, by linarith⟩

/-- A negative diagonal of an analytic strip source survives on every real tail. -/
theorem StripSource.negative_tail_packet_of_negative_diagonal
    (P : StripSource) {x : ℝ} (hx : P.realKernel x x < 0) (a : ℝ) :
    ∃ (S : Finset (Complex.ofReal '' Ioi a)) (b : (Complex.ofReal '' Ioi a) → ℝ),
      ∑ i ∈ S, ∑ j ∈ S, b i*b j*P.realKernel i.val.re j.val.re < 0 := by
  have hdiag : (inner ℂ (P.realization.kernelSection (x:ℂ))
      (P.realization.form (P.realization.kernelSection (x:ℂ)))).re < 0 := by
    change (P.realization.kernel (x:ℂ) (x:ℂ)).re < 0
    rw [P.realization_kernel_real]
    simp only [Complex.ofReal_re]
    linarith
  obtain ⟨d, hd⟩ := P.realization.exists_negative_packet_on_accumulationSet
    (P.tailAccumulationSet a) hdiag
  have hk (z w : Complex.ofReal '' Ioi a) :
      P.realization.kernel z w = ((2*P.realKernel z.val.re w.val.re:ℝ):ℂ) := by
    obtain ⟨r, hr, he⟩ := z.property
    obtain ⟨s, hs, hf⟩ := w.property
    rw [← he, ← hf, Complex.ofReal_re, Complex.ofReal_re]
    exact P.realization_kernel_real r s
  change (∑ i ∈ d.support, ∑ j ∈ d.support,
    star (d j)*d i*P.realization.kernel i j).re < 0 at hd
  simp_rw [hk] at hd
  obtain ⟨b, hb⟩ := real_packet_of_negative_complex_packet d.support
    (fun i j => P.realKernel i.val.re j.val.re) d hd
  exact ⟨d.support, b, hb⟩

end RHTower.DominatedL2Sections

noncomputable section
namespace RHTower.DominatedL2Sections
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace

/-- The obstruction is a literal finite real Gram matrix on nodes beyond any threshold. -/
theorem StripSource.exists_finite_negative_tail_of_negative_diagonal
    (P : StripSource) {x : ℝ} (hx : P.realKernel x x < 0) (a : ℝ) :
    ∃ (n : ℕ) (t b : Fin n → ℝ),
      (∀ i, a < t i) ∧ (∑ i, ∑ j, b i*b j*P.realKernel (t i) (t j)) < 0 := by
  classical
  obtain ⟨S, b, hb⟩ := P.negative_tail_packet_of_negative_diagonal hx a
  let e := S.equivFin.symm
  let t : Fin S.card → ℝ := fun i => (e i).val.val.re
  let c : Fin S.card → ℝ := fun i => b (e i).val
  refine ⟨S.card, t, c, ?_, ?_⟩
  · intro i
    obtain ⟨r, hr, he⟩ := (e i).val.property
    change a < (e i).val.val.re
    rw [← he, Complex.ofReal_re]
    exact hr
  · have hi (z : Complex.ofReal '' Ioi a) :
        (∑ j, b z*c j*P.realKernel z.val.re (t j)) =
          ∑ w ∈ S, b z*b w*P.realKernel z.val.re w.val.re := by
      dsimp [c, t, e]
      rw [Equiv.sum_comp S.equivFin.symm
        (fun w : S => b z*b w.val*P.realKernel z.val.re w.val.val.re),
        Finset.univ_eq_attach,
        Finset.sum_attach S (fun w => b z*b w*P.realKernel z.val.re w.val.re)]
    have he : (∑ i, ∑ j, c i*c j*P.realKernel (t i) (t j)) =
        ∑ z ∈ S, ∑ w ∈ S, b z*b w*P.realKernel z.val.re w.val.re := by
      change (∑ i, ∑ j, b (e i).val*c j*P.realKernel (e i).val.val.re (t j)) = _
      simp_rw [hi]
      dsimp [e]
      rw [Equiv.sum_comp S.equivFin.symm
        (fun z : S => ∑ w ∈ S, b z.val*b w*P.realKernel z.val.val.re w.val.re),
        Finset.univ_eq_attach,
        Finset.sum_attach S (fun z => ∑ w ∈ S, b z*b w*P.realKernel z.val.re w.val.re)]
    exact he ▸ hb

/-- All finite negative dimensions of the actual source realization survive every real tail. -/
theorem StripSource.negative_dimensions_tail_iff (P : StripSource) (a : ℝ) (r : ℕ) :
    P.realization.HasFiniteGramNegativeDimensionOn (Complex.ofReal '' Ioi a) r ↔
      P.realization.HasFiniteGramNegativeDimensionOn thetaCuspStrip r := by
  exact P.realization.hasFiniteGramNegativeDimensionOn_accumulationSet_iff
    (P.tailAccumulationSet a) r

end RHTower.DominatedL2Sections


namespace RHTower.DominatedL2Sections
open Set

theorem completeThetaSource_realKernel (x y : ℝ) :
    completeThetaSource.realKernel x y = thetaTailFirstMomentKernel x y :=
  (thetaTailFirstMomentKernel_eq_shiftTail x y).symm

/-- Exact source identity; the closed-span realization retains the complete theta sum. -/
theorem completeThetaSource_realization_kernel (x y : ℝ) :
    completeThetaSource.realization.kernel (x:ℂ) (y:ℂ) =
      ((2*thetaTailFirstMomentKernel x y:ℝ):ℂ) := by
  rw [completeThetaSource.realization_kernel_real, completeThetaSource_realKernel]

/-- Every finite negative dimension of the complete theta kernel is visible on every real tail. -/
theorem completeTheta_negative_dimensions_tail_iff (a : ℝ) (r : ℕ) :
    completeThetaSource.realization.HasFiniteGramNegativeDimensionOn
        (Complex.ofReal '' Ioi a) r ↔
      completeThetaSource.realization.HasFiniteGramNegativeDimensionOn thetaCuspStrip r :=
  completeThetaSource.negative_dimensions_tail_iff a r

end RHTower.DominatedL2Sections
