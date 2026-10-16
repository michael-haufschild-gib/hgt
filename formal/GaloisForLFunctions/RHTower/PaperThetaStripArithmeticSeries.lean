import GaloisForLFunctions.RHTower.PaperThetaStripSeries
import GaloisForLFunctions.RHTower.PaperThetaArithmeticHolomorphy

/-! # Literal convergence in the complete arithmetic graph

One BV control admits every full edge difference. Summable control admits
the series in the complete graph; injectivity of its source projection
identifies the graph sum with the original uniform sum.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph

theorem nativeMassMemLp (f : NativeContinuousSpace) : MemLp f 2 massMeasure :=
  MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖ (Eventually.of_forall f.norm_coe_le_norm)

def nativeMassOne : Lp ℂ 2 massMeasure :=
  (memLp_const (1:ℂ) : MemLp (fun _ : ℝ => (1:ℂ)) 2 massMeasure).toLp (fun _ => 1)

def nativeMassLM : NativeContinuousSpace →ₗ[ℂ] Lp ℂ 2 massMeasure where
  toFun f := (nativeMassMemLp f).toLp f
  map_add' f g := (nativeMassMemLp f).toLp_add (nativeMassMemLp g)
  map_smul' c f := (nativeMassMemLp f).toLp_const_smul c

theorem norm_nativeMass_le (f : NativeContinuousSpace) :
    ‖nativeMassLM f‖ ≤ ‖nativeMassOne‖*‖f‖ := by
  have h₁ : (nativeMassOne : ℝ → ℂ) =ᵐ[massMeasure] (fun _ => 1) :=
    (memLp_const (1:ℂ) : MemLp (fun _ : ℝ => (1:ℂ)) 2 massMeasure).coeFn_toLp
  have hb : ‖nativeMassLM f‖ ≤ ‖f‖*‖nativeMassOne‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(nativeMassMemLp f).coeFn_toLp, h₁] with x hx h1
    change ‖(nativeMassMemLp f).toLp f x‖ ≤ ‖f‖*‖nativeMassOne x‖
    rw [hx, h1, norm_one, mul_one]
    exact f.norm_coe_le_norm x
  exact hb.trans_eq (mul_comm _ _)

def nativeMassCLM : NativeContinuousSpace →L[ℂ] Lp ℂ 2 massMeasure :=
  nativeMassLM.mkContinuous ‖nativeMassOne‖ norm_nativeMass_le

theorem nativeMassCLM_injective : Function.Injective nativeMassCLM := by
  intro f g he
  have hf : (nativeMassCLM f : ℝ → ℂ) =ᵐ[massMeasure] f := (nativeMassMemLp f).coeFn_toLp
  have hg : (nativeMassCLM g : ℝ → ℂ) =ᵐ[massMeasure] g := (nativeMassMemLp g).coeFn_toLp
  rw [he] at hf
  have hfg := (f.continuous.ae_eq_iff_eq (μ := (volume : Measure ℝ)) g.continuous).mp
    (volume_absolutelyContinuous_mass.ae_eq (hf.symm.trans hg))
  exact BoundedContinuousFunction.ext (congrFun hfg)

def stripEdgeVector (B : ℝ) : Lp ℝ 2 edgeMeasure :=
  (bv_memLp_difference (boundedVariationOn_stripCutControl B)).toLp (difference (stripCutControl B))

theorem strip_control_memLp_edge (B : ℝ) (f : NativeContinuousSpace) (c : ℝ)
    (hi : ∀ x y, ‖f y-f x‖ ≤ c*|stripCutControl B y-stripCutControl B x|) :
    MemLp (fun e => f (left e)-f (right e)) 2 edgeMeasure := by
  apply (bv_memLp_difference (boundedVariationOn_stripCutControl B)).of_le_mul
  · exact ((f.continuous.measurable.comp measurable_snd).sub
      (f.continuous.measurable.comp (measurable_snd.add measurable_fst))).aestronglyMeasurable
  · exact Eventually.of_forall fun e => by
      simpa only [difference, Real.norm_eq_abs] using hi (right e) (left e)

def stripArithmeticLift (B : ℝ) (f : NativeContinuousSpace) (c : ℝ)
    (hi : ∀ x y, ‖f y-f x‖ ≤ c*|stripCutControl B y-stripCutControl B x|) :
    ComplexArithmeticGraph :=
  CHMDComplexJump.ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right
    f (nativeMassMemLp f) (strip_control_memLp_edge B f c hi)

@[simp] theorem stripArithmeticLift_source (B : ℝ) (f : NativeContinuousSpace) (c : ℝ)
    (hi : ∀ x y, ‖f y-f x‖ ≤ c*|stripCutControl B y-stripCutControl B x|) :
    (stripArithmeticLift B f c hi).val.fst = nativeMassCLM f := rfl

theorem stripArithmeticLift_edge (B : ℝ) (f : NativeContinuousSpace) (c : ℝ)
    (hi : ∀ x y, ‖f y-f x‖ ≤ c*|stripCutControl B y-stripCutControl B x|) :
    ((stripArithmeticLift B f c hi).val.snd : ℝ × ℝ → ℂ) =ᵐ[edgeMeasure]
      (fun e => f (left e)-f (right e)) :=
  (strip_control_memLp_edge B f c hi).coeFn_toLp

theorem stripArithmeticLift_norm_le (B : ℝ) (f : NativeContinuousSpace) (c : ℝ)
    (hi : ∀ x y, ‖f y-f x‖ ≤ c*|stripCutControl B y-stripCutControl B x|)
    (hn : ‖f‖ ≤ c) :
    ‖stripArithmeticLift B f c hi‖ ≤ c*(‖nativeMassOne‖+‖stripEdgeVector B‖) := by
  let p := stripArithmeticLift B f c hi
  have hs : ‖p.val.fst‖ ≤ c*‖nativeMassOne‖ := by
    calc
      _ ≤ ‖nativeMassOne‖*‖f‖ := norm_nativeMass_le f
      _ ≤ ‖nativeMassOne‖*c := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = _ := mul_comm _ _
  have he : ‖p.val.snd‖ ≤ c*‖stripEdgeVector B‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [stripArithmeticLift_edge B f c hi,
      (bv_memLp_difference (boundedVariationOn_stripCutControl B)).coeFn_toLp] with e hp hv
    change ‖p.val.snd e‖ ≤ c*‖stripEdgeVector B e‖
    change stripEdgeVector B e = difference (stripCutControl B) e at hv
    rw [hp, hv, Real.norm_eq_abs]
    exact hi (right e) (left e)
  have hp : ‖p‖ ≤ ‖p.val.fst‖+‖p.val.snd‖ := by
    change ‖p.val‖ ≤ _
    have hsq := WithLp.prod_norm_sq_eq_of_L2 p.val
    nlinarith [norm_nonneg p.val, norm_nonneg p.val.fst, norm_nonneg p.val.snd,
      mul_nonneg (norm_nonneg p.val.fst) (norm_nonneg p.val.snd)]
  exact hp.trans (by nlinarith)

/-- Full graph convergence, with the original uniform sum as its literal source. -/
theorem stripArithmeticSeries {f : ℕ → NativeContinuousSpace} {c : ℕ → ℝ} (B : ℝ)
    (hc : Summable c) (hn : ∀ n, ‖f n‖ ≤ c n)
    (hi : ∀ n x y, ‖f n y-f n x‖ ≤ c n*|stripCutControl B y-stripCutControl B x|) :
    HasSum (fun n => stripArithmeticLift B (f n) (c n) (hi n))
      (stripArithmeticLift B (∑' n, f n) (∑' n, c n) (stripSeries_increment hc hn hi)) := by
  let p := fun n => stripArithmeticLift B (f n) (c n) (hi n)
  have hf := hc.of_norm_bounded hn
  have hp : Summable p := (hc.mul_right (‖nativeMassOne‖+‖stripEdgeVector B‖)).of_norm_bounded
    (fun n => stripArithmeticLift_norm_le B (f n) (c n) (hi n) (hn n))
  have he : (∑' n, p n) =
      stripArithmeticLift B (∑' n, f n) (∑' n, c n) (stripSeries_increment hc hn hi) := by
    apply CHMDComplexJump.source_injective massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right
    change (CHMDComplexJump.sourceMap massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right) (∑' n, p n) = _
    rw [ContinuousLinearMap.map_tsum _ hp]
    change (∑' n, nativeMassCLM (f n)) = nativeMassCLM (∑' n, f n)
    exact (nativeMassCLM.map_tsum hf).symm
  rw [← he]
  exact hp.hasSum

end RHTower.PaperThetaEndpoint
