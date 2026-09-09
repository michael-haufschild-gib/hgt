import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWeightRotatedEnergy
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Removing the cusp truncation in the original product measure. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Pointwise convergence of the actual bounded profiles to the unbounded cusp weight. -/
theorem cuspWeightProfile_tendsto (y : ℝ) :
    Tendsto (fun n : ℕ => cuspWeightProfile (n+1) y) atTop (𝓝 (cuspWeightLimit y)) := by
  have h := ((tendsto_natCast_div_add_atTop y).comp (tendsto_add_atTop_nat 1)).mul_const y
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)*y/((n:ℝ)+1+y)) atTop (𝓝 y) := by
    simpa only [Function.comp_apply,Nat.cast_add,Nat.cast_one,one_mul,div_mul_eq_mul_div] using h
  exact (ht.const_mul (cuspWeightCutoff y)).const_add cuspWeightBase

private theorem limit_continuous : Continuous (fun p : ℝ × UpperHalfPlane =>
    (cuspWeightLimit p.2.im : ℂ)) := by
  unfold cuspWeightLimit cuspWeightCutoff
  fun_prop

private theorem height_continuous : Continuous (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)) := by
  fun_prop

private theorem cell_ae : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
    p.2 ∈ ModularGroup.fd :=
  Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)

private theorem profile_ae (N : ℝ) (hN : 0 < N) (u : SpatialSpace) :
    cuspSpatialMultiply N hN u =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      fun p => (cuspWeightProfile N p.2.im:ℂ)*u p := by
  filter_upwards [cuspSpatialMultiply_coe N hN u,cell_ae] with p hp hf
  rw [hp]
  dsimp only [cuspWeightSymbol]
  rw [(modularCuspWeight_germ N p.2 hf).eq_of_nhds]

private theorem limit_nonneg (y : ℝ) (hy : 0 < y) : 0 ≤ cuspWeightLimit y := by
  have h := (cuspWeightProfile_bounds 1 y (by norm_num) hy).1.trans
    (cuspWeightProfile_le_limit 1 y (by norm_num) hy)
  linarith [cuspWeightBase_one_le]

/-- Uniform bounds on the bounded multipliers admit their actual pointwise weighted limit. -/
theorem cuspWeightLimit_memLp_of_uniform (u : SpatialSpace) (C : ℝ)
    (hC : ∀ N : ℝ, ∀ hN : 0 < N, ‖cuspSpatialMultiply N hN u‖ ≤ C) :
    MemLp (fun p : ℝ × UpperHalfPlane => (cuspWeightLimit p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure) := by
  let f (n : ℕ) := cuspSpatialMultiply (n+1) (by positivity) u
  have hrep : ∀ᵐ p ∂radialMeasure.prod D4BMModularCore.measure,
      ∀ n : ℕ, f n p = (cuspWeightProfile (n+1) p.2.im:ℂ)*u p :=
    ae_all_iff.mpr (fun n => profile_ae (n+1) (by positivity) u)
  have ht : ∀ᵐ p ∂radialMeasure.prod D4BMModularCore.measure,
      Tendsto (fun n => f n p) atTop (𝓝 ((cuspWeightLimit p.2.im:ℂ)*u p)) := by
    filter_upwards [hrep] with p hp
    simp_rw [hp]
    exact ((Complex.continuous_ofReal.tendsto _).comp (cuspWeightProfile_tendsto p.2.im)).mul_const _
  have hb : ∀ᶠ n in atTop, eLpNorm (f n) 2 (radialMeasure.prod D4BMModularCore.measure) ≤ ENNReal.ofReal C := by
    apply Eventually.of_forall
    intro n
    rw [← Lp.enorm_def,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC (n+1) (by positivity))
  exact ⟨limit_continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u),
    (Lp.eLpNorm_le_of_ae_tendsto hb (fun n => (Lp.aestronglyMeasurable (f n))) ht).trans_lt ENNReal.ofReal_lt_top⟩

/-- Every bounded source multiplier is dominated by the same unbounded source class. -/
theorem cuspSpatialMultiply_norm_le_limit (N : ℝ) (hN : 0 < N) (F : SpatialSpace)
    (hF : MemLp (fun p : ℝ × UpperHalfPlane => (cuspWeightLimit p.2.im:ℂ)*F p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    ‖cuspSpatialMultiply N hN F‖ ≤ ‖hF.toLp _‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [profile_ae N hN F,hF.coeFn_toLp] with p hp hq
  rw [hp,hq]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hn : 0 ≤ cuspWeightProfile N p.2.im := by
    linarith [(cuspWeightProfile_bounds N p.2.im hN p.2.im_pos).1,cuspWeightBase_one_le]
  rw [abs_of_nonneg hn,abs_of_nonneg (limit_nonneg _ p.2.im_pos)]
  exact mul_le_mul_of_nonneg_right (cuspWeightProfile_le_limit N _ hN p.2.im_pos) (norm_nonneg _)

/-- Weighted source admission propagates through the original causal response in its coercive chamber. -/
theorem jointWaveResponse_cuspWeight_memLp (w : ℂ) (hw : 0 < w.re)
    (hd : 3/2 < w.re) (F : SpatialSpace)
    (hF : MemLp (fun p : ℝ × UpperHalfPlane => (cuspWeightLimit p.2.im:ℂ)*F p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    MemLp (fun p : ℝ × UpperHalfPlane =>
      (cuspWeightLimit p.2.im:ℂ)*jointEmbedding (jointWaveResponse w hw F) p)
      2 (radialMeasure.prod D4BMModularCore.measure) := by
  let C := w.re*‖w‖/((w.re^2+w.im^2)*(w.re^2-9/4))
  have hδ : 0 < w.re^2-(9/4:ℝ) := by nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply cuspWeightLimit_memLp_of_uniform _ (C*‖hF.toLp _‖)
  intro N hN
  exact (jointWaveResponse_cuspWeight_rotated_bound N hN w hw hd F).trans
    (mul_le_mul_of_nonneg_left (cuspSpatialMultiply_norm_le_limit N hN F hF) hC)

/-- The proved unbounded weight controls the literal cusp height in the original measure. -/
theorem height_memLp_of_cuspWeight (u : SpatialSpace)
    (hu : MemLp (fun p : ℝ × UpperHalfPlane => (cuspWeightLimit p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure) := by
  apply hu.of_le_mul (c := 3) (height_continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  filter_upwards with p
  simp only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos p.2.im_pos,abs_of_nonneg (limit_nonneg _ p.2.im_pos)]
  have h := mul_le_mul_of_nonneg_right (cuspWeightLimit_height_le _ p.2.im_pos) (norm_nonneg (u p))
  nlinarith only [h]

/-- Height-admitted sources also lie in the topology used by the squared energy test. -/
theorem cuspWeight_memLp_of_height (F : SpatialSpace)
    (hF : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*F p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    MemLp (fun p : ℝ × UpperHalfPlane => (cuspWeightLimit p.2.im:ℂ)*F p)
      2 (radialMeasure.prod D4BMModularCore.measure) := by
  have he : MemLp (fun p : ℝ × UpperHalfPlane =>
      (cuspWeightCutoff p.2.im:ℂ)*((p.2.im:ℂ)*F p)) 2
      (radialMeasure.prod D4BMModularCore.measure) := by
    apply hF.of_le
    · have hc : Continuous (fun p : ℝ × UpperHalfPlane => (cuspWeightCutoff p.2.im:ℂ)) := by
        unfold cuspWeightCutoff
        fun_prop
      exact hc.aestronglyMeasurable.mul hF.aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      simp only [Complex.norm_real,Real.norm_eq_abs,cuspWeightCutoff,
        abs_of_nonneg (Real.smoothTransition.nonneg (p.2.im-2))]
      exact Real.smoothTransition.le_one _
  apply ((Lp.memLp F).const_mul (cuspWeightBase:ℂ) |>.add he).ae_eq
  filter_upwards with p
  simp only [Pi.add_apply,cuspWeightLimit,Complex.ofReal_add,Complex.ofReal_mul]
  ring

/-- The actual original response inherits height admission from the actual forcing. -/
theorem jointWaveResponse_height_memLp (w : ℂ) (hw : 0 < w.re)
    (hd : 3/2 < w.re) (F : SpatialSpace)
    (hF : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*F p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    MemLp (fun p : ℝ × UpperHalfPlane =>
      (p.2.im:ℂ)*jointEmbedding (jointWaveResponse w hw F) p)
      2 (radialMeasure.prod D4BMModularCore.measure) :=
  height_memLp_of_cuspWeight _ (jointWaveResponse_cuspWeight_memLp w hw hd F
    (cuspWeight_memLp_of_height F hF))

end
end RHTower.D4BMJointWave
