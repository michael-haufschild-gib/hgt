import GaloisForLFunctions.RHTower.PrimeLogCongruenceLaplaceSynthesis
import GaloisForLFunctions.HTGeometry.PaperDiagonalStrongConvergence

/-!
# Prime damping and the critical Laplace graph

Every positive prime damping has a Hilbert–Schmidt synthesized output.
Density of finite prime packets then admits every damped square-summable
source to the original closed critical graph.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

def primeLogLaplaceDampingWeight (h : ℝ≥0) (p : Nat.Primes) : ℂ :=
  ((p : ℝ) ^ (-(h : ℝ)) : ℝ)

theorem norm_primeLogLaplaceDampingWeight_le (h : ℝ≥0) (p : Nat.Primes) :
    ‖primeLogLaplaceDampingWeight h p‖ ≤ 1 := by
  rw [primeLogLaplaceDampingWeight, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast p.property.one_lt.le
  · exact neg_nonpos.mpr h.coe_nonneg

def primeLogLaplaceDamping (h : ℝ≥0) : primeLogCriticalSourceL2 →L[ℂ] primeLogCriticalSourceL2 :=
  lpDiagonalCLM (primeLogLaplaceDampingWeight h) zero_le_one
    (norm_primeLogLaplaceDampingWeight_le h)

theorem primeLogLaplaceDamping_apply (h : ℝ≥0) (a : primeLogCriticalSourceL2) (p : Nat.Primes) :
    primeLogLaplaceDamping h a p = primeLogLaplaceDampingWeight h p * a p := rfl

theorem primeLogLaplaceDamping_zero (a : primeLogCriticalSourceL2) :
    primeLogLaplaceDamping 0 a = a := by
  apply lp.ext
  funext p
  simp [primeLogLaplaceDamping_apply, primeLogLaplaceDampingWeight]

theorem continuous_primeLogLaplaceDamping (a : primeLogCriticalSourceL2) :
    Continuous (fun h : ℝ≥0 => primeLogLaplaceDamping h a) := by
  apply continuous_iff_seqContinuous.mpr
  intro r s hrs
  apply paperLpDiagonal_strong_tendsto
    (fun n => primeLogLaplaceDampingWeight (r n)) (primeLogLaplaceDampingWeight s)
    1 zero_le_one (fun n => norm_primeLogLaplaceDampingWeight_le (r n))
    (norm_primeLogLaplaceDampingWeight_le s) _ a
  intro p
  have hp : (p : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast p.property.pos)
  have hc : Continuous (fun h : ℝ≥0 => primeLogLaplaceDampingWeight h p) :=
    Complex.continuous_ofReal.comp
      ((Real.continuous_const_rpow hp).comp NNReal.continuous_coe.neg)
  exact (hc.tendsto s).comp hrs

theorem tendsto_primeLogLaplaceDamping_zero (a : primeLogCriticalSourceL2) :
    Tendsto (fun h : ℝ≥0 => primeLogLaplaceDamping h a) (𝓝 0) (𝓝 a) := by
  simpa only [primeLogLaplaceDamping_zero] using (continuous_primeLogLaplaceDamping a).tendsto 0

theorem primeLogLaplaceDamping_single (h : ℝ≥0) (p : Nat.Primes) :
    primeLogLaplaceDamping h (lp.single 2 p (1 : ℂ)) =
      primeLogLaplaceDampingWeight h p • lp.single 2 p (1 : ℂ) := by
  rw [primeLogLaplaceDamping, lpDiagonalCLM_single, ← lp.single_smul]
  simp

def primeLogLaplaceDampedSynthesis (h : ℝ≥0) (hh : 0 < h) :
    primeLogCriticalSourceL2 →L[ℂ] primeLogCriticalHalfLineL2 :=
  ((Real.sqrt (8 * (h : ℝ)) : ℂ)⁻¹) •
    primeLogCongruenceLaplaceSynthesisOp (d := h) (u := 0) hh
      ((summable_primeLogCongruenceWeight_iff hh (le_refl (0 : ℝ))).2 hh)

theorem primeLogLaplaceDampedSynthesis_single (h : ℝ≥0) (hh : 0 < h) (p : Nat.Primes) :
    primeLogLaplaceDampedSynthesis h hh (lp.single 2 p (1 : ℂ)) =
      primeLogLaplaceDampingWeight h p • primeLogCriticalLaplaceFeatureL2 p := by
  have hs : (Real.sqrt (8 * (h : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < 8 * (h : ℝ))))
  simp only [primeLogLaplaceDampedSynthesis, smul_apply,
    primeLogCongruenceLaplaceSynthesisOp_single, primeLogCongruenceLaplaceColumn,
    smul_smul, zero_sub, Complex.ofReal_mul, primeLogLaplaceDampingWeight]
  rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem primeLogLaplaceDampedSynthesis_isHilbertSchmidt (h : ℝ≥0) (hh : 0 < h) :
    ContinuousLinearMap.IsHilbertSchmidt (primeLogLaplaceDampedSynthesis h hh) := by
  have hHS : ContinuousLinearMap.IsHilbertSchmidt
      (primeLogCongruenceLaplaceSynthesisOp (d := h) (u := 0) hh
        ((summable_primeLogCongruenceWeight_iff hh (le_refl (0 : ℝ))).2 hh)) := by
    apply ContinuousLinearMap.isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis Nat.Primes)
    apply ((summable_primeLogCongruenceWeight_iff (d := (h : ℝ)) (u := 0)
      hh (le_refl (0 : ℝ))).2 hh).congr
    intro p
    rw [HilbertSchmidt.lpBasis_apply, primeLogCongruenceLaplaceSynthesisOp_single]
    exact (norm_sq_primeLogCongruenceLaplaceColumn (d := (h : ℝ)) hh 0 p).symm
  exact hHS.smul _

theorem primeLogLaplaceDamped_pair_mem_closureGraph
    (h : ℝ≥0) (hh : 0 < h) (a : primeLogCriticalSourceL2) :
    (primeLogLaplaceDamping h a, primeLogLaplaceDampedSynthesis h hh a) ∈
      primeLogCriticalLaplaceSynthesis.closure.graph := by
  let G := primeLogCriticalLaplaceSynthesis.closure.graph
  have hb (p : Nat.Primes) :
      ((lp.single 2 p (1 : ℂ) : primeLogCriticalSourceL2),
        primeLogCriticalLaplaceFeatureL2 p) ∈ G := by
    change ((lp.single 2 p (1 : ℂ) : primeLogCriticalSourceL2),
      primeLogCriticalLaplaceFeatureL2 p) ∈ primeLogCriticalLaplaceSynthesis.closure.graph
    rw [← primeLogCriticalLaplaceSynthesis_isClosable.graph_closure_eq_closure_graph]
    apply primeLogCriticalLaplaceSynthesis.graph.le_topologicalClosure
    have hm : HTGeometry.ConstraintMotiveRelativity.srcEmb (Finsupp.single p (1 : ℂ)) ∈
        primeLogCriticalLaplaceSynthesis.domain := ⟨_, rfl⟩
    refine primeLogCriticalLaplaceSynthesis.mem_graph_iff.mpr ⟨⟨_, hm⟩, ?_, ?_⟩
    · simp [HTGeometry.ConstraintMotiveRelativity.srcEmb_single,
        HTGeometry.ConstraintMotiveRelativity.srcBasis]
    · rw [primeLogCriticalLaplaceSynthesis_apply]
      simp [primeLogCriticalLaplaceMass]
  have hc : IsClosed {a : primeLogCriticalSourceL2 |
      (primeLogLaplaceDamping h a, primeLogLaplaceDampedSynthesis h hh a) ∈ G} :=
    primeLogCriticalLaplaceSynthesis_closure_isClosed.preimage
      ((primeLogLaplaceDamping h).continuous.prodMk (primeLogLaplaceDampedSynthesis h hh).continuous)
  apply closure_minimal (t := {a : primeLogCriticalSourceL2 |
      (primeLogLaplaceDamping h a, primeLogLaplaceDampedSynthesis h hh a) ∈ G}) ?_ hc
    (dense_primeLogCriticalLaplaceSynthesis_domain a)
  rintro _ ⟨l, rfl⟩
  change (primeLogLaplaceDamping h (HTGeometry.ConstraintMotiveRelativity.srcEmb l),
    primeLogLaplaceDampedSynthesis h hh (HTGeometry.ConstraintMotiveRelativity.srcEmb l)) ∈ G
  induction l using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    exact G.zero_mem
  | add l m hl hm =>
    simpa only [map_add, Prod.mk_add_mk] using G.add_mem hl hm
  | single p c =>
    simp only [HTGeometry.ConstraintMotiveRelativity.srcEmb_single,
      HTGeometry.ConstraintMotiveRelativity.srcBasis, map_smul,
      primeLogLaplaceDamping_single, primeLogLaplaceDampedSynthesis_single]
    exact G.smul_mem c (G.smul_mem (primeLogLaplaceDampingWeight h p) (hb p))

end RHTower
