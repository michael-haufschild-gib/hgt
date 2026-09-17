import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleGreen
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Joint regularity of the literal full theta-circle response.

The result is joint smoothness in signed radius, horizontal coordinate, and
logarithmic height.  It is the actual circle integral, not a mode or trace
replacement.  No global growth, transport interchange, cap limit, current, or
contact comparison is asserted here.
-/

namespace RHTower.D4BMFullAngularCircleJointJets

open Set Filter Topology MeasureTheory
open scoped ContDiff
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMNativeCircle D4BMCausalKernel
open D4BMFullAngularCircle

noncomputable section
set_option autoImplicit false

private def circleSource (q : XiZeroCopy) (branch : Bool) (d theta X k : ℝ) : ℂ :=
  fullAngularField q branch (logCircle d theta X k)

private def partialMap {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E × P → G) (p : E × P) : E →L[ℝ] G :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E P)

private theorem partialMap_smooth {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × P → G} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (partialMap f) := by
  have hh : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by exact_mod_cast hf
  exact (hh.fderiv_right le_rfl).clm_comp contDiff_const

private theorem partialMap_derivative {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × P → G} (hf : ContDiff ℝ 1 f) (x : E) (p : P) :
    HasFDerivAt (fun y => f (y, p)) (partialMap f (x, p)) x :=
  ((hf.differentiable (by norm_num) (x, p)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const p x))

private theorem compactIntegralInfty {E P K : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    [T2Space K] {μ : Measure K} [IsLocallyFiniteMeasure μ]
    (S : Set K) (hS : IsCompact S) (gamma : K → P) (hgamma : Continuous gamma)
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : E × P → G} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => ∫ k in S, f (y, gamma k) ∂μ) := by
  have first (n : ℕ) : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
      [CompleteSpace H] {g : E × P → H}, ContDiff ℝ n g →
      ContDiff ℝ n (fun y => ∫ k in S, g (y, gamma k) ∂μ) := by
    induction n with
    | zero =>
      intro H _ _ _ g hg
      apply contDiff_zero.mpr
      apply continuous_parametric_integral_of_continuous _ hS
      exact hg.continuous.comp (continuous_fst.prodMk (hgamma.comp continuous_snd))
    | succ n ih =>
      intro H _ _ _ g hg
      have hg1 : ContDiff ℝ 1 g := hg.of_le (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨(fun x => ∫ k in S, partialMap g (x, gamma k) ∂μ), ?_, ?_⟩
      · exact ih (partialMap_smooth (n := n) hg)
      · intro x
        have hc : Continuous (fun q : E × K => g (q.1, gamma q.2)) :=
          hg.continuous.comp (continuous_fst.prodMk (hgamma.comp continuous_snd))
        have hd : Continuous (fun q : E × K => partialMap g (q.1, gamma q.2)) :=
          (partialMap_smooth (n := 0) hg1).continuous.comp
            (continuous_fst.prodMk (hgamma.comp continuous_snd))
        obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod hS).exists_bound_of_continuousOn
          hd.continuousOn
        apply hasFDerivAt_integral_of_dominated_of_fderiv_le
          (s := Metric.closedBall x 1) (bound := fun _ => C)
          (Metric.closedBall_mem_nhds x (by norm_num))
        · exact Eventually.of_forall fun y =>
            ((hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).restrict
        · exact ((hc.comp (continuous_const.prodMk continuous_id)).continuousOn).integrableOn_compact hS
        · exact ((hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).restrict
        · filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with k hk
          intro y hy
          exact hC (y, k) ⟨hy, hk⟩
        · exact integrableOn_const hS.measure_ne_top
        · exact Eventually.of_forall fun k y _ => partialMap_derivative hg1 y (gamma k)
  exact contDiff_infty.mpr fun n => first n (contDiff_infty.mp hf n)

private def jointMean (q : XiZeroCopy) (branch : Bool) (p : Fin 3 → ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) * ∫ theta in Icc 0 (2 * Real.pi),
    circleSource q branch (p 0) theta (p 1) (p 2)

private theorem jointIntegrand_smooth (q : XiZeroCopy) (branch : Bool) :
    ContDiff ℝ ∞ (fun p : (Fin 3 → ℝ) × ℝ =>
      circleSource q branch (p.1 0) p.2 (p.1 1) (p.1 2)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle (p.1 0) p.2 (p.1 1) (p.1 2) 1 := by
    dsimp [logCircle, circle, height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hF := fullAngularField_smooth q branch
    (logCircle (p.1 0) p.2 (p.1 1) (p.1 2)) hp
  apply hF.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle, circle, offset, height, denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem jointMean_smooth (q : XiZeroCopy) (branch : Bool) :
    ContDiff ℝ ∞ (jointMean q branch) := by
  unfold jointMean
  exact (compactIntegralInfty (E := Fin 3 → ℝ) (P := ℝ) (K := ℝ)
    (μ := volume) (Icc 0 (2 * Real.pi)) isCompact_Icc id continuous_id
    (jointIntegrand_smooth q branch)).const_mul (1 / (2 * Real.pi : ℂ))

private theorem jointMean_eq_angularMean (q : XiZeroCopy) (branch : Bool)
    (p : Fin 3 → ℝ) :
    jointMean q branch p = angularMean q branch (p 0) (p 1) (p 2) := by
  change (1 / (2 * Real.pi : ℂ)) * ∫ theta in Icc 0 (2 * Real.pi),
      fullAngularField q branch (logCircle (p 0) theta (p 1) (p 2)) = _
  rw [angularMean, D4BMNativeCircle.average, integral_Icc_eq_integral_Ioc]
  rfl

/-- Joint smoothness of literal full circle response in radius, horizontal coordinate,
and logarithmic height. -/
theorem angularMean_joint_smooth (q : XiZeroCopy) (branch : Bool) :
    ContDiff ℝ ∞ (fun p : Fin 3 → ℝ => angularMean q branch (p 0) (p 1) (p 2)) := by
  have he : (fun p : Fin 3 → ℝ => angularMean q branch (p 0) (p 1) (p 2)) =
      jointMean q branch := by
    funext p
    exact (jointMean_eq_angularMean q branch p).symm
  rw [he]
  exact jointMean_smooth q branch

/-- Literal full circle response in the physical `(X,Y)` chart. -/
def physicalMean (q : XiZeroCopy) (branch : Bool) (d : ℝ) (z : Point) : ℂ :=
  angularMean q branch d (z 0) (Real.log (z 1))

/-- The physical-height lift has an actual all-order local jet at every positive height. -/
theorem physicalMean_contDiffAt (q : XiZeroCopy) (branch : Bool) (d : ℝ)
    (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (physicalMean q branch d) z := by
  have hlog : ContDiffAt ℝ ∞ (fun w : Point => Real.log (w 1)) z :=
    (Real.contDiffAt_log.mpr hz.ne').comp z (contDiff_apply ℝ ℝ 1).contDiffAt
  have hmap : ContDiffAt ℝ ∞ (fun w : Point => ![d, w 0, Real.log (w 1)]) z := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact contDiffAt_const
    · simpa using (contDiff_apply ℝ ℝ 0).contDiffAt
    · simpa using hlog
  simpa only [physicalMean, Function.comp_def] using
    (angularMean_joint_smooth q branch).contDiffAt.comp z hmap

end
end RHTower.D4BMFullAngularCircleJointJets
