import GaloisForLFunctions.HTGeometry.ClockParametricIntegralHolomorphy
import GaloisForLFunctions.RHTower.Sieve.InghamGabrielPoleClearedBound
import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielIntegralInterpolation

/-!
# Analyticity of the concrete Gabriel scalar family

This module differentiates the coefficient-three scalar integral under its compact height integral.
The delicate point is joint continuity of the dual power when its center datum vanishes; that seam
is supplied by `continuousAt_inghamUniformGabrielDualPower_pair`.
-/

namespace RHTower.Sieve

open Set Complex Metric MeasureTheory intervalIntegral

noncomputable section

private theorem differentiableOn_intervalIntegral_of_holomorphic_on_open
    {a b : ℝ} {U : Set ℂ} (hU : IsOpen U) {F : ℝ → ℂ → ℂ}
    (hFc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (univ ×ˢ U))
    (hFd : ∀ t : ℝ, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun w => ∫ t in a..b, F t w) U := by
  intro z hz
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hU z hz
  let R : ℝ := ε / 2
  let r : ℝ := ε / 4
  have hRpos : 0 < R := by dsimp only [R]; linarith
  have hrpos : 0 < r := by dsimp only [r]; linarith
  have hbig : closedBall z R ⊆ U := by
    intro w hw
    apply hεsub
    rw [mem_ball]
    exact (mem_closedBall.mp hw).trans_lt (by dsimp only [R]; linarith)
  have hslice : ∀ t : ℝ, ContinuousOn (F t) U := fun t =>
    hFc.comp ((continuous_const.prodMk continuous_id).continuousOn)
      fun ζ hζ => ⟨mem_univ _, hζ⟩
  have hfixed : ∀ w ∈ U, Continuous fun t : ℝ => F t w := fun w hw =>
    hFc.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hw⟩
  obtain ⟨M, hM⟩ := ((isCompact_uIcc (a := a) (b := b)).prod
    (isCompact_closedBall z R)).exists_bound_of_continuousOn
      (hFc.mono fun q hq => ⟨mem_univ _, hbig hq.2⟩)
  have hnear : ∀ w ∈ ball z r, closedBall w r ⊆ closedBall z R := by
    intro w hw
    refine closedBall_subset_closedBall' ?_
    have hdist : dist w z < r := mem_ball.mp hw
    dsimp only [r] at hdist
    dsimp only [R, r]
    linarith
  have hdiffAt : ∀ (t : ℝ), ∀ ζ ∈ closedBall z R,
      DifferentiableAt ℂ (F t) ζ := by
    intro t ζ hζ
    exact (hFd t).differentiableAt (hU.mem_nhds (hbig hζ))
  have hbound : ∀ (t : ℝ), t ∈ uIcc a b → ∀ w ∈ ball z r,
      ‖deriv (F t) w‖ ≤ M / r := by
    intro t ht w hw
    have hsub := hnear w hw
    have hdc : DiffContOnCl ℂ (F t) (ball w r) := by
      refine ⟨fun ζ hζ =>
          (hdiffAt t ζ (hsub (ball_subset_closedBall hζ))).differentiableWithinAt, ?_⟩
      rw [closure_ball w hrpos.ne']
      exact (hslice t).mono fun ζ hζ => hbig (hsub hζ)
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdc fun ζ hζ => ?_
    exact hM (t, ζ) ⟨ht, hsub (sphere_subset_closedBall hζ)⟩
  have hderivCont : Continuous fun t : ℝ => deriv (F t) z := by
    refine GaloisForLFunctions.HTGeometry.continuous_deriv_parametric_on
      hRpos hFc hbig fun t ζ hζ => ?_
    exact hdiffAt t ζ (ball_subset_closedBall hζ)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball z r) (bound := fun _ => M / r) (F := fun w t => F t w)
    (F' := fun w t => deriv (F t) w) (ball_mem_nhds z hrpos)
    ?_ ?_ ?_ ?_ ?_ ?_).2.differentiableAt.differentiableWithinAt
  · refine Filter.eventually_of_mem (ball_mem_nhds z hrpos) fun w hw => ?_
    exact (hfixed w (hbig (hnear w hw (mem_closedBall_self hrpos.le)))).aestronglyMeasurable
  · exact (hfixed z hz).intervalIntegrable a b
  · exact hderivCont.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht w hw => ?_
    exact hbound t (uIoc_subset_uIcc ht) w hw
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t _ w hw => ?_
    exact (hdiffAt t w (hnear w hw (mem_closedBall_self hrpos.le))).hasDerivAt

private def inghamUniformGabrielSafeHalfPlane : Set ℂ := {z | 1 / 4 < z.re}

private theorem isOpen_inghamUniformGabrielSafeHalfPlane : IsOpen inghamUniformGabrielSafeHalfPlane := by
  exact isOpen_lt continuous_const continuous_re

private def inghamUniformGabrielScalarIntegrand
    (sigma : ℝ) (X : ℕ) (kappa T : ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  inghamGabrielPoleClearedError X kappa T (z + (t : ℂ) * I) *
    inghamUniformGabrielDualPower sigma
      (inghamUniformGabrielDualSeed sigma
        (inghamGabrielPoleClearedError X kappa T
          ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z

private theorem continuous_inghamUniformGabrielCenterDualDatum
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) (kappa T : ℝ) :
    Continuous fun t : ℝ => inghamUniformGabrielDualSeed sigma
      (inghamGabrielPoleClearedError X kappa T
        ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)) := by
  apply (continuous_inghamUniformGabrielDualSeed hsigma0 hsigma1).comp
  rw [continuous_iff_continuousAt]
  intro t
  have hpoint : (inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hc := inghamUniformGabrielCenter_ge_half hsigma0
    simp at hre
    linarith
  exact ContinuousAt.comp
    (f := fun u : ℝ => (inghamUniformGabrielCenter sigma : ℂ) + (u : ℂ) * I)
    (analyticAt_inghamGabrielPoleClearedError X kappa T hpoint).continuousAt
    (by fun_prop)

private theorem continuousOn_inghamUniformGabrielScalarIntegrand
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) (kappa T : ℝ) :
    ContinuousOn (fun q : ℝ × ℂ =>
      inghamUniformGabrielScalarIntegrand sigma X kappa T q.1 q.2)
      (univ ×ˢ inghamUniformGabrielSafeHalfPlane) := by
  intro q hq
  have hshiftPoint : q.2 + (q.1 : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hsafe : 1 / 4 < q.2.re := hq.2
    simp at hre
    linarith
  have hfield : ContinuousAt (fun p : ℝ × ℂ =>
      inghamGabrielPoleClearedError X kappa T (p.2 + (p.1 : ℂ) * I)) q :=
    ContinuousAt.comp
      (f := fun p : ℝ × ℂ => p.2 + (p.1 : ℂ) * I)
      (analyticAt_inghamGabrielPoleClearedError X kappa T hshiftPoint).continuousAt
      (by fun_prop)
  let datum : ℝ → ℂ := fun t => inghamUniformGabrielDualSeed sigma
    (inghamGabrielPoleClearedError X kappa T
      ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))
  have hdatum : Continuous datum :=
    continuous_inghamUniformGabrielCenterDualDatum
      hsigma0 hsigma1 X kappa T
  have hexp : 0 < (inghamUniformGabrielDualExponent sigma q.2).re := by
    have hsafe : 1 / 4 < q.2.re := hq.2
    rw [inghamUniformGabrielDualExponent_re]
    apply div_pos
    · unfold inghamUniformGabrielRightEdge
      nlinarith
    · exact uniformGabrielSeedDenominator_pos hsigma0
  have hpair := continuousAt_inghamUniformGabrielDualPower_pair
    (sigma := sigma) (w := datum q.1) (z := q.2) hexp
  have hdual : ContinuousAt (fun p : ℝ × ℂ =>
      inghamUniformGabrielDualPower sigma (datum p.1) p.2) q :=
    ContinuousAt.comp (f := fun p : ℝ × ℂ => (datum p.1, p.2)) hpair
      ((hdatum.comp continuous_fst).continuousAt.prodMk
        continuous_snd.continuousAt)
  exact (hfield.mul hdual).continuousWithinAt

private theorem differentiableOn_inghamUniformGabrielScalarIntegrand
    (sigma : ℝ) (X : ℕ) (kappa T : ℝ) (t : ℝ) :
    DifferentiableOn ℂ
      (inghamUniformGabrielScalarIntegrand sigma X kappa T t)
      inghamUniformGabrielSafeHalfPlane := by
  intro z hz
  have hshiftPoint : z + (t : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    have hzpos : 0 < z.re := lt_trans (by norm_num) hz
    exact hzpos.ne' hre
  have hshiftDiff : DifferentiableAt ℂ (fun w : ℂ => w + (t : ℂ) * I) z := by
    fun_prop
  have hfield : DifferentiableAt ℂ (fun w : ℂ =>
      inghamGabrielPoleClearedError X kappa T (w + (t : ℂ) * I)) z :=
    DifferentiableAt.fun_comp' (x := z)
      (f := fun w : ℂ => w + (t : ℂ) * I)
      (g := inghamGabrielPoleClearedError X kappa T)
      (analyticAt_inghamGabrielPoleClearedError X kappa T hshiftPoint).differentiableAt
      hshiftDiff
  have hdual : DifferentiableAt ℂ (fun w : ℂ =>
      inghamUniformGabrielDualPower sigma
        (inghamUniformGabrielDualSeed sigma
          (inghamGabrielPoleClearedError X kappa T
            ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) w) z :=
    (analyticAt_inghamUniformGabrielDualPower sigma _ z).differentiableAt
  exact (hfield.mul hdual).differentiableWithinAt

private theorem differentiableOn_inghamUniformGabrielScalarFamily_poleCleared
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) {kappa T : ℝ} (hT : 0 ≤ T) :
    DifferentiableOn ℂ
      (inghamUniformGabrielScalarFamily sigma
        (inghamGabrielPoleClearedError X kappa T) T)
      inghamUniformGabrielSafeHalfPlane := by
  have hdiff := differentiableOn_intervalIntegral_of_holomorphic_on_open
    isOpen_inghamUniformGabrielSafeHalfPlane
    (continuousOn_inghamUniformGabrielScalarIntegrand
      hsigma0 hsigma1 X kappa T)
    (differentiableOn_inghamUniformGabrielScalarIntegrand sigma X kappa T)
    (a := -T) (b := T)
  have heq : (fun z => inghamUniformGabrielScalarFamily sigma
      (inghamGabrielPoleClearedError X kappa T) T z) =
      fun z => ∫ t in (-T)..T,
        inghamUniformGabrielScalarIntegrand sigma X kappa T t z := by
    funext z
    rw [inghamUniformGabrielScalarFamily,
      intervalIntegral.integral_of_le (by linarith),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  change DifferentiableOn ℂ (fun z => inghamUniformGabrielScalarFamily sigma
    (inghamGabrielPoleClearedError X kappa T) T z) inghamUniformGabrielSafeHalfPlane
  rw [heq]
  exact hdiff

/-- The actual Gaussian pole-cleared coefficient-three scalar family has all strip regularity
required by Hadamard three-lines. -/
theorem diffContOnCl_inghamUniformGabrielScalarFamily_poleCleared
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) {kappa T : ℝ} (hT : 0 ≤ T) :
    DiffContOnCl ℂ
      (inghamUniformGabrielScalarFamily sigma
        (inghamGabrielPoleClearedError X kappa T) T)
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)) := by
  have hdiff := differentiableOn_inghamUniformGabrielScalarFamily_poleCleared
    hsigma0 hsigma1 X (kappa := kappa) (T := T) hT
  have hclosure : closure (Complex.HadamardThreeLines.verticalStrip
      (1 / 2) (inghamUniformGabrielRightEdge sigma)) ⊆
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma) := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.1.le, hz.2.le⟩
    · exact isClosed_Icc.preimage continuous_re
  constructor
  · intro z hz
    exact (hdiff z (by
      change 1 / 4 < z.re
      linarith [hz.1])).mono (by
        intro w hw
        change 1 / 4 < w.re
        linarith [hw.1])
  · intro z hz
    have hzclosed := hclosure hz
    have hzsafe : z ∈ inghamUniformGabrielSafeHalfPlane := by
      change 1 / 4 < z.re
      linarith [hzclosed.1]
    exact (hdiff.differentiableAt
      (isOpen_inghamUniformGabrielSafeHalfPlane.mem_nhds hzsafe)).continuousAt.continuousWithinAt

end

end RHTower.Sieve
