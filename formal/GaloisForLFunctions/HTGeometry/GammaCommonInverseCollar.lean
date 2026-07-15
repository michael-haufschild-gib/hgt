import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# A common analytic inverse collar for the Gamma pole microscopes

The normalized reciprocal-Gamma maps

`Aₙ(X) = -1 / Gamma(-n + sₙ X)`,  `sₙ = (-1)^(n+1) / n!`,

converge locally uniformly to the identity.  Their derivatives therefore converge locally
uniformly to `1`.  On one fixed disk, every sufficiently late `Aₙ` is a quantitative perturbation
of the identity.  Mathlib's quantitative inverse theorem then supplies inverse branches on one
fixed target disk, with a common Lipschitz bound.

The terminal declaration `gammaCommonInverseCollar` is unconditional: its fields are proved from
the Euler Gamma function and contain no assumed analytic input.
-/

namespace GaloisForLFunctions

open Complex Filter Function Metric Set Topology

noncomputable section

/-- The reciprocal-Gamma microscope normalized to converge to the identity. -/
def gammaPoleMicroscope (n : ℕ) (x : ℂ) : ℂ :=
  -reciprocalGammaEntire
    (-(n : ℂ) + reciprocalGammaFactorialScale n * x)

@[simp]
theorem gammaPoleMicroscope_zero (n : ℕ) : gammaPoleMicroscope n 0 = 0 := by
  simp [gammaPoleMicroscope, reciprocalGammaEntire, Complex.Gamma_neg_nat_eq_zero]

theorem differentiable_gammaPoleMicroscope (n : ℕ) :
    Differentiable ℂ (gammaPoleMicroscope n) := by
  unfold gammaPoleMicroscope
  fun_prop

/-- The pole microscopes converge to the identity on every compact set. -/
theorem tendsto_gammaPoleMicroscope_locallyUniformly :
    TendstoLocallyUniformly gammaPoleMicroscope id atTop := by
  have hconst : TendstoLocallyUniformly
      (fun (_n : ℕ) (_x : ℂ) => (-1 : ℂ)) (fun _x : ℂ => -1) atTop :=
    tendstoLocallyUniformly_const_sequence (fun _x : ℂ => (-1 : ℂ))
  have h := hconst.mul₀ tendsto_reciprocalGammaFactorialBlowUp_locallyUniformly
    continuous_const continuous_neg
  simpa [gammaPoleMicroscope, id_eq] using h

/-- The derivatives of the pole microscopes converge locally uniformly to `1`. -/
theorem tendsto_deriv_gammaPoleMicroscope_locallyUniformly :
    TendstoLocallyUniformly
      (fun n => deriv (gammaPoleMicroscope n)) (fun _ : ℂ => 1) atTop := by
  have hloc : TendstoLocallyUniformlyOn gammaPoleMicroscope id atTop Set.univ := by
    simpa [tendstoLocallyUniformlyOn_univ] using
      tendsto_gammaPoleMicroscope_locallyUniformly
  have hder := hloc.deriv
    (Filter.Eventually.of_forall fun n =>
      (differentiable_gammaPoleMicroscope n).differentiableOn)
    isOpen_univ
  simpa [Function.comp_def] using hder

private def gammaPoleIdentity : ℂ ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.refl ℂ ℂ

private def GammaPoleCollarGood (n : ℕ) : Prop :=
  ApproximatesLinearOn (gammaPoleMicroscope n)
      (gammaPoleIdentity : ℂ →L[ℂ] ℂ) (Metric.ball 0 1) (1 / 2 : ℝ≥0) ∧
    ∀ x ∈ Metric.ball (0 : ℂ) 1,
      dist (deriv (gammaPoleMicroscope n) x) 1 < 1 / 2

/-- Eventually every Gamma pole microscope is a `1/2`-perturbation of the identity on the same
unit disk. -/
private theorem eventually_gammaPoleCollarGood :
    ∀ᶠ n : ℕ in atTop, GammaPoleCollarGood n := by
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  have huniform : TendstoUniformlyOn
      (fun n => deriv (gammaPoleMicroscope n)) (fun _ : ℂ => 1) atTop
      (Metric.closedBall 0 1) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp
      tendsto_deriv_gammaPoleMicroscope_locallyUniformly)
      (Metric.closedBall 0 1) hcompact
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  filter_upwards [huniform (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  have hderiv : ∀ x ∈ Metric.ball (0 : ℂ) 1,
      dist (deriv (gammaPoleMicroscope n) x) 1 < 1 / 2 := by
    intro x hx
    exact (dist_comm _ _ ▸ hn x (Metric.ball_subset_closedBall hx))
  refine ⟨?_, hderiv⟩
  apply LipschitzOnWith.approximatesLinearOn
  have hlip : LipschitzOnWith (1 / 2 : ℝ≥0)
      (fun x : ℂ => gammaPoleMicroscope n x - x) (Metric.ball 0 1) := by
    apply convex_ball.lipschitzOnWith_of_nnnorm_deriv_le
    · intro x hx
      exact (differentiable_gammaPoleMicroscope n x).sub differentiableAt_id
    · intro x hx
      have hder : deriv (fun z : ℂ => gammaPoleMicroscope n z - z) x =
          deriv (gammaPoleMicroscope n) x - 1 :=
        ((differentiable_gammaPoleMicroscope n x).hasDerivAt.sub
          (hasDerivAt_id x)).deriv
      rw [hder]
      exact_mod_cast (le_of_lt (by simpa [dist_eq_norm] using hderiv x hx) :
        ‖deriv (gammaPoleMicroscope n) x - 1‖ ≤ (1 / 2 : ℝ))
  simpa [gammaPoleIdentity] using hlip

private theorem gammaPoleApproximation_small :
    Subsingleton ℂ ∨
      (1 / 2 : ℝ≥0) <
        ‖((gammaPoleIdentity).symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ := by
  right
  norm_num [gammaPoleIdentity]

private noncomputable def gammaPolePartialHomeomorph
    (n : ℕ) (h : GammaPoleCollarGood n) : OpenPartialHomeomorph ℂ ℂ :=
  h.1.toOpenPartialHomeomorph (gammaPoleMicroscope n) (Metric.ball 0 1)
    gammaPoleApproximation_small isOpen_ball

private theorem gammaPole_closedBall_target
    (n : ℕ) (h : GammaPoleCollarGood n) :
    Metric.closedBall (0 : ℂ) (1 / 4) ⊆
      (gammaPolePartialHomeomorph n h).target := by
  have ht := h.1.closedBall_subset_target gammaPoleApproximation_small isOpen_ball
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show Metric.closedBall (0 : ℂ) (1 / 2) ⊆ Metric.ball 0 1 by
      exact Metric.closedBall_subset_ball (by norm_num))
  simpa [gammaPolePartialHomeomorph, gammaPoleIdentity,
    gammaPoleMicroscope_zero] using ht

/-- Unconditional common-collar data for all sufficiently late negative Gamma poles. -/
structure GammaCommonInverseCollar where
  /-- All pole labels at or beyond this threshold share the collar. -/
  threshold : ℕ
  threshold_ge_five : 5 ≤ threshold
  /-- The selected analytic inverse branches of the normalized pole microscopes. -/
  branch : ℕ → ℂ → ℂ
  branch_maps : ∀ {n : ℕ}, threshold ≤ n →
    MapsTo (branch n) (Metric.closedBall (0 : ℂ) (1 / 4)) (Metric.ball 0 1)
  rightInverse : ∀ {n : ℕ}, threshold ≤ n →
    Set.RightInvOn (branch n) (gammaPoleMicroscope n)
      (Metric.closedBall (0 : ℂ) (1 / 4))
  leftInverse : ∀ {n : ℕ}, threshold ≤ n →
    Set.LeftInvOn (branch n) (gammaPoleMicroscope n) (Metric.ball (0 : ℂ) 1)
  lipschitzOn : ∀ {n : ℕ}, threshold ≤ n →
    LipschitzOnWith 2 (branch n) (Metric.closedBall (0 : ℂ) (1 / 4))
  analyticOn : ∀ {n : ℕ}, threshold ≤ n →
    AnalyticOnNhd ℂ (branch n) (Metric.ball (0 : ℂ) (1 / 4))

private theorem exists_gammaCommonInverseCollar : Nonempty GammaCommonInverseCollar := by
  rw [eventually_atTop] at eventually_gammaPoleCollarGood
  obtain ⟨N₀, hN₀⟩ := eventually_gammaPoleCollarGood
  let N := max N₀ 5
  have hgood : ∀ n, N ≤ n → GammaPoleCollarGood n := by
    intro n hn
    exact hN₀ n ((le_max_left N₀ 5).trans hn)
  let B : ℕ → ℂ → ℂ := fun n =>
    if hn : N ≤ n then (gammaPolePartialHomeomorph n (hgood n hn)).symm else 0
  refine ⟨{
    threshold := N
    threshold_ge_five := le_max_right N₀ 5
    branch := B
    branch_maps := ?_
    rightInverse := ?_
    leftInverse := ?_
    lipschitzOn := ?_
    analyticOn := ?_ }⟩
  · intro n hn t ht
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    exact (gammaPolePartialHomeomorph n (hgood n hn)).symm.map_source
      (gammaPole_closedBall_target n (hgood n hn) ht)
  · intro n hn t ht
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    have htarget := gammaPole_closedBall_target n (hgood n hn) ht
    simpa [gammaPolePartialHomeomorph] using
      (gammaPolePartialHomeomorph n (hgood n hn)).apply_symm_apply htarget
  · intro n hn x hx
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    have hsource : x ∈ (gammaPolePartialHomeomorph n (hgood n hn)).source := by
      simpa [gammaPolePartialHomeomorph] using hx
    simpa [gammaPolePartialHomeomorph] using
      (gammaPolePartialHomeomorph n (hgood n hn)).symm_apply_apply hsource
  · intro n hn
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    let P := gammaPolePartialHomeomorph n (hgood n hn)
    have hxt : x ∈ P.target := gammaPole_closedBall_target n (hgood n hn) hx
    have hyt : y ∈ P.target := gammaPole_closedBall_target n (hgood n hn) hy
    have hanti := (hgood n hn).1.antilipschitz gammaPoleApproximation_small
    have hdist := hanti.le_mul_dist
      ⟨P.symm x, P.symm.map_target hxt⟩ ⟨P.symm y, P.symm.map_target hyt⟩
    simpa [P, gammaPolePartialHomeomorph] using hdist
  · intro n hn t ht
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    let P := gammaPolePartialHomeomorph n (hgood n hn)
    have htarget : t ∈ P.target :=
      gammaPole_closedBall_target n (hgood n hn) (Metric.ball_subset_closedBall ht)
    have hsource : P.symm t ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [P, gammaPolePartialHomeomorph] using P.symm.map_source htarget
    have hderiv_ne : deriv (gammaPoleMicroscope n) (P.symm t) ≠ 0 := by
      intro hz
      have hlt := (hgood n hn).2 (P.symm t) hsource
      rw [hz] at hlt
      norm_num [dist_eq_norm] at hlt
    let i : ℂ ≃L[ℂ] ℂ :=
      ContinuousLinearEquiv.unitsEquivAut ℂ
        (Units.mk0 (deriv (gammaPoleMicroscope n) (P.symm t)) hderiv_ne)
    have han : AnalyticAt ℂ P (P.symm t) := by
      simpa [P, gammaPolePartialHomeomorph] using
        (differentiable_gammaPoleMicroscope n).analyticAt (P.symm t)
    have hfder : fderiv ℂ P (P.symm t) = i := by
      ext z
      simp [P, gammaPolePartialHomeomorph, i, fderiv_eq_deriv_mul,
        mul_comm]
    exact P.analyticAt_symm htarget han hfder

/-- The selected common inverse collar, constructed unconditionally from Gamma. -/
noncomputable def gammaCommonInverseCollar : GammaCommonInverseCollar :=
  Classical.choice exists_gammaCommonInverseCollar

theorem gammaCommonInverseCollar_threshold_ge_five :
    5 ≤ gammaCommonInverseCollar.threshold :=
  gammaCommonInverseCollar.threshold_ge_five

theorem gammaCommonInverseCollar_rightInverse
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (1 / 4)) :
    gammaPoleMicroscope n (gammaCommonInverseCollar.branch n t) = t :=
  gammaCommonInverseCollar.rightInverse hn ht

theorem gammaCommonInverseCollar_branch_mem
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (1 / 4)) :
    gammaCommonInverseCollar.branch n t ∈ Metric.ball (0 : ℂ) 1 :=
  gammaCommonInverseCollar.branch_maps hn ht

end

end GaloisForLFunctions
