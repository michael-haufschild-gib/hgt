import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthFifthLogCooling

/-!
# C5 likelihood-homotopy seam ratio orientation

This module closes the exact source invariant in the first nonzero seam coefficient of the
structural-tail C5 likelihood homotopy.  Write `Fₖ` for the `k`th source jet of the literal
higher-theta likelihood log partition.  Then, for `x ≥ 0` and first-atom scale `A(x) ≥ 6`,

`F₂ F₅ - 2 F₃ F₄ > 0`.

Equivalently, the projective fourth-likelihood curvature `F₄ / F₂²` has strictly positive
source derivative and is strictly increasing after any structural-tail entrance point.

The proof is division-free at the sign gate.  The corpus lower cooling law
`3 A F₂ < -F₃` is multiplied by positive `F₄`; the fourth/fifth cooling law
`-F₅ < 6 A F₄` is multiplied by positive `F₂`; their strict reserves add exactly to the
displayed invariant.  No generic cumulant Cauchy inequality is used: the corresponding
pointwise fourth/sixth route is false for this source.

RH chain: positive homotopy seam invariant -> positive first nonzero `M'''` seam coefficient ->
convex likelihood lift -> literal full-theta structural-tail C5 compensation -> fixed-action
direct-J orientation -> reflection-odd rank-four/Ptolemy wall -> CLG/TTF or Weil positivity -> RH.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Normalized fourth likelihood source jet selected by the first nonzero C5 homotopy seam. -/
def thetaCuspLikelihoodFourthSecondSquaredRatio (x : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceLogPartitionJetFour x /
    thetaCuspLikelihoodSourceLogPartitionJetTwo x ^ 2

/-- Exact strict source invariant in the first nonzero C5 likelihood-homotopy seam coefficient. -/
theorem thetaCuspLikelihoodHomotopyC5SeamInvariant_pos
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspLikelihoodSourceLogPartitionJetTwo x *
          thetaCuspLikelihoodSourceLogPartitionJetFive x -
        2 * thetaCuspLikelihoodSourceLogPartitionJetThree x *
          thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let F₂ := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let F₃ := thetaCuspLikelihoodSourceLogPartitionJetThree x
  let F₄ := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let F₅ := thetaCuspLikelihoodSourceLogPartitionJetFive x
  have hF₂ : 0 < F₂ := by
    simpa only [F₂] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hF₄ : 0 < F₄ := by
    simpa only [F₄] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx
  have hlow : 3 * A * F₂ < -F₃ := by
    simpa only [A, F₂, F₃] using
      three_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
        x hx hscale
  have hupp : -F₅ < 6 * A * F₄ := by
    simpa only [A, F₄, F₅] using
      neg_thetaCuspLikelihoodSourceLogPartitionJetFive_lt_six_mul_scale_mul_jetFour
        hx hscale
  have hlowMul : (3 * A * F₂) * F₄ < (-F₃) * F₄ :=
    mul_lt_mul_of_pos_right hlow hF₄
  have huppMul : (-F₅) * F₂ < (6 * A * F₄) * F₂ :=
    mul_lt_mul_of_pos_right hupp hF₂
  dsimp only [F₂, F₃, F₄, F₅] at hlowMul huppMul ⊢
  nlinarith

/-- Quotient-rule identity for the C5 seam-normalized fourth likelihood jet. -/
theorem hasDerivAt_thetaCuspLikelihoodFourthSecondSquaredRatio
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspLikelihoodFourthSecondSquaredRatio
      ((thetaCuspLikelihoodSourceLogPartitionJetTwo x *
            thetaCuspLikelihoodSourceLogPartitionJetFive x -
          2 * thetaCuspLikelihoodSourceLogPartitionJetThree x *
            thetaCuspLikelihoodSourceLogPartitionJetFour x) /
        thetaCuspLikelihoodSourceLogPartitionJetTwo x ^ 3) x := by
  let F₂ := thetaCuspLikelihoodSourceLogPartitionJetTwo
  let F₄ := thetaCuspLikelihoodSourceLogPartitionJetFour
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx
  have hF₂ : HasDerivAt F₂
      (thetaCuspLikelihoodSourceLogPartitionJetThree x) x := by
    simpa only [F₂] using
      hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hB
  have hF₄ : HasDerivAt F₄
      (thetaCuspLikelihoodSourceLogPartitionJetFive x) x := by
    simpa only [F₄] using
      hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour hB
  have hF₂pos : 0 < F₂ x := by
    simpa only [F₂] using thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hF₂ne : thetaCuspLikelihoodSourceLogPartitionJetTwo x ≠ 0 := by
    exact (thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx).ne'
  have hquot := hF₄.div (hF₂.pow 2) (pow_ne_zero 2 hF₂pos.ne')
  have hcoeff :
      (thetaCuspLikelihoodSourceLogPartitionJetFive x * (F₂ ^ 2) x -
          F₄ x * ((2 : ℝ) * F₂ x ^ (2 - 1) *
            thetaCuspLikelihoodSourceLogPartitionJetThree x)) /
          (F₂ ^ 2) x ^ 2 =
        (thetaCuspLikelihoodSourceLogPartitionJetTwo x *
              thetaCuspLikelihoodSourceLogPartitionJetFive x -
            2 * thetaCuspLikelihoodSourceLogPartitionJetThree x *
              thetaCuspLikelihoodSourceLogPartitionJetFour x) /
          thetaCuspLikelihoodSourceLogPartitionJetTwo x ^ 3 := by
    simp only [Pi.pow_apply, F₂, F₄]
    apply (div_eq_div_iff
      (pow_ne_zero 2 (pow_ne_zero 2 hF₂ne))
      (pow_ne_zero 3 hF₂ne)).2
    ring
  change HasDerivAt (F₄ / F₂ ^ 2)
    ((thetaCuspLikelihoodSourceLogPartitionJetTwo x *
          thetaCuspLikelihoodSourceLogPartitionJetFive x -
        2 * thetaCuspLikelihoodSourceLogPartitionJetThree x *
          thetaCuspLikelihoodSourceLogPartitionJetFour x) /
      thetaCuspLikelihoodSourceLogPartitionJetTwo x ^ 3) x
  rw [← hcoeff]
  exact hquot

/-- Structural-tail projective likelihood curvature selected by C5 has strict positive drift. -/
theorem deriv_thetaCuspLikelihoodFourthSecondSquaredRatio_pos
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < deriv thetaCuspLikelihoodFourthSecondSquaredRatio x := by
  rw [(hasDerivAt_thetaCuspLikelihoodFourthSecondSquaredRatio hx).deriv]
  exact div_pos
    (thetaCuspLikelihoodHomotopyC5SeamInvariant_pos hx hscale)
    (pow_pos (thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx) 3)

/-- Once the structural scale threshold is crossed, the C5 seam-normalized fourth likelihood
jet is strictly increasing on the entire remaining source ray. -/
theorem strictMonoOn_thetaCuspLikelihoodFourthSecondSquaredRatio_of_scale
    {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hscale₀ : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x₀) :
    StrictMonoOn thetaCuspLikelihoodFourthSecondSquaredRatio (Set.Ici x₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
  · intro x hx
    have hx0 : 0 ≤ x := hx₀.trans hx
    exact (hasDerivAt_thetaCuspLikelihoodFourthSecondSquaredRatio hx0).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hxx : x₀ < x := hx
    have hx0 : 0 ≤ x := hx₀.trans hxx.le
    have hscaleMono :
        thetaCuspSingleAtomReflectionScale 1 x₀ ≤
          thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale
      norm_num
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith [hxx])) Real.pi_pos.le
    exact deriv_thetaCuspLikelihoodFourthSecondSquaredRatio_pos
      hx0 (hscale₀.trans hscaleMono)

end

end RHTower
