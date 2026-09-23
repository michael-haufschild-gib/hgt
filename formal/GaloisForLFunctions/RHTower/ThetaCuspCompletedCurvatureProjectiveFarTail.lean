import GaloisForLFunctions.RHTower.ThetaCuspCompletedInverseCurvatureTransport
import GaloisForLFunctions.RHTower.ThetaCuspExactCompletedC5SeamFarTail

/-!
# Completed curvature projective drift on the cofinal theta tail

Write `A = -(log Theta)''`.  The completed endpoint in the fixed-action C5 likelihood
homotopy is governed by the projective ratio `A'' / A`.  This file proves, without a
finite computation, that this ratio is strictly decreasing on a cofinal positive ray.

The first atom has the exact reserve

`A' * A'' - A * A''' = (2q+3)^(2 : ℕ) *
  (1296/q^(3 : ℕ) + 4536/q^(4 : ℕ) + 4536/q^(5 : ℕ) + 2916/q^(6 : ℕ) + 2916/q^(7 : ℕ))`.

After multiplication by first-atom scale this tends to `5184`.  Every likelihood
correction, with two additional powers of scale, tends to zero by the fixed spectral
support gap.  Hence completion retains a positive projective reserve cofinally.

RH chain: cofinal decrease of `A''/A` supplies the companion projective law for the
completed endpoint `velocityCenter(1) < 0`; this removes the noncompact part of
Conjecture K's zero-face burden before the remaining compact structural chamber.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Third curvature jet, in the same positive-curvature sign convention as the first
two curvature jets. -/
def thetaCuspLogCurvatureJetThree (x : ℝ) : ℝ :=
  -iteratedDeriv 5 thetaCuspLogSource x

/-- Completed projective reserve controlling the derivative of `A'' / A`. -/
def thetaCuspCompletedCurvatureProjectiveEnergy (x : ℝ) : ℝ :=
  thetaCuspLogCurvatureJet x * thetaCuspLogCurvatureJetTwo x -
    thetaCuspLogCurvature x * thetaCuspLogCurvatureJetThree x

/-- Completed curvature projective ratio. -/
def thetaCuspCompletedCurvatureProjectiveRatio (x : ℝ) : ℝ :=
  thetaCuspLogCurvatureJetTwo x / thetaCuspLogCurvature x

private theorem thetaCuspC5FarTail_scale_ne_zero (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
  unfold thetaCuspSingleAtomReflectionScale
  positivity

private theorem thetaCuspC5FarTail_scale_sq_likelihoodJetTwo_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo x) atTop (nhds 0) := by
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 4
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 3
  have h := (hv.const_mul 4).sub (hm.const_mul 4)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
    ring
  · norm_num

private theorem thetaCuspC5FarTail_scale_sq_likelihoodJetThree_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
        thetaCuspLikelihoodSourceLogPartitionJetThree x) atTop (nhds 0) := by
  have hk := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 5
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 4
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 3
  have h := ((hk.const_mul (-8)).add (hv.const_mul 24)).sub (hm.const_mul 8)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetThree
    ring
  · norm_num

private theorem thetaCuspC5FarTail_scale_sq_likelihoodJetFour_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
        thetaCuspLikelihoodSourceLogPartitionJetFour x) atTop (nhds 0) := by
  have hk4 := thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero 6
  have hk3 := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 5
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 4
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 3
  have h := (((hk4.const_mul 16).sub (hk3.const_mul 96)).add
    (hv.const_mul 112)).sub (hm.const_mul 16)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetFour
    ring
  · norm_num

private theorem thetaCuspC5FarTail_scale_sq_likelihoodJetFive_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
        thetaCuspLikelihoodSourceLogPartitionJetFive x) atTop (nhds 0) := by
  have hk5 := thetaCuspC5FarTail_scaled_likelihoodFifthCumulant_source_tendsto_zero 7
  have hk4 := thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero 6
  have hk3 := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 5
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 4
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 3
  have h1 := (hk5.const_mul (-32)).add (hk4.const_mul 320)
  have h2 := h1.sub (hk3.const_mul 800)
  have h3 := h2.add (hv.const_mul 480)
  have h := h3.sub (hm.const_mul 32)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetFive
    ring
  · norm_num

private def thetaCuspBornWittenCurvatureProjectiveEnergy (x : ℝ) : ℝ :=
  thetaCuspBornWittenLogThirdDerivative 1 x *
      thetaCuspBornWittenLogFourthDerivative 1 x -
    thetaCuspBornWittenLogCurvature 1 x *
      thetaCuspBornWittenLogFifthDerivative 1 x

private theorem thetaCuspBornWittenCurvatureProjectiveEnergy_formula
    {x : ℝ} (hx : 0 ≤ x) :
    let q := thetaCuspBornWittenWeight 1 x
    thetaCuspBornWittenCurvatureProjectiveEnergy x =
      (2 * q + 3) ^ (2 : ℕ) *
        (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ) + 4536 / q ^ (5 : ℕ) +
          2916 / q ^ (6 : ℕ) + 2916 / q ^ (7 : ℕ)) := by
  dsimp only
  let q := thetaCuspBornWittenWeight 1 x
  have hq : 0 < q := by
    simpa only [q] using thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  unfold thetaCuspBornWittenCurvatureProjectiveEnergy
    thetaCuspBornWittenLogThirdDerivative
    thetaCuspBornWittenLogFourthDerivative
    thetaCuspBornWittenLogFifthDerivative
  have hcurv : thetaCuspBornWittenLogCurvature 1 x =
      (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) := by
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    change 4 * q + 6 + 6 / q + 9 / q ^ (2 : ℕ) =
      (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ))
    field_simp [hq.ne']
    ring
  rw [hcurv]
  change
    (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) *
          ((2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ))) -
        ((2 * q + 3) * (2 + 3 / q ^ (2 : ℕ))) *
          ((2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) -
            1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ))) =
      (2 * q + 3) ^ (2 : ℕ) *
        (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ) + 4536 / q ^ (5 : ℕ) +
          2916 / q ^ (6 : ℕ) + 2916 / q ^ (7 : ℕ))
  field_simp [hq.ne']
  ring

private theorem thetaCuspC5FarTail_bornProjectiveEnergy_scaled_tendsto_5184 :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspBornWittenCurvatureProjectiveEnergy x)
      atTop (nhds 5184) := by
  let S : ℝ → ℝ := thetaCuspSingleAtomReflectionScale 1
  let q : ℝ → ℝ := thetaCuspLikelihoodCoordinate
  have hratio := thetaCuspC5FarTail_scale_div_coordinate_tendsto_one.pow 3
  have hq1 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 1 (by norm_num)
  have hq2 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have hq3 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 3 (by norm_num)
  have hq4 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 4 (by norm_num)
  have h := ((((hratio.const_mul 5184).add
      ((hratio.mul hq1).const_mul 18144)).add
      ((hratio.mul hq2).const_mul 18144)).add
      ((hratio.mul hq3).const_mul 11664)).add
      ((hratio.mul hq4).const_mul 11664)
  have h0 : Tendsto (fun x : ℝ =>
      5184 * (S x / q x) ^ (3 : ℕ) +
        18144 * ((S x / q x) ^ (3 : ℕ) * (1 / q x ^ (1 : ℕ))) +
        18144 * ((S x / q x) ^ (3 : ℕ) * (1 / q x ^ (2 : ℕ))) +
        11664 * ((S x / q x) ^ (3 : ℕ) * (1 / q x ^ (3 : ℕ))) +
        11664 * ((S x / q x) ^ (3 : ℕ) * (1 / q x ^ (4 : ℕ))))
      atTop (nhds 5184) := by
    simpa only [one_pow, mul_one, mul_zero, add_zero] using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hqpos : 0 < q x := by
    dsimp only [q]
    exact thetaCuspLikelihoodCoordinate_pos hx
  rw [thetaCuspBornWittenCurvatureProjectiveEnergy_formula hx]
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate]
  have hSq : 2 * q x + 3 = 2 * S x := by
    dsimp only [S, q]
    rw [thetaCuspC5FarTail_scale_eq_coordinate_add]
    ring
  rw [hSq]
  dsimp only [S, q]
  field_simp [hqpos.ne']
  ring

private theorem thetaCuspC5FarTail_completedProjectiveCorrection_scaled_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x *
        (thetaCuspCompletedCurvatureProjectiveEnergy x -
          thetaCuspBornWittenCurvatureProjectiveEnergy x))
      atTop (nhds 0) := by
  let S : ℝ → ℝ := thetaCuspSingleAtomReflectionScale 1
  let A0 : ℝ → ℝ := thetaCuspBornWittenLogCurvature 1
  let p0 : ℝ → ℝ := thetaCuspBornWittenLogThirdDerivative 1
  let B0 : ℝ → ℝ := thetaCuspBornWittenLogFourthDerivative 1
  let C0 : ℝ → ℝ := thetaCuspBornWittenLogFifthDerivative 1
  let F2 : ℝ → ℝ := thetaCuspLikelihoodSourceLogPartitionJetTwo
  let F3 : ℝ → ℝ := thetaCuspLikelihoodSourceLogPartitionJetThree
  let F4 : ℝ → ℝ := thetaCuspLikelihoodSourceLogPartitionJetFour
  let F5 : ℝ → ℝ := thetaCuspLikelihoodSourceLogPartitionJetFive
  have hp0 := thetaCuspC5FarTail_bornWittenLogThirdDerivative_div_scale_tendsto_eight
  have hB0 := thetaCuspC5FarTail_bornWittenLogFourthDerivative_div_scale_tendsto_sixteen
  have hA0 := thetaCuspC5FarTail_bornWittenLogCurvature_div_scale_tendsto_four
  have hC0 := thetaCuspC5FarTail_bornWittenLogFifthDerivative_div_scale_tendsto_thirtytwo
  have hF2 := thetaCuspC5FarTail_scale_sq_likelihoodJetTwo_tendsto_zero
  have hF3 := thetaCuspC5FarTail_scale_sq_likelihoodJetThree_tendsto_zero
  have hF4 := thetaCuspC5FarTail_scale_sq_likelihoodJetFour_tendsto_zero
  have hF5 := thetaCuspC5FarTail_scale_sq_likelihoodJetFive_tendsto_zero
  have hF3div := thetaCuspC5FarTail_likelihoodJetThree_div_scale_tendsto_zero
  have hF4div := thetaCuspC5FarTail_likelihoodJetFour_div_scale_tendsto_zero
  have hF5div := thetaCuspC5FarTail_likelihoodJetFive_div_scale_tendsto_zero
  have h1 := (hp0.mul hF4).neg
  have h2 := (hF3.mul hB0).neg
  have h3 := hF3.mul hF4div
  have h4 := hA0.mul hF5
  have h5 := hF2.mul hC0
  have h6 := (hF2.mul hF5div).neg
  have h := (((((h1.add h2).add h3).add h4).add h5).add h6)
  have h0 := by
    simpa only [mul_zero, zero_mul, neg_zero, add_zero] using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hS : S x ≠ 0 := by
    dsimp only [S]
    exact thetaCuspC5FarTail_scale_ne_zero x
  unfold thetaCuspCompletedCurvatureProjectiveEnergy
    thetaCuspBornWittenCurvatureProjectiveEnergy
    thetaCuspLogCurvature thetaCuspLogCurvatureJet thetaCuspLogCurvatureJetTwo
    thetaCuspLogCurvatureJetThree
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx0,
    iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx0,
    iteratedDeriv_four_thetaCuspLogSource_eq_factor hx0,
    iteratedDeriv_five_thetaCuspLogSource_eq_full_jets hx0,
    ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx0,
    ← thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hx0,
    ← thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hx0]
  unfold thetaCuspFirstAtomLogJetThree thetaCuspFullLogJetFive
  field_simp [hS]
  ring

/-- Scale-normalized completed projective reserve tends to the exact positive first-atom
constant `5184`. -/
theorem thetaCuspCompletedCurvatureProjectiveEnergy_scaled_tendsto_5184 :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspCompletedCurvatureProjectiveEnergy x)
      atTop (nhds 5184) := by
  have h := thetaCuspC5FarTail_bornProjectiveEnergy_scaled_tendsto_5184.add
    thetaCuspC5FarTail_completedProjectiveCorrection_scaled_tendsto_zero
  convert h using 1
  · funext x
    ring
  · norm_num

/-- The completed projective reserve is strictly positive on a cofinal source ray. -/
theorem eventually_thetaCuspCompletedCurvatureProjectiveEnergy_pos :
    ∀ᶠ x : ℝ in atTop, 0 < thetaCuspCompletedCurvatureProjectiveEnergy x := by
  have hlim := thetaCuspCompletedCurvatureProjectiveEnergy_scaled_tendsto_5184
  have hprod : ∀ᶠ x : ℝ in atTop,
      0 < thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspCompletedCurvatureProjectiveEnergy x :=
    (tendsto_order.1 hlim).1 0 (by norm_num)
  filter_upwards [hprod] with x hx
  have hS : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  nlinarith

theorem hasDerivAt_thetaCuspLogCurvatureJetTwo (x : ℝ) :
    HasDerivAt thetaCuspLogCurvatureJetTwo
      (thetaCuspLogCurvatureJetThree x) x := by
  unfold thetaCuspLogCurvatureJetTwo thetaCuspLogCurvatureJetThree
  change HasDerivAt (-iteratedDeriv 4 thetaCuspLogSource)
    (-iteratedDeriv 5 thetaCuspLogSource x) x
  simpa only [Nat.reduceAdd] using
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 4 x).neg

theorem hasDerivAt_thetaCuspCompletedCurvatureProjectiveRatio (x : ℝ) :
    HasDerivAt thetaCuspCompletedCurvatureProjectiveRatio
      (-thetaCuspCompletedCurvatureProjectiveEnergy x /
        thetaCuspLogCurvature x ^ (2 : ℕ)) x := by
  have hB := hasDerivAt_thetaCuspLogCurvatureJetTwo x
  have hA := hasDerivAt_thetaCuspLogCurvature x
  have hApos := thetaCuspLogCurvature_pos x
  have h := hB.div hA hApos.ne'
  unfold thetaCuspCompletedCurvatureProjectiveRatio
  refine h.congr_deriv ?_
  unfold thetaCuspCompletedCurvatureProjectiveEnergy
  field_simp [hApos.ne']
  ring

/-- **Cofinal completed companion law.**  There is a positive source threshold beyond which
`A'' / A` is strictly decreasing.  This is the source-specific projective premise needed by
the completed C5 endpoint transport. -/
theorem exists_strictAntiOn_thetaCuspCompletedCurvatureProjectiveRatio_farTail :
    ∃ x₀ : ℝ, 0 < x₀ ∧
      StrictAntiOn thetaCuspCompletedCurvatureProjectiveRatio (Set.Ici x₀) := by
  have henergy := eventually_thetaCuspCompletedCurvatureProjectiveEnergy_pos
  have htail : ∀ᶠ x : ℝ in atTop,
      0 < x ∧ 0 < thetaCuspCompletedCurvatureProjectiveEnergy x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), henergy] with x hx hE
    exact ⟨hx, hE⟩
  obtain ⟨x₀, hx₀⟩ := (eventually_atTop.1 htail)
  refine ⟨x₀, (hx₀ x₀ le_rfl).1, ?_⟩
  apply strictAntiOn_of_deriv_neg (convex_Ici x₀)
  · intro x hx
    exact (hasDerivAt_thetaCuspCompletedCurvatureProjectiveRatio x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_thetaCuspCompletedCurvatureProjectiveRatio x).deriv]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (hx₀ x hx.le).2)
      (sq_pos_of_pos (thetaCuspLogCurvature_pos x))

end

end RHTower
