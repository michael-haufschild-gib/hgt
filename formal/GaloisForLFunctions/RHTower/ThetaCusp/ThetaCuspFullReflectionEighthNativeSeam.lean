import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthHankelSeam
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthBellTransfer

/-!
# Native rank-three reflected curvature at the theta seam

The raw eighth reflected-Hankel determinant is strictly positive at the self-dual seam, while its
factorization through normalized logarithmic jets was previously available only for positive source
coordinate.  This module proves continuity of the normalized curvature at zero and transports that
punctured factorization to the seam.  Consequently the native normalized D1 curvature itself is
strictly positive at zero.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- The normalized rank-three reflected curvature reaches the modular seam continuously. -/
theorem continuousAt_thetaCuspFullReflectionEighthHankelCurvature_zero :
    ContinuousAt thetaCuspFullReflectionEighthHankelCurvature 0 := by
  have hcoordpos : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos (by norm_num)
  have hborn8 : ContinuousAt (thetaCuspBornWittenLogEighthDerivative 1) 0 := by
    have hq := (hasDerivAt_thetaCuspBornWittenWeight 1 0).continuousAt
    have hqne : thetaCuspBornWittenWeight 1 0 ≠ 0 :=
      (thetaCuspBornWittenWeight_pos (by norm_num) (by norm_num)).ne'
    unfold thetaCuspBornWittenLogEighthDerivative
    fun_prop (disch := aesop)
  have hlike8 : ContinuousAt thetaCuspLikelihoodSourceLogPartitionJetEight 0 := by
    have hscale := (hasDerivAt_thetaCuspSingleAtomReflectionScale_one 0).continuousAt
    have hB := thetaCuspLikelihoodCoordinate_pos (by norm_num : (0 : ℝ) ≤ 0)
    have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate 0
    have hk7 := ((hasDerivAt_thetaCuspLikelihoodSeventhCumulant hB).comp
      0 hcoord).continuousAt
    have hk6 := ((hasDerivAt_thetaCuspLikelihoodSixthCumulant hB).comp
      0 hcoord).continuousAt
    have hk5 := ((hasDerivAt_thetaCuspLikelihoodFifthCumulant hB).comp
      0 hcoord).continuousAt
    have hk4 := ((hasDerivAt_thetaCuspLikelihoodFourthCumulant hB).comp
      0 hcoord).continuousAt
    have hk3 := ((hasDerivAt_thetaCuspLikelihoodThirdCumulant hB).comp
      0 hcoord).continuousAt
    have hv := ((hasDerivAt_thetaCuspLikelihoodVariance hB).comp
      0 hcoord).continuousAt
    have hm := ((hasDerivAt_thetaCuspLikelihoodMean hB).comp
      0 hcoord).continuousAt
    have hk8 : ContinuousAt
        (fun x => thetaCuspLikelihoodEighthCumulant
          (thetaCuspLikelihoodCoordinate x)) 0 := by
      have hm := ((hasDerivAt_thetaCuspLikelihoodMean hB).comp 0 hcoord).continuousAt
      have he2 := ((hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 2).comp
        0 hcoord).continuousAt
      have he3 := ((hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 3).comp
        0 hcoord).continuousAt
      have he4 := ((hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 4).comp
        0 hcoord).continuousAt
      have he5 := ((hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 5).comp
        0 hcoord).continuousAt
      have he6 := ((hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 6).comp
        0 hcoord).continuousAt
      have he7 := ((hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 7).comp
        0 hcoord).continuousAt
      have he8 := ((hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 8).comp
        0 hcoord).continuousAt
      unfold thetaCuspLikelihoodEighthCumulant
      fun_prop
    unfold thetaCuspLikelihoodSourceLogPartitionJetEight
    fun_prop
  have hborn6 : ContinuousAt (thetaCuspBornWittenLogSixthDerivative 1) 0 :=
    (hasDerivAt_thetaCuspBornWittenLogSixthDerivative
      (n := 1) (by norm_num) (by norm_num)).continuousAt
  have hlike6 : ContinuousAt thetaCuspLikelihoodSourceLogPartitionJetSix 0 :=
    (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSix
      (by norm_num)).continuousAt
  have hborn4 : ContinuousAt (thetaCuspBornWittenLogFourthDerivative 1) 0 :=
    (hasDerivAt_thetaCuspBornWittenLogFourthDerivative
      (n := 1) (by norm_num) (by norm_num)).continuousAt
  have hlike4 : ContinuousAt thetaCuspLikelihoodSourceLogPartitionJetFour 0 :=
    (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour hcoordpos).continuousAt
  have hborn2 : ContinuousAt (thetaCuspBornWittenLogCurvature 1) 0 :=
    (hasDerivAt_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) (by norm_num)).continuousAt
  have hlike2 : ContinuousAt thetaCuspLikelihoodSourceLogPartitionJetTwo 0 :=
    (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hcoordpos).continuousAt
  unfold thetaCuspFullReflectionEighthHankelCurvature
    thetaCuspFullReflectedLogCurvature
    thetaCuspFullReflectedLogFourthJet
    thetaCuspFullReflectedLogSixthJet
    thetaCuspFullReflectedLogEighthJet
  fun_prop

/-- The positive-coordinate raw/native factorization extends exactly to the seam. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_zero_eq_fullReflection :
    thetaCuspFullSourceReflectionEighthHankelCurvature 0 =
      4 * thetaCuspFullSource 0 ^ (6 : ℕ) *
        thetaCuspFullReflectionEighthHankelCurvature 0 := by
  let rhs : ℝ → ℝ := fun x =>
    4 * thetaCuspFullSource x ^ (6 : ℕ) *
      thetaCuspFullReflectionEighthHankelCurvature x
  have heq : thetaCuspFullSourceReflectionEighthHankelCurvature =ᶠ[𝓝[>] 0] rhs := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact thetaCuspFullSourceReflectionEighthHankelCurvature_eq_fullReflection hx
  have hraw : Tendsto thetaCuspFullSourceReflectionEighthHankelCurvature
      (𝓝[>] 0) (𝓝 (thetaCuspFullSourceReflectionEighthHankelCurvature 0)) :=
    continuous_thetaCuspFullSourceReflectionEighthHankelCurvature.continuousAt.continuousWithinAt
  have hrhs0 : ContinuousAt rhs 0 := by
    dsimp only [rhs]
    have hsource : ContinuousAt thetaCuspFullSource 0 :=
      contDiff_thetaCuspFullSource.continuous.continuousAt
    have hnative := continuousAt_thetaCuspFullReflectionEighthHankelCurvature_zero
    fun_prop
  have hrhs : Tendsto rhs (𝓝[>] 0) (𝓝 (rhs 0)) :=
    hrhs0.continuousWithinAt
  have hraw' : Tendsto thetaCuspFullSourceReflectionEighthHankelCurvature
      (𝓝[>] 0) (𝓝 (rhs 0)) := hrhs.congr' heq.symm
  have hz := tendsto_nhds_unique hraw hraw'
  simpa only [rhs] using hz

/-- Native normalized rank-three reflected eighth curvature is strict at the modular seam. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_zero_pos :
    0 < thetaCuspFullReflectionEighthHankelCurvature 0 := by
  have hraw := thetaCuspFullSourceReflectionEighthHankelCurvature_zero_pos
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_zero_eq_fullReflection] at hraw
  rcases (mul_pos_iff.mp hraw) with hpos | hneg
  · exact hpos.2
  · exact False.elim ((not_lt_of_ge (by positivity)) hneg.1)

end


end RHTower
