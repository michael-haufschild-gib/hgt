import GaloisForLFunctions.HilbertMetric.RankOneSchurGaussianConcavity
import GaloisForLFunctions.HilbertMetric.DegreeFiveGaussianCurvature

/-!
# Gaussian metric rank-one concavity and higher-rank fracture

This module gives the invariant finite-Hilbert form of the rank-one Schur--Gaussian law.
Appending one weighted scalar feature is a rank-one update of the squared Hilbert metric, so its
Gaussian log-volume has exact negative self-commutator curvature.  The already formalized
degree-five configuration supplies the complementary higher-rank positive-curvature witness.
-/

open Filter
open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Gaussian Gram matrix obtained by appending one scalar feature with squared weight `t` to a
finite Euclidean feature family. -/
def gaussianMetricRankOneExtensionGram {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp
    (-(∑ k, (y i k - y j k) ^ 2 + t * (a i - a j) ^ 2))

/-- Appending one metric feature is literally Schur multiplication of the background Gaussian
Gram by the one-dimensional Gaussian semigroup. -/
theorem gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (t : ℝ) :
    gaussianMetricRankOneExtensionGram y a t =
      rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a t := by
  ext i j
  simp only [gaussianMetricRankOneExtensionGram, rankOneSchurGaussianPath,
    finiteGaussianDistanceGram, one_mul]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The unit-scale Gaussian distance Gram of every injective finite Euclidean family is positive
definite.  This supplies the unconditional positive background required by the metric law. -/
theorem finiteGaussianDistanceGram_one_posDef_of_injective {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    (finiteGaussianDistanceGram y 1).PosDef := by
  let z : Fin n → Fin d → ℝ := fun i k => Real.sqrt 2 * y i k
  let B : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (finiteGaussianGauge z 1)
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : Function.Injective z := by
    intro i j hij
    apply hy
    funext k
    exact mul_left_cancel₀ hsqrt (congrFun hij k)
  have hmetric : finiteGaussianDistanceGram y 1 =
      finiteHalfGaussianDistanceGram z 1 := by
    ext i j
    simp only [finiteGaussianDistanceGram, finiteHalfGaussianDistanceGram,
      one_mul, one_div, z]
    congr 1
    rw [Finset.sum_congr rfl (fun k _ => show
      (Real.sqrt 2 * y i k - Real.sqrt 2 * y j k) ^ 2 =
        2 * (y i k - y j k) ^ 2 by
          rw [show Real.sqrt 2 * y i k - Real.sqrt 2 * y j k =
            Real.sqrt 2 * (y i k - y j k) by ring]
          rw [mul_pow, hsquare]
          ring)]
    rw [Finset.mul_sum]
    ring
  have hinnerEq : finiteExponentialInnerGram z 1 = gaussianCoherentGram z := by
    ext i j
    simp [finiteExponentialInnerGram, gaussianCoherentGram, coordinateDot]
  have hinner : (finiteExponentialInnerGram z 1).PosDef := by
    rw [hinnerEq]
    exact gaussianCoherentGram_posDef_of_injective z hz
  have hB : B.PosDef := by
    dsimp [B]
    exact Matrix.PosDef.diagonal fun i => Real.exp_pos _
  have hBinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_of_isUnit hB.isUnit
  have hcong := hinner.conjTranspose_mul_mul_same (B := B) hBinj
  rw [hmetric, finiteHalfGaussianDistanceGram_eq_gauge]
  change (B * finiteExponentialInnerGram z 1 * B).PosDef
  simpa [B, Matrix.conjTranspose_eq_transpose_of_trivial] using hcong

/-- Exact Legendre--Hadamard curvature of finite Gaussian log-volume under one rank-one Hilbert
metric extension. -/
theorem gaussianMetricRankOneExtension_logDet_secondDerivative_eq {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (hy : Function.Injective y) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (gaussianMetricRankOneExtensionGram y a s).det)) t =
        -2 * matrixHilbertSchmidtEnergy
          (matrixSelfCommutator
            (matrixSqrtSimilarity
              (rankOneSchurExponentialPath (finiteGaussianDistanceGram y 1) a (2 * t))
              (rankOneLabelDiagonal a))) := by
  have hfun :
      (fun s => Real.log (gaussianMetricRankOneExtensionGram y a s).det) =
        fun s => Real.log
          (rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a s).det := by
    funext s
    rw [gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath]
  rw [hfun]
  exact rankOneSchurGaussian_logDet_secondDerivative_eq
    (finiteGaussianDistanceGram y 1) a
    (finiteGaussianDistanceGram_one_posDef_of_injective y hy) t ht

/-- Gaussian log-volume is globally concave along every rank-one finite-Hilbert metric extension. -/
theorem gaussianMetricRankOneExtension_logDet_concaveOn {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (hy : Function.Injective y) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun t => Real.log (gaussianMetricRankOneExtensionGram y a t).det) := by
  have hfun :
      (fun t => Real.log (gaussianMetricRankOneExtensionGram y a t).det) =
        fun t => Real.log
          (rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a t).det := by
    funext t
    rw [gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath]
  rw [hfun]
  exact rankOneSchurGaussian_logDet_concaveOn
    (finiteGaussianDistanceGram y 1) a
    (finiteGaussianDistanceGram_one_posDef_of_injective y hy)

/-- Rank-one metric curvature vanishes exactly when the appended scalar feature is constant. -/
theorem gaussianMetricRankOneExtension_logDet_secondDerivative_eq_zero_iff_constant {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (hy : Function.Injective y) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (gaussianMetricRankOneExtensionGram y a s).det)) t = 0 ↔
        ∀ i j, a i = a j := by
  have hfun :
      (fun s => Real.log (gaussianMetricRankOneExtensionGram y a s).det) =
        fun s => Real.log
          (rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a s).det := by
    funext s
    rw [gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath]
  rw [hfun]
  have hbase := finiteGaussianDistanceGram_one_posDef_of_injective y hy
  constructor
  · intro hzero i j
    have hblock :=
      (rankOneSchurGaussian_logDet_secondDerivative_eq_zero_iff_block
        (finiteGaussianDistanceGram y 1) a hbase t ht).1 hzero
    by_contra hij
    have hentry := hblock i j hij
    simp [finiteGaussianDistanceGram] at hentry
  · intro hconstant
    apply (rankOneSchurGaussian_logDet_secondDerivative_eq_zero_iff_block
      (finiteGaussianDistanceGram y 1) a hbase t ht).2
    intro i j hij
    exact (hij (hconstant i j)).elim

/-- A nonconstant added metric feature makes the rank-one curvature strictly negative at every
nonnegative scale. -/
theorem gaussianMetricRankOneExtension_logDet_secondDerivative_lt_zero {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (hy : Function.Injective y) (t : ℝ) (ht : 0 ≤ t)
    (hlabels : ∃ i j, a i ≠ a j) :
    deriv (deriv (fun s =>
      Real.log (gaussianMetricRankOneExtensionGram y a s).det)) t < 0 := by
  have hfun :
      (fun s => Real.log (gaussianMetricRankOneExtensionGram y a s).det) =
        fun s => Real.log
          (rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a s).det := by
    funext s
    rw [gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath]
  rw [hfun]
  apply rankOneSchurGaussian_logDet_secondDerivative_lt_zero
    (finiteGaussianDistanceGram y 1) a
    (finiteGaussianDistanceGram_one_posDef_of_injective y hy) t ht
  · intro i j
    exact Real.exp_ne_zero _
  · exact hlabels

/-- **Gaussian metric rank-one/full-rank fracture.**  Every one-feature metric extension is
log-volume concave, while an injective finite Euclidean Gaussian family exists whose isotropic
higher-rank metric scaling has strictly positive log-volume curvature. -/
theorem gaussianMetricRankOneConcavity_and_higherRankFracture :
    (∀ (n d : ℕ) (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ),
      Function.Injective y →
        ConcaveOn ℝ (Set.Ici 0)
          (fun t => Real.log (gaussianMetricRankOneExtensionGram y a t).det)) ∧
      ∃ x : DegreeFiveIndex 16 → (Fin 16 ⊕ DegreeFiveTopIndex 16 → ℝ),
        Function.Injective x ∧
        (finiteGaussianDistanceGram x 1).det ≠ 0 ∧
        0 < deriv (deriv
          (fun t => Real.log (finiteGaussianDistanceGram x t).det)) 1 := by
  constructor
  · intro n d y a hy
    exact gaussianMetricRankOneExtension_logDet_concaveOn y a hy
  · exact exists_finiteGaussianDistanceGram_positiveLogDetCurvature

end

end GaloisForLFunctions.HilbertMetric
