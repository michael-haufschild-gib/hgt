import GaloisForLFunctions.RHTower.VonMangoldtAdditiveLogJetHankelCurvature
import GaloisForLFunctions.RHTower.VonMangoldtGammaJuliaBianchiJointGram

/-!
# Exact finite successor--Bianchi Hankel weld

The successor Dirichlet and pointed Gamma--Bianchi features use the same square-root von Mangoldt
mass on the same finite source coordinates.  Putting them in one carrier, rather than taking their
orthogonal direct sum, gives the endpoint identity

`sqrt(c_n) (f(n+1)-f(n)) + sqrt(c_n) f(n) = sqrt(c_n) f(n+1)`.

Consequently their coupled Gram is exactly a positive Hankel moment matrix at every finite
aperture and every jet order.  The mixed block is forced, has strictly positive first Hankel
curvature on every nonempty aperture, and cancels the strictly negative successor curvature
exactly.  This supplies the finite Green-boundary weld missing from the direct-sum construction.
It does not claim that its raw boundary vectors have a cofinal Hilbert limit; that singular
normalization is the remaining source frontier.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive logarithmic depth aligned with the admissible pointed Bianchi coordinates. -/
def positiveLogJetDepth {N : ℕ} (i : Fin N) : ℕ := (i : ℕ) + 1

/-- Finite restriction of the successor edge feature at positive jet depths. -/
def finiteVonMangoldtSuccessorPositiveFeature
    (M : ℕ) {N : ℕ} (i : Fin N) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 fun p : Fin M =>
    Real.sqrt (finiteVonMangoldtRealWeight ((p : ℕ) + 2)) *
      vonMangoldtAdditiveLogJetDifference (positiveLogJetDepth i) ((p : ℕ) + 2)

/-- Pointed Gamma--Bianchi raw feature on the identical finite source coordinate. -/
def finiteVonMangoldtPointedBianchiPositiveFeature
    (M : ℕ) {N : ℕ} (i : Fin N) : EuclideanSpace ℝ (Fin M) :=
  finiteVonMangoldtGammaRawFeatureVector M 0 positiveLogJetDepth i

/-- Head-endpoint feature produced by coupling the edge and pointed boundary legs. -/
def finiteVonMangoldtSuccessorHeadFeature
    (M : ℕ) {N : ℕ} (i : Fin N) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 fun p : Fin M =>
    Real.sqrt (finiteVonMangoldtRealWeight ((p : ℕ) + 2)) *
      vonMangoldtAdditiveLogJet (positiveLogJetDepth i) ((p : ℕ) + 3)

/-- **Pointed endpoint weld.** Successor difference plus actual pointed Bianchi tail evaluation is
exactly head evaluation, coordinate by coordinate. -/
theorem finiteVonMangoldtSuccessor_add_pointedBianchi_eq_headFeature
    (M : ℕ) {N : ℕ} (i : Fin N) :
    finiteVonMangoldtSuccessorPositiveFeature M i +
        finiteVonMangoldtPointedBianchiPositiveFeature M i =
      finiteVonMangoldtSuccessorHeadFeature M i := by
  ext p
  simp only [finiteVonMangoldtSuccessorPositiveFeature,
    finiteVonMangoldtSuccessorHeadFeature,
    finiteVonMangoldtPointedBianchiPositiveFeature,
    finiteVonMangoldtGammaRawFeatureVector,
    finiteExponentialGammaRawFeature, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply,
    zero_mul, neg_zero, Real.exp_zero, mul_one, positiveLogJetDepth, pow_succ]
  rw [finiteVonMangoldtRealWeight]
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  push_cast
  ring_nf

/-- Coupled successor--pointed-boundary Gram on a finite source aperture. -/
def finiteVonMangoldtSuccessorPointedWeldGram
    (M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.gram ℝ (fun i : Fin N =>
    finiteVonMangoldtSuccessorPositiveFeature M i +
      finiteVonMangoldtPointedBianchiPositiveFeature M i)

/-- Uncoupled finite successor Gram. -/
def finiteVonMangoldtSuccessorPositiveFiniteGram
    (M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.gram ℝ (finiteVonMangoldtSuccessorPositiveFeature M)

/-- Actual adjacent-depth Bianchi boundary matrix on all chosen positive jet depths. -/
def finiteVonMangoldtPointedBianchiPositiveBoundary
    (M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  finiteVonMangoldtGammaAnomalyBianchiMixedGram M 0
    positiveLogJetDepth (fun _ ↦ 0) (by
      intro i j
      simp only [positiveLogJetDepth]
      omega)

/-- Pointed Ward reconstruction identifies the Bianchi boundary with its raw moment Gram. -/
theorem finiteVonMangoldtPointedBianchiPositiveBoundary_eq_rawGram
    (M N : ℕ) :
    finiteVonMangoldtPointedBianchiPositiveBoundary M N =
      finiteVonMangoldtGammaRawGram M 0
        (positiveLogJetDepth : Fin N → ℕ) := by
  rw [finiteVonMangoldtPointedBianchiPositiveBoundary]
  apply finiteVonMangoldtGammaAnomalyBianchiMixedGram_eq_rawGram

/-- Forced symmetrized mixed block on the common source coordinates. -/
def finiteVonMangoldtSuccessorPointedBianchiCross
    (M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦
    inner ℝ (finiteVonMangoldtSuccessorPositiveFeature M i)
        (finiteVonMangoldtPointedBianchiPositiveFeature M j) +
      inner ℝ (finiteVonMangoldtPointedBianchiPositiveFeature M i)
        (finiteVonMangoldtSuccessorPositiveFeature M j)

/-- Exact decomposition into successor Gram, pointed Bianchi Gram, and forced mixed block. -/
theorem finiteVonMangoldtSuccessorPointedWeldGram_decomposition
    (M N : ℕ) :
    finiteVonMangoldtSuccessorPointedWeldGram M N =
      finiteVonMangoldtSuccessorPositiveFiniteGram M N +
        finiteVonMangoldtPointedBianchiPositiveBoundary M N +
          finiteVonMangoldtSuccessorPointedBianchiCross M N := by
  ext i j
  rw [finiteVonMangoldtSuccessorPointedWeldGram,
    finiteVonMangoldtSuccessorPositiveFiniteGram,
    finiteVonMangoldtPointedBianchiPositiveBoundary_eq_rawGram]
  simp only [Matrix.add_apply, Matrix.gram_apply,
    finiteVonMangoldtSuccessorPointedBianchiCross,
    finiteVonMangoldtPointedBianchiPositiveFeature]
  simp only [inner_add_left, inner_add_right]
  rw [finiteVonMangoldtGammaRawFeatureVector_gram]
  ring

/-- Shifted head-endpoint moment sequence of the finite source aperture. -/
def finiteVonMangoldtSuccessorHeadMoment (M : ℕ) (k : ℕ) : ℝ :=
  ∑ p : Fin M,
    finiteVonMangoldtRealWeight ((p : ℕ) + 2) *
      Real.log ((p : ℕ) + 3) ^ (k + 2)

/-- Every coupled Gram entry is the corresponding shifted head-endpoint moment. -/
theorem finiteVonMangoldtSuccessorPointedWeldGram_apply
    (M N : ℕ) (i j : Fin N) :
    finiteVonMangoldtSuccessorPointedWeldGram M N i j =
      finiteVonMangoldtSuccessorHeadMoment M ((i : ℕ) + (j : ℕ)) := by
  rw [finiteVonMangoldtSuccessorPointedWeldGram, Matrix.gram_apply,
    finiteVonMangoldtSuccessor_add_pointedBianchi_eq_headFeature,
    finiteVonMangoldtSuccessor_add_pointedBianchi_eq_headFeature,
    PiLp.inner_apply]
  simp only [finiteVonMangoldtSuccessorHeadFeature, WithLp.ofLp_toLp,
    RCLike.inner_apply, conj_trivial, finiteVonMangoldtSuccessorHeadMoment]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    Real.sqrt (finiteVonMangoldtRealWeight ((p : ℕ) + 2)) *
          vonMangoldtAdditiveLogJet (positiveLogJetDepth j) ((p : ℕ) + 3) *
        (Real.sqrt (finiteVonMangoldtRealWeight ((p : ℕ) + 2)) *
          vonMangoldtAdditiveLogJet (positiveLogJetDepth i) ((p : ℕ) + 3)) =
        (Real.sqrt (finiteVonMangoldtRealWeight ((p : ℕ) + 2)) *
          Real.sqrt (finiteVonMangoldtRealWeight ((p : ℕ) + 2))) *
        (vonMangoldtAdditiveLogJet (positiveLogJetDepth i) ((p : ℕ) + 3) *
          vonMangoldtAdditiveLogJet (positiveLogJetDepth j) ((p : ℕ) + 3)) := by ring
    _ = finiteVonMangoldtRealWeight ((p : ℕ) + 2) *
        (vonMangoldtAdditiveLogJet (positiveLogJetDepth i) ((p : ℕ) + 3) *
          vonMangoldtAdditiveLogJet (positiveLogJetDepth j) ((p : ℕ) + 3)) := by
      rw [Real.mul_self_sqrt (finiteVonMangoldtRealWeight_nonneg _)]
    _ = _ := by
      unfold positiveLogJetDepth vonMangoldtAdditiveLogJet
      push_cast
      rw [← pow_add]
      congr 2
      omega

/-- **Finite all-order Hankel weld.** The coupled successor--Bianchi Gram is exactly a moment
Hankel matrix at every finite source aperture and every jet size. -/
theorem finiteVonMangoldtSuccessorPointedWeldGram_eq_momentHankelMatrix
    (M N : ℕ) :
    finiteVonMangoldtSuccessorPointedWeldGram M N =
      HTGeometry.momentHankelMatrix (finiteVonMangoldtSuccessorHeadMoment M) N := by
  ext i j
  rw [finiteVonMangoldtSuccessorPointedWeldGram_apply]
  rfl

/-- Exact first curvature of the finite successor block. -/
theorem finiteVonMangoldtSuccessorPositiveFiniteGram_firstCurvature_eq
    (M : ℕ) :
    finiteVonMangoldtSuccessorPositiveFiniteGram M 3 2 0 -
        finiteVonMangoldtSuccessorPositiveFiniteGram M 3 1 1 =
      -(∑ p : Fin M,
        vonMangoldtAdditiveLogJetAdjacentHankelCost 1 ((p : ℕ) + 2)) := by
  rw [finiteVonMangoldtSuccessorPositiveFiniteGram, Matrix.gram_apply,
    Matrix.gram_apply, PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [finiteVonMangoldtSuccessorPositiveFeature, WithLp.ofLp_toLp,
    RCLike.inner_apply, conj_trivial, positiveLogJetDepth]
  norm_num
  have hcurv :=
    vonMangoldtAdditiveLogJetFeature_adjacentHankelCurvature_eq 1 ((p : ℕ) + 2)
  unfold vonMangoldtAdditiveLogJetFeature at hcurv
  ring_nf at hcurv ⊢
  exact hcurv

/-- Every nonempty finite successor block has strict negative first Hankel curvature. -/
theorem finiteVonMangoldtSuccessorPositiveFiniteGram_firstCurvature_neg
    (M : ℕ) (hM : 0 < M) :
    finiteVonMangoldtSuccessorPositiveFiniteGram M 3 2 0 -
        finiteVonMangoldtSuccessorPositiveFiniteGram M 3 1 1 < 0 := by
  rw [finiteVonMangoldtSuccessorPositiveFiniteGram_firstCurvature_eq]
  apply neg_neg_of_pos
  apply Finset.sum_pos'
  · intro p hp
    exact vonMangoldtAdditiveLogJetAdjacentHankelCost_nonneg 1 ((p : ℕ) + 2)
  · let p : Fin M := ⟨0, hM⟩
    refine ⟨p, Finset.mem_univ p, ?_⟩
    simpa [p] using vonMangoldtAdditiveLogJetAdjacentHankelCost_two_pos 1

/-- **Curvature cancellation law.** The forced mixed block carries exactly the opposite of the
successor block's first Hankel curvature. -/
theorem finiteVonMangoldtSuccessorPointedBianchiCross_firstCurvature_eq
    (M : ℕ) :
    finiteVonMangoldtSuccessorPointedBianchiCross M 3 2 0 -
        finiteVonMangoldtSuccessorPointedBianchiCross M 3 1 1 =
      -(finiteVonMangoldtSuccessorPositiveFiniteGram M 3 2 0 -
        finiteVonMangoldtSuccessorPositiveFiniteGram M 3 1 1) := by
  have hweld : finiteVonMangoldtSuccessorPointedWeldGram M 3 2 0 =
      finiteVonMangoldtSuccessorPointedWeldGram M 3 1 1 := by
    rw [finiteVonMangoldtSuccessorPointedWeldGram_eq_momentHankelMatrix]
    rfl
  have hboundary : finiteVonMangoldtPointedBianchiPositiveBoundary M 3 2 0 =
      finiteVonMangoldtPointedBianchiPositiveBoundary M 3 1 1 := by
    rw [finiteVonMangoldtPointedBianchiPositiveBoundary_eq_rawGram,
      finiteVonMangoldtGammaRawGram_apply, finiteVonMangoldtGammaRawGram_apply]
    rfl
  have hdecomp := finiteVonMangoldtSuccessorPointedWeldGram_decomposition M 3
  have h20 := congrFun (congrFun hdecomp (2 : Fin 3)) (0 : Fin 3)
  have h11 := congrFun (congrFun hdecomp (1 : Fin 3)) (1 : Fin 3)
  simp only [Matrix.add_apply] at h20 h11
  linarith

/-- On every nonempty aperture the mixed block has strict positive cancelling curvature. -/
theorem finiteVonMangoldtSuccessorPointedBianchiCross_firstCurvature_pos
    (M : ℕ) (hM : 0 < M) :
    0 < finiteVonMangoldtSuccessorPointedBianchiCross M 3 2 0 -
        finiteVonMangoldtSuccessorPointedBianchiCross M 3 1 1 := by
  rw [finiteVonMangoldtSuccessorPointedBianchiCross_firstCurvature_eq]
  exact neg_pos.mpr
    (finiteVonMangoldtSuccessorPositiveFiniteGram_firstCurvature_neg M hM)

/-- Coupled finite weld is positive semidefinite before any target or Xi character is read. -/
theorem finiteVonMangoldtSuccessorPointedWeldGram_posSemidef
    (M N : ℕ) :
    (finiteVonMangoldtSuccessorPointedWeldGram M N).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

end

end RHTower

