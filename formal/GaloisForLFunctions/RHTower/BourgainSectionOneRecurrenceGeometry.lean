/-
# Exact physical-scale geometry for Bourgain's Section-1 recurrence

If a fine interval contains `J*H` samples, Bourgain's physical scales are
`N = (JH)²` and `K = J²`.  Hence `N/K = H²`.  This module proves the
corresponding exact cover of the fine phase ball by `H⁸` coarse cubes and
computes the translated coarse-cube volume.  These identities are the
normalization cancellation behind equations (1.19)--(1.20).
-/
import GaloisForLFunctions.RHTower.BourgainSectionOneIndependentTranslation
import GaloisForLFunctions.RHTower.BourgainExplicitCubeGrid

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Paper's fine physical scale `N`, up to the harmless fixed factor `16`
coming from the two separated quarter-arcs. -/
def bourgainSectionOneFinePhysicalRadius (J H : ℕ) : ℝ :=
  bourgainSectionOneBlockDenominator J H ^ (2 : ℕ)

/-- Paper's coarse physical scale `K`, with the same fixed factor `16`. -/
def bourgainSectionOneCoarsePhysicalRadius (J : ℕ) : ℝ :=
  (4 * (J : ℝ)) ^ (2 : ℕ)

/-- Exact scale ratio `N/K = H²`, stated without division. -/
theorem bourgainSectionOne_fineRadius_eq_card_sq_mul_coarseRadius
    (J H : ℕ) :
    bourgainSectionOneFinePhysicalRadius J H =
      (H : ℝ) ^ (2 : ℕ) *
        bourgainSectionOneCoarsePhysicalRadius J := by
  unfold bourgainSectionOneFinePhysicalRadius
    bourgainSectionOneCoarsePhysicalRadius
    bourgainSectionOneBlockDenominator
  ring

/-- For positive block length, the predecessor grid has exactly `H²`
centers in each physical coordinate. -/
theorem bourgainSectionOne_gridSideLength
    {H : ℕ} (hH : 0 < H) :
    H ^ (2 : ℕ) - 1 + 1 = H ^ (2 : ℕ) := by
  exact Nat.sub_add_cancel (pow_pos hH _)

/-- Exact cover used in the recurrence: the fine ball is covered by a
product grid with `H²` coarse cubes per coordinate. -/
theorem bourgainSectionOne_finePhaseBall_subset_coarseGridCover
    (J H : ℕ) (hH : 0 < H) :
    bourgainSectionOnePhaseBall
        (bourgainSectionOneBlockDenominator J H) ⊆
      ⋃ k : Fin 4 → Fin (H ^ (2 : ℕ)),
        bourgainTranslatedNormCube
          (bourgainGridCenter (H ^ (2 : ℕ))
            (bourgainSectionOneCoarsePhysicalRadius J) k)
          (bourgainSectionOneCoarsePhysicalRadius J) := by
  have hr : 0 ≤ bourgainSectionOneCoarsePhysicalRadius J := by
    unfold bourgainSectionOneCoarsePhysicalRadius
    positivity
  have hcover :=
    bourgain_normCube_subset_gridCover
      (H ^ (2 : ℕ) - 1) hr
  rw [bourgainSectionOne_gridSideLength hH] at hcover
  change
    {x : BourgainPhaseSpace |
        ‖x‖ ≤ bourgainSectionOneFinePhysicalRadius J H} ⊆ _
  rw [bourgainSectionOne_fineRadius_eq_card_sq_mul_coarseRadius]
  simpa only [Nat.cast_pow] using hcover

/-- The recurrence cover contains exactly `H⁸` coarse physical cubes. -/
theorem card_bourgainSectionOneCoarseGridIndex
    (H : ℕ) :
    Fintype.card (Fin 4 → Fin (H ^ (2 : ℕ))) = H ^ (8 : ℕ) := by
  rw [card_bourgainGridIndex]
  ring

/-- A translated sup-norm cube is the corresponding metric closed ball. -/
theorem bourgainTranslatedNormCube_eq_closedBall
    (y : BourgainPhaseSpace) (R : ℝ) :
    bourgainTranslatedNormCube y R = Metric.closedBall y R := by
  ext x
  rw [mem_bourgainTranslatedNormCube_iff, Metric.mem_closedBall]
  rw [dist_eq_norm]

/-- Exact four-dimensional volume of every translated sup-norm cube. -/
theorem volume_bourgainTranslatedNormCube
    (y : BourgainPhaseSpace) {R : ℝ} (hR : 0 ≤ R) :
    volume (bourgainTranslatedNormCube y R) =
      ENNReal.ofReal ((2 * R) ^ (4 : ℕ)) := by
  rw [bourgainTranslatedNormCube_eq_closedBall]
  simpa using Real.volume_pi_closedBall y hR

/-- Exact coarse-cube volume at Section-1 scale `K`. -/
theorem volume_bourgainSectionOne_coarsePhysicalCube
    (J : ℕ) (y : BourgainPhaseSpace) :
    volume
        (bourgainTranslatedNormCube y
          (bourgainSectionOneCoarsePhysicalRadius J)) =
      ENNReal.ofReal
        ((2 * bourgainSectionOneCoarsePhysicalRadius J) ^ (4 : ℕ)) := by
  exact volume_bourgainTranslatedNormCube y (by
    unfold bourgainSectionOneCoarsePhysicalRadius
    positivity)

/-- In four-dimensional sup norm, open and closed balls differ only on a
null boundary. -/
theorem bourgain_closedBall_ae_eq_ball
    (y : BourgainPhaseSpace) {R : ℝ} (hR : 0 < R) :
    Metric.closedBall y R =ᵐ[volume] Metric.ball y R := by
  exact (ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
    (by rw [Real.volume_pi_ball y hR,
      Real.volume_pi_closedBall y hR.le])
    measurableSet_ball.nullMeasurableSet
    (by rw [Real.volume_pi_closedBall y hR.le]
        exact ENNReal.ofReal_ne_top)).symm

/-- Distinct product-grid centers are separated by at least two radii in
sup norm. -/
theorem two_mul_le_dist_bourgainGridCenter
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (k l : Fin 4 → Fin n) (hkl : k ≠ l) :
    2 * R ≤
      dist (bourgainGridCenter n R k)
        (bourgainGridCenter n R l) := by
  have hexists : ∃ i : Fin 4, k i ≠ l i := by
    by_contra h
    apply hkl
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hexists
  have hcoord :
      |(bourgainGridCenter n R k -
          bourgainGridCenter n R l) i| ≤
        ‖bourgainGridCenter n R k -
          bourgainGridCenter n R l‖ :=
    abs_bourgainPhaseSpace_apply_le_norm
      (bourgainGridCenter n R k - bourgainGridCenter n R l) i
  have habs :
      2 * R ≤
        |bourgainGridCenter n R k i -
          bourgainGridCenter n R l i| := by
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hcast : ((k i : ℕ) : ℝ) + 1 ≤ (l i : ℕ) := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      have hdiff :
          bourgainGridCenter n R k i -
              bourgainGridCenter n R l i ≤ -2 * R := by
        unfold bourgainGridCenter bourgainGridCenter1D
        nlinarith
      rw [abs_of_nonpos (hdiff.trans (by nlinarith))]
      linarith
    · have hcast : ((l i : ℕ) : ℝ) + 1 ≤ (k i : ℕ) := by
        exact_mod_cast Nat.succ_le_of_lt hgt
      have hdiff :
          2 * R ≤
            bourgainGridCenter n R k i -
              bourgainGridCenter n R l i := by
        unfold bourgainGridCenter bourgainGridCenter1D
        nlinarith
      rw [abs_of_nonneg (by linarith)]
      exact hdiff
  rw [dist_eq_norm]
  exact habs.trans (by simpa only [Pi.sub_apply] using hcoord)

/-- Open cubes in the exact product grid are pairwise disjoint. -/
theorem pairwise_disjoint_bourgainGridCenter_ball
    (n : ℕ) {R : ℝ} (hR : 0 < R) :
    Pairwise fun k l : Fin 4 → Fin n =>
      Disjoint
        (Metric.ball (bourgainGridCenter n R k) R)
        (Metric.ball (bourgainGridCenter n R l) R) := by
  intro k l hkl
  exact Metric.ball_disjoint_ball
    (by simpa [two_mul] using
      two_mul_le_dist_bourgainGridCenter n hR.le k l hkl)

/-- Closed cubes in the exact product grid are pairwise disjoint modulo
Lebesgue-null boundaries. -/
theorem pairwise_aedisjoint_bourgainGridCenter_closedBall
    (n : ℕ) {R : ℝ} (hR : 0 < R) :
    Pairwise fun k l : Fin 4 → Fin n =>
      AEDisjoint volume
        (Metric.closedBall (bourgainGridCenter n R k) R)
        (Metric.closedBall (bourgainGridCenter n R l) R) := by
  intro k l hkl
  have hopen :
      AEDisjoint volume
        (Metric.ball (bourgainGridCenter n R k) R)
        (Metric.ball (bourgainGridCenter n R l) R) :=
    (pairwise_disjoint_bourgainGridCenter_ball n hR hkl).aedisjoint
  exact hopen.congr
    (bourgain_closedBall_ae_eq_ball
      (bourgainGridCenter n R k) hR)
    (bourgain_closedBall_ae_eq_ball
      (bourgainGridCenter n R l) hR)

/-- One grid center plus one radius remains inside the ambient grid radius. -/
theorem abs_bourgainGridCenter_apply_add_radius_le
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (k : Fin 4 → Fin n) (i : Fin 4) :
    |bourgainGridCenter n R k i| + R ≤ (n : ℝ) * R := by
  have hki0 : 0 ≤ ((k i : ℕ) : ℝ) := by positivity
  have hkin : ((k i : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (k i).isLt
  unfold bourgainGridCenter bourgainGridCenter1D
  have habs :
      |(2 * ((k i : ℕ) : ℝ) + 1 - (n : ℝ)) * R| ≤
        (n : ℝ) * R - R := by
    rw [abs_le]
    constructor <;> nlinarith
  linarith

/-- Every closed product-grid cube lies inside the ambient grid cube. -/
theorem bourgain_gridCover_subset_normCube
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (⋃ k : Fin 4 → Fin n,
        bourgainTranslatedNormCube
          (bourgainGridCenter n R k) R) ⊆
      {x : BourgainPhaseSpace | ‖x‖ ≤ (n : ℝ) * R} := by
  intro x hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  rw [mem_bourgainTranslatedNormCube_iff,
    pi_norm_le_iff_of_nonneg hR] at hk
  change ‖x‖ ≤ (n : ℝ) * R
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hR)]
  intro i
  have hki := hk i
  rw [Pi.sub_apply, Real.norm_eq_abs] at hki
  rw [Real.norm_eq_abs]
  calc
    |x i| ≤
        |x i - bourgainGridCenter n R k i| +
          |bourgainGridCenter n R k i| := by
      simpa using
        (abs_add_le (x i - bourgainGridCenter n R k i)
          (bourgainGridCenter n R k i))
    _ ≤ R + |bourgainGridCenter n R k i| := by
      gcongr
    _ ≤ (n : ℝ) * R := by
      simpa [add_comm] using
        abs_bourgainGridCenter_apply_add_radius_le n hR k i

/-- The Section-1 grid is an exact set cover of the fine physical ball. -/
theorem bourgainSectionOne_finePhaseBall_eq_coarseGridCover
    (J H : ℕ) (hH : 0 < H) :
    bourgainSectionOnePhaseBall
        (bourgainSectionOneBlockDenominator J H) =
      ⋃ k : Fin 4 → Fin (H ^ (2 : ℕ)),
        bourgainTranslatedNormCube
          (bourgainGridCenter (H ^ (2 : ℕ))
            (bourgainSectionOneCoarsePhysicalRadius J) k)
          (bourgainSectionOneCoarsePhysicalRadius J) := by
  apply Set.Subset.antisymm
  · exact bourgainSectionOne_finePhaseBall_subset_coarseGridCover
      J H hH
  · have hsub := bourgain_gridCover_subset_normCube
        (H ^ (2 : ℕ))
        (show 0 ≤ bourgainSectionOneCoarsePhysicalRadius J by
          unfold bourgainSectionOneCoarsePhysicalRadius
          positivity)
    change _ ⊆
      {x : BourgainPhaseSpace |
        ‖x‖ ≤ bourgainSectionOneFinePhysicalRadius J H}
    rw [bourgainSectionOne_fineRadius_eq_card_sq_mul_coarseRadius]
    simpa only [Nat.cast_pow] using hsub

/-- Exact integral partition over the `H⁸` recurrence cubes.  Closed-cube
overlap occurs only on null boundaries, so there is no hidden multiplicity
constant. -/
theorem sum_setLIntegral_bourgainSectionOne_coarseGrid_eq_finePhaseBall
    (J H : ℕ) (hJ : 0 < J) (hH : 0 < H)
    (f : BourgainPhaseSpace → ENNReal) :
    (∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
      ∫⁻ x in bourgainTranslatedNormCube
          (bourgainGridCenter (H ^ (2 : ℕ))
            (bourgainSectionOneCoarsePhysicalRadius J) k)
          (bourgainSectionOneCoarsePhysicalRadius J),
        f x) =
      ∫⁻ x in bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H), f x := by
  have hR : 0 < bourgainSectionOneCoarsePhysicalRadius J := by
    unfold bourgainSectionOneCoarsePhysicalRadius
    positivity
  let U : (Fin 4 → Fin (H ^ (2 : ℕ))) → Set BourgainPhaseSpace :=
    fun k => bourgainTranslatedNormCube
      (bourgainGridCenter (H ^ (2 : ℕ))
        (bourgainSectionOneCoarsePhysicalRadius J) k)
      (bourgainSectionOneCoarsePhysicalRadius J)
  have hnull (k : Fin 4 → Fin (H ^ (2 : ℕ))) :
      NullMeasurableSet (U k) volume := by
    rw [show U k = Metric.closedBall
        (bourgainGridCenter (H ^ (2 : ℕ))
          (bourgainSectionOneCoarsePhysicalRadius J) k)
        (bourgainSectionOneCoarsePhysicalRadius J) by
      exact bourgainTranslatedNormCube_eq_closedBall _ _]
    exact measurableSet_closedBall.nullMeasurableSet
  have hdisjoint :
      Pairwise fun k l => AEDisjoint volume (U k) (U l) := by
    simpa [U, bourgainTranslatedNormCube_eq_closedBall] using
      pairwise_aedisjoint_bourgainGridCenter_closedBall
        (H ^ (2 : ℕ)) hR
  have hpartition :=
    lintegral_iUnion₀ (s := U) hnull hdisjoint f
  rw [tsum_fintype] at hpartition
  rw [bourgainSectionOne_finePhaseBall_eq_coarseGridCover J H hH]
  simpa [U] using hpartition.symm

end

end RHTower
