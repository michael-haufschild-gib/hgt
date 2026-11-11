import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheLogarithmsOfInterpolationWeightsAreStable
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Nodes whose interpolation weights are exponential coefficients

A logarithmic correction moves separated nodes until the exponential of
each node is exactly its Lagrange weight. The contraction constant depends
on node count and separation, without an exponential weight factor.
-/

open Complex Finset Metric Set

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nearby logarithm of each reference weight calibrates all nodes simultaneously. -/
theorem exists_self_consistent_interpolation_nodes {b a : ι → ℂ} {s r T : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hT : 0 < T) (hsmall : 8 * r ≤ s)
    (hb : ∀ j, s ≤ ‖b j‖) (hsep : ∀ j k, j ≠ k → s ≤ ‖b j - b k‖)
    (hcontract : 12 * (Fintype.card ι : ℝ) ≤ s * T)
    (ha : ∀ j, Complex.exp (a j) = zeroInterpolationWeight b j)
    (hnear : ∀ j, ‖a j / (T : ℂ) - b j‖ ≤ r / 2) :
    ∃ z : ι → ℂ, (∀ j, ‖z j - b j‖ ≤ r) ∧ Function.Injective z ∧
      (∀ j, z j ≠ 0) ∧ ∀ j, Complex.exp ((T : ℂ) * z j) = zeroInterpolationWeight z j := by
  let F : (ι → ℂ) → (ι → ℂ) := fun z j =>
    (a j + interpolationLogCorrection b z j) / (T : ℂ)
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hnum {D : ℝ} (hD : 0 ≤ D) :
      ((Fintype.card ι : ℝ) * (6 * D / s)) / T ≤ D / 2 := by
    have hc : (6 * (Fintype.card ι : ℝ)) / (s * T) ≤ 1 / 2 := by
      apply (div_le_iff₀ (mul_pos hs hT)).mpr
      nlinarith only [hcontract]
    calc
      _ = ((6 * (Fintype.card ι : ℝ)) / (s * T)) * D := by ring
      _ ≤ (1 / 2) * D := mul_le_mul_of_nonneg_right hc hD
      _ = _ := by ring
  have hcoordinates {z : ι → ℂ} (hz : z ∈ closedBall b r) :
      ∀ j, ‖z j - b j‖ ≤ r := by
    rw [mem_closedBall, dist_eq_norm] at hz
    intro j
    exact (norm_le_pi_norm (z - b) j).trans hz
  have hmaps : MapsTo F (closedBall b r) (closedBall b r) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hr.le).mpr
    intro j
    have hc := norm_interpolationLogCorrection_le hs hr.le hsmall hb hsep (hcoordinates hz) j
    have hdiv : ‖interpolationLogCorrection b z j / (T : ℂ)‖ ≤ r / 2 := by
      rw [norm_div, Complex.norm_of_nonneg hT.le]
      exact (div_le_div_of_nonneg_right hc hT.le).trans (hnum hr.le)
    change ‖(a j + interpolationLogCorrection b z j) / (T : ℂ) - b j‖ ≤ r
    calc
      _ = ‖(a j / (T : ℂ) - b j) + interpolationLogCorrection b z j / (T : ℂ)‖ := by
        congr 1
        ring
      _ ≤ ‖a j / (T : ℂ) - b j‖ + ‖interpolationLogCorrection b z j / (T : ℂ)‖ := norm_add_le _ _
      _ ≤ r := by linarith only [hnear j, hdiv]
  have hlip : LipschitzOnWith (1 / 2) F (closedBall b r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simp only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    have hc := norm_interpolationLogCorrection_sub_le hs hr.le hsmall hb hsep
      (hcoordinates hz) (hcoordinates hw) (norm_nonneg (z - w))
      (fun k => norm_le_pi_norm (z - w) k) j
    change ‖(a j + interpolationLogCorrection b z j) / (T : ℂ) -
        (a j + interpolationLogCorrection b w j) / (T : ℂ)‖ ≤ _
    calc
      _ = ‖(interpolationLogCorrection b z j - interpolationLogCorrection b w j) / (T : ℂ)‖ := by
        congr 1
        ring
      _ = ‖interpolationLogCorrection b z j - interpolationLogCorrection b w j‖ / T := by
        rw [norm_div, Complex.norm_of_nonneg hT.le]
      _ ≤ ((Fintype.card ι : ℝ) * (6 * ‖z - w‖ / s)) / T :=
        div_le_div_of_nonneg_right hc hT.le
      _ ≤ ‖z - w‖ / 2 := hnum (norm_nonneg _)
      _ = _ := by ring
  have hcontr : ContractingWith (1 / 2)
      (MapsTo.restrict F (closedBall b r) (closedBall b r) hmaps) := by
    refine ⟨by norm_num, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro z w
    simpa [MapsTo.restrict, Subtype.dist_eq] using hlip.dist_le_mul z.1 z.2 w.1 w.2
  have hcenter : b ∈ closedBall b r := by simpa only [mem_closedBall, dist_self] using hr.le
  obtain ⟨z, hz, hfix, _, _⟩ := hcontr.exists_fixedPoint'
    isClosed_closedBall.isComplete hmaps hcenter (edist_ne_top b (F b))
  have hzc := hcoordinates hz
  obtain ⟨hzn, hzd⟩ := interpolation_factors_mem_ball hs hr.le hsmall hb hsep hzc
  have hbn : ∀ j, b j ≠ 0 := fun j => norm_pos_iff.mp (hs.trans_le (hb j))
  have hbi : Function.Injective b := by
    intro j k he
    by_contra hjk
    have hh := hsep j k hjk
    rw [he, sub_self, norm_zero] at hh
    exact (not_le_of_gt hs) hh
  have hzi : Function.Injective z := by
    intro j k he
    by_contra hjk
    have hh := HTGeometry.mem_slitPlane_of_mem_ball_one (hzd j k hjk)
    have hn := Complex.slitPlane_ne_zero hh
    exact hn (by simp only [he, sub_self, zero_div])
  have hzne : ∀ j, z j ≠ 0 := by
    intro j he
    have hh := HTGeometry.mem_slitPlane_of_mem_ball_one (hzn j)
    exact Complex.slitPlane_ne_zero hh (by simp only [he, zero_div])
  refine ⟨z, hzc, hzi, hzne, ?_⟩
  intro j
  have hj := congrFun hfix j
  change (a j + interpolationLogCorrection b z j) / (T : ℂ) = z j at hj
  have he : (T : ℂ) * z j = a j + interpolationLogCorrection b z j := by
    rw [mul_comm]
    exact ((div_eq_iff hTc).mp hj).symm
  rw [he, Complex.exp_add, ha j]
  exact (zeroInterpolationWeight_eq_mul_exp hbn hzne hbi hzi j).symm

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
