import GaloisForLFunctions.HTGeometry.PhaseTorusEmbeddingDimension

/-!
# Diagonal scalings are bi-Lipschitz

Multiplying each coordinate of a complex tuple by a fixed nonzero scalar distorts the supremum
metric by at most the largest scalar in one direction and the reciprocal of the smallest in the
other.  Composing such a scaling with the embedded presenting torus keeps the box dimension, which
is the geometric content of the completed-orbit dimension theorem for weighted reporters: a
reporter tuple is a fixed diagonal rescaling of the phase tuple.
-/

open Metric Set
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise multiplication by a fixed tuple. -/
def diagScale (c : ι → ℂ) (x : ι → ℂ) : ι → ℂ := fun i => c i * x i

theorem lipschitzWith_diagScale {c : ι → ℂ} {L : ℝ≥0} (hL : ∀ i, ‖c i‖ ≤ (L : ℝ)) :
    LipschitzWith L (diagScale c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
  have hcoord : dist (diagScale c x i) (diagScale c y i) = ‖c i‖ * dist (x i) (y i) := by
    rw [dist_eq_norm, dist_eq_norm, diagScale, diagScale, ← mul_sub, norm_mul]
  rw [hcoord]
  refine mul_le_mul (hL i) (dist_le_pi_dist x y i) dist_nonneg (by positivity)

theorem antilipschitzWith_diagScale {c : ι → ℂ} {K : ℝ≥0} (hK : ∀ i, 1 ≤ (K : ℝ) * ‖c i‖) :
    AntilipschitzWith K (diagScale c) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
  have hcoord : dist (diagScale c x i) (diagScale c y i) = ‖c i‖ * dist (x i) (y i) := by
    rw [dist_eq_norm, dist_eq_norm, diagScale, diagScale, ← mul_sub, norm_mul]
  have hstep : dist (x i) (y i) ≤ (K : ℝ) * dist (diagScale c x i) (diagScale c y i) := by
    rw [hcoord]
    have hd : 0 ≤ dist (x i) (y i) := dist_nonneg
    nlinarith [hK i, hd]
  refine le_trans hstep ?_
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ i) (by positivity)

/-- A diagonal scaling with nonzero entries is antilipschitz. -/
theorem exists_antilipschitzWith_diagScale {c : ι → ℂ} (hc : ∀ i, c i ≠ 0) :
    ∃ K : ℝ≥0, 0 < (K : ℝ) ∧ AntilipschitzWith K (diagScale c) := by
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨i₀⟩ := hne
    set m : ℝ := Finset.univ.inf' ⟨i₀, Finset.mem_univ i₀⟩ fun i => ‖c i‖ with hm
    have hmpos : 0 < m := by
      rw [hm]
      refine (Finset.lt_inf'_iff ⟨i₀, Finset.mem_univ i₀⟩).mpr fun i _ => ?_
      exact norm_pos_iff.mpr (hc i)
    have hmle : ∀ i, m ≤ ‖c i‖ := by
      intro i
      rw [hm]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    refine ⟨Real.toNNReal m⁻¹, ?_, ?_⟩
    · rw [Real.coe_toNNReal _ (by positivity)]
      positivity
    · refine antilipschitzWith_diagScale fun i => ?_
      rw [Real.coe_toNNReal _ (by positivity)]
      rw [inv_mul_eq_div, le_div_iff₀ hmpos, one_mul]
      exact hmle i
  · refine ⟨1, by norm_num, ?_⟩
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hx : x = y := by
      funext i
      exact absurd ⟨i⟩ hne
    rw [hx]
    simp

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- **A rescaled embedded torus has the box dimension of the torus.** -/
theorem hasBoxDim_range_diagScale_comp {d : Type*} [Fintype d] [DecidableEq d]
    (M : d → k → ℤ) (hinj : Function.Injective (torusIntegerHom M)) {c : d → ℂ}
    (hc : ∀ i, c i ≠ 0) :
    HasBoxDim (Set.range (diagScale c ∘ torusEmbed ∘ torusIntegerHom M)) (Fintype.card k) := by
  obtain ⟨K, hKpos, hK⟩ := exists_antilipschitzWith_torusIntegerHom M hinj
  obtain ⟨Kc, hKcpos, hKc⟩ := exists_antilipschitzWith_diagScale hc
  have hlipM : LipschitzWith (Real.toNNReal (matrixAbsSum M + 1)) (torusIntegerHom M) :=
    (lipschitzWith_torusIntegerHom M).weaken (Real.toNNReal_mono (by linarith))
  have hAnn : 0 ≤ matrixAbsSum M := matrixAbsSum_nonneg M
  have hlipc : LipschitzWith (Real.toNNReal (∑ i, ‖c i‖ + 1)) (diagScale c) := by
    refine lipschitzWith_diagScale fun i => ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    have hsingle : ‖c i‖ ≤ ∑ i, ‖c i‖ := by
      refine Finset.single_le_sum (f := fun i => ‖c i‖) (fun i _ => norm_nonneg _)
        (Finset.mem_univ i)
    linarith
  refine hasBoxDim_range_of_biLipschitz
    (L := Real.toNNReal (∑ i, ‖c i‖ + 1) *
      (Real.toNNReal (2 * Real.pi) * Real.toNNReal (matrixAbsSum M + 1)))
    (K := (K * Real.toNNReal (1 / 4)) * Kc) ?_ ?_
    (hlipc.comp (lipschitzWith_torusEmbed.comp hlipM))
    (hKc.comp (antilipschitzWith_torusEmbed.comp hK))
  · rw [NNReal.coe_mul, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ matrixAbsSum M + 1)]
    have hpi := Real.pi_pos
    have hsum : (0 : ℝ) ≤ ∑ i, ‖c i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    positivity
  · rw [NNReal.coe_mul, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 1 / 4)]
    have hKR : (0 : ℝ) < (K : ℝ) := hKpos
    have hKcR : (0 : ℝ) < (Kc : ℝ) := hKcpos
    positivity

end

end GaloisForLFunctions.HTGeometry
