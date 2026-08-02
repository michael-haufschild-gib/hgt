import GaloisForLFunctions.HTGeometry.OrbitBoxDimension
import GaloisForLFunctions.HTGeometry.CircleEmbeddingBiLipschitz
import GaloisForLFunctions.HTGeometry.TorusHomBiLipschitz

/-!
# The embedded phase torus has the box dimension of its rank

Composing the bi-Lipschitz coordinatewise embedding of the phase torus in the plane with the
two-sided covering estimate of the torus: the embedded phase torus, sitting in the space of complex
phase tuples, has box dimension equal to the number of phases.

This is the completed-orbit dimension statement for the phase carrier itself; the reporter version
follows by composing with the linear reporter map.
-/

open Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- **The embedded phase torus has box dimension its number of phases.** -/
theorem hasBoxDim_range_torusEmbed :
    HasBoxDim (Set.range (torusEmbed (k := k))) (Fintype.card k) := by
  refine hasBoxDim_range_of_biLipschitz (L := Real.toNNReal (2 * Real.pi))
    (K := Real.toNNReal (1 / 4)) ?_ ?_ lipschitzWith_torusEmbed antilipschitzWith_torusEmbed
  · rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  · rw [Real.coe_toNNReal _ (by positivity)]
    norm_num

/-- **The completed orbit of a frequency packet has the box dimension of its rank.**  For an
injective presenting homomorphism of tori, the embedded image of the presenting torus — the
completed phase orbit — has box dimension the rank of the presentation. -/
theorem hasBoxDim_range_torusEmbed_comp {d : Type*} [Fintype d] [DecidableEq d]
    (M : d → k → ℤ) (hinj : Function.Injective (torusIntegerHom M)) :
    HasBoxDim (Set.range (torusEmbed ∘ torusIntegerHom M)) (Fintype.card k) := by
  obtain ⟨K, hKpos, hK⟩ := exists_antilipschitzWith_torusIntegerHom M hinj
  have hlipM : LipschitzWith (Real.toNNReal (matrixAbsSum M + 1)) (torusIntegerHom M) :=
    (lipschitzWith_torusIntegerHom M).weaken (Real.toNNReal_mono (by linarith))
  have hAnn : 0 ≤ matrixAbsSum M := matrixAbsSum_nonneg M
  refine hasBoxDim_range_of_biLipschitz
    (L := Real.toNNReal (2 * Real.pi) * Real.toNNReal (matrixAbsSum M + 1))
    (K := K * Real.toNNReal (1 / 4)) ?_ ?_
    (lipschitzWith_torusEmbed.comp hlipM)
    (antilipschitzWith_torusEmbed.comp hK)
  · rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ matrixAbsSum M + 1)]
    have hpi := Real.pi_pos
    positivity
  · rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 1 / 4)]
    have hKR : (0 : ℝ) < (K : ℝ) := hKpos
    positivity

end

end GaloisForLFunctions.HTGeometry
