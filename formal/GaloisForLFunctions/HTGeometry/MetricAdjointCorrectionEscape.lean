import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# Metric-adjoint correction escape

An operator with nonzero metric-adjoint defect cannot be repaired by operator corrections tending
to zero while its repairing metrics tend to the original metric.  Exact algebra gives quantitative
cost decomposition

`‖G B - B† G‖ ≤ 2 ‖G - Q‖ ‖B‖ + 2 ‖Q‖ ‖E‖`

whenever `Q (B + E) = (B + E)† Q`.  Thus a nonzero defect forces either correction mass or metric
escape.  Closedness of adjunction in operator norm supplies corresponding limit rigidity theorem.
-/

open Complex
open scoped InnerProduct

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact noncommutative decomposition of metric-adjoint defect under a repaired metric `Q` and
operator correction `E`. -/
theorem metricAdjointCorrection_defect_decomposition
    (B G Q E : H →L[ℂ] H)
    (hrepair : Q * (B + E) = ContinuousLinearMap.adjoint (B + E) * Q) :
    G * B - ContinuousLinearMap.adjoint B * G =
      (G - Q) * B - ContinuousLinearMap.adjoint B * (G - Q) +
        ContinuousLinearMap.adjoint E * Q - Q * E := by
  have hrepair' :
      Q * B + Q * E =
        ContinuousLinearMap.adjoint B * Q + ContinuousLinearMap.adjoint E * Q := by
    simpa only [mul_add, map_add, add_mul] using hrepair
  calc
    G * B - ContinuousLinearMap.adjoint B * G =
        G * B - ContinuousLinearMap.adjoint B * G +
          ((ContinuousLinearMap.adjoint B * Q + ContinuousLinearMap.adjoint E * Q) -
            (Q * B + Q * E)) := by rw [← hrepair']; simp
    _ = (G - Q) * B - ContinuousLinearMap.adjoint B * (G - Q) +
          ContinuousLinearMap.adjoint E * Q - Q * E := by noncomm_ring

/-- Quantitative singular-polarization escape law.  Every exact repair pays through metric drift
or operator correction; neither cost can disappear when original defect is nonzero. -/
theorem norm_metricAdjointCorrection_defect_le
    (B G Q E : H →L[ℂ] H)
    (hrepair : Q * (B + E) = ContinuousLinearMap.adjoint (B + E) * Q) :
    ‖G * B - ContinuousLinearMap.adjoint B * G‖ ≤
      2 * ‖G - Q‖ * ‖B‖ + 2 * ‖Q‖ * ‖E‖ := by
  rw [metricAdjointCorrection_defect_decomposition B G Q E hrepair]
  calc
    ‖(G - Q) * B - ContinuousLinearMap.adjoint B * (G - Q) +
          ContinuousLinearMap.adjoint E * Q - Q * E‖
        ≤ ‖(G - Q) * B‖ + ‖ContinuousLinearMap.adjoint B * (G - Q)‖ +
            ‖ContinuousLinearMap.adjoint E * Q‖ + ‖Q * E‖ := by
          calc
            _ ≤ ‖(G - Q) * B - ContinuousLinearMap.adjoint B * (G - Q) +
                    ContinuousLinearMap.adjoint E * Q‖ + ‖Q * E‖ := norm_sub_le _ _
            _ ≤ (‖(G - Q) * B - ContinuousLinearMap.adjoint B * (G - Q)‖ +
                    ‖ContinuousLinearMap.adjoint E * Q‖) + ‖Q * E‖ := by
                  gcongr
                  exact norm_add_le _ _
            _ ≤ (‖(G - Q) * B‖ + ‖ContinuousLinearMap.adjoint B * (G - Q)‖ +
                    ‖ContinuousLinearMap.adjoint E * Q‖) + ‖Q * E‖ := by
                  gcongr
                  exact norm_sub_le _ _
            _ = _ := by ring
    _ ≤ (‖G - Q‖ * ‖B‖) + (‖B‖ * ‖G - Q‖) +
            (‖E‖ * ‖Q‖) + (‖Q‖ * ‖E‖) := by
          gcongr <;> try exact norm_mul_le _ _
          · simpa using norm_mul_le (ContinuousLinearMap.adjoint B) (G - Q)
          · simpa using norm_mul_le (ContinuousLinearMap.adjoint E) Q
    _ = 2 * ‖G - Q‖ * ‖B‖ + 2 * ‖Q‖ * ‖E‖ := by ring

/-- Vanishing corrections and convergent repairing metrics force original operator to be
metric-adjoint. -/
theorem metricAdjointCorrection_limit_rigidity
    (B G : H →L[ℂ] H) (Q E : ℕ → H →L[ℂ] H)
    (hQ : Filter.Tendsto Q Filter.atTop (nhds G))
    (hE : Filter.Tendsto E Filter.atTop (nhds 0))
    (hrepair : ∀ᶠ n in Filter.atTop, Q n * (B + E n) =
      ContinuousLinearMap.adjoint (B + E n) * Q n) :
    G * B = ContinuousLinearMap.adjoint B * G := by
  have hBE : Filter.Tendsto (fun n => B + E n) Filter.atTop (nhds B) := by
    simpa using (tendsto_const_nhds.add hE)
  have hleft : Filter.Tendsto (fun n => Q n * (B + E n)) Filter.atTop
      (nhds (G * B)) := hQ.mul hBE
  have hadj : Filter.Tendsto
      (fun n => ContinuousLinearMap.adjoint (B + E n)) Filter.atTop
      (nhds (ContinuousLinearMap.adjoint B)) := by
    exact ((ContinuousLinearMap.adjoint :
      (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] H →L[ℂ] H).continuous.tendsto B).comp hBE
  have hright : Filter.Tendsto
      (fun n => ContinuousLinearMap.adjoint (B + E n) * Q n) Filter.atTop
      (nhds (ContinuousLinearMap.adjoint B * G)) := hadj.mul hQ
  have hrepair' : ∀ᶠ n in Filter.atTop,
      ContinuousLinearMap.adjoint (B + E n) * Q n = Q n * (B + E n) := by
    filter_upwards [hrepair] with n hn
    exact hn.symm
  exact tendsto_nhds_unique hleft (hright.congr' hrepair')

/-- Metric-adjoint relation is closed when both operator and metric converge in operator norm. -/
theorem metricAdjoint_limit_rigidity
    (B G : H →L[ℂ] H) (A Q : ℕ → H →L[ℂ] H)
    (hA : Filter.Tendsto A Filter.atTop (nhds B))
    (hQ : Filter.Tendsto Q Filter.atTop (nhds G))
    (hrepair : ∀ᶠ n in Filter.atTop,
      Q n * A n = ContinuousLinearMap.adjoint (A n) * Q n) :
    G * B = ContinuousLinearMap.adjoint B * G := by
  have hleft : Filter.Tendsto (fun n => Q n * A n) Filter.atTop
      (nhds (G * B)) := hQ.mul hA
  have hadj : Filter.Tendsto
      (fun n => ContinuousLinearMap.adjoint (A n)) Filter.atTop
      (nhds (ContinuousLinearMap.adjoint B)) := by
    exact ((ContinuousLinearMap.adjoint :
      (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] H →L[ℂ] H).continuous.tendsto B).comp hA
  have hright : Filter.Tendsto
      (fun n => ContinuousLinearMap.adjoint (A n) * Q n) Filter.atTop
      (nhds (ContinuousLinearMap.adjoint B * G)) := hadj.mul hQ
  have hrepair' : ∀ᶠ n in Filter.atTop,
      ContinuousLinearMap.adjoint (A n) * Q n = Q n * A n := by
    filter_upwards [hrepair] with n hn
    exact hn.symm
  exact tendsto_nhds_unique hleft (hright.congr' hrepair')

end GaloisForLFunctions.HTGeometry
