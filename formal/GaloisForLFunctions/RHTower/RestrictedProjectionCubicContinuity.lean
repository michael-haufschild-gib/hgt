import GaloisForLFunctions.RHTower.RestrictedProjectionCubicTrace
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison

/-!
# Trace-norm continuity of the cubic restricted-projection defect

The cubic map is continuous from the Hilbert--Schmidt topology to the trace-norm topology on
self-adjoint contractions.  This is the analytic homotopy mechanism required by RUCRI-A(6) and
FACHD-B: projection displacements have operator norm at most one, so no extra uniform-bound
premise is needed after their Hilbert--Schmidt convergence is known.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Difference of two Hilbert--Schmidt Gram operators is controlled in trace norm by root
distance.  This is the sharp constant-one two-factor estimate used in the cubic proof. -/
theorem traceNorm_hilbertSchmidtGram_sub_le
    {K L : H →L[ℂ] H} (hK : K.IsHilbertSchmidt) (hL : L.IsHilbertSchmidt) :
    traceNorm H (K ∘L ContinuousLinearMap.adjoint K -
      L ∘L ContinuousLinearMap.adjoint L) ≤
      (K.hsNorm + L.hsNorm) * (K - L).hsNorm := by
  let D := K - L
  let A := D ∘L ContinuousLinearMap.adjoint K
  let B := L ∘L ContinuousLinearMap.adjoint D
  have hD : D.IsHilbertSchmidt := hK.sub hL
  have hArect : MemRectSchattenClass 1 A :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hK.adjoint hD
  have hBrect : MemRectSchattenClass 1 B :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hD.adjoint hL
  have hA : MemSchattenClass 1 A :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hArect
  have hB : MemSchattenClass 1 B :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hBrect
  have htri : traceNorm H (A + B) ≤ traceNorm H A + traceNorm H B :=
    traceNorm_add_le (hA.isCompactOperator one_pos) (hB.isCompactOperator one_pos)
      hA.one_summable_approxNumber hB.one_summable_approxNumber
  have hAbound : traceNorm H A ≤ K.hsNorm * D.hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hK.adjoint hD
    simpa [A, ContinuousLinearMap.hsNorm, hK.hsNormSq_adjoint] using h
  have hBbound : traceNorm H B ≤ D.hsNorm * L.hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hD.adjoint hL
    simpa [B, ContinuousLinearMap.hsNorm, hD.hsNormSq_adjoint, mul_comm] using h
  have hdecomp :
      K ∘L ContinuousLinearMap.adjoint K -
          L ∘L ContinuousLinearMap.adjoint L = A + B := by
    dsimp [A, B, D]
    rw [ContinuousLinearMap.adjoint.map_sub]
    ext z
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hdecomp]
  calc
    traceNorm H (A + B) ≤ traceNorm H A + traceNorm H B := htri
    _ ≤ K.hsNorm * D.hsNorm + D.hsNorm * L.hsNorm := add_le_add hAbound hBbound
    _ = (K.hsNorm + L.hsNorm) * D.hsNorm := by ring

/-- Quantitative continuity bound for cubing self-adjoint Hilbert--Schmidt operators. -/
theorem traceNorm_cubic_sub_le_of_selfAdjoint_hilbertSchmidt
    (A B : H →L[ℂ] H) (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt)
    (hAadj : ContinuousLinearMap.adjoint A = A)
    (hBadj : ContinuousLinearMap.adjoint B = B) :
    traceNorm H (A ^ (3 : ℕ) - B ^ (3 : ℕ)) ≤
      (‖A‖ * (A.hsNorm + B.hsNorm) + B.hsNorm * ‖B‖) * (A - B).hsNorm := by
  let D := A - B
  let G := A ∘L ContinuousLinearMap.adjoint A -
    B ∘L ContinuousLinearMap.adjoint B
  let X := A ∘L G
  let Y := (D ∘L B) ∘L B
  have hD : D.IsHilbertSchmidt := hA.sub hB
  have hAArect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hA.adjoint hA
  have hBBrect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hB.adjoint hB
  have hAA : MemSchattenClass 1 (A ∘L ContinuousLinearMap.adjoint A) :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hAArect
  have hBB : MemSchattenClass 1 (B ∘L ContinuousLinearMap.adjoint B) :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hBBrect
  have hG : MemSchattenClass 1 G := hAA.one_sub hBB
  have hX : MemSchattenClass 1 X := by
    simpa [X] using memSchattenClass_one_comp_left hG A
  have hDBrect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hB hD
  have hDB : MemSchattenClass 1 (D ∘L B) :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hDBrect
  have hY : MemSchattenClass 1 Y := by
    simpa [Y] using memSchattenClass_one_comp_right hDB B
  have htri : traceNorm H (X + Y) ≤ traceNorm H X + traceNorm H Y :=
    traceNorm_add_le (hX.isCompactOperator one_pos) (hY.isCompactOperator one_pos)
      hX.one_summable_approxNumber hY.one_summable_approxNumber
  have hXbound : traceNorm H X ≤ ‖A‖ * traceNorm H G := by
    simpa [X] using traceNorm_comp_left_le hG.one_summable_approxNumber A
  have hGbound : traceNorm H G ≤ (A.hsNorm + B.hsNorm) * D.hsNorm := by
    simpa [G, D] using traceNorm_hilbertSchmidtGram_sub_le hA hB
  have hDBbound : traceNorm H (D ∘L B) ≤ D.hsNorm * B.hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    simpa [mul_comm] using
      rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hB hD
  have hYbound : traceNorm H Y ≤ (D.hsNorm * B.hsNorm) * ‖B‖ := by
    calc
      traceNorm H Y ≤ traceNorm H (D ∘L B) * ‖B‖ := by
        simpa [Y] using traceNorm_comp_right_le hDB.one_summable_approxNumber B
      _ ≤ (D.hsNorm * B.hsNorm) * ‖B‖ :=
        mul_le_mul_of_nonneg_right hDBbound (norm_nonneg B)
  have hdecomp : A ^ (3 : ℕ) - B ^ (3 : ℕ) = X + Y := by
    change (A * A) * A - (B * B) * B = X + Y
    dsimp [X, Y, G, D]
    change (A * A) * A - (B * B) * B =
      A * (A * ContinuousLinearMap.adjoint A -
        B * ContinuousLinearMap.adjoint B) + ((A - B) * B) * B
    rw [hAadj, hBadj]
    noncomm_ring
  rw [hdecomp]
  calc
    traceNorm H (X + Y) ≤ traceNorm H X + traceNorm H Y := htri
    _ ≤ ‖A‖ * traceNorm H G + (D.hsNorm * B.hsNorm) * ‖B‖ :=
      add_le_add hXbound hYbound
    _ ≤ ‖A‖ * ((A.hsNorm + B.hsNorm) * D.hsNorm) +
        (D.hsNorm * B.hsNorm) * ‖B‖ := by
      gcongr
    _ = (‖A‖ * (A.hsNorm + B.hsNorm) + B.hsNorm * ‖B‖) * D.hsNorm := by ring

/-- RUCRI-A(6): Hilbert--Schmidt convergence of self-adjoint contractions makes their cubic
defects converge in Schatten-one norm. -/
theorem traceNorm_cubic_tendsto_of_hsNorm_displacement_tendsto
    {ι : Type*} {l : Filter ι} {A : ι → H →L[ℂ] H} {B : H →L[ℂ] H}
    (hA : ∀ i, (A i).IsHilbertSchmidt) (hB : B.IsHilbertSchmidt)
    (hAadj : ∀ i, ContinuousLinearMap.adjoint (A i) = A i)
    (hBadj : ContinuousLinearMap.adjoint B = B)
    (hAnorm : ∀ i, ‖A i‖ ≤ 1) (hBnorm : ‖B‖ ≤ 1)
    (htend : Tendsto (fun i => (A i - B).hsNorm) l (nhds 0)) :
    Tendsto (fun i => traceNorm H ((A i) ^ (3 : ℕ) - B ^ (3 : ℕ))) l (nhds 0) := by
  have hupper : Tendsto (fun i => ((A i - B).hsNorm + 3 * B.hsNorm) *
      (A i - B).hsNorm) l (nhds 0) := by
    convert htend.add_const (3 * B.hsNorm) |>.mul htend using 1
    all_goals ring
  refine squeeze_zero' (Eventually.of_forall fun i => traceNorm_nonneg _) ?_ hupper
  refine Eventually.of_forall fun i => ?_
  have hhsA : (A i).hsNorm ≤ (A i - B).hsNorm + B.hsNorm := by
    have hadd := hsNorm_add_le (hA i |>.sub hB) hB
    simpa [sub_add_cancel] using hadd
  calc
    traceNorm H ((A i) ^ (3 : ℕ) - B ^ (3 : ℕ)) ≤
        (‖A i‖ * ((A i).hsNorm + B.hsNorm) + B.hsNorm * ‖B‖) *
          (A i - B).hsNorm :=
      traceNorm_cubic_sub_le_of_selfAdjoint_hilbertSchmidt
        (A i) B (hA i) hB (hAadj i) hBadj
    _ ≤ ((A i).hsNorm + 2 * B.hsNorm) * (A i - B).hsNorm := by
      apply mul_le_mul_of_nonneg_right _
        (ContinuousLinearMap.hsNorm_nonneg (A i - B))
      calc
        ‖A i‖ * ((A i).hsNorm + B.hsNorm) + B.hsNorm * ‖B‖ ≤
            ((A i).hsNorm + B.hsNorm) + B.hsNorm :=
          add_le_add
            (by
              simpa [mul_comm] using
                mul_le_of_le_one_right
                  (add_nonneg (ContinuousLinearMap.hsNorm_nonneg (A i))
                    (ContinuousLinearMap.hsNorm_nonneg B)) (hAnorm i))
            (by
              simpa [mul_comm] using
                mul_le_of_le_one_left (ContinuousLinearMap.hsNorm_nonneg B) hBnorm)
        _ = (A i).hsNorm + 2 * B.hsNorm := by ring
    _ ≤ ((A i - B).hsNorm + 3 * B.hsNorm) * (A i - B).hsNorm := by
      apply mul_le_mul_of_nonneg_right _
        (ContinuousLinearMap.hsNorm_nonneg (A i - B))
      linarith

/-- Projection-pair form of the trace-norm homotopy law.  Both polarizations may vary; the sole
metric input is convergence of their relative displacement in `S₂`. -/
theorem traceNorm_restrictedProjectionCubicDefect_tendsto
    {ι : Type*} {l : Filter ι}
    {R P : ι → H →L[ℂ] H} {R₀ P₀ : H →L[ℂ] H}
    (hR : ∀ i, IsIdempotentElem (R i)) (hP : ∀ i, IsIdempotentElem (P i))
    (hR₀ : IsIdempotentElem R₀) (hP₀ : IsIdempotentElem P₀)
    (hRadj : ∀ i, ContinuousLinearMap.adjoint (R i) = R i)
    (hPadj : ∀ i, ContinuousLinearMap.adjoint (P i) = P i)
    (hR₀adj : ContinuousLinearMap.adjoint R₀ = R₀)
    (hP₀adj : ContinuousLinearMap.adjoint P₀ = P₀)
    (hDelta : ∀ i, (restrictedProjectionDisplacement (R i) (P i)).IsHilbertSchmidt)
    (hDelta₀ : (restrictedProjectionDisplacement R₀ P₀).IsHilbertSchmidt)
    (htend : Tendsto (fun i =>
      (restrictedProjectionDisplacement (R i) (P i) -
        restrictedProjectionDisplacement R₀ P₀).hsNorm) l (nhds 0)) :
    Tendsto (fun i => traceNorm H
      (restrictedProjectionCubicDefect (R i) (P i) -
        restrictedProjectionCubicDefect R₀ P₀)) l (nhds 0) := by
  apply traceNorm_cubic_tendsto_of_hsNorm_displacement_tendsto
    hDelta hDelta₀
    (fun i => adjoint_restrictedProjectionDisplacement (R i) (P i)
      (hRadj i) (hPadj i))
    (adjoint_restrictedProjectionDisplacement R₀ P₀ hR₀adj hP₀adj)
    (fun i => HTGeometry.norm_twoProjection_difference_le_one
      (R i) (P i) (hR i) (hP i) (hRadj i) (hPadj i))
    (HTGeometry.norm_twoProjection_difference_le_one
      R₀ P₀ hR₀ hP₀ hR₀adj hP₀adj)
    htend

end RHTower
