import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.FieldResponse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.GaussianDistinction

/-! # Physical first-return sensitivity to the field on the first spin -/
open Matrix MeasureTheory Filter Topology Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity
noncomputable section
open PrecisionReturns

/-- At error 1/10 the first empty date after the original near-Hilbert
crossing has a nonzero derivative in the first-site Z field. The
observation origin is the actual crossing of the unperturbed draw. -/
theorem gaussian_first_crossing_field_derivative :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let Z : selfAdjoint (Register N) := ⟨finitePauliMatrix (pauliZLabel (0:Fin N)),finitePauliMatrix_isHermitian _⟩
      let E := H.2.isHermitian.eigenvalues
      let V : Register N := H.2.isHermitian.eigenvectorUnitary
      let d (j : Fin N→Bool) := ((star V*Z.val*V) j j).re
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        let v := firstVisit H σ 0 (1/10)
        ∃ i j : Fin N→Bool, E i≠E j ∧
          let slope := -v*(d i-d j)/(E i-E j)
          slope≠0 ∧ HasDerivAt (fun z => firstVisit (fieldLine H Z z) σ 0 (1/10)) slope 0 := by
  have hs : (1/10:ℝ) < sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ) ≤ 2),sqrt_nonneg 2]
  filter_upwards [gaussian_first_empty_field_response (1/10) (by norm_num) hs,
    FirstGate.Boundary.gaussian_firstZ_distinguishes,LocalPatches.gaussian_first_crossing_local_width] with ω hw hd hc
  filter_upwards [hc] with k hk
  intro N H P Z E V d
  obtain ⟨σ,hσ,he,hbefore,hafter⟩ := hk
  have hb : 0 ≤ LocalPatches.localCrossingWidth N := by unfold LocalPatches.localCrossingWidth; positivity
  have hpos := hb.trans_lt hσ
  have hfar : 1/10 < orbitCircuitDistance H 0 σ := by
    by_contra! h
    have hscalar := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr h
    obtain ⟨w,hw,hmin⟩ := hafter 0 (Nat.zero_le _)
    have hle : w ≤ σ := hmin.2 ⟨le_rfl,hscalar⟩
    linarith only [hw,hle,hb]
  obtain ⟨i,j,hij,hr⟩ := hw k σ hpos hfar
  let v := firstVisit H σ 0 (1/10)
  have hv : 0 < v := hpos.trans_le (firstVisit_isLeast H σ 0 (by norm_num : (0:ℝ) < 1/10)).1.1
  have hne : d i≠d j := (hd (k+1)).ne (fun h => hij (congrArg E h))
  exact ⟨σ,hpos,he,hbefore,i,j,hij,div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hv.ne') (sub_ne_zero.mpr hne)) (sub_ne_zero.mpr hij),hr Z⟩

#print axioms gaussian_first_crossing_field_derivative
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity
