import GaloisForLFunctions.HTGeometry.GomesFockThresholdCompressedPOVM

/-! Exact information preservation under removal of impossible threshold labels.
Any centered two-effect report has the same aggregate before and after compression.
Uncentered reports have an explicit correction determined by their zero-effect
baseline and the number of removed labels. Spectral Hellinger affinities, all
positive integer power distances, and the existing finite-POVM Hellinger score
are therefore unchanged. This sharpens the corpus reconstruction experiment
inspired by Gomes, arXiv:2607.24901v1. -/

open scoped Matrix Classical
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Every two-effect report, centered at the zero effects, has exactly the same aggregate after compression. -/
theorem gomesFockThreshold_centeredReport_compression {d e k l n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (C : Fin l → Matrix (Fin (e+1)) (Fin (e+1)) ℂ) (cuts : Fin n → ℝ)
    (report : Matrix (Fin (d+1)) (Fin (d+1)) ℂ → Matrix (Fin (e+1)) (Fin (e+1)) ℂ → ℝ) :
    (∑ r, (report (gomesFockThresholdCompressedEffect B cuts r)
      (gomesFockThresholdCompressedEffect C cuts r) - report 0 0)) =
    ∑ bits, (report (gomesFockThresholdEffect B cuts bits)
      (gomesFockThresholdEffect C cuts bits) - report 0 0) := by
  apply Fintype.sum_of_injective (gomesFockThresholdBoundaryRecord cuts)
    (gomesFockThresholdBoundaryRecord_injective cuts)
  · intro bits hbits
    have hn : ¬(gomesFockThresholdCell cuts bits).Nonempty := by
      intro hcell
      obtain ⟨r,hr⟩ := (gomesFockThresholdCell_boundary_classification cuts bits).mp hcell
      exact hbits ⟨r,hr⟩
    have he : gomesFockThresholdCell cuts bits = ∅ := by
      ext t
      constructor
      · intro ht
        exact False.elim (hn ⟨t,ht⟩)
      · intro ht
        cases ht
    simp only [gomesFockThresholdEffect_eq_window,he,gomesFockWindowMatrix_empty,sub_self]
  · intro r
    rfl

/-- Uncentered aggregate scores differ by exactly the number of impossible labels times their empty-record baseline. -/
theorem gomesFockThreshold_report_baseline_correction {d e k l n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (C : Fin l → Matrix (Fin (e+1)) (Fin (e+1)) ℂ) (cuts : Fin n → ℝ)
    (report : Matrix (Fin (d+1)) (Fin (d+1)) ℂ → Matrix (Fin (e+1)) (Fin (e+1)) ℂ → ℝ) :
    (∑ bits, report (gomesFockThresholdEffect B cuts bits) (gomesFockThresholdEffect C cuts bits)) =
      (∑ r, report (gomesFockThresholdCompressedEffect B cuts r)
        (gomesFockThresholdCompressedEffect C cuts r)) +
      (((2^n : ℕ) : ℝ) - (((gomesFockThresholdCutSet cuts).card+1 : ℕ) : ℝ)) * report 0 0 := by
  have h := gomesFockThreshold_centeredReport_compression B C cuts report
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  rw [gomesFockThresholdCompressedPOVM_outcome_count,gomesFockThresholdOutcome_card] at h
  linear_combination -h

/-- Spectral Hellinger affinity is exactly preserved, including comparison of sources with different dimensions. -/
theorem gomesFockThreshold_hellinger_compression {d e k l n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (C : Fin l → Matrix (Fin (e+1)) (Fin (e+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (y : Fin (e+1) → ℂ) :
    (∑ r, Real.sqrt (gomesFockWindowMass B (gomesFockThresholdCompressedCell cuts r) x *
      gomesFockWindowMass C (gomesFockThresholdCompressedCell cuts r) y)) =
    ∑ bits, Real.sqrt (gomesFockWindowMass B (gomesFockThresholdCell cuts bits) x *
      gomesFockWindowMass C (gomesFockThresholdCell cuts bits) y) := by
  have h := gomesFockThreshold_centeredReport_compression B C cuts
    (fun M N => Real.sqrt ((star x ⬝ᵥ (M*ᵥx)).re * (star y ⬝ᵥ (N*ᵥy)).re))
  simpa [gomesFockThresholdCompressedEffect_eq_original,gomesFockThresholdEffect_eq_window,
    gomesFockWindowMatrix_quadratic,gomesFockThresholdCompressedCell] using h

/-- Every positive integer power distance between spectral records is unchanged by compression. -/
theorem gomesFockThreshold_powerDistance_compression {d e k l n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (C : Fin l → Matrix (Fin (e+1)) (Fin (e+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (y : Fin (e+1) → ℂ) (m : ℕ) :
    (∑ r, |gomesFockWindowMass B (gomesFockThresholdCompressedCell cuts r) x -
      gomesFockWindowMass C (gomesFockThresholdCompressedCell cuts r) y|^(m+1)) =
    ∑ bits, |gomesFockWindowMass B (gomesFockThresholdCell cuts bits) x -
      gomesFockWindowMass C (gomesFockThresholdCell cuts bits) y|^(m+1) := by
  have h := gomesFockThreshold_centeredReport_compression B C cuts
    (fun M N => |(star x ⬝ᵥ (M*ᵥx)).re - (star y ⬝ᵥ (N*ᵥy)).re|^(m+1))
  simpa [gomesFockThresholdCompressedEffect_eq_original,gomesFockThresholdEffect_eq_window,
    gomesFockWindowMatrix_quadratic,gomesFockThresholdCompressedCell] using h

/-- The existing finite-POVM Hellinger score has exactly the same value on the compressed readout. -/
theorem gomesFockThresholdPOVM_hellinger_compression {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (Y Z : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    finiteHellingerAffinity
      (fun j => ((Y*(gomesFockThresholdCompressedPOVM B cuts).effect j).trace).re)
      (fun j => ((Z*(gomesFockThresholdCompressedPOVM B cuts).effect j).trace).re) =
    finiteHellingerAffinity
      (fun j => ((Y*(gomesFockThresholdPOVM B cuts).effect j).trace).re)
      (fun j => ((Z*(gomesFockThresholdPOVM B cuts).effect j).trace).re) := by
  unfold finiteHellingerAffinity
  change (∑ j, Real.sqrt ((Y*gomesFockThresholdCompressedEffect B cuts
        ((Fintype.equivFin (Option ↑(gomesFockThresholdCutSet cuts))).symm j)).trace.re *
      (Z*gomesFockThresholdCompressedEffect B cuts
        ((Fintype.equivFin (Option ↑(gomesFockThresholdCutSet cuts))).symm j)).trace.re)) =
    ∑ j, Real.sqrt ((Y*gomesFockThresholdEffect B cuts
        ((Fintype.equivFin (Fin n → Bool)).symm j)).trace.re *
      (Z*gomesFockThresholdEffect B cuts ((Fintype.equivFin (Fin n → Bool)).symm j)).trace.re)
  rw [(Fintype.equivFin (Option ↑(gomesFockThresholdCutSet cuts))).symm.sum_comp
      (fun r => Real.sqrt ((Y*gomesFockThresholdCompressedEffect B cuts r).trace.re *
        (Z*gomesFockThresholdCompressedEffect B cuts r).trace.re)),
    (Fintype.equivFin (Fin n → Bool)).symm.sum_comp
      (fun bits => Real.sqrt ((Y*gomesFockThresholdEffect B cuts bits).trace.re *
        (Z*gomesFockThresholdEffect B cuts bits).trace.re))]
  have h := gomesFockThreshold_centeredReport_compression B B cuts
    (fun M N => Real.sqrt ((Y*M).trace.re * (Z*N).trace.re))
  simpa using h

end GaloisForLFunctions.HTGeometry
