import GaloisForLFunctions.HTGeometry.CompactOperatorGeneralSpectrum
import GaloisForLFunctions.HTGeometry.RieszProjectionSpectral

namespace GaloisForLFunctions.HTGeometry

open Metric Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- A circular Riesz window for a compact operator, separated from the only possible
non-eigenvalue spectral point `0`, vanishes exactly when its closed window is resolvent. -/
theorem rieszProjection_eq_zero_iff_closedBall_subset_resolvent_of_compact
    {T : H →L[ℂ] H} (hT : IsCompactOperator T) {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hboundary : ∀ mu ∈ sphere c r, mu ∈ resolventSet ℂ T)
    (hzero : 0 ∉ closedBall c r) :
    rieszProjection T c r = 0 ↔ closedBall c r ⊆ resolventSet ℂ T := by
  constructor
  · intro hP mu hmu
    rcases lt_or_eq_of_le (mem_closedBall.mp hmu) with hinside | hsphere
    · by_contra hnures
      have hspec : mu ∈ spectrum ℂ T := by simpa [spectrum] using hnures
      have hmu0 : mu ≠ 0 := by
        intro h
        exact hzero (h ▸ hmu)
      obtain ⟨v, hv⟩ := (hT.hasEigenvalue_iff_mem_spectrum hmu0).2 hspec |>.exists_hasEigenvector
      have hTv : T v = mu • v := Module.End.mem_eigenspace_iff.mp hv.1
      have hpoly : ((T - mu • (1 : H →L[ℂ] H)) ^ 1) v = 0 := by
        simpa using sub_eq_zero.mpr hTv
      have hfix := rieszProjection_apply_eq_self hr hboundary
        (mem_ball.mpr hinside) hpoly
      rw [hP, zero_apply] at hfix
      exact hv.2 hfix.symm
    · exact hboundary mu hsphere
  · intro hsubset
    exact rieszProjection_eq_zero_of_closedBall_subset T hr hsubset

/-- Open-window form: under boundary resolvent and separation from zero, a compact-operator
Riesz projection vanishes exactly when the open window contains no spectrum. -/
theorem rieszProjection_eq_zero_iff_ball_inter_spectrum_empty_of_compact
    {T : H →L[ℂ] H} (hT : IsCompactOperator T) {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hboundary : ∀ mu ∈ sphere c r, mu ∈ resolventSet ℂ T)
    (hzero : 0 ∉ closedBall c r) :
    rieszProjection T c r = 0 ↔ ball c r ∩ spectrum ℂ T = ∅ := by
  rw [rieszProjection_eq_zero_iff_closedBall_subset_resolvent_of_compact
    hT hr hboundary hzero]
  constructor
  · intro hsubset
    apply Set.Subset.antisymm
    · rintro mu ⟨hball, hspec⟩
      exact (hspec (hsubset (mem_ball.mp hball |>.le))).elim
    · exact Set.empty_subset _
  · intro hempty mu hclosed
    rcases lt_or_eq_of_le (mem_closedBall.mp hclosed) with hinside | hsphere
    · by_contra hnot
      have hspec : mu ∈ spectrum ℂ T := by simpa [spectrum] using hnot
      have : mu ∈ ball c r ∩ spectrum ℂ T := ⟨mem_ball.mpr hinside, hspec⟩
      simpa [hempty] using this
    · exact hboundary mu hsphere

end

end GaloisForLFunctions.HTGeometry
