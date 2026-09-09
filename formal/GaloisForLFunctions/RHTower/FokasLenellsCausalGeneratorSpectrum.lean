import GaloisForLFunctions.RHTower.FokasLenellsCausalComplexResolvent
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundaryEigenvectors

/-! Exact spectrum of the actual unbounded causal generator. The resolvent set is defined by
bounded two-sided inverses on its actual maximal domain, not by a bounded-operator surrogate. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual unbounded resolvent set: the complex shift has a bounded two-sided inverse. -/
def causalGeneratorResolventSet : Set ℂ :=
  {z | ∃ R : hardyL2ᗮ →L[ℂ] causalGeneratorDomain,
    (∀ u : hardyL2ᗮ, causalComplexGeneratorShift z (R u) = u) ∧
    (∀ u : causalGeneratorDomain, R (causalComplexGeneratorShift z u) = u)}

/-- Spectrum of the actual maximal causal generator, complementing its bounded-inverse set. -/
def causalGeneratorSpectrum : Set ℂ := causalGeneratorResolventSetᶜ

/-- The explicit Neumann construction places the entire open right half-plane in the resolvent. -/
theorem causalGenerator_rightHalfPlane_mem_resolvent (z : {z : ℂ // 0 < z.re}) :
    z.val ∈ causalGeneratorResolventSet :=
  ⟨causalComplexResolvent z, causalComplexGeneratorShift_resolvent z,
    causalComplexResolvent_generatorShift z⟩

/-- The actual rational eigenvectors place every open-left-half-plane point in the spectrum. -/
theorem causalGenerator_leftHalfPlane_mem_spectrum (z : {z : ℂ // z.re < 0}) :
    z.val ∈ causalGeneratorSpectrum := by
  rintro ⟨R, _, hleft⟩
  have hs : causalComplexGeneratorShift z.val (causalLeftEigenvector z) = 0 := by
    change z.val • (causalLeftEigenvector z).val - causalGenerator (causalLeftEigenvector z) = 0
    rw [causalGenerator_leftEigenvector, sub_self]
  have h := hleft (causalLeftEigenvector z)
  rw [hs, map_zero] at h
  exact causalLeftEigenvector_ne_zero z h.symm

/-- The explicit unit approximate eigenvectors rule out bounded inverses at every boundary point. -/
theorem causalGenerator_imaginaryAxis_mem_spectrum (ω : ℝ) :
    (ω : ℂ)*I ∈ causalGeneratorSpectrum := by
  rintro ⟨R, _, hleft⟩
  have hb (b : ℝ) : 1 ≤ ‖R‖ * Real.exp b := by
    have h := R.le_opNorm
      (causalComplexGeneratorShift ((ω : ℂ)*I) (causalBoundaryEigenvector b ω))
    rw [hleft, norm_causalBoundaryEigenvector,
      norm_causalComplexGeneratorShift_boundaryEigenvector] at h
    exact h
  have ht : Tendsto (fun b : ℝ => ‖R‖ * Real.exp b) atBot (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_atBot
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hb)
  linarith

/-- A complex number admits an actual bounded causal-generator inverse exactly when its real part
is positive. -/
theorem causalGenerator_mem_resolvent_iff (z : ℂ) :
    z ∈ causalGeneratorResolventSet ↔ 0 < z.re := by
  constructor
  · intro h
    by_contra hp
    have hle : z.re ≤ 0 := le_of_not_gt hp
    rcases lt_or_eq_of_le hle with hn | hz
    · exact causalGenerator_leftHalfPlane_mem_spectrum ⟨z, hn⟩ h
    · have he : z = (z.im : ℂ)*I := by
        apply Complex.ext <;> simp [hz]
      rw [he] at h
      exact causalGenerator_imaginaryAxis_mem_spectrum z.im h
  · intro hp
    exact causalGenerator_rightHalfPlane_mem_resolvent ⟨z, hp⟩

/-- The actual generator spectrum is exactly characterized by nonpositive real part. -/
theorem causalGenerator_mem_spectrum_iff (z : ℂ) :
    z ∈ causalGeneratorSpectrum ↔ z.re ≤ 0 := by
  change (z ∉ causalGeneratorResolventSet) ↔ _
  rw [causalGenerator_mem_resolvent_iff, not_lt]

/-- The completed causal Cauchy generator has precisely the closed left half-plane as its spectrum. -/
theorem causalGeneratorSpectrum_eq_closedLeftHalfPlane :
    causalGeneratorSpectrum = {z : ℂ | z.re ≤ 0} :=
  Set.ext causalGenerator_mem_spectrum_iff

/-- The actual bounded-inverse set is precisely the open right half-plane. -/
theorem causalGeneratorResolventSet_eq_openRightHalfPlane :
    causalGeneratorResolventSet = {z : ℂ | 0 < z.re} :=
  Set.ext causalGenerator_mem_resolvent_iff

end
end RHTower.FokasLenells
