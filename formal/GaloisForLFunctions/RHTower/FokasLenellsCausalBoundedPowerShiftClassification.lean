import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedSquarePointSpectrum

/-! Exact uniqueness and surjectivity boundaries for the higher-order Cauchy shifted equations. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPowerClassificationLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPowerClassificationChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPowerClassificationChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPowerClassificationChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPowerClassificationEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPowerClassificationEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPowerClassificationEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPowerClassificationEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPowerClassificationEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- Uniqueness of every actual shifted power equation is exactly exclusion from its point spectrum. -/
theorem causalBoundedChainShift_pow_shift_injective_iff (m : ℕ) (z : ℂ) :
    Function.Injective (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) z -
      causalBoundedChainShift^m) ↔ z ∉ causalBoundedChainPowerPointSpectrum m := by
  let F : causalBoundedChain →L[ℂ] causalBoundedChain :=
    algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) z - causalBoundedChainShift^m
  constructor
  · intro hi hp
    obtain ⟨u, hu, he⟩ := hp
    have hf : F u = 0 := by
      change z • u - (causalBoundedChainShift^m) u = 0
      exact sub_eq_zero.mpr he.symm
    exact hu (hi (hf.trans (map_zero F).symm))
  · intro hn u v huv
    by_contra hne
    have hd : u-v ≠ 0 := sub_ne_zero.mpr hne
    have hf : F (u-v) = 0 := (F.map_sub u v).trans (sub_eq_zero.mpr huv)
    change z • (u-v) - (causalBoundedChainShift^m) (u-v) = 0 at hf
    exact hn ⟨u-v, hd, (sub_eq_zero.mp hf).symm⟩

/-- At order at least three, a shifted equation has unique solutions exactly at zero or outside the disk. -/
theorem causalBoundedChainShift_higher_shift_injective_iff (n : ℕ) (z : ℂ) :
    Function.Injective (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) z -
      causalBoundedChainShift^(n+3)) ↔ z = 0 ∨ 1 < ‖z‖ := by
  have h := not_congr (causalBoundedChainShift_higher_mem_pointSpectrum_iff n z)
  exact (causalBoundedChainShift_pow_shift_injective_iff (n+3) z).trans
    (by simpa only [not_and_or, not_not, not_le] using h)

/-- Second-order shifted equations also retain uniqueness on the whole nonpositive real radius. -/
theorem causalBoundedChainShift_square_shift_injective_iff (z : ℂ) :
    Function.Injective (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) z -
      causalBoundedChainShift^2 : causalBoundedChain →L[ℂ] causalBoundedChain) ↔ 1 < ‖z‖ ∨ (z.re ≤ 0 ∧ z.im = 0) := by
  have h := not_congr (causalBoundedChainShift_square_mem_pointSpectrum_iff z)
  exact (causalBoundedChainShift_pow_shift_injective_iff 2 z).trans
    (by simpa only [not_and_or, not_or, not_not, not_le, not_lt] using h)

/-- Every nonpositive real shift of the actual second derivative is injective. -/
theorem causalBoundedChainShift_square_negative_injective (t : ℝ≥0) :
    Function.Injective (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) (-(t : ℂ)) -
      causalBoundedChainShift^2 : causalBoundedChain →L[ℂ] causalBoundedChain) := by
  apply (causalBoundedChainShift_square_shift_injective_iff (-(t : ℂ))).mpr
  right
  constructor
  · change -(t : ℝ) ≤ 0
    exact neg_nonpos.mpr t.property
  · simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]

/-- Along the negative real axis, unique second-order solutions exist for all data exactly beyond radius one. -/
theorem causalBoundedChainShift_square_negative_surjective_iff (t : ℝ≥0) :
    Function.Surjective (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) (-(t : ℂ)) -
      causalBoundedChainShift^2 : causalBoundedChain →L[ℂ] causalBoundedChain) ↔ 1 < (t : ℝ) := by
  let F : causalBoundedChain →L[ℂ] causalBoundedChain :=
    algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) (-(t : ℂ)) - causalBoundedChainShift^2
  have hb : Function.Surjective F ↔ IsUnit F :=
    ⟨fun hs => ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨causalBoundedChainShift_square_negative_injective t, hs⟩,
      fun h => (ContinuousLinearMap.isUnit_iff_bijective.mp h).2⟩
  have h := hb.trans (causalBoundedChainShift_square_isUnit_iff (-(t : ℂ)))
  have hn : ‖-(t : ℂ)‖ = (t : ℝ) :=
    (norm_neg (t : ℂ)).trans (Complex.norm_of_nonneg t.property)
  have ht := congrArg (fun r : ℝ => Function.Surjective F ↔ 1 < r) hn
  exact ht.mp h

/-- The entire missing second-order eigenvalue set is the closed negative-real unit radius. -/
theorem causalBoundedChainShift_square_spectrum_diff_pointSpectrum :
    spectrum ℂ (causalBoundedChainShift^2) \ causalBoundedChainPowerPointSpectrum 2 =
      {z : ℂ | ‖z‖ ≤ 1 ∧ z.re ≤ 0 ∧ z.im = 0} := by
  rw [causalBoundedChainShift_square_spectrum, causalBoundedChainPowerPointSpectrum_square]
  ext z
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, not_and_or, not_or, not_le, not_lt, not_not]
  constructor
  · rintro ⟨hb, hn⟩
    rcases hn with hn | hn
    · exact False.elim ((not_lt_of_ge hb) hn)
    · exact ⟨hb, hn⟩
  · rintro ⟨hb, hr, hi⟩
    exact ⟨hb, Or.inr ⟨hr, hi⟩⟩

end
end RHTower.FokasLenells
