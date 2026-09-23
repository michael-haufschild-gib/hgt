import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedExactSpectrum
import GaloisForLFunctions.RHTower.FokasLenellsCausalPointSpectrum

/-! Exact point spectrum and imaginary-axis injectivity of the actual bounded derivative shift. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fokasLenellsCausalBoundedPointSpectrumInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance fokasLenellsCausalBoundedPointSpectrumInst2 : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance fokasLenellsCausalBoundedPointSpectrumInst3 : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance fokasLenellsCausalBoundedPointSpectrumInst4 : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance fokasLenellsCausalBoundedPointSpectrumInst5 : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance fokasLenellsCausalBoundedPointSpectrumInst6 : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance fokasLenellsCausalBoundedPointSpectrumInst7 : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance fokasLenellsCausalBoundedPointSpectrumInst8 : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance fokasLenellsCausalBoundedPointSpectrumInst9 : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- Each bounded derivative coordinate as an element of the actual maximal generator domain. -/
def causalBoundedChainDomainCoordinate (j : ℕ) (u : causalBoundedChain) : causalGeneratorDomain :=
  causalBoundedEntireDomain j u 0

/-- The maximal-domain view retains the literal original Hilbert-valued coordinate. -/
theorem causalBoundedChainDomainCoordinate_val (j : ℕ) (u : causalBoundedChain) :
    (causalBoundedChainDomainCoordinate j u).val = causalBoundedChainCoordinate j u :=
  causalBoundedEntireOrbit_zero j u

/-- The genuine maximal generator sends each bounded coordinate to its actual successor. -/
theorem causalGenerator_boundedChainDomainCoordinate (j : ℕ) (u : causalBoundedChain) :
    causalGenerator (causalBoundedChainDomainCoordinate j u) = causalBoundedChainCoordinate (j+1) u :=
  (causalGenerator_boundedEntireDomain j u 0).trans (causalBoundedEntireOrbit_zero (j+1) u)

private theorem initial_domain_ne_zero {u : causalBoundedChain} (hu : u ≠ 0) :
    causalBoundedChainDomainCoordinate 0 u ≠ 0 := by
  intro hd
  apply hu
  apply causalBoundedChainCoordinate_zero_injective
  have he := congrArg (fun v : causalGeneratorDomain => v.val) hd
  exact (causalBoundedChainDomainCoordinate_val 0 u).symm.trans
    (he.trans (map_zero (causalBoundedChainCoordinate 0)).symm)

/-- Actual point spectrum of the bounded genuine derivative shift. -/
def causalBoundedChainPointSpectrum : Set ℂ :=
  {z | ∃ u : causalBoundedChain, u ≠ 0 ∧ causalBoundedChainShift u = z • u}

/-- Genuine bounded-shift eigenvalues are exactly the strictly-left part of the closed unit disk. -/
theorem causalBoundedChainShift_mem_pointSpectrum_iff (z : ℂ) :
    z ∈ causalBoundedChainPointSpectrum ↔ z.re < 0 ∧ ‖z‖ ≤ 1 := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hg : causalGenerator (causalBoundedChainDomainCoordinate 0 u) =
        z • (causalBoundedChainDomainCoordinate 0 u).val := by
      have hcoord := congrArg (fun v : causalBoundedChain => causalBoundedChainCoordinate 0 v) he
      exact (causalGenerator_boundedChainDomainCoordinate 0 u).trans
        ((causalBoundedChainShift_coordinate 0 u).symm.trans
          (hcoord.trans (((causalBoundedChainCoordinate 0).map_smul z u).trans
            (congrArg (fun v : hardyL2ᗮ => z • v) (causalBoundedChainDomainCoordinate_val 0 u).symm))))
    have hr := (causalGenerator_mem_pointSpectrum_iff z).mp
      ⟨causalBoundedChainDomainCoordinate 0 u, initial_domain_ne_zero hu, hg⟩
    have hn : ‖z‖*‖u‖ ≤ ‖u‖ := (norm_smul z u).symm.trans_le
      ((congrArg (fun v : causalBoundedChain => ‖v‖) he).symm.trans_le (causalBoundedChainShift_norm_le u))
    have hbound : ‖z‖ ≤ 1 := (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hu)).mp
      (hn.trans_eq (one_mul ‖u‖).symm)
    exact ⟨hr, hbound⟩
  · intro hz
    exact ⟨causalBoundedDiskEigenchain ⟨z, hz⟩, causalBoundedDiskEigenchain_ne_zero _,
      causalBoundedChainShift_diskEigenchain _⟩

/-- The full actual point spectrum excludes the imaginary diameter while retaining the left circular arc. -/
theorem causalBoundedChainPointSpectrum_eq :
    causalBoundedChainPointSpectrum = {z : ℂ | z.re < 0 ∧ ‖z‖ ≤ 1} :=
  Set.ext causalBoundedChainShift_mem_pointSpectrum_iff

/-- Every purely imaginary scalar shift is injective on the genuine bounded-chain space. -/
theorem causalBoundedChainShift_imaginary_injective (ω : ℝ) :
    Function.Injective (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) ((ω : ℂ)*I) -
      causalBoundedChainShift) := by
  intro u v h
  by_cases hd : u-v = 0
  · exact sub_eq_zero.mp hd
  · let F : causalBoundedChain →L[ℂ] causalBoundedChain :=
      algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) ((ω : ℂ)*I) - causalBoundedChainShift
    have he : F (u-v) = 0 := (F.map_sub u v).trans (sub_eq_zero.mpr h)
    change ((ω : ℂ)*I) • (u-v) - causalBoundedChainShift (u-v) = 0 at he
    have hp := ((causalBoundedChainShift_mem_pointSpectrum_iff ((ω : ℂ)*I)).mp
      ⟨u-v, hd, (sub_eq_zero.mp he).symm⟩).1
    have hz : ((ω : ℂ)*I).re = 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero]
    exact False.elim (lt_irrefl (0 : ℝ) (hz ▸ hp))

/-- Imaginary shifted equations are onto exactly outside the actual spectral diameter. -/
theorem causalBoundedChainShift_imaginary_surjective_iff (ω : ℝ) :
    Function.Surjective (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) ((ω : ℂ)*I) -
      causalBoundedChainShift) ↔ 1 < |ω| := by
  let F : causalBoundedChain →L[ℂ] causalBoundedChain :=
    algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) ((ω : ℂ)*I) - causalBoundedChainShift
  have hb : Function.Surjective F ↔ IsUnit F :=
    ⟨fun hs => ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨causalBoundedChainShift_imaginary_injective ω, hs⟩,
      fun h => (ContinuousLinearMap.isUnit_iff_bijective.mp h).2⟩
  have h := hb.trans (causalBoundedChainShift_isUnit_iff ((ω : ℂ)*I))
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, lt_self_iff_false, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, false_or] using h

/-- The actual bounded derivative shift has trivial kernel. -/
theorem causalBoundedChainShift_injective : Function.Injective causalBoundedChainShift := by
  intro u v h
  apply causalBoundedChainShift_imaginary_injective 0
  change ((0 : ℂ)*I) • u-causalBoundedChainShift u = ((0 : ℂ)*I) • v-causalBoundedChainShift v
  simp only [zero_mul, zero_smul, zero_sub, h]

/-- The genuine bounded derivative shift is injective but fails to be onto its own chain space. -/
theorem causalBoundedChainShift_not_surjective : ¬ Function.Surjective causalBoundedChainShift := by
  intro hs
  have hu : IsUnit causalBoundedChainShift := ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨causalBoundedChainShift_injective, hs⟩
  have hz : (0 : ℂ) ∈ spectrum ℂ causalBoundedChainShift :=
    (causalBoundedChainShift_mem_spectrum_iff 0).mpr ⟨by simp, by simp⟩
  apply spectrum.mem_iff.mp hz
  simpa only [map_zero, zero_sub] using hu.neg

end
end RHTower.FokasLenells
