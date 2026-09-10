import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialPeriodicity

/-! Actual entire polynomial evolution on the genuine bounded Cauchy derivative space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialClockLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialClockChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialClockChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialClockChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialClockEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPolynomialClockEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialClockEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPolynomialClockEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPolynomialClockEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open Polynomial

private theorem constant_nonzero_period (c : ℂ) :
    ∃ z : ℂ, z ≠ 0 ∧ causalBoundedPolynomialExponential (C c) z = 1 := by
  by_cases hc : c = 0
  · subst c
    refine ⟨1, one_ne_zero, (causalBoundedPolynomialExponential_eq_one_iff (C 0) 1).mpr ⟨0, ?_⟩⟩
    simp
  · have hper : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
    refine ⟨(2*Real.pi*Complex.I)/c, div_ne_zero hper hc,
      (causalBoundedPolynomialExponential_eq_one_iff (C c) ((2*Real.pi*Complex.I)/c)).mpr ⟨1, ?_⟩⟩
    have hs := Polynomial.smul_C ((2*Real.pi*Complex.I : ℂ)/c) c
    have hm : ((2*Real.pi*Complex.I : ℂ)/c)*c = 2*Real.pi*Complex.I := div_mul_cancel₀ _ hc
    simpa only [smul_eq_mul, Int.cast_one, one_mul] using hs.trans (congrArg Polynomial.C hm)

/-- Complex time is faithfully distinguished by the actual polynomial flow exactly for nonconstant polynomials. -/
theorem causalBoundedPolynomialExponential_injective_time_iff (p : ℂ[X]) :
    Function.Injective (causalBoundedPolynomialExponential p) ↔ p.natDegree ≠ 0 := by
  constructor
  · intro hinj hd
    obtain ⟨z, hz, he⟩ := constant_nonzero_period (p.coeff 0)
    have hp := Polynomial.eq_C_of_natDegree_eq_zero hd
    have hs : causalBoundedPolynomialExponential p z = 1 :=
      (congrArg (fun r : ℂ[X] => causalBoundedPolynomialExponential r z) hp).trans he
    exact hz (hinj (hs.trans (causalBoundedPolynomialExponential_zero p).symm))
  · intro hp z w he
    obtain ⟨n, hn⟩ := (causalBoundedPolynomialExponential_eq_iff p p z w).mp he
    by_contra hzw
    have hs : (z-w) • p = C ((n : ℂ)*(2*Real.pi*Complex.I)) := (sub_smul z w p).trans hn
    have hd : p.natDegree = 0 :=
      (Polynomial.natDegree_smul p (sub_ne_zero.mpr hzw)).symm.trans
        ((congrArg Polynomial.natDegree hs).trans (Polynomial.natDegree_C _))
    exact hp hd

/-- A nonzero common return time exists exactly for a constant polynomial derivative operator. -/
theorem causalBoundedPolynomialExponential_has_nonzero_period_iff (p : ℂ[X]) :
    (∃ z : ℂ, z ≠ 0 ∧ causalBoundedPolynomialExponential p z = 1) ↔ p.natDegree = 0 := by
  constructor
  · rintro ⟨z, hz, he⟩
    by_contra hp
    have hinj := (causalBoundedPolynomialExponential_injective_time_iff p).mpr hp
    exact hz (hinj (he.trans (causalBoundedPolynomialExponential_zero p).symm))
  · intro hd
    obtain ⟨z, hz, he⟩ := constant_nonzero_period (p.coeff 0)
    have hp := Polynomial.eq_C_of_natDegree_eq_zero hd
    exact ⟨z, hz, (congrArg (fun r : ℂ[X] => causalBoundedPolynomialExponential r z) hp).trans he⟩

/-- Observing the actual flow at one real and one imaginary time determines the entire polynomial generator. -/
theorem causalBoundedPolynomialExponential_two_times_injective :
    Function.Injective (fun p : ℂ[X] =>
      (causalBoundedPolynomialExponential p 1, causalBoundedPolynomialExponential p Complex.I)) := by
  intro p q he
  have hreal := congrArg Prod.fst he
  have himag := congrArg Prod.snd he
  obtain ⟨n, hn⟩ := (causalBoundedPolynomialExponential_one_eq_iff p q).mp hreal
  obtain ⟨m, hm⟩ := (causalBoundedPolynomialExponential_eq_iff p q Complex.I Complex.I).mp himag
  have hs : Complex.I • (p-q) = C ((m : ℂ)*(2*Real.pi*Complex.I)) :=
    (smul_sub Complex.I p q).trans hm
  have ht : Complex.I • (p-q) = C (Complex.I*((n : ℂ)*(2*Real.pi*Complex.I))) :=
    (congrArg (fun r : ℂ[X] => Complex.I • r) hn).trans
      (Polynomial.smul_C Complex.I ((n : ℂ)*(2*Real.pi*Complex.I)))
  have hc := Polynomial.C_injective (ht.symm.trans hs)
  have hr := congrArg Complex.re hc
  norm_num [Complex.mul_re, Complex.mul_im] at hr
  have hnzero : n = 0 := hr
  have hpq : p-q = 0 := hn.trans (by simp only [hnzero, Int.cast_zero, zero_mul, Polynomial.C_0])
  exact sub_eq_zero.mp hpq

end
end RHTower.FokasLenells
