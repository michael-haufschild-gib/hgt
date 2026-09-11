import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanParametricVacuity

/-!
# Saturation of the Big-Witt source energy graph

The finite prime-energy reporter has coefficient `A / p` on a packet whose left prime is `p`.
Its graph over the completed one-leg source is dense in the full source-energy Hilbert product
exactly when `A` is nonzero. Indeed, a nonzero energy component of a joint annihilator would
produce a bounded extension of the reporter, contradicting the actual fixed-prime row limits.
The source component then vanishes by density of finite packet admission.

Thus adding the reporter as another graph coordinate admits every energy value over every source
vector when the retained coefficient is nonzero. At a Xi copy, full saturation is exactly failure
of critical-line placement. This classifies an enlarged source domain; it does not identify its
energy projection with a boundary-annihilating physical reader.
-/

open Complex Filter Function Set Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.HedenmalmThetaSource
noncomputable section

/-- One-leg source together with its proposed scalar energy coordinate. -/
abbrev DeningerBigWittPrimeEnergyGraphSpace := WithLp 2 (DeningerBigWittCrossPairSingularOneLegGraph × ℂ)

/-- Joint finite graph of literal source admission and the prime reciprocal reporter. -/
def deningerBigWittPrimeEnergyGraph (A : ℝ) : Submodule ℂ DeningerBigWittPrimeEnergyGraphSpace :=
  linearGraphSubmodule deningerBigWittCrossPairFiniteOneLegGraphAdmission
    (primeLabelledEnergyReporter (fun p => A / (p : ℕ)))

/-- A nonzero retained coefficient makes the enlarged graph dense in the entire product. -/
theorem deningerBigWittPrimeEnergyGraph_closure_eq_top (A : ℝ) :
    A ≠ 0 → (deningerBigWittPrimeEnergyGraph A).topologicalClosure = ⊤ := by
  intro hA
  apply linearGraphSubmodule_closure_eq_top_of_annihilator
  intro x y h
  have hy : y = 0 := by
    by_contra hy
    have hstar : (starRingEnd ℂ) y ≠ 0 := by simpa using hy
    let reporter : DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ] ℂ :=
      (-((starRingEnd ℂ) y)⁻¹) • innerSL ℂ x
    have hagree (d : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
        reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission d) =
          primeLabelledEnergyReporter (fun p => A / (p : ℕ)) d := by
      have hc := congrArg (starRingEnd ℂ) (h d)
      simp only [map_add, inner_conj_symm, map_zero] at hc
      rw [RCLike.inner_apply] at hc
      have hi := eq_neg_of_add_eq_zero_left hc
      change -((starRingEnd ℂ) y)⁻¹ * inner ℂ x
        (deningerBigWittCrossPairFiniteOneLegGraphAdmission d) = _
      rw [hi]
      field_simp
    exact hA ((abstractPrimeReciprocalSourceDescends_iff A).1
      ⟨reporter, fun a n => hagree _⟩)
  refine ⟨?_, hy⟩
  apply deningerBigWittCrossPairFiniteOneLegGraphAdmission_dense.eq_zero_of_inner_right ℂ
  intro d
  simpa [hy] using h d

/-- Exact source-parameter classification of full graph saturation. -/
theorem deningerBigWittPrimeEnergyGraph_closure_eq_top_iff (A : ℝ) :
    (deningerBigWittPrimeEnergyGraph A).topologicalClosure = ⊤ ↔ A ≠ 0 := by
  constructor
  · intro hfull hA
    subst A
    have hE : primeLabelledEnergyReporter (fun p => (0 : ℝ) / (p : ℕ)) = 0 := by
      apply Finsupp.lhom_ext
      intro i z
      simp
    let project : DeningerBigWittPrimeEnergyGraphSpace →L[ℂ] ℂ :=
      WithLp.sndL 2 ℂ DeningerBigWittCrossPairSingularOneLegGraph ℂ
    have hsubset : (deningerBigWittPrimeEnergyGraph 0).topologicalClosure ≤ project.ker := by
      apply Submodule.topologicalClosure_minimal
      · rintro z ⟨d, rfl⟩
        change primeLabelledEnergyReporter (fun p => (0 : ℝ) / (p : ℕ)) d = 0
        rw [hE]
        rfl
      · exact isClosed_eq project.continuous continuous_const
    have hbad := hsubset (show WithLp.toLp 2
        ((0 : DeningerBigWittCrossPairSingularOneLegGraph), (1 : ℂ)) ∈
        (deningerBigWittPrimeEnergyGraph 0).topologicalClosure from by rw [hfull]; trivial)
    exact one_ne_zero (show (1 : ℂ) = 0 from hbad)
  · exact deningerBigWittPrimeEnergyGraph_closure_eq_top A

/-- Full energy-graph saturation at a Xi copy occurs exactly off the critical line. -/
theorem xiGammaSixWoldJordanEnergyGraph_closure_eq_top_iff (q : XiZeroCopy) :
    (deningerBigWittPrimeEnergyGraph (xiGammaSixWoldJordanHarmonicWeight q)).topologicalClosure = ⊤ ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [deningerBigWittPrimeEnergyGraph_closure_eq_top_iff]
  exact not_congr ((xiGammaSixWoldJordanHarmonicWeight_eq_zero_iff q).trans
    (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1))

end
end RHTower.HedenmalmThetaSource
