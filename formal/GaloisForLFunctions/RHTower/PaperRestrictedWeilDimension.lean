import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanDenseFormCore
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap

/-! # Infinite dimension of the actual restricted-Weil form domain

Infinitely many orthonormal shells fit inside every positive aperture. Density of
the complete form embedding then excludes finite dimension of its source space.
-/

noncomputable section

namespace RHTower.PaperRestrictedWeil

theorem shell_mem_aperture (a : SuzukiPositiveAperture) (n : ℕ) :
    (evenShellVectorEven (a.val / 2) a.val (by linarith [a.property]) n : SoninL2) ∈
      suzukiApertureHilbert a := by
  refine ⟨(evenShellVectorEven (a.val / 2) a.val (by linarith [a.property]) n : SoninL2), ?_⟩
  exact congrArg Subtype.val
    (evenIndicatorCutoff_evenShellVectorEven_of_le (a.val / 2) a.val a.val
      (by linarith [a.property]) le_rfl n)

def apertureShell (a : SuzukiPositiveAperture) (n : ℕ) : suzukiApertureHilbert a :=
  ⟨evenShellVectorEven (a.val / 2) a.val (by linarith [a.property]) n,
    shell_mem_aperture a n⟩

theorem apertureShell_orthonormal (a : SuzukiPositiveAperture) :
    Orthonormal ℂ (apertureShell a) := by
  exact (evenShellVector_orthonormal (a.val / 2) a.val
    (by linarith [a.property]) (by linarith [a.property])).codRestrict
      (suzukiApertureHilbert a) (shell_mem_aperture a)

theorem aperture_not_finiteDimensional (a : SuzukiPositiveAperture) :
    ¬ FiniteDimensional ℂ (suzukiApertureHilbert a) := by
  intro h
  letI := h
  exact Module.Finite.not_linearIndependent_of_infinite (apertureShell a)
    (apertureShell_orthonormal a).linearIndependent

theorem formDomain_not_finiteDimensional (a : SuzukiPositiveAperture) :
    ¬ FiniteDimensional ℂ (CCMArchimedeanFormDomain a) := by
  intro h
  letI := h
  let J := (ccmArchimedeanFormToAperture a).toLinearMap
  have hclosed : IsClosed (Set.range J) := J.range.closed_of_finiteDimensional
  have hdense : Dense (Set.range J) := denseRange_ccmArchimedeanFormToAperture a
  have hsurj : Function.Surjective J := by
    intro x
    have hx : x ∈ Set.range J := by
      rw [← hclosed.closure_eq]
      exact hdense x
    exact hx
  exact aperture_not_finiteDimensional a (FiniteDimensional.of_surjective J hsurj)

end RHTower.PaperRestrictedWeil
