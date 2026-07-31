import GaloisForLFunctions.RHTower.WeldSectionDefectPrimeLogGate
import GaloisForLFunctions.RHTower.PrimeIsingTreeFKExpansion

/-!
# Two remaining premise witnesses: global choice, and bond configurations

The global-choice hypothesis of the polarization gate — that a section defect is the coboundary of
a single global cochain — is realized by the global-choice defect itself, by definition.  And the
bond-configuration membership hypothesis of the FK layer is never vacuous: the FK coefficients of a
tree's bond configurations sum to one, so the configuration list cannot be empty.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The global-choice defect is a global coboundary, so the global-choice hypothesis is
realized. -/
theorem SectionDefect.globalChoiceDefect_exists_twoCoboundary
    {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] (b : G → A) :
    ∃ c : G → A, (SectionDefect.globalChoiceDefect (G := G) (A := A) b).defect =
      twoCoboundary c :=
  ⟨b, rfl⟩

/-- Every finite prime Ising tree has at least one bond configuration: the FK coefficients of its
configurations sum to one, which an empty list cannot do. -/
theorem treeBondConfigurations_ne_nil (T : PrimeIsingTree) :
    treeBondConfigurations T ≠ [] := by
  intro hnil
  have hsum := sum_treeBondCoefficient_treeBondConfigurations T
  rw [hnil] at hsum
  simp at hsum

/-- Hence the bond-configuration membership hypothesis is never vacuous. -/
theorem exists_mem_treeBondConfigurations (T : PrimeIsingTree) :
    ∃ B : PrimeIsingBondTree, B ∈ treeBondConfigurations T := by
  rcases hlist : treeBondConfigurations T with _ | ⟨B, rest⟩
  · exact absurd hlist (treeBondConfigurations_ne_nil T)
  · exact ⟨B, by simp⟩

end

end GaloisForLFunctions.RHTower
