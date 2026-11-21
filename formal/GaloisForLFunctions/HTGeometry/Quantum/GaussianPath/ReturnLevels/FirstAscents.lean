import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.CrossingVisits
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstAscent

/-! # The strictly ordered first ascents at the same prescribed tolerance -/
open MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels
noncomputable section

/-- The first time a larger circuit set reaches the prescribed distance
is strictly later, simultaneously for every pair of budgets separated by
one sweep up to the exponential first-ascent threshold. -/
theorem gaussian_first_ascent_order :
    ∀ᵐ ε : ℝ ∂volume, ε ∈ Ioc (0:ℝ) (13/10) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let x := pathPauliDisorderShell ω (k+1)
        let N := k+3
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
        let J := Fintype.card (PathLabel (k+1))
        ∀ s : ℕ, s+J ≤ 2^N/(32*(N+1)) →
          ∃ a b : ℝ, 0 < a ∧ a < b ∧ orbitCircuitDistance H s a=ε ∧
            (∀ t ∈ Ico 0 a, orbitCircuitDistance H s t < ε) ∧ orbitCircuitDistance H (s+J) b=ε ∧
            ∀ t ∈ Ico 0 b, orbitCircuitDistance H (s+J) t < ε := by
  obtain ⟨_,hasc⟩ := SharpOccupation.gaussian_first_ascent_occupation
  filter_upwards [gaussian_prescribed_levels] with ε hε htol
  filter_upwards [hasc,hε] with ω hω hreg
  filter_upwards [hω] with k hk
  intro x N H J s hs
  obtain ⟨a,ha,hae,hprev,_,_⟩ := hk s ((Nat.le_add_right s J).trans hs) ε htol
  obtain ⟨b,hb,hbe,hprev',_,_⟩ := hk (s+J) hs ε htol
  have hle : orbitCircuitDistance H (s+J) b ≤ orbitCircuitDistance H s b := by
    simpa only [sub_self,abs_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero] using path_increment x s b b
  have hlt : orbitCircuitDistance H (s+J) b < orbitCircuitDistance H s b := hle.lt_of_ne fun he =>
    hreg (k+1) (mem_iUnion.mpr ⟨s,b,he.symm,he.symm.trans hbe⟩)
  refine ⟨a,b,ha,?_,hae,hprev,hbe,hprev'⟩
  rcases lt_trichotomy a b with h|h|h
  · exact h
  · exact False.elim ((hbe ▸ hlt).ne' (h ▸ hae))
  · exact False.elim ((hprev b ⟨hb.le,h⟩).not_ge ((hbe ▸ hlt).le))

#print axioms gaussian_first_ascent_order
end
end GaloisForLFunctions.HTGeometry.ReturnLevels
