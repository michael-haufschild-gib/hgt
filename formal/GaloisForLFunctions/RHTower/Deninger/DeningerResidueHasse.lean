import GaloisForLFunctions.RHTower.Deninger.DeningerResidueSequence

/-!
# Hasse quotient for the Deninger logarithmic residue sequence

Constant logarithmic stage forms modulo extensions from the divisor are exactly the divisor residue
forms.  This packages exactness and surjectivity as a quotient equivalence, local congruence
criterion, and existence with uniqueness modulo extension.
-/

namespace RHTower

open Complex

noncomputable section

/-- Constant logarithmic forms modulo extensions from the divisor are exactly their residues. -/
noncomputable def deningerResidueHasseQuotientEquiv (r n : ℕ) :
    (((Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) ⧸
      LinearMap.range (deningerExtendForm r (n + 1))) ≃ₗ[ℂ]
        ((Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :=
  (Submodule.quotEquivOfEq _ _
    (LinearMap.exact_iff.mp (deningerResidue_exact_sequence (r := r) (n := n))).symm).trans
      (LinearMap.quotKerEquivOfSurjective
        (deningerResidueForm r n) deningerResidueForm_surjective)

/-- The Deninger residue quotient equivalence is induced by the residue map. -/
@[simp] theorem deningerResidueHasseQuotientEquiv_mk
    (r n : ℕ) (α : (Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    deningerResidueHasseQuotientEquiv r n (Submodule.Quotient.mk α) =
      deningerResidueForm r n α := by
  simp [deningerResidueHasseQuotientEquiv]

/-- Two stage forms agree modulo extension from the divisor exactly when their local residues
agree. -/
theorem deningerResidue_congr_hasse_iff
    (r n : ℕ)
    (α β : (Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    α - β ∈ LinearMap.range (deningerExtendForm r (n + 1)) ↔
      deningerResidueForm r n α = deningerResidueForm r n β := by
  rw [← LinearMap.exact_iff.mp (deningerResidue_exact_sequence (r := r) (n := n))]
  change deningerResidueForm r n (α - β) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every divisor residue has a stage-form representative, unique modulo extension from the
divisor. -/
theorem deningerResidue_exists_unique_mod_extension
    (r n : ℕ) (ω : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :
    ∃ α : (Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ,
      deningerResidueForm r n α = ω ∧
        ∀ β, deningerResidueForm r n β = ω ↔
          β - α ∈ LinearMap.range (deningerExtendForm r (n + 1)) := by
  obtain ⟨α, hα⟩ := deningerResidueForm_surjective ω
  refine ⟨α, hα, fun β => ?_⟩
  rw [← hα, deningerResidue_congr_hasse_iff]

end


end RHTower
