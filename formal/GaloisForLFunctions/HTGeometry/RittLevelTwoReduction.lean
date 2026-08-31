import GaloisForLFunctions.HTGeometry.RittSeedDescent
import GaloisForLFunctions.HTGeometry.RittJetDefect

/-!
# The tower collapse reduces to jet order two

The monotone descent stops only where a jet has no shift defect, and the defect vanishes just at jet
orders zero and one whenever the chain-rule factor is nonconstant.  Running the descent with floor
two therefore removes that exit altogether: the collapse of the jet tower always leaves a relation
over the first two jets whose multiplier is a nontrivial monomial in `q` and `ρ`.

Below jet order two the shift is diagonal — `σ τ = q·τ` and `σ(dτ) = (q/ρ)·dτ` — so what remains is a
two-variable problem with a diagonal substitution, where the eigenvectors are the monomials
`κ·τ^{e₀}(dτ)^{e₁}`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- **The tower collapse reduces to jet order two.** -/
theorem exists_nontrivial_level_two_relation (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) {n : ℕ}
    (htr : ∀ j, j < n → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ))
    (W : L) (A : ℕ → K) (hW0 : W ≠ 0) (hWmem : W ∈ Fr.jetPrefixField τ n)
    (hrel : Fr.σ W = algebraMap K L (q / Fr.ρ ^ n) * W
        + ∑ j ∈ Finset.range n, algebraMap K L (A j) * Fr.d^[j] τ) :
    ∃ (n' : ℕ) (V : L) (c' g' : K) (A' : ℕ → K) (i' k' : ℤ),
      n' ≤ 2 ∧ V ≠ 0 ∧ V ∈ Fr.jetPrefixField τ n' ∧ c' ≠ 0 ∧
      c' = q ^ i' * Fr.ρ ^ k' ∧ ¬(i' = 0 ∧ k' = 0) ∧
      Fr.σ V = algebraMap K L c' * V + algebraMap K L g'
        + ∑ j ∈ Finset.range n', algebraMap K L (A' j) * Fr.d^[j] τ := by
  rcases exists_nontrivial_floor_relation_of_jet_seed Fr hqconst hshift hq 2 n htr W A hW0 hWmem
      hrel with ⟨m, hFm, hmn, hdiag⟩ | hgood
  · exfalso
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    have hjet : Fr.d^[m' + 1] τ ∉ Fr.jetPrefixField τ (m' + 1) := by
      intro hmem
      exact htr (m' + 1) (by omega)
        (isAlgebraic_algebraMap
          (⟨Fr.d^[m' + 1] τ, hmem⟩ : ↥(Fr.jetPrefixField τ (m' + 1))))
    exact jetDefect_ne_zero Fr hqconst hshift hq hdρ m' hjet (by
      rw [RittFrame.jetDefect, hdiag, sub_self])
  · exact hgood

end GaloisForLFunctions.HTGeometry
