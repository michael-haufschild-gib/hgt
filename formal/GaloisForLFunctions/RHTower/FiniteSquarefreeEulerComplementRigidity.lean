import GaloisForLFunctions.RHTower.Sieve.EulerExpansion

/-!
# Finite squarefree Euler complement coefficients

This is the exact finite Boolean-complement coefficient algebra behind the
finite Euler functional-equation card.  It deliberately contains no analytic
continuation claim: a separate wrapper must derive these coefficient identities
from an equality of finite Dirichlet polynomials.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- The complement coefficient at a squarefree subset. -/
def finiteEulerComplementCoefficient (P S : Finset ℕ) (a : ℕ → ℂ) (C : ℂ) : ℂ :=
  C * (∏ p ∈ P \ S, a p) / (∏ p ∈ P \ S, (p : ℂ))

/-- The top Boolean coefficient is the complement constant. -/
theorem finiteEulerComplement_topCoefficient
    (P : Finset ℕ) (a : ℕ → ℂ) (C : ℂ)
    (hcoeff : ∀ S, S ⊆ P → (∏ p ∈ S, a p) =
      finiteEulerComplementCoefficient P S a C) :
    (∏ p ∈ P, a p) = C := by
  have h := hcoeff P (by simp)
  simpa [finiteEulerComplementCoefficient, Finset.sdiff_self] using h

/-- The complement of the one-prime-deleted Boolean coefficient is that prime. -/
theorem finiteEulerComplement_eraseCoefficient
    (P : Finset ℕ) (a : ℕ → ℂ) (C : ℂ) {p : ℕ} (hp : p ∈ P)
    (hcoeff : ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a C) :
    (∏ q ∈ P.erase p, a q) = C * a p / (p : ℂ) := by
  have h := hcoeff (P.erase p) (Finset.erase_subset p P)
  unfold finiteEulerComplementCoefficient at h
  rw [show P \ P.erase p = {p} by
    rw [Finset.sdiff_erase hp, Finset.sdiff_self, Finset.insert_empty]] at h
  simpa using h

/-- Exact finite rigidity: nonzero Boolean-complement coefficients force every
local Euler parameter to square to its prime. -/
theorem finiteEulerComplement_coefficients_force_localSquares
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (C : ℂ)
    (hC : C ≠ 0)
    (hcoeff : ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a C) :
    ∀ p ∈ P, a p ^ 2 = (p : ℂ) := by
  intro p hp
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero (hP p hp))
  have htop := finiteEulerComplement_topCoefficient P a C hcoeff
  have herase := finiteEulerComplement_eraseCoefficient P a C hp hcoeff
  have hprod : (∏ q ∈ P.erase p, a q) * a p = C := by
    rw [Finset.prod_erase_mul P a hp, htop]
  rw [herase] at hprod
  field_simp [hpC, hC] at hprod
  exact hprod

/-- Conversely, the local square relations imply every Boolean-complement
coefficient identity with the top coefficient as complement constant. -/
theorem finiteEulerComplement_coefficients_of_localSquares
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (hlocal : ∀ p ∈ P, a p ^ 2 = (p : ℂ)) :
    ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a (∏ q ∈ P, a q) := by
  intro S hS
  let T : Finset ℕ := P \ S
  have hdisj : Disjoint S T := by
    exact Finset.disjoint_sdiff
  have hunion : S ∪ T = P := by
    exact Finset.union_sdiff_of_subset hS
  have hTsq : (∏ q ∈ T, a q) ^ 2 = (∏ q ∈ T, (q : ℂ)) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    exact hlocal q (Finset.sdiff_subset hq)
  have hTne : (∏ q ∈ T, a q) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    have hqP : q ∈ P := Finset.sdiff_subset hq
    have hqC : (q : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.Prime.ne_zero (hP q hqP))
    intro hzero
    have hsq := hlocal q hqP
    simp [hzero] at hsq
    exact hqC hsq.symm
  rw [finiteEulerComplementCoefficient]
  change (∏ q ∈ S, a q) = (∏ q ∈ P, a q) * (∏ q ∈ T, a q) /
    (∏ q ∈ T, (q : ℂ))
  rw [← hTsq, ← hunion, Finset.prod_union hdisj]
  field_simp [hTne]

end

end RHTower
