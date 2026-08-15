import GaloisForLFunctions.HTGeometry.OrbitBaire
import GaloisForLFunctions.HTGeometry.TranscendentalProfileCountableFamily

/-!
# The orbit lemma for a countable member set

A joint relation involves only finitely many members, so it suffices to be good for every finite
subset.  Tasks are therefore indexed by a finite member set together with a finite jet-monomial
family over it — a countable index — and Baire's theorem on the compact box of sources produces one
source family good for all of them at once.

This is the card's orbit lemma in one variable: finitely many nonzero frequencies, a countable set of
members with pairwise distinct translation classes on each source, and entire sources whose whole
orbit family satisfies no algebraic differential equation with complex coefficients.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {L : ℕ} {ι : Type} [Countable ι] [DecidableEq ι]

/-- The countable index of tasks: a finite member set with a finite jet-monomial family over it. -/
abbrev orbTaskCountable (ι : Type) [DecidableEq ι] : Type :=
  Σ A : Finset ι, Σ p : ℕ × ℕ, (Fin p.2 → (Option (↥A × Fin (p.1 + 1)) →₀ ℕ))

/-- **The orbit lemma in one variable, for a countable member set.** -/
theorem exists_source_jointlyHypertranscendental_countable [Nonempty ι]
    (lam : Fin L → ℂ) (hlam : ∀ j, lam j ≠ 0) (src : ι → Fin L) (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' → Complex.exp (sh i) ≠ Complex.exp (sh i')) :
    ∃ C : Fin L → sourceBox, JointlyHypertranscendental (orbFun lam src sh C) := by
  classical
  have hdistA : ∀ A : Finset ι, ∀ i i' : ↥A,
      src (i : ι) = src (i' : ι) → i ≠ i' →
        Complex.exp (sh (i : ι)) ≠ Complex.exp (sh (i' : ι)) := by
    intro A i i' hsrc hne
    exact hdist (i : ι) (i' : ι) hsrc fun h => hne (Subtype.ext h)
  set G : orbTaskCountable ι → Set (Fin L → sourceBox) := fun τ =>
    if Function.Injective τ.2.2 then
      orbGood lam (fun i : ↥τ.1 => src (i : ι)) (fun i : ↥τ.1 => sh (i : ι)) τ.2.2
    else Set.univ with hG
  have hGopen : ∀ τ, IsOpen (G τ) := by
    intro τ
    rw [hG]
    by_cases h : Function.Injective τ.2.2
    · simp only [if_pos h]
      exact isOpen_orbGood lam _ _ τ.2.2
    · simp only [if_neg h]
      exact isOpen_univ
  have hGdense : ∀ τ, Dense (G τ) := by
    intro τ
    rw [hG]
    by_cases h : Function.Injective τ.2.2
    · simp only [if_pos h]
      exact dense_orbGood lam hlam _ _ (hdistA τ.1) τ.2.2 h
    · simp only [if_neg h]
      exact dense_univ
  obtain ⟨C, hC⟩ := (dense_iInter_of_isOpen hGopen hGdense).nonempty
  refine ⟨C, jointlyHypertranscendental_of_finite_restrictions _ fun S hS => ?_⟩
  have hres : (fun i : ↥S => orbFun lam src sh C (i : ι))
      = orbFun lam (fun i : ↥S => src (i : ι)) (fun i : ↥S => sh (i : ι)) C := rfl
  rw [hres]
  refine jointlyHypertranscendental_of_orbGood_all _ _ _ C ?_
  intro n K M hM
  have hmem := Set.mem_iInter.mp hC (⟨S, (n, K), M⟩ : orbTaskCountable ι)
  rw [hG] at hmem
  simpa only [if_pos hM] using hmem

end

end GaloisForLFunctions.HTGeometry
