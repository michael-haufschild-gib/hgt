import GaloisForLFunctions.HTGeometry.RittBasisTheorem

/-!
# The ascending chain condition on radical differential ideals

Ritt's basis theorem gives the Noetherian property: an ascending chain of radical differential
ideals of `K{y}` stabilises, because the union is again a radical differential ideal, hence the
radical differential ideal of a finite set, and that finite set already lies at one stage.

This is the Noetherianity of the Kolchin topology in ideal form.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [Differential K]

attribute [local instance] differentialPolynomialDifferential

/-- **The ascending chain condition.**  A monotone chain of radical differential ideals of `K{y}`
stabilises. -/
theorem acc_radicalDifferentialIdeal (I : ℕ → Ideal (DifferentialPolynomial Unit K))
    (hmono : Monotone I) (hrad : ∀ n, (I n).IsRadical)
    (hδ : ∀ n, ∀ x ∈ I n, Differential.deriv x ∈ I n) :
    ∃ N : ℕ, ∀ n, N ≤ n → I n = I N := by
  classical
  have hdir : Directed (· ≤ ·) I := hmono.directed_le
  have hmem : ∀ x, x ∈ (⨆ n, I n) ↔ ∃ n, x ∈ I n := fun x =>
    Submodule.mem_iSup_of_directed I hdir
  have hJrad : (⨆ n, I n).IsRadical := by
    intro y hy
    obtain ⟨n, hn⟩ := hy
    obtain ⟨m, hm⟩ := (hmem _).mp hn
    exact (hmem y).mpr ⟨m, hrad m ⟨n, hm⟩⟩
  have hJδ : ∀ x ∈ (⨆ n, I n), Differential.deriv x ∈ (⨆ n, I n) := by
    intro x hx
    obtain ⟨n, hn⟩ := (hmem x).mp hx
    exact (hmem _).mpr ⟨n, hδ n x hn⟩
  obtain ⟨T, hT⟩ := radDiffFG_differentialPolynomial (⨆ n, I n) hJrad hJδ
  have hTmem : ∀ t ∈ T, ∃ n, t ∈ I n := by
    intro t ht
    refine (hmem t).mp ?_
    rw [hT]
    exact subset_radicalDifferentialIdeal _ (by exact_mod_cast ht)
  choose! f hf using hTmem
  refine ⟨T.sup f, fun n hn => ?_⟩
  have hTN : ↑T ⊆ (I (T.sup f) : Set (DifferentialPolynomial Unit K)) := by
    intro t ht
    have htT : t ∈ T := by exact_mod_cast ht
    exact hmono (Finset.le_sup (f := f) htT) (hf t htT)
  have hJN : (⨆ n, I n) ≤ I (T.sup f) := by
    rw [hT]
    exact radicalDifferentialIdeal_le hTN (hrad _) (hδ _)
  exact le_antisymm (le_trans (le_iSup I n) hJN) (hmono hn)

end

end GaloisForLFunctions.HTGeometry
