import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardQubal

/-!
# The spread condition of Grynkiewicz's STEP 3

Write `T = dysonFull A B` for the set of full translations and `H = S(T · B)`.  CASE 3.2 needs
that `B` is *not* contained in a single `H`-coset.  Granting the coset-transfer statement
"`B` inside one `K`-coset forces `A` inside one `K`-coset" — which is where the induction
hypothesis enters — the proof is short: if `B ⊆ c · H` then `#H ≥ #B ≥ t + 1`, and `A` inside a
single `H`-coset together with the `H`-periodicity of `T · B ⊆ A` forces `T · B = A`, so that
`H = S(A)` has at most `t − 1` elements, a contradiction.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **The spread condition.**  `B` meets at least two cosets of `S(T · B)`. -/
theorem not_subset_smul_mulStab_dysonFull_mul {A B : Finset G} {t : ℕ}
    (hB : t + 1 ≤ B.card)
    (hstabA : (mulStab A).card + 1 ≤ t)
    (hTne : (dysonFull A B).Nonempty)
    (hSP1 : ∀ c : G, B ⊆ c • mulStab (dysonFull A B * B) →
        ∃ d : G, A ⊆ d • mulStab (dysonFull A B * B)) :
    ∀ c : G, ¬ (B ⊆ c • mulStab (dysonFull A B * B)) := by
  classical
  intro c hc
  have hHgrp : IsSubgroupFinset (mulStab (dysonFull A B * B)) :=
    isSubgroupFinset_mulStab _
  have hBne : B.Nonempty := Finset.card_pos.1 (by omega)
  have hBH : B.card ≤ (mulStab (dysonFull A B * B)).card := by
    calc B.card ≤ (c • mulStab (dysonFull A B * B)).card := Finset.card_le_card hc
      _ = (mulStab (dysonFull A B * B)).card := Finset.card_smul_finset _ _
  obtain ⟨d, hd⟩ := hSP1 c hc
  obtain ⟨z, hz⟩ := hTne
  obtain ⟨b, hb⟩ := hBne
  have hw : z * b ∈ dysonFull A B * B := Finset.mul_mem_mul hz hb
  have hwA : z * b ∈ A := dysonFull_mul_subset A B hw
  -- the coset of `d` is exactly `T · B`
  have hcoset : d • mulStab (dysonFull A B * B) ⊆ dysonFull A B * B := by
    have h1 : (z * b) • mulStab (dysonFull A B * B) = d • mulStab (dysonFull A B * B) :=
      hHgrp.smul_eq_smul_of_mem (hd hwA)
    rw [← h1]
    intro u hu
    obtain ⟨h, hh, rfl⟩ := Finset.mem_smul_finset.1 hu
    have : z * b * h ∈ dysonFull A B * B * mulStab (dysonFull A B * B) :=
      Finset.mul_mem_mul hw hh
    rwa [mul_mulStab] at this
  have hAeq : A = dysonFull A B * B :=
    Subset.antisymm (fun a ha => hcoset (hd ha)) (dysonFull_mul_subset A B)
  rw [← hAeq] at hBH
  omega

end GaloisForLFunctions.HTGeometry.AddComb
