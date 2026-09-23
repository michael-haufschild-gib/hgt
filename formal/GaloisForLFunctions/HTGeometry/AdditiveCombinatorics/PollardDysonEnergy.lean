import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardDysonMeasure

/-!
# From the Dyson transform to the energy bound

`dysonFull A B` is the set of translations carrying `B` inside `A`; it satisfies
`dysonFull A B · B ⊆ A`.  The identity `rep_inv_eq_card_dysonSmall`,
`r_{A,B⁻¹}(x) = #((x • B) ∩ A)`, is what connects Grynkiewicz's Lemma 2.1 — whose hypothesis is a
pointwise bound on difference representations off a set `T` — to the Dyson transform: off
`dysonFull A B`, the small part is a proper subset of `B`, so a maximal Dyson witness bounds it.

`repSum_ge_min_dyson` records the resulting instance of Lemma 2.1, which is the analytic engine of
Grynkiewicz's STEP 3.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- The set of translations carrying `B` inside `A`. -/
def dysonFull (A B : Finset G) : Finset G := univ.filter (fun x => x • B ⊆ A)

@[simp] theorem mem_dysonFull {A B : Finset G} {x : G} :
    x ∈ dysonFull A B ↔ x • B ⊆ A := by simp [dysonFull]

theorem dysonFull_mul_subset (A B : Finset G) : dysonFull A B * B ⊆ A := by
  intro z hz
  rw [mem_mul] at hz
  obtain ⟨x, hx, b, hb, rfl⟩ := hz
  rw [mem_dysonFull] at hx
  exact hx (Finset.smul_mem_smul_finset hb)

omit [Fintype G] in
/-- **The bridge to Lemma 2.1.**  The difference representation count is the size of the Dyson
small part. -/
theorem rep_inv_eq_card_dysonSmall (A B : Finset G) (x : G) :
    rep A B⁻¹ x = (dysonSmall A B x).card := by
  rw [rep_eq_card_inter, dysonSmall, inv_inv, Finset.inter_comm]

/-- Off `dysonFull A B`, the difference representation count is bounded by the maximal Dyson small
part. -/
theorem rep_inv_le_of_notMem_dysonFull {A B : Finset G} {x₀ : G}
    (hmax : ∀ y : G, (dysonSmall A B y).Nonempty → (dysonSmall A B y).card < B.card →
        (dysonSmall A B y).card ≤ (dysonSmall A B x₀).card)
    {x : G} (hx : x ∉ dysonFull A B) :
    rep A B⁻¹ x ≤ (dysonSmall A B x₀).card := by
  classical
  rw [rep_inv_eq_card_dysonSmall]
  rcases Finset.eq_empty_or_nonempty (dysonSmall A B x) with hemp | hne
  · rw [hemp]
    simp
  · refine hmax x hne ?_
    rw [mem_dysonFull] at hx
    have hsub : dysonSmall A B x ⊆ x • B := Finset.inter_subset_left
    have hcard : (x • B).card = B.card := Finset.card_smul_finset _ _
    rcases lt_or_eq_of_le (Finset.card_le_card hsub) with h | h
    · omega
    · exfalso
      apply hx
      have : dysonSmall A B x = x • B := Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
      rw [← this]
      exact Finset.inter_subset_right


/-- **Grynkiewicz's Lemma 2.1 in the Dyson setting.**  With `T = dysonFull A B` and
`k = #(dysonSmall A B x₀)` for a maximal Dyson witness `x₀`, the energy bound reads
`repSum A B t ≥ min ( t·#A·#B/(t+√(t(t−1))), t·#A²·#B/(k·#A + #T·(#B−k)) )`. -/
theorem repSum_ge_min_dyson {A B : Finset G} {x₀ : G} {t : ℕ} (ht : 1 ≤ t)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hk1 : 1 ≤ (dysonSmall A B x₀).card)
    (hkB : (dysonSmall A B x₀).card ≤ B.card)
    (hmax : ∀ y : G, (dysonSmall A B y).Nonempty → (dysonSmall A B y).card < B.card →
        (dysonSmall A B y).card ≤ (dysonSmall A B x₀).card) :
    min ((t : ℝ) * ((A.card : ℝ) * B.card)
          / ((t : ℝ) + Real.sqrt ((t : ℝ) * ((t : ℝ) - 1))))
        ((t : ℝ) * (A.card : ℝ) ^ (2 : ℕ) * (B.card : ℝ)
          / ((((dysonSmall A B x₀).card : ℕ) : ℝ) * A.card
             + ((dysonFull A B).card : ℝ)
               * ((B.card : ℝ) - (((dysonSmall A B x₀).card : ℕ) : ℝ))))
      ≤ (repSum A B t : ℝ) :=
  repSum_ge_min_of_rep_inv_le ht hA hB hk1 hkB
    (fun _ hx => rep_inv_le_of_notMem_dysonFull hmax hx)

end GaloisForLFunctions.HTGeometry.AddComb
