import GaloisForLFunctions.RHTower.HardyListDivision
import GaloisForLFunctions.RHTower.ZetaShiftCore

/-!
# `s(s-1)ζ(s)/((s-ρ₁)(s-ρ₂)(s-ρ)^l)` is a pure tail transform

Burnol's Proposition 6.5 needs these functions to be the right Mellin transforms of elements of the
Sonine space `K₁`, that is — after the change of variable `s = w + 1/2` — Hardy functions of the
right half-plane.  Divide the Hardy core by the list `[ρ₁ - 1/2, ρ₂ - 1/2]` followed by `l` copies
of `ρ - 1/2`, absorbing three factors of `w + 1/2`; the multiplicity bookkeeping is the count of a
point in that list.

## Main results

* `exists_isHalfPlaneHardy_zetaTriple`
-/

open Complex Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem meromorphicAt_zetaShiftCoreNF (s : ℂ) : MeromorphicAt zetaShiftCoreNF s :=
  (meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ s)).meromorphicAt

/-- The list of divisors: the two omitted zeros, then `l` copies of the working zero. -/
def tripleList (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) : List ℂ :=
  (ρ₁ - 1 / 2) :: (ρ₂ - 1 / 2) :: List.replicate l (ρ - 1 / 2)

theorem tripleList_length (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) : (tripleList ρ₁ ρ₂ ρ l).length = l + 2 := by
  simp [tripleList]

theorem tripleList_count (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) (z : ℂ) :
    (((tripleList ρ₁ ρ₂ ρ l).count z : ℕ) : ℤ)
      = (if ρ - 1 / 2 = z then (l : ℤ) else 0)
        + (if ρ₂ - 1 / 2 = z then 1 else 0) + (if ρ₁ - 1 / 2 = z then 1 else 0) := by
  classical
  rw [tripleList, List.count_cons, List.count_cons, List.count_replicate]
  push_cast
  by_cases h0 : ρ - 1 / 2 = z <;> by_cases h1 : ρ₁ - 1 / 2 = z <;> by_cases h2 : ρ₂ - 1 / 2 = z <;>
    simp [beq_iff_eq]

theorem tripleList_mem_ne_neg_half {ρ₁ ρ₂ ρ : ℂ} {l : ℕ} (hρ₁0 : ρ₁ ≠ 0) (hρ₂0 : ρ₂ ≠ 0)
    (hρ0 : ρ ≠ 0) : ∀ z ∈ tripleList ρ₁ ρ₂ ρ l, z ≠ -(1 / 2) := by
  intro z hz
  rw [tripleList] at hz
  simp only [List.mem_cons] at hz
  rcases hz with h | h | h
  · rw [h]; intro hc; exact hρ₁0 (by linear_combination hc)
  · rw [h]; intro hc; exact hρ₂0 (by linear_combination hc)
  · rw [List.eq_of_mem_replicate h]; intro hc; exact hρ0 (by linear_combination hc)

theorem shift_eq_iff (a b : ℂ) : (a - 1 / 2 = b - 1 / 2) ↔ a = b := by
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]

theorem meromorphicOrderAt_zetaShiftCoreNF_ge {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) {k : ℕ}
    (hord : (k : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ((k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt zetaShiftCoreNF (ρ - 1 / 2) := by
  have hw2 : (ρ : ℂ) - 1 / 2 ≠ -(1 / 2) := by
    intro h; exact hρ0 (by linear_combination h)
  have hana : AnalyticAt ℂ zetaShiftCoreNF (ρ - 1 / 2) := analyticAt_zetaShiftCoreNF hw2
  have h := natCast_le_analyticOrderAt_zetaShiftCoreNF hρ1 hρ0 hord
  rw [hana.meromorphicOrderAt_eq]
  induction hx : analyticOrderAt zetaShiftCoreNF (ρ - 1 / 2) with
  | top => simp
  | coe n =>
      rw [hx] at h
      have hn : (k : ℕ) ≤ n := by exact_mod_cast h
      have h1 : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      simpa using h1

theorem zero_le_meromorphicOrderAt_zetaShiftCoreNF {z : ℂ} (hz : z ≠ -(1 / 2)) :
    (0 : WithTop ℤ) ≤ meromorphicOrderAt zetaShiftCoreNF z := by
  have h := meromorphicOrderAt_nonneg_of_analyticAt (analyticAt_zetaShiftCoreNF hz)
  simpa using h

/-- **The triple quotient is a Hardy function of the right half-plane.** -/
theorem exists_isHalfPlaneHardy_zetaTriple {ρ₁ ρ₂ ρ : ℂ} {l m₁ m₂ mρ : ℕ}
    (hρ₁0 : ρ₁ ≠ 0) (hρ₁1 : ρ₁ ≠ 1) (hρ₂0 : ρ₂ ≠ 0) (hρ₂1 : ρ₂ ≠ 1)
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hl : 1 ≤ l)
    (hm₁ : (m₁ : ℕ∞) ≤ analyticOrderAt riemannZeta ρ₁)
    (hm₂ : (m₂ : ℕ∞) ≤ analyticOrderAt riemannZeta ρ₂)
    (hmρ : (mρ : ℕ∞) ≤ analyticOrderAt riemannZeta ρ)
    (hb₀ : (l : ℤ) + (if ρ₂ = ρ then 1 else 0) + (if ρ₁ = ρ then 1 else 0) ≤ (mρ : ℤ))
    (hb₁ : (if ρ = ρ₁ then (l : ℤ) else 0) + (if ρ₂ = ρ₁ then 1 else 0) + 1 ≤ (m₁ : ℤ))
    (hb₂ : (if ρ = ρ₂ then (l : ℤ) else 0) + 1 + (if ρ₁ = ρ₂ then 1 else 0) ≤ (m₂ : ℤ)) :
    ∃ (K : ℂ → ℂ) (M : ℝ), IsHalfPlaneHardy K M ∧
      ∀ w : ℂ, w ≠ -(1 / 2) → w ≠ ρ - 1 / 2 → w ≠ ρ₁ - 1 / 2 → w ≠ ρ₂ - 1 / 2 →
        K w = (w + 1 / 2) ^ (3 : ℕ) * zetaShiftCoreNF w
          / ((w - (ρ₁ - 1 / 2)) * ((w - (ρ₂ - 1 / 2)) * (w - (ρ - 1 / 2)) ^ l)) := by
  classical
  obtain ⟨MC, hMC⟩ := isHalfPlaneHardy_zetaShiftCoreNF
  have hlen : 3 ≤ (tripleList ρ₁ ρ₂ ρ l).length := by
    rw [tripleList_length]
    omega
  have hcnt : ∀ z : ℂ, z ≠ -(1 / 2) →
      (((tripleList ρ₁ ρ₂ ρ l).count z : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt zetaShiftCoreNF z := by
    intro z hz
    rw [tripleList_count]
    by_cases h0 : ρ - 1 / 2 = z
    · subst h0
      refine le_trans ?_ (meromorphicOrderAt_zetaShiftCoreNF_ge hρ1 hρ0 hmρ)
      refine WithTop.coe_le_coe.2 ?_
      have e₂ : (ρ₂ - 1 / 2 = ρ - 1 / 2) ↔ ρ₂ = ρ := shift_eq_iff _ _
      have e₁ : (ρ₁ - 1 / 2 = ρ - 1 / 2) ↔ ρ₁ = ρ := shift_eq_iff _ _
      simp only [e₁, e₂]
      exact hb₀
    · by_cases h1 : ρ₁ - 1 / 2 = z
      · subst h1
        refine le_trans ?_ (meromorphicOrderAt_zetaShiftCoreNF_ge hρ₁1 hρ₁0 hm₁)
        refine WithTop.coe_le_coe.2 ?_
        have e₀ : (ρ - 1 / 2 = ρ₁ - 1 / 2) ↔ ρ = ρ₁ := shift_eq_iff _ _
        have e₂ : (ρ₂ - 1 / 2 = ρ₁ - 1 / 2) ↔ ρ₂ = ρ₁ := shift_eq_iff _ _
        simp only [e₀, e₂]
        exact hb₁
      · by_cases h2 : ρ₂ - 1 / 2 = z
        · subst h2
          refine le_trans ?_ (meromorphicOrderAt_zetaShiftCoreNF_ge hρ₂1 hρ₂0 hm₂)
          refine WithTop.coe_le_coe.2 ?_
          have e₀ : (ρ - 1 / 2 = ρ₂ - 1 / 2) ↔ ρ = ρ₂ := shift_eq_iff _ _
          have e₁ : (ρ₁ - 1 / 2 = ρ₂ - 1 / 2) ↔ ρ₁ = ρ₂ := shift_eq_iff _ _
          simp only [e₀, e₁]
          exact hb₂
        · rw [if_neg h0, if_neg h1, if_neg h2]
          simpa using zero_le_meromorphicOrderAt_zetaShiftCoreNF hz
  obtain ⟨K, N, hK, _, _, _, hval⟩ :=
    exists_isHalfPlaneHardy_listDiv hMC meromorphicAt_zetaShiftCoreNF
      (fun s hs => analyticAt_zetaShiftCoreNF hs) (tripleList ρ₁ ρ₂ ρ l) 3 hlen
      (tripleList_mem_ne_neg_half hρ₁0 hρ₂0 hρ0) hcnt
  refine ⟨K, N, hK, ?_⟩
  intro w hw hw₀ hw₁ hw₂
  have hmem : ∀ z ∈ tripleList ρ₁ ρ₂ ρ l, w ≠ z := by
    intro z hz
    rw [tripleList] at hz
    simp only [List.mem_cons] at hz
    rcases hz with h | h | h
    · rw [h]; exact hw₁
    · rw [h]; exact hw₂
    · rw [List.eq_of_mem_replicate h]; exact hw₀
  rw [hval w hw hmem, tripleList]
  simp only [List.map_cons, List.prod_cons, List.map_replicate, List.prod_replicate]

end

end RHTower
