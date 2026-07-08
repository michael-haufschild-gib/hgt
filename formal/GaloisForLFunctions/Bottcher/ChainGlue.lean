import Mathlib

/-!
# Chain gluing of locally-defined branches

The generic engine behind the connected-case constructions: given a sequence of opens
`U₀, U₁, …` each carrying local data `Fᵢ` satisfying a gluable predicate `P` on its domain, with
every running union meeting the next domain in a **connected** overlap, a single object satisfying
`P` exists on the union `⋃_{j ≤ k} Uⱼ`.  The two-patch glue for `P` (analytic branches with matching
real part, primitives with matching derivative, …) enters as the abstract hypothesis `glue`; the
lemma supplies only the induction over the chain.
-/

open Set

namespace Bottcher

/-- **Chain gluing.**  If a predicate `P` on `(function, domain)` pairs admits a two-patch glue
`glue` on connected overlaps, and each `Fᵢ` satisfies `P` on the open `Uᵢ` with connected running
overlaps, then some `G` satisfies `P` on `⋃_{j ≤ k} Uⱼ`. -/
theorem exists_glue_chain {P : (ℂ → ℂ) → Set ℂ → Prop}
    (U : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ)
    (hUo : ∀ i, IsOpen (U i))
    (hbase : ∀ i, P (F i) (U i))
    (glue : ∀ {V W : Set ℂ} {f h : ℂ → ℂ}, IsOpen V → IsOpen W →
       IsConnected (V ∩ W) → P f V → P h W → ∃ g : ℂ → ℂ, P g (V ∪ W))
    (hconn : ∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), U j) ∩ U (i + 1)))
    (k : ℕ) :
    ∃ G : ℂ → ℂ, P G (⋃ j ∈ Finset.range (k + 1), U j) := by
  induction k with
  | zero => exact ⟨F 0, by simpa [Finset.range_one] using hbase 0⟩
  | succ n ih =>
    obtain ⟨G, hG⟩ := ih
    have hVopen : IsOpen (⋃ j ∈ Finset.range (n + 1), U j) := isOpen_biUnion (fun j _ => hUo j)
    obtain ⟨H, hH⟩ := glue hVopen (hUo (n + 1)) (hconn n) hG (hbase (n + 1))
    have hunion : (⋃ j ∈ Finset.range (n + 1 + 1), U j)
        = (⋃ j ∈ Finset.range (n + 1), U j) ∪ U (n + 1) := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert]; exact Set.union_comm _ _
    exact ⟨H, by rw [hunion]; exact hH⟩

end Bottcher
