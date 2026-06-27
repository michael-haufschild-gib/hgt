/-
# Chain gluing of local Böttcher branches — the local→semilocal step of the connected cover

The genuine disconnected-case close (`noRelation_of_kummer_inputs` with radicand `bc`, non-square by
`SquareFree.bottcher_X_pow_sub_C_irreducible`) needs the descent
`Q62Assembly.noRelation_of_precompMap`, which consumes the **connected dyadic cover**: a region on
which the multivalued `φ_c = bc` is single-valued, with the `z`-projection sectioned.
`CoverConstruction` builds the *local* single-valued branches (`exists_local_greenConjugate_basin`,
`exists_greenConjugate_explicit`) and the *two-patch* glue (`exists_greenConjugate_glue`).

This file iterates the two-patch glue into an **N-patch chain glue**: along any simply-chained sequence
of patches (consecutive overlaps connected) the local branches assemble into a *single* analytic
green-conjugate `G` (hence a single-valued `φ̃c = exp G`) on the whole prefix union.  This is the
local→semilocal step toward the global cover — the only remaining obstruction being a chain that
*closes into a loop* around a Cantor cylinder, where the accumulated `2πi/2ⁿ` period is the dyadic
monodromy (the deck).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.CoverConstruction

open Set

namespace Bottcher

/-- **Chain gluing of local Böttcher green-conjugates into a semilocal single-valued branch.**
Given patches `U i` with local green-conjugates `F i` (`Re (F i) = G_c` on `U i`), if at every step the
next patch meets the running prefix-union in a CONNECTED overlap, the local branches glue (iterating
`exists_greenConjugate_glue`) into a single analytic `G` on `⋃_{j≤m} U j` with `Re G = G_c`.  Induction
on `m`: the base is `F 0`; the step glues the prefix branch with `F (n+1)` across their connected
overlap.  The multivalued `φ_c = exp F` is thereby single-valued along any simple chain; the only
obstruction to a global branch is a chain closing into a loop (the dyadic monodromy period). -/
theorem exists_greenConjugate_chainGlue {c : ℂ} (U : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ)
    (hUo : ∀ i, IsOpen (U i))
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (U i))
    (hRe : ∀ i, EqOn (fun w => (F i w).re) (greenLimit c) (U i))
    (hov : ∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), U j) ∩ U (i + 1))) :
    ∀ m : ℕ, ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (⋃ j ∈ Finset.range (m + 1), U j) ∧
      EqOn (fun w => (G w).re) (greenLimit c) (⋃ j ∈ Finset.range (m + 1), U j) := by
  intro m
  induction m with
  | zero =>
    refine ⟨F 0, ?_, ?_⟩
    · simpa using hF 0
    · simpa using hRe 0
  | succ n ih =>
    obtain ⟨G, hGan, hGre⟩ := ih
    have hpre_open : IsOpen (⋃ j ∈ Finset.range (n + 1), U j) :=
      isOpen_biUnion (fun i _ => hUo i)
    obtain ⟨G', hG'an, hG're⟩ :=
      exists_greenConjugate_glue (c := c) hpre_open (hUo (n + 1)) (hov n) hGan (hF (n + 1)) hGre
        (hRe (n + 1))
    have hunion : (⋃ j ∈ Finset.range (n + 1), U j) ∪ U (n + 1)
        = ⋃ j ∈ Finset.range (n + 2), U j := by
      have hr : Finset.range (n + 2) = insert (n + 1) (Finset.range (n + 1)) :=
        Finset.range_add_one
      rw [hr, Finset.set_biUnion_insert, union_comm]
    rw [hunion] at hG'an hG're
    exact ⟨G', hG'an, hG're⟩

/-- **Single-valued Böttcher branch on a chain-coverable region.**  Exponentiating the chain-glued
green-conjugate: on the prefix union `⋃_{j≤m} U j` (local Böttcher patches, consecutive overlaps
connected), `β = exp G` is a single-valued analytic nowhere-zero branch of `φ_c` with `‖β‖ = exp(G_c)`.
The single-valued lift `φ̃c` on the chained region — the raw material the connected dyadic cover
assembles, the remaining input being the loop-closure / deck where the chain wraps a Cantor cylinder. -/
theorem exists_bottcherBranch_chainGlue {c : ℂ} (U : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ)
    (hUo : ∀ i, IsOpen (U i))
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (U i))
    (hRe : ∀ i, EqOn (fun w => (F i w).re) (greenLimit c) (U i))
    (hov : ∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), U j) ∩ U (i + 1))) (m : ℕ) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (⋃ j ∈ Finset.range (m + 1), U j) ∧
      (∀ w ∈ (⋃ j ∈ Finset.range (m + 1), U j), ‖β w‖ = Real.exp (greenLimit c w)) ∧
      (∀ w ∈ (⋃ j ∈ Finset.range (m + 1), U j), β w ≠ 0) := by
  obtain ⟨G, hGan, hGre⟩ := exists_greenConjugate_chainGlue U F hUo hF hRe hov m
  refine ⟨fun w => Complex.exp (G w), hGan.cexp, ?_, fun w _ => Complex.exp_ne_zero _⟩
  intro w hw
  exact norm_exp_greenConjugate (hGre hw)

end Bottcher

namespace Bottcher
open Set

/-- **Cover transition multiplier (deck cocycle).**  Two single-valued green-conjugate branches
`F₁, F₂` (each `Re = G_c`) on opens `U₁, U₂` with CONNECTED overlap differ there by an imaginary
constant (`greenConjugate_sub_imaginary_const`), so their Böttcher lifts `exp F₁, exp F₂` differ by a
fixed UNIMODULAR factor `ζ = exp a` on the overlap: `exp F₁ = ζ · exp F₂`, `‖ζ‖ = 1`.  This `ζ` is the
transition cocycle of the connected dyadic cover — going around a loop it accumulates the dyadic
monodromy multiplier (order `2ⁿ`); `ζ ≠ 1` means the two patches sit on genuinely distinct sheets.
Together with `exists_greenConjugate_chainGlue`, this is the cover's structure: glue along a simple
chain, and read off the deck multiplier where the chain closes into a loop. -/
theorem exp_greenConjugate_transition {c : ℂ} {F₁ F₂ : ℂ → ℂ} {U₁ U₂ : Set ℂ}
    (hU₁o : IsOpen U₁) (hU₂o : IsOpen U₂) (hovc : IsConnected (U₁ ∩ U₂))
    (hF1 : AnalyticOnNhd ℂ F₁ U₁) (hF2 : AnalyticOnNhd ℂ F₂ U₂)
    (h1 : EqOn (fun w => (F₁ w).re) (greenLimit c) U₁)
    (h2 : EqOn (fun w => (F₂ w).re) (greenLimit c) U₂) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      EqOn (fun w => Complex.exp (F₁ w)) (fun w => ζ * Complex.exp (F₂ w)) (U₁ ∩ U₂) := by
  obtain ⟨a, ha0, ha⟩ := greenConjugate_sub_imaginary_const (hU₁o.inter hU₂o) hovc
    (hF1.mono inter_subset_left) (hF2.mono inter_subset_right)
    (h1.mono inter_subset_left) (h2.mono inter_subset_right)
  refine ⟨Complex.exp a, ?_, ?_⟩
  · rw [Complex.norm_exp, ha0, Real.exp_zero]
  · intro w hw
    simp only [ha hw, Complex.exp_add]
    ring

end Bottcher

namespace Bottcher
open Set

/-- **The cover transition multiplier is a `k`-th root of unity.**  If two nowhere-zero branches
`β₁, β₂` differ by a constant `ζ` on `S` (`β₁ = ζ·β₂`) and are both `k`-th roots of the SAME function
there (`β₁^k = β₂^k`, e.g. `φ̃c^{2ⁿ} = bc∘f^[n]` the single-valued base), then `ζ^k = 1`.  The algebraic
core of the deck: the monodromy multiplier between two sheets of the `2ⁿ`-fold dyadic cover is a `2ⁿ`-th
root of unity (`exp_greenConjugate_transition` gives `ζ` unimodular; this pins it to `μ_{2ⁿ}`), exactly
the Kummer/Galois multiplier `kummer_deck_datum` consumes. -/
theorem cover_multiplier_pow_eq_one {β₁ β₂ : ℂ → ℂ} {ζ : ℂ} {S : Set ℂ} {k : ℕ}
    (hS : S.Nonempty) (hsc : Set.EqOn β₁ (fun w => ζ * β₂ w) S)
    (hpow : Set.EqOn (fun w => β₁ w ^ k) (fun w => β₂ w ^ k) S) (hne : ∀ w ∈ S, β₂ w ≠ 0) :
    ζ ^ k = 1 := by
  obtain ⟨w, hw⟩ := hS
  have h1 : β₁ w = ζ * β₂ w := hsc hw
  have h2 : β₁ w ^ k = β₂ w ^ k := hpow hw
  rw [h1, mul_pow] at h2
  exact mul_right_cancel₀ (pow_ne_zero k (hne w hw)) (by rw [h2, one_mul])

/-- **Full deck-multiplier datum from the cover.**  On the connected overlap of two green-conjugate
branches that are both `k`-th roots of the same single-valued base (`(exp F₁)^k = (exp F₂)^k`, e.g.
`φ̃c^{2ⁿ} = bc∘f^[n]`), the Böttcher lifts differ by a multiplier `ζ` that is BOTH unimodular AND a
`k`-th root of unity — i.e. `ζ ∈ μ_k`.  Combines `exp_greenConjugate_transition` (`‖ζ‖=1`) with
`cover_multiplier_pow_eq_one` (`ζ^k=1`).  The complete deck multiplier the disconnected cover's
Galois/Kummer deck (`kummer_deck_datum`) scales `φ̃c` by; for `k=2ⁿ` and the dyadic period it is the
primitive `2ⁿ`-th root. -/
theorem cover_deck_multiplier {c : ℂ} {F₁ F₂ : ℂ → ℂ} {U₁ U₂ : Set ℂ} {k : ℕ}
    (hU₁o : IsOpen U₁) (hU₂o : IsOpen U₂) (hovc : IsConnected (U₁ ∩ U₂))
    (hF1 : AnalyticOnNhd ℂ F₁ U₁) (hF2 : AnalyticOnNhd ℂ F₂ U₂)
    (h1 : EqOn (fun w => (F₁ w).re) (greenLimit c) U₁)
    (h2 : EqOn (fun w => (F₂ w).re) (greenLimit c) U₂)
    (hpow : Set.EqOn (fun w => Complex.exp (F₁ w) ^ k) (fun w => Complex.exp (F₂ w) ^ k) (U₁ ∩ U₂)) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ ^ k = 1 ∧
      EqOn (fun w => Complex.exp (F₁ w)) (fun w => ζ * Complex.exp (F₂ w)) (U₁ ∩ U₂) := by
  obtain ⟨ζ, hζ1, hζeq⟩ := exp_greenConjugate_transition hU₁o hU₂o hovc hF1 hF2 h1 h2
  exact ⟨ζ, hζ1, cover_multiplier_pow_eq_one hovc.nonempty hζeq hpow
    (fun w _ => Complex.exp_ne_zero _), hζeq⟩

end Bottcher

namespace Bottcher
open Set

/-- **Deck multiplier for genuine Böttcher cover branches (non-vacuous).**  Two green-conjugate
branches `F₁, F₂` (`Re = G_c`) that BOTH satisfy the radical relation `(exp Fᵢ)^{2ⁿ} = bc∘f^[n]` on
their patches — exactly the genuine Böttcher lifts `φ̃c` (`exp_greenConjugate_explicit_pow`) — have on
their connected overlap a deck multiplier `ζ ∈ μ_{2ⁿ}` (unimodular, `ζ^{2ⁿ}=1`) with `exp F₁ = ζ·exp F₂`.
The `hpow` hypothesis of `cover_deck_multiplier` is discharged here by the common base `bc∘f^[n]`, so
this applies directly to the actual `2ⁿ`-fold dyadic cover sheets — the deck `kummer_deck_datum`
consumes, realized for genuine branches (NOT vacuous). -/
theorem cover_deck_multiplier_of_radical {c : ℂ} (n : ℕ) {F₁ F₂ : ℂ → ℂ} {U₁ U₂ : Set ℂ}
    (hU₁o : IsOpen U₁) (hU₂o : IsOpen U₂) (hovc : IsConnected (U₁ ∩ U₂))
    (hF1 : AnalyticOnNhd ℂ F₁ U₁) (hF2 : AnalyticOnNhd ℂ F₂ U₂)
    (h1 : EqOn (fun w => (F₁ w).re) (greenLimit c) U₁)
    (h2 : EqOn (fun w => (F₂ w).re) (greenLimit c) U₂)
    (hrad1 : EqOn (fun w => Complex.exp (F₁ w) ^ (2 ^ n))
      (fun w => bottcherCoord c ((quadratic c)^[n] w)) U₁)
    (hrad2 : EqOn (fun w => Complex.exp (F₂ w) ^ (2 ^ n))
      (fun w => bottcherCoord c ((quadratic c)^[n] w)) U₂) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ ^ (2 ^ n) = 1 ∧
      EqOn (fun w => Complex.exp (F₁ w)) (fun w => ζ * Complex.exp (F₂ w)) (U₁ ∩ U₂) := by
  have hpow : Set.EqOn (fun w => Complex.exp (F₁ w) ^ (2 ^ n))
      (fun w => Complex.exp (F₂ w) ^ (2 ^ n)) (U₁ ∩ U₂) := by
    intro w hw
    rw [hrad1 hw.1, hrad2 hw.2]
  exact cover_deck_multiplier hU₁o hU₂o hovc hF1 hF2 h1 h2 hpow

end Bottcher
