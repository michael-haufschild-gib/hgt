/-
# Lattice (S-mono) ⟹ SPUR-R reader exactness

Ties the constant-δ lattice electrostatics (`SpurLattice`) to the SPUR-R/AMP reader capstone
(`SpurCapstone`/`SpurSMono`). The reader consumes an (anti)tone *dressing* of the ordered
margin readings; the lattice reduced energy `W = latticeEnergyS` is exactly that dressing, and
(S-mono) — `latticeEnergyS_antitoneOn` — is its monotonicity. The one modeling input that
remains is that the actual reader margins ARE `W` applied to an `AdjacentStepPos` list of
equilibrium near-ahead distances lying in the domain `(0, δ/2)` (the (F)-field identification).
Given that, reader exactness `Z = 2` follows.

* `isChain_map_ge_on` — a *local* (`AntitoneOn` + list-in-range) dressing gives a nonincreasing
  AMP-margin chain (the global-`Antitone` `SpurSMono.isChain_map_ge_of_adjacentStepPos` relaxed
  to the domain the lattice (S-mono) actually lives on).
* `lattice_reader_exact` — the capstone: lattice (S-mono) dressing over an in-domain
  `AdjacentStepPos` s-list ⟹ `Z = 2`.
-/
import GaloisForLFunctions.RHTower.SpurLattice
import GaloisForLFunctions.RHTower.SpurCapstone
import GaloisForLFunctions.RHTower.SpurSMono

namespace RHTower

open Set

/-- A dressing that is only `AntitoneOn` a range (not globally antitone) still produces a
nonincreasing AMP-margin chain, provided every S-reading lies in that range — the form the
lattice (S-mono) supplies, since `latticeEnergyS` is antitone only on `(0, δ/2)`. -/
theorem isChain_map_ge_on {dress : ℝ → ℝ} {rng : Set ℝ} (hdress : AntitoneOn dress rng) :
    ∀ {S : List ℝ}, AdjacentStepPos S → (∀ x ∈ S, x ∈ rng) →
      List.IsChain (fun x y => y ≤ x) (S.map dress)
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: ys, hS, hmem => by
      rcases hS with ⟨hxy, htail⟩
      have htailChain := isChain_map_ge_on hdress htail
        (fun z hz => hmem z (List.mem_cons_of_mem _ hz))
      apply List.IsChain.cons htailChain
      intro z hz
      simp at hz
      subst z
      have hxr : x ∈ rng := hmem x (by simp)
      have hyr : y ∈ rng := hmem y (by simp)
      exact hdress hxr hyr (le_of_lt (by linarith : x < y))

/-- **Capstone: lattice (S-mono) ⟹ reader exactness.** If the ordered reader margins are the
lattice reduced energy `W = latticeEnergyS δ M N` applied to an `AdjacentStepPos` list `S` of
near-ahead distances all in the domain `(0, δ/2)` (the (F)-field identification of the actual
section field with the constant-δ model), then — with the finite reader hypotheses (Hurwitz
visibility, evenness, the corrected `Z ≤ 2+T` count) — the non-real zero count is exactly `2`:
the DISC reader is exact. This composes the entire `SpurLattice`/`CothInfra` (S-mono) stack
(`latticeEnergyS_antitoneOn`) with the banked reader capstone. -/
theorem lattice_reader_exact {δ : ℝ} {M N Z : ℕ} {S : List ℝ}
    (hδ : 0 < δ) (hN : 1 ≤ N) (hNM : N ≤ M)
    (hS : AdjacentStepPos S) (hmem : ∀ x ∈ S, x ∈ Ioo (0 : ℝ) (δ / 2))
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map (latticeEnergyS δ M N)))) :
    Z = 2 :=
  amp_reader_exact_pair_of_chain_ge
    (isChain_map_ge_on (latticeEnergyS_antitoneOn hδ hN hNM) hS hmem)
    hvisible heven hbound

end RHTower
