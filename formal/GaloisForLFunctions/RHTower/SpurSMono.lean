/-
S-mono provider bridge for the SPUR-R / AMP stack.

`LedgerConvex` proves positivity of individual `ΔS` steps under explicit
deep/endpoint/direct-evaluation hypotheses.  `SpurCapstone` consumes a monotone
chain of AMP margin readings.  This module connects those shapes: positive
adjacent S-increments give a monotone S-chain; a monotone or antitone dressing
from S-readings to AMP margins then feeds the reader exactness capstone.
-/
import GaloisForLFunctions.RHTower.SpurCapstone

noncomputable section

namespace RHTower

/-- Positive adjacent increments for an ordered list of S-readings. -/
def AdjacentStepPos : List ℝ → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => 0 < y - x ∧ AdjacentStepPos (y :: xs)

/-- Positive adjacent increments make the S-readings a strict increasing chain. -/
theorem isChain_lt_of_adjacentStepPos :
    ∀ xs : List ℝ, AdjacentStepPos xs → List.IsChain (fun x y => x < y) xs := by
  intro xs
  induction xs with
  | nil =>
      intro _h
      exact List.IsChain.nil
  | cons x xs ih =>
      intro h
      cases xs with
      | nil =>
          exact List.IsChain.singleton x
      | cons y ys =>
          rcases h with ⟨hxy, htail⟩
          have htailChain : List.IsChain (fun x y => x < y) (y :: ys) := ih htail
          apply List.IsChain.cons htailChain
          intro z hz
          simp at hz
          subst z
          linarith

/-- Positive adjacent increments make the S-readings nondecreasing. -/
theorem isChain_le_of_adjacentStepPos {xs : List ℝ} (h : AdjacentStepPos xs) :
    List.IsChain (fun x y => x ≤ y) xs :=
  (isChain_lt_of_adjacentStepPos xs h).imp (by intro _a _b hab; exact le_of_lt hab)

private theorem isChain_map_of_adjacentStepPos {S : List ℝ} {dress : ℝ → ℝ}
    {R : ℝ → ℝ → Prop} (hS : AdjacentStepPos S)
    (hrel : ∀ {x y : ℝ}, x < y → R (dress x) (dress y)) :
    List.IsChain R (S.map dress) := by
  induction S with
  | nil =>
      simp
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp
      | cons y ys =>
          rcases hS with ⟨hxy, htail⟩
          have htailChain := ih htail
          apply List.IsChain.cons htailChain
          intro z hz
          simp at hz
          subst z
          exact hrel (by linarith : x < y)

/-- A monotone dressing of S-readings gives nondecreasing AMP margins. -/
theorem isChain_map_le_of_adjacentStepPos {S : List ℝ} {dress : ℝ → ℝ}
    (hS : AdjacentStepPos S) (hdress : Monotone dress) :
    List.IsChain (fun x y => x ≤ y) (S.map dress) :=
  isChain_map_of_adjacentStepPos hS (fun hxy => hdress (le_of_lt hxy))

/-- An antitone dressing of S-readings gives nonincreasing AMP margins. -/
theorem isChain_map_ge_of_adjacentStepPos {S : List ℝ} {dress : ℝ → ℝ}
    (hS : AdjacentStepPos S) (hdress : Antitone dress) :
    List.IsChain (fun x y => y ≤ x) (S.map dress) :=
  isChain_map_of_adjacentStepPos hS (fun hxy => hdress (le_of_lt hxy))

/-- S-mono provider package from positive adjacent S-increments and monotone dressing. -/
theorem ampReaderInput_of_smono_dressing_le {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (hS : AdjacentStepPos S) (hdress : Monotone dress)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))) :
    AMPReaderInput (S.map dress) Z :=
  ampReaderInput_of_chain_le (isChain_map_le_of_adjacentStepPos hS hdress)
    hvisible heven hbound

/-- S-mono provider package from positive adjacent S-increments and antitone dressing. -/
theorem ampReaderInput_of_smono_dressing_ge {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (hS : AdjacentStepPos S) (hdress : Antitone dress)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))) :
    AMPReaderInput (S.map dress) Z :=
  ampReaderInput_of_chain_ge (isChain_map_ge_of_adjacentStepPos hS hdress)
    hvisible heven hbound

/-- Exact reader pair from S-mono and a monotone S-to-margin dressing. -/
theorem amp_reader_exact_pair_of_smono_dressing_le {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (hS : AdjacentStepPos S) (hdress : Monotone dress)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))) :
    Z = 2 :=
  amp_reader_exact_pair_of_input
    (ampReaderInput_of_smono_dressing_le hS hdress hvisible heven hbound)

/-- Exact reader pair from S-mono and an antitone S-to-margin dressing. -/
theorem amp_reader_exact_pair_of_smono_dressing_ge {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (hS : AdjacentStepPos S) (hdress : Antitone dress)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))) :
    Z = 2 :=
  amp_reader_exact_pair_of_input
    (ampReaderInput_of_smono_dressing_ge hS hdress hvisible heven hbound)

end RHTower
