/-
SPUR-R / AMP reader capstone.

The sister proof stacks expose a single theorem surface after their local
providers are isolated.  This module does the same for the SPUR-R / AMP reader:
the S-mono or ledger side supplies a monotone chain of AMP margin readings, and
the finite threshold/counting stack closes exact reader visibility.
-/
import GaloisForLFunctions.RHTower.SpurMonotone

noncomputable section

namespace RHTower

/-- Packaged provider input for SPUR-R/AMP reader exactness.

The analytic side is only the monotonicity of the ordered AMP margin readings.
The other fields are the finite reader-counting hypotheses from doc 24:
Hurwitz visibility, evenness of the non-real zero count, and the corrected
`Z ≤ 2 + T` bound with `T` instantiated as the actual copy/flip transitions. -/
structure AMPReaderInput (margins : List ℝ) (Z : ℕ) : Prop where
  monotone :
    List.Pairwise (fun x y => x ≤ y) margins ∨
      List.Pairwise (fun x y => y ≤ x) margins
  visible : 0 < Z
  even : Even Z
  counting_bound : Z ≤ 2 + copyFlipTransitions (ampMarginStates margins)

/-- Adjacent nondecreasing AMP margins produce the reader input package.

This is the shape expected from the S-mono/LedgerConvex side: it proves positivity
step-by-step, and `List.IsChain.pairwise` upgrades adjacent monotonicity to the
pairwise monotonicity consumed by `SpurMonotone`. -/
theorem ampReaderInput_of_chain_le {margins : List ℝ} {Z : ℕ}
    (hchain : List.IsChain (fun x y => x ≤ y) margins)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates margins)) :
    AMPReaderInput margins Z :=
  ⟨Or.inl (List.IsChain.pairwise hchain), hvisible, heven, hbound⟩

/-- Adjacent nonincreasing AMP margins produce the reader input package. -/
theorem ampReaderInput_of_chain_ge {margins : List ℝ} {Z : ℕ}
    (hchain : List.IsChain (fun x y => y ≤ x) margins)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates margins)) :
    AMPReaderInput margins Z :=
  ⟨Or.inr (List.IsChain.pairwise hchain), hvisible, heven, hbound⟩

/-- SPUR-R/AMP reader exactness capstone from the packaged provider input. -/
theorem amp_reader_exact_pair_of_input {margins : List ℝ} {Z : ℕ}
    (h : AMPReaderInput margins Z) : Z = 2 := by
  rcases h with ⟨hmono, hvisible, heven, hbound⟩
  rcases hmono with hle | hge
  · exact corrected_counting_exact_pair_of_ampMargin_pairwise_le hle hvisible heven hbound
  · exact corrected_counting_exact_pair_of_ampMargin_pairwise_ge hge hvisible heven hbound

/-- SPUR-R/AMP reader exactness from adjacent nondecreasing AMP margins. -/
theorem amp_reader_exact_pair_of_chain_le {margins : List ℝ} {Z : ℕ}
    (hchain : List.IsChain (fun x y => x ≤ y) margins)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates margins)) :
    Z = 2 :=
  amp_reader_exact_pair_of_input (ampReaderInput_of_chain_le hchain hvisible heven hbound)

/-- SPUR-R/AMP reader exactness from adjacent nonincreasing AMP margins. -/
theorem amp_reader_exact_pair_of_chain_ge {margins : List ℝ} {Z : ℕ}
    (hchain : List.IsChain (fun x y => y ≤ x) margins)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates margins)) :
    Z = 2 :=
  amp_reader_exact_pair_of_input (ampReaderInput_of_chain_ge hchain hvisible heven hbound)

end RHTower
