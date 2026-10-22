# Aperture Morse charge: monotone, vanishing = positivity, first crossing — formalized closure

- **ID:** `ccm-aperture-morse-index-conservation-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-aperture-morse-index-conservation-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCM.CCMApertureMorseCharge`

Umbrella: `GaloisForLFunctions.RHTower` (imported at `formal/GaloisForLFunctions/RHTower.lean`).

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)` | `HasNegDefSubspaceOfDim`, `morseCharge` | the achievable negative-definite dimensions of a real form on a trial submodule, and their supremum |
| `(4)`–`(5)` | `HasNegDefSubspaceOfDim.mono` | zero extension: every negative-definite subspace of the smaller aperture domain is one of the larger, of the same dimension. In the submodule representation this is literal inclusion `D ≤ D'`, so no isometry has to be constructed and no form-preservation identity has to be checked |
| `(3)` | `morseCharge_mono` | the charge is monotone in the trial domain |
| `(ii)` ↔ `(iii)` | `hasNegDefSubspaceOfDim_one`, `negDefDims_eq_zero_iff_nonneg` | the charge vanishes exactly when the form is nonnegative on the domain; the nontrivial direction builds an explicit one-dimensional negative subspace `span{v}` from a single negative vector, using only degree-two homogeneity |
| `(6)` | `morseCharge_eq_zero_of_nonneg` | the small-aperture anchor: a nonnegative form has charge `0` |
| `(9)` | `exists_crossing_of_pos_of_neg` | the first crossing: a continuous aperture-indexed bottom eigenvalue positive at a small aperture and negative at a larger one vanishes strictly in between |

`morseCharge_mono` carries `BddAbove` on the larger domain's dimension set. That is not an
assumption about the aperture geometry: it is exactly the finiteness `(2)` that the card derives
analytically from discreteness of `spec(A_a)`, and it is genuinely needed because `sSup` of an
unbounded set of naturals is `0`. The set-level statement `HasNegDefSubspaceOfDim.mono` carries no
hypothesis at all.

## Axioms

`#print axioms` on all six theorems of the module returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is used.

## Deliberately outside the Lean statement

These are the card's cited parents, not theorems it proves:

- discreteness and lower boundedness of `spec(A_a)`, which is what supplies finiteness `(2)`;
- Yoshida's localized Weil criterion `(i) ↔ (iii)` and his nondegeneracy criterion `(i) ↔ (iv)`;
- Suzuki's identity `(8)` and the completed-space generalized eigenvalue equivalence `(iv) ↔ (v)`,
  with the corona statement `(7a)`;
- continuity of `lambda_0` in the aperture, which is the hypothesis `exists_crossing_of_pos_of_neg`
  consumes.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
- Every declaration named in the card's Lean status section exists in the tree.
