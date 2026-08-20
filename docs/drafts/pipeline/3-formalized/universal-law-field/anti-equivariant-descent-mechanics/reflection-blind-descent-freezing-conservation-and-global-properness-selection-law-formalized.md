# Reflection-blind descent freezing and global properness selection — Lean certification

- **ID:** ULF-AEDM-1
- **Paper card:** `reflection-blind-descent-freezing-conservation-and-global-properness-selection-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.AntiEquivariantDescentFormation`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## Certified declarations

### Theorem 1.1 — reflection-pair defect conservation (AED.5)

`antiEquivariantDescentDefect` types the descent failure `qD − D̄q`;
`antiEquivariantDescentDefect_reflection_conservation` proves
`Δ(x) + Δ(Rx) = (−2)·D̄(qx)` from `RD = −DR` and `qR = q` alone.

### Corollary 1.2 — blind descent freezing (AED.7, AED.8)

`antiEquivariant_blind_descent_zero` (`D̄ ∘ q = 0`) and
`antiEquivariant_blind_surjective_descent_zero` (`D̄ = 0`).  Invertibility of `2` over `ℝ` is the
load-bearing step, exactly as the card's hostile boundary 3 records.

### Theorem 2.1 — marked descent transports anti-equivariance (AED.10)

`marked_surjective_descent_transports_antiEquivariance`: `S D̄ = −D̄ S`.

### Theorem 3.1 — reversible blind flow freezing (AED.13)

Two forms.  `reversible_blind_surjective_action_static` is the coordinate-free statement of the
card's §3 — *sets only*, no linearity, no topology, no continuity — and
`reversible_blind_surjective_flow_static` is the linear-operator form.  Divisibility of `ℝ` is used
exactly once (`t = t/2 + t/2`), matching the card's hostile boundary 4 on discrete time.

### Lemma 4.1 and Theorem 4.2 — the properness selector (AED.15, AED.17)

`constantFamily_not_compactPreimageProper_of_noncompactClosure` is Lemma 4.1;
`reversible_blind_proper_formation_forces_neutral` is Theorem 4.2, with the card's independent
source-formation input `(AED.16)` carried as the hypothesis it is on the card
(`IsCompact (closure (range fun t => U t x)) ↔ a = 0`).  `CompactPreimageProper` comes from
`HTGeometry.NomologicalHomotopyGeometry.GaugeProperness`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AntiEquivariantDescentFormation.lean
```

Elaborates with no errors or warnings.  `#print axioms` on all eight declarations
(`reversible_blind_surjective_action_static`,
`antiEquivariantDescentDefect_reflection_conservation`, `antiEquivariant_blind_descent_zero`,
`antiEquivariant_blind_surjective_descent_zero`,
`marked_surjective_descent_transports_antiEquivariance`,
`reversible_blind_surjective_flow_static`,
`constantFamily_not_compactPreimageProper_of_noncompactClosure`,
`reversible_blind_proper_formation_forces_neutral`) reports only `propext`, `Classical.choice`,
`Quot.sound`.  The module is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Still open (not a proved theorem)

Gate 3 → 4 of the card: construct a literal pre-zero source formation satisfying `(AED.16)` with a
source-normal compact-preimage-proper recovery.  The card states this as an open construction
burden, not as a proved statement, so it does not block stage 3.
