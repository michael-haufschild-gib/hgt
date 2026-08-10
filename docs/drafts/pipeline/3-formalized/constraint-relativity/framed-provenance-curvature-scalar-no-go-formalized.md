# Framed provenance curvature and universal scalar no-go — formalized

- **ID:** `framed-provenance-curvature-scalar-no-go-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `framed-provenance-curvature-scalar-no-go.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ProvenanceCurvature` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ProvenanceCurvature.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Section 2 — completion compositors realize every interval:

1. `midClosure`, `midClosure_monotone`, `midClosure_extensive`, `midClosure_idempotent` — the
   closure of the three-chain that collapses the middle point upward, verified to be a closure
   operator.
2. `rawTransport`, `rawTransport_monotone` — the transport `C₂ → C₃` hitting the non-closed point.
3. `interval_is_completion_defect` — **Lemma 2.1**: for any comparable pair `a ≤ b` in any partial
   order with bottom there is a monotone `V` with `V(T 1) = a` and `V(c(T 1)) = b`, i.e. the
   compositor `(2.2)` is exactly `a ≤ b`.

Section 3 — the nucleus forgets flatness:

4. `nucleusTransport`, `collapseReporter` and their monotonicity.
5. `nucleus_forgets_flatness` — **Theorem 3.1**: the raw transport and the nucleus transport have
   the same completion, the nucleus transport already lands in the nucleus, yet the first
   compositor is strict and the second is flat.  So BC-flatness is not an invariant of the nucleus
   plus induced completed maps; the closure unit is not expendable syntax.

Section 4 — additive scalars are potentials:

6. `additive_eq_potential_sub` — **Theorem 4.1**, `(4.3)`: `D(x,y) = v(y) − v(x)` with
   `v = D(⊥, ·)`.
7. `additive_bot_self` — `D(⊥,⊥) = 0`.
8. `faithful_iff_strict_potential` — **Theorem 4.1**, faithfulness holds exactly when the potential
   is strictly increasing.

Section 5 — the sharp scalar no-go:

9. `embedExtreme`, `retractDown`, `embedLower`, `retractUp` — the four bottom-preserving join maps
   between the two- and three-element chains.
10. `scalar_nogo` — **Theorem 5.1**: chain additivity, faithfulness and data processing along those
    four maps are jointly contradictory.  The proof is the card's: data processing in both
    directions pins `D₃(0,1) = D₃(0,2) = δ`, and additivity then forces `D₃(1,2) = 0`.

Section 6 — the universal positive survivor:

11. `provenance`, `provenanceClass` — **card `(6.1)`–`(6.2)`**: the free provenance group
    `ℤ^{L∖{⊥}}` and the oriented class `J(x,y) = e_y − e_x`.
12. `provenanceClass_add` — the universal class is chain-additive.
12b. `provenance_injective`, `provenanceClass_eq_zero_iff`, `provenanceClass_swap` — **card
    `(6.3)`**: the universal class vanishes exactly on the diagonal and reverses sign under
    swapping.  It is a faithful *oriented* invariant, which no scalar magnitude of it is.
12c. `provenanceMap`, `provenanceMap_provenance`, `provenanceMap_provenanceClass` — **card
    `(6.5)`**: functoriality of the provenance group, and naturality of the universal class along
    any bottom-preserving map of the base.
13. `additive_factors_through_provenance` — **the universal survivor**: every chain-additive
    divergence is `φ ∘ J` for an additive `φ`, i.e. for an observer-chosen potential.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ProvenanceCurvature.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                   # green
```
