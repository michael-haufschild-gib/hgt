# Source-law base and observer-fibre nonreconstruction — formalized

- **ID:** `cfr-source-law-base-nonreconstruction-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `source-law-base-and-observer-fibre-nonreconstruction-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.SourceLawNonreconstruction` | new |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 1.1 — same observer indices, opposite jet law, card `(SL.1)`/`(SL.2)`:

1. `freeProlongation` — the derivation `D₊ X_j = X_{j+1}` of `MvPolynomial ℕ K`, built by
   `MvPolynomial.mkDerivation`, so it is the unique `K`-derivation with the prescribed values on
   the transcendence basis.
2. `truncProlongation` — the derivation `D_m` of `(SL.2)`: `X_j ↦ X_{j+1}` for `j < m` and
   `X_j ↦ 0` for `j ≥ m`.
3. `freeProlongation_iterate` — `D₊ⁿ X_0 = X_n`.
4. `freeProlongation_algebraicIndependent` — the complete `D₊`-jet tower is algebraically
   independent.
5. `truncProlongation_iterate_le` — `D_mʲ X_0 = X_j` for `j ≤ m`.
6. `truncProlongation_iterate_wall` — `D_m^{m+1} X_0 = 0`.
7. `truncProlongation_iterate_gt`, `truncProlongation_orbit_mem_span` — the whole `D_m`-orbit of
   `X_0` lies in `span_K {X_0, …, X_m}`.
8. `jet_law_nonreconstruction` — the theorem: on the same algebra, the same packet and the same
   observed jet depth `m + 1`, one jet tower is algebraically independent and nonzero while the
   other is annihilated.

Theorem 2.1 — fixed observer coordinates, changed Lorentz law, card `(SL.3)`/`(SL.4)`:

9. `contactForm` — the exact form `Q_j = ((1+j)/2) z² + ((3-j)/2) t²` of `(SL.4)`.
10. `contactForm_pos` — at `j = 1` the form is positive definite, so its negative index is zero.
11. `contactForm_neg` — at `j = 4` the form takes a negative value on the port direction, so its
    negative index is one.
12. `contactForm_port` — the port coefficient is the `t²` coefficient, unchanged in form.
13. `cluster_split` — the boxed identity `(SL.3)`:
    `-2(k-ℓ) X_U X_V = ((k-ℓ)/2)((X_U - X_V)² - M²)` with `M = X_U + X_V`.

Theorem 3.1 — nonreconstruction:

Items 8 and 10–11 are the two exact pairs the card uses: each shares the tuple
`(coefficient doctrine, prolongation index, aperture, history)` and differs in the governing law,
so no invariant of that tuple determines it.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/SourceLawNonreconstruction.lean  # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
