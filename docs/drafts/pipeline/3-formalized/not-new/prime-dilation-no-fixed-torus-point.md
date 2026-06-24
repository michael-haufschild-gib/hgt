# Prime dilation has no fixed torus point

- **ID:** prime-dilation-no-fixed-torus-point
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/multi-q-shafarevich-gluing-group.md` R3 repaired non-retraction argument
- **Statement:** The prime-lane dilation `z |-> p^{-1} z` has no nonzero fixed point, hence no coordinate of the algebraic torus `C^x` and no torus point can be fixed by all prime-lane dilations.

## Goal
This banks the algebraic fixed-point obstruction used in the repaired non-retraction argument for the multi-`q` Shafarevich gluing group. It does not formalize nonabelian `H^1`, the character-variety/Procesi import, or the direct C5-star coboundary-regularity identification.

## Paper Proof
If `p^{-1} z = z`, then `(p^{-1}-1) z = 0`. Since `p` is prime, `p != 1`, hence `p^{-1}-1 != 0`; therefore
`z=0`. Thus no element of `C^x` is fixed by `z |-> p^{-1} z`. A torus point fixed coordinatewise by all
prime dilations would in particular have its `p=2` coordinate fixed, impossible because that coordinate lies
in `C^x`.

## Gates
- [x] 0 -> 1  in-progress: exact no-fixed-point lemma extracted from the repaired R3 non-retraction argument.
- [x] 1 -> 2  fully-proven: paper proof above, using only `p != 1` and cancellation in `C`.
- [x] 2 -> 3  formalized: Lean theorems `primeDilation_fixed_eq_zero`, `primeDilation_no_fixed_unit`, and `no_primeDilation_fixed_torus_point` in `formal/GaloisForLFunctions/OrbitFreeness.lean`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the Lean certificate for the non-retraction sublemma.

## Log
- 2026-06-19 — Leaner split this exact no-fixed-point lemma from `multi-q-shafarevich-gluing-group`. The parent card remains in `2-fully-proven` because the full `Ш` computation is not fully Lean-formalized.

