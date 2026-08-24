# Source-pointed normal-jet conservation

- **ID:** RH-SOURCE-POINTED-NORMAL-JET
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus synthesis of BV--Wold asymptotic gauge blindness and finite source splitting
- **Statement:** Dividing distinguished-splitting displacement by canonical normalized BV--Wold potential recovers hidden modulus exactly, independent of prime and depth; Xi reflection negates this normal jet.

## Goal

Test claim that RH-bearing datum survives only as first normal jet of source-pointed filtered degeneration, although ordinary frame and associated graded collapse.

## Gates

- [x] 0 → 1 in-progress: source-pure definition and falsifiable exact formula
- [x] 1 → 2 fully-proven: complete algebraic proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem `primeDepthBVWoldSourcePointedNormalJet_eq`
- [ ] 3 → 4 publication-ready

## Approach

At finite cell `i`, resolved relative gauge sends distinguished section `(0,1)` to
`(a P_i,1)`, where `P_i > 0` is normalized BV--Wold potential. Hence horizontal
displacement divided by `P_i` equals `a`. This quotient is cell-independent even
though `P_(p,e) → 0` and unrenormalized frames tend to identity. Xi specialization
sets `a = 2 Re rho - 1`; line reflection sends `a` to `-a`, so fixedness is exactly
`Re rho = 1/2`.

## Log

- 2026-08-24 — `[PROVED HERE]` paper proof closed after corpus novelty search.
- 2026-08-24 — formalized; targeted build and axiom audit passed.
