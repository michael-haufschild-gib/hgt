# Exact bounded kernel of the literal Fermi correlation-jet packet

- **ID:** pm-correlation-jet-kernel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route PM; correlation-Mellin multiplicity coordinates
- **Statement:** For every actual Fermi witness, its full submultiplicity correlation-jet packet vanishes iff it is dyadically self-similar iff it is bounded on `(0,1]`.
- **Novelty:** Supporting classification for the new physical coordinates; elementary compactness and classical Mellin factorization are not claimed novel. Exact packet classification was not found in scoped corpus searches. Publication novelty remains provisional.

## Goal

Identify exactly what the multiplicity coordinates forget. Their kernel consists of bounded
periodic-in-log witnesses, not the Hermitian radical. This can support a source decomposition
and a faithful action on the quotient; it does not show every witness is bounded.

## Gates

- [x] 0 → 1: intrinsic witness packet and boundedness well defined
- [x] 1 → 2: dependency-closed proof below, [PROVED HERE]
- [x] 2 → 3: actual-leaf Lean audit and axiom audit
- [ ] 3 → 4: standalone publication and completed novelty review

## Dependency-closed paper proof

1. Zero jet packet implies dyadic self-similarity by the audited local cancellation theorem.
2. Suppose `w(t/2)=w(t)` on `(0,1]`. Continuity bounds its norm on `[1/2,1]`. For every
   `0<t≤1`, choose `n≥0` with `2^(-n-1)<t≤2^(-n)` and put `x=2^n t`. Then `x∈[1/2,1]`
   and iteration gives `w(t)=w(x)`. The same compact bound therefore applies on all `(0,1]`.
3. A bounded literal witness has Mellin exponent zero. Its correlation-Mellin transform obeys
   the literal source Fubini identity throughout `0<Re s<1`:

   `C_w(s)=U_1(s) zeta(s) W_(conj w)(1-s)`.

   Here `U_1` is analytic away from `0` and the witness Mellin transform is analytic for
   `Re(1-s)>0`. Near every actual right-strip zero, the analytic order of correlation is at
   least the zeta order. Every derivative below that order vanishes, hence the conjugated
   coordinate packet is zero.
4. Steps 1–3 prove all three equivalences unconditionally for each actual witness.

## Audit boundaries

The common kernel is a neutral subspace, but it is not asserted to be the form radical:
spurious self-similar witnesses have nonzero pairing with admitted zero jets whenever those
zero jets exist. Equality of kernels is proved from the literal source factorization, not
inferred from equal ranks in infinite dimension.

Corpus search `Fermi bounded correlation jet kernel selfsimilar --any --module FermiNyman`
returned prior boundedness-to-self-similarity and new zero-packet-to-self-similarity implications,
but no converse packet theorem. Search reported `partial: true`; coverage limits are retained.
Scoped public checks found classical zero-jet and dilation work; no global novelty certification.

## Log

- 2026-09-29 — closed paper proof; `/tmp/pm_kernel.lean` drafted, compiler audit pending.

## Complete Lean certificate

`formal/GaloisForLFunctions/RHTower/FermiNymanCorrelationKernel.lean` proves the literal
compact-interval dyadic reduction, analytic source factorization at every actual right-strip
zero, and vanishing of every derivative below its full analytic multiplicity.
`RHTower.IsFermiNymanWitness.jetPacket_eq_zero_iff_bounded` and
`RHTower.IsFermiNymanWitness.jetPacket_eq_zero_iff_selfSimilar` give both stated equivalences
on the original witness domain. The intrinsic capstone
`RHTower.fermiMultiplicityJetKernelSet_eq_boundedFermiWitnessSet` has no hypothesis parameters.
The analytic-order comparison assumes neither RH, simple zeros nor a finite zero set.

Needed leaf artifacts passed the targeted PM `lake --old build`; final
`lake env lean GaloisForLFunctions/RHTower/FermiNymanCorrelationKernel.lean` passed exit 0.
The shared 52-declaration PM axiom audit found only `propext`, `Classical.choice`, and
`Quot.sound`. The leaf is imported by `RHTower.lean`. Authoritative formal lint reported only
ten unrelated concurrent reachability failures, with no finding on this certificate.

- 2026-09-29 — every paper implication and intrinsic kernel equality audited; moved to Stage 3.
