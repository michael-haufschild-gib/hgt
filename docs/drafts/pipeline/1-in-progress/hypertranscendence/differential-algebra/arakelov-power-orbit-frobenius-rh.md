# Arakelov power-orbit Frobenius route to RH

- **ID:** `arakelov-power-orbit-frobenius-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [RH ROUTE] [LARGE OUTLANDISH DETOUR]`
- **Source:** `ArakelovW.lean`, `ArakelovModularLambdaFE.lean`,
  `LocalDivisorJetAdamsDilation.lean`, and the complete Böttcher power/cover corpus
- **Lean:** `formal/GaloisForLFunctions/RHTower/ArakelovPowerOrbitRH.lean`

## Claim

Put

```text
w(rho) = 1 - 1/rho,
P_n(rho) = 1 / (1 - w(rho)^n).
```

The functional equation acts by `w -> w^(-1)`, while the critical line is exactly
`|w| = 1`.  For every fixed `n >= 2`, forward invariance of the Xi divisor under `P_n`
forces RH:

```text
xi(rho)=0 -> xi(P_n(rho))=0
  -> xi(P_n^k(rho))=0 for every k
  -> w(P_n^k(rho)) = w(rho)^(n^k).
```

If `rho` were a right-half zero, then `|w(rho)|<1`, so the power orbit converges to
`w=0`, hence `P_n^k(rho)->1`.  Continuity would give `xi(1)=0`, contradicting
`xi(1)=1/2`.  Functional-equation reflection already reduces RH to excluding right-half
zeros, so no separate outside-unit-circle argument is needed.

`[PROVED LEAN]` The complete right end is formalized.  In particular,
`riemannHypothesis_of_xiRightArakelovPowerStable` uses stability only on hypothetical
right-half zeros, and `riemannHypothesis_of_xiArakelovPowerPreperiodic` uses only a finite
power orbit of their Arakelov marks.

Lean also proves that both right-half-only certificates are equivalent to RH.  Their reverse
directions are vacuous under RH, so neither is standalone progress: the mathematical content must
come from a separately defined source endomorphism or finite-monodromy object.

## Two-ended closure

```text
prime Adams / Frobenius operation p -> p^n
  -> source-canonical global endomorphism of the completed prime--Gamma constraint
  -> Arakelov spectral coordinate transforms by w -> w^n
       [OPEN CORE]
  -> the actual Xi divisor is forward invariant under P_n
  -> every right-half zero has a zero orbit accumulating at the nonzero anchor s=1
  -> contradiction
  -> RH.
```

The right end is independent of multiplicity, simplicity, positivity, Weil forms,
Hermitian spectra, and roots of Xi.  It needs only one fixed power `n>=2` and ordinary
analytic continuity.

There is an even weaker finite-monodromy closure.  It is enough to prove that every Xi zero has
a preperiodic Arakelov coordinate under one power map whenever it lies in the right half-plane:

```text
w(rho)^(n^a) = w(rho)^(n^b) for some a<b.
```

A right-half zero has `0<|w(rho)|<1`, where distinct powers cannot agree.  This variant never
asks that a powered point remain in the Xi divisor.  A finite source monodromy orbit for the
Arakelov mark therefore proves RH directly.

The forward-invariance hypothesis also needs to hold only on the hypothetical right-half
divisor.  The power lift preserves that half-plane, so the orbit induction never asks for an
identity at the known critical-line zeros.  This removes the implausibly strong demand that a
source map permute the actual on-line divisor.

## Attack and firewalls

1. **A coordinate power chosen after reading a zero is circular.**  The endomorphism must
   act on the completed Euler--Gamma source before any divisor is extracted.
2. **The prime-local Adams law is not yet the global law.**  The proved prime-power jet
   transformation scales a local exponential variable; it does not prove that the global
   Arakelov coordinate of a zero is powered.
3. **Böttcher dynamics alone is external.**  The power map and its coherent roots exist in
   the dynamical cover, but an arbitrary identification of a Xi point with a Böttcher fibre
   does not transport the Xi divisor.
4. **Setwise invariance is enough; multiplicity preservation is unnecessary.**  A viable
   source comparison may therefore be much weaker than determinant equality or local purity.
5. **Finite monodromy is weaker still.**  A source-defined finite orbit of the Arakelov mark at
   each divisor point suffices even if no global self-map of the divisor exists.
6. **The ordinary modular deck group cannot be the producer.**  The existing theorem
   `lambdaPunct_invariant` says every `Gamma(2)` deck transformation fixes `lambda`; it cannot
   induce `lambda -> lambda^n` except at a torsion value.  The positive successor is a non-deck
   modular correspondence or a source operation before passage to the modular quotient.
7. **Bare prime Adams is in the wrong coordinate.**  The local theorem sends the Euler variable
   `p^(-rho)` to `p^(-n rho)` and dilates divisor jets.  It does not send
   `w(rho)` to `w(rho)^n`; indeed the latter power lift fixes the anchor `rho=1`, whereas spectral
   dilation sends it to `n`.  A successful construction must use the completed two-boundary
   cross-ratio, not the uncompleted local Euler dilation.
8. **The right-half certificates are RH-equivalent.**  A source theorem may not simply restate
   stability or preperiodicity on Xi zeros.  It must first construct the acting object on the
   completed source, with its power law established independently of the divisor.

## Positive statement from the present no-go

The local-Adams failure to imply reducedness does not kill Frobenius dynamics.  It selects a
different global target:

> construct one source endomorphism whose induced map on the Arakelov spectral parameter is
> `w -> w^n` and which carries Xi zeros to Xi zeros, without requiring equal local weights or
> an action on the local divisor jet.

This is strictly weaker than a source factorization of Xi and orthogonal to the local-purity
premise.  Any such endomorphism closes the full RH chain by accumulation at `s=1`.

## Gates

- [x] 0 -> 1: exact source and RH endpoints identified; circular implementations excluded
- [ ] 1 -> 2: analytic power-orbit and finite-monodromy endpoints proved; construct the source
  Frobenius or free-orbit finite-monodromy theorem
- [ ] 2 -> 3: formalize the complete composition and audit axioms
- [ ] 3 -> 4: only after the source endomorphism is obtained without divisor input
