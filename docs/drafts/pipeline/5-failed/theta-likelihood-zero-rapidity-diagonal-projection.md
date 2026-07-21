# Theta-likelihood zero-rapidity diagonal projection

- **Status:** `[FAILED] [UNCONDITIONAL COUNTEREXAMPLE] [POSITIVE SURVIVOR FORMALIZED]`
- **Parent:**
  `../3-formalized/new_scientific_knowledge/theta-likelihood-prime-square-conormal-sign-wall.md`
- **Counterexample:**
  `../3-formalized/new_scientific_knowledge/theta-likelihood-prime-cube-lee-yang-cone.md`

## Proposed route

For each composite likelihood product fibre, remove its zero-rapidity divisor modes from phase
value while leaving spectral derivative unchanged.  Prime-square wall theorem makes this proposal
natural: its unique central mode reverses raw wall current, and deleting exactly that amplitude
restores strict negative wall current.

## Exact failure

Prime cube has factor exponents `0,1,2,3`, hence rapidities

```text
-3 log(p)/2, -log(p)/2, log(p)/2, 3 log(p)/2.
```

Lean proves every rapidity is nonzero.  Thus zero-rapidity projection acts identically on complete
`p^3` packet.

On likelihood face `D=0`, actual packet is

```text
F(z)=a(B)[exp(-3iLz/2)+exp(3iLz/2)]
    +b(B)[exp(-iLz/2)+exp(iLz/2)],

a(B)=B R_(p^3),
b(B)=S_p(B)R_(p^2)+R_pS_(p^2)(B),
L=log p.
```

For every sufficiently small `B>0`, exact boundary values give `b(B)>3a(B)`.  Sharp formal
classifier supplies `z` in upper half-plane with positive current.  Since diagonal projection
changes nothing, it cannot orient this shell.

## Corpus-level hostile audit

This failure does not license arbitrary replacement of weighted packet by favorable unweighted
divisor phase.  Corpus already proves

```text
actual fibre current = coherent oriented base + corrected Hermitian/window seam,
corrected seam >= actual fibre current,
```

and finite-arithmetic/Haar conservation returns raw current as surviving remainder.  Therefore a
fibrewise endpoint projection solves only a surrogate carrier; without exact seam identity it does
not solve RH-bearing source current.

## Positive survivor

`[FORMALIZED]` For every positive symmetric four-band packet, global strict negative
upper-half-plane current holds exactly on Lee--Yang coefficient cone

```text
b <= 3a.
```

Equivalently coefficient polynomial

```text
1+(b/a)X+(b/a)X^2+X^3
```

has all roots on unit circle.  Outside cone, explicit reflection-wall point has positive current.
This is stronger than failed diagonal rule because it detects interference between distinct
nonzero rapidity bands.

## Exact next problem

Local stationary-mode deletion is retired.  Actual corpus frontier remains:

> Prove unconditional source law controlling raw theta-tail/Hermitian seam current after exact
> cofinal summation.  Any local fibre correction must enter through equality with actual seam;
> favorable orientation of replacement carrier alone is inadmissible.

Candidate must survive three tests:

1. reproduce prime-square and prime-cube coefficient-cone laws;
2. retain exact positive-half-line Hermitian/window seam rather than discard it;
3. break finite-arithmetic conservation law that otherwise returns raw RH-equivalent current.

## Log

- 2026-07-21 — Proposed from exact prime-square diagonal repair.
- 2026-07-21 — Refuted unconditionally by diagonal-free prime-cube anti-cone exit.
- 2026-07-21 — Sharp Lee--Yang coefficient cone extracted and formalized as positive survivor.
