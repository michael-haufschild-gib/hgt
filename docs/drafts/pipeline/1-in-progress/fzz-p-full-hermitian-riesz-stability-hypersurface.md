# FZZ-P full Hermitian Riesz stability hypersurface

- **ID:** FZZ-P-HC36
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / exact four-parameter classification and no-go
- **Source:** HC1--HC3 Hermitian reporter coordinates + HC34--HC35 Riesz stability laws
- **Frontier map:** read-only; no edit permitted

## Frozen conjecture

Let `G_beta=[[P,Q],[Q,R]]`, `E=Q^2-PR>0`, and let `A_beta` be the canonical
source-Krein generator. For every Hermitian reporter

`H(a,b,c,d)=[[a,b+i c],[b-i c,d]]`,

its literal source-metric Riesz representative is

`B=E^-1 [[-Ra+Qb-iQc, -Rb+Qd-iRc],`

`          [ Qa-Pb+iPc,  Qb-Pd+iQc]]`.

For `M=A+B`, define

`T=(-Ra+2Qb-Pd)/E`,

`D=((b^2+c^2)-(a-PE/R)(d+E))/E`,

`Delta=T^2-4D`.

Conjecture:

1. `B` Riesz-represents `H` and `M` is formally `G_beta`-self-adjoint;
2. every eigenvalue of `M` satisfies `lambda^2-T lambda+D=0`;
3. actual spectral reality of `M` is equivalent to `Delta>=0`;
4. `Delta<0` carries an explicit nonreal neutral eigenpair;
5. source-defined reporter `(a,b,c,d)=(PE/R,0,0,-E)` is unique reporter with `M=0`;
6. this annihilating reporter lies strictly inside existing reflection-detector cone because
   `d=-E!=0` and `b^2+c^2=0<d^2`.

Items 5--6 would show that even a universal RH-strength radial-reflection detector can annihilate
the canonical local generator unconditionally. Hence no spectral-stability or stationary-kernel
principle on complete local Hermitian Riesz family can supply missing FZZ/GFZZ divisor matching.

## Paper derivation

`det G=PR-Q^2=-E`, so direct inversion gives displayed `B=G^-1 H`. Moreover

`G A = diag(-PE/R,E)`.

Therefore

`G M = [[a-PE/R,b+i c],[b-i c,d+E]]`.

Taking trace after multiplication by `G^-1` gives `T`; multiplicativity of two-by-two determinant
gives

`det M = det(GM)/det G = ((b^2+c^2)-(a-PE/R)(d+E))/E=D`.

Characteristic polynomial has real coefficients. Its roots are real exactly for `Delta>=0`; for
`Delta<0`, `T/2+i sqrt(-Delta)/2` is a nonreal root and a two-case explicit kernel vector of
`M-lambda I` supplies eigenpair. Formal self-adjointness makes every nonreal eigenvector neutral.
Finally `M=0` iff `GM=0`, which forces four displayed coefficients, and cone claim follows from
`E>0`.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "FZZ nonlinear Riesz feedback state dependent coupling parity stability"`
- `scripts/formal_tools.py research "FZZ Hermitian quadratic observable Riesz representative general coefficients"`
- `scripts/formal_tools.py research "FZZ full Hermitian reporter spectral stability source metric"`

Corpus contains four reporter coordinates and two-coordinate Riesz slice, but no complete
four-parameter Riesz representative, stability hypersurface, or detector-annihilator theorem.

## Literature boundary

Current primary-source search found generic pseudo-Hermitian/Krein spectral theory and FZZ
duality papers, but no source-specific four-parameter stability hypersurface or detector-annihilator
law. Generic two-by-two discriminant and Riesz inversion are standard; novelty claim is limited to
literal FZZ source synthesis and resulting route closure.

## Status

- [x] corpus-led conjecture frozen
- [x] dependency-closed paper derivation
- [ ] Lean formalization
- [ ] direct check, targeted build, axiom/lint audit, umbrella wiring
- [ ] move to `3-formalized`
