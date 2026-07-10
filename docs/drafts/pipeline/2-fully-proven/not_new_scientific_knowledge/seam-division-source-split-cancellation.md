# Seam Division Source Split Requires FE Cancellation

- **ID:** seam-division-source-split-cancellation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / analytic source-split guardrail
- **Source:** `seam-log-derivative-weld-identity.md`;
  `archimedean-prime-cross-term.md`; `carrier-herglotz-rh.md`
- **Statement:** After division by the seam coordinate, the completed
  log-derivative is holomorphic, but its archimedean and prime summands are not.
  Each summand has a nonzero simple pole at the seam, and the functional equation
  cancels those poles exactly.

## Setup

Let

`Xi(w)=xi(1/2+w)`,

with

`xi(s)=1/2 s(s-1) pi^(-s/2) Gamma(s/2) zeta(s)`.

Write `s=1/2+w` and split the completed logarithmic derivative as

`Xi'(w)/Xi(w)=A(w)+P(w)`,

where

`A(w)=1/s+1/(s-1)-(1/2)log pi+(1/2)psi(s/2)`

and

`P(w)=zeta'(s)/zeta(s)`.

By `seam-log-derivative-weld-identity.md`, the seam-log Markov candidate is

`G_src(-w^2)=Xi'(w)/(w Xi(w))`.

## Theorem

The completed quotient

`(A(w)+P(w))/w`

is holomorphic at `w=0`, but the two source pieces `A(w)/w` and `P(w)/w` each
have a nonzero simple pole there. Their residues are opposite:

`Res_{w=0} A(w)/w = (1/2)(psi(1/4)-log pi)`,

and

`Res_{w=0} P(w)/w = -(1/2)(psi(1/4)-log pi)`.

Moreover,

`(1/2)(psi(1/4)-log pi)=-(1/2)(gamma+pi/2+3log 2+log pi)<0`,

so neither residue vanishes.

## Proof

The displayed formula for `xi` gives the logarithmic derivative split above.

The functional equation makes `Xi` even. Since `Xi(0)!=0`, the logarithmic
derivative `Xi'/Xi` is odd and vanishes at `w=0`. Therefore

`(A(w)+P(w))/w = Xi'(w)/(w Xi(w))`

has a removable singularity at `w=0`.

The archimedean summand is regular at `w=0`, and its value is

```text
A(0) = 1/(1/2) + 1/(-1/2) - (1/2)log pi + (1/2)psi(1/4)
     = (1/2)(psi(1/4)-log pi).
```

The standard digamma value

`psi(1/4)=-gamma-pi/2-3log 2`

gives

`A(0)=-(1/2)(gamma+pi/2+3log 2+log pi)<0`.

Thus `A(w)/w` has a nonzero simple pole at `w=0` with residue `A(0)`.

Since `A(w)+P(w)=Xi'(w)/Xi(w)` vanishes at `w=0`, one has

`P(0)=-A(0)`.

Therefore `P(w)/w` also has a nonzero simple pole at `w=0`, with the opposite
residue. The sum has no pole because these two residues cancel exactly.

## Consequence For The RH Route

The divided seam-log object is a completed object. It is not a termwise
Markov/Pick object on the archimedean and prime pieces.

A proof cannot split

`G_src(-w^2)=A(w)/w+P(w)/w`

and then ask each summand to be separately positive, Herglotz, Pick, or
Stieltjes near the seam: neither summand is even holomorphic there. The
functional equation supplies local cancellation, not a square-test inequality.

Thus the source theorem must control the completed sum after the seam
division, or must keep the cancellation mechanism inside the source-built
boundary object. Piecewise positivity of the divided source terms is not a
valid feeder for the repair theorem.

## Source Boundary

This theorem is a local analytic guardrail. It proves no RH positivity and no
zero localization. Its role is to prevent a source split from being promoted to
a Markov/Stieltjes proof before the functional-equation cancellation has been
accounted for.

## Gates

- [x] 0 -> 1 in-progress: divided source-split pole issue isolated.
- [x] 1 -> 2 fully-proven: residue calculation and FE cancellation written.
- [ ] 2 -> 3 formalized: optional local meromorphic-series lemma plus imported
  digamma value.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation after checking
  that the existing seam-log derivative identity normalized the completed
  object but did not record the nonzero residues of the divided source pieces.
