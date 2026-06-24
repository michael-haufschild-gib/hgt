# Seam-Log Derivative Weld Identity

- **ID:** seam-log-derivative-weld-identity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / analytic coordinate weld
- **Source:** `seam-log-markov-pick-rh-equivalence.md`;
  `reciprocal-seam-canonical-gauge-extraction.md`;
  `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** The seam-log Markov candidate is exactly the completed
  log-derivative divided by the seam coordinate:

  `G_src(-w^2)=Xi'(w)/(w Xi(w))`.

  Equivalently, on any local square-root branch,

  `G_src(x)=Xi'(sqrt(-x))/(sqrt(-x) Xi(sqrt(-x)))`,

  and the expression is branch-independent near `x=0`.

## Setup

Let

`Xi(w)=xi(1/2+w)`,

and let the functional equation quotient be

`Phi(z)=Xi(sqrt(z))`.

Near `z=0`, define

`L(z)=log(Phi(z)/Phi(0))`

and

`G_src(x)=2 L'(-x)`.

Since `Xi` is even and `Xi(0)!=0`, the quotient

`B(w)=Xi'(w)/(w Xi(w))`

has a removable singularity at `w=0` and is even.

## Theorem

For `w` near `0`,

`G_src(-w^2)=B(w)=Xi'(w)/(w Xi(w))`.

Consequently, if

`Xi'(w)/Xi(w)=sum_{n>=0} (-1)^n T_{n+1} w^(2n+1)`,

then

`G_src(-w^2)=sum_{n>=0} (-1)^n T_{n+1} w^(2n)`,

which is the same coefficient tower as

`G_src(x)=sum_{n>=0} T_{n+1} x^n`.

## Proof

For `z!=0`, choose a local branch of `sqrt(z)`. The chain rule gives

`L'(z)=Phi'(z)/Phi(z)
      =Xi'(sqrt(z))/(2 sqrt(z) Xi(sqrt(z)))`.

Multiplying by `2` and putting `z=w^2` gives

`2 L'(w^2)=Xi'(w)/(w Xi(w))`.

Since `G_src(x)=2L'(-x)`, setting `x=-w^2` proves

`G_src(-w^2)=Xi'(w)/(w Xi(w))`.

The possible branch change `w -> -w` does not change the right side: `Xi` is even
and `Xi'` is odd, so the two signs cancel. The quotient is also holomorphic at
`w=0`, because `Xi'(0)=0` and `Xi(0)!=0`.

For the coefficient form, divide

`Xi'(w)/Xi(w)=sum_{n>=0} (-1)^n T_{n+1} w^(2n+1)`

by `w`. This gives

`Xi'(w)/(w Xi(w))=sum_{n>=0} (-1)^n T_{n+1} w^(2n)`.

On the other hand,

`G_src(-w^2)=sum_{n>=0} T_{n+1}(-w^2)^n
            =sum_{n>=0} (-1)^n T_{n+1} w^(2n)`.

Thus the two expansions agree.

## Consequence for the RH Route

This card identifies the Markov/Pick target as the divided completed
log-derivative in the reciprocal seam coordinate. It is not a positivity theorem.

Therefore a route through the carrier or completed log-derivative must do more
than prove a generic analytic property of `Xi'/Xi`. It must prove that after
division by `w` and the reciprocal square substitution `x=-w^2`, the resulting
even function is a Markov transform of a positive measure on `R_+`.

Equivalently, if one splits

`Xi'(w)/Xi(w)=A(w)+P(w)`

into archimedean and prime parts, then

`G_src(-w^2)=A(w)/w + P(w)/w`.

The singular-looking division is removable for the completed even object, but it
does not supply a sign or square-test inequality. Any proof must still derive the
Stieltjes cone condition from source data.

## Theatre Test

This theorem answers only a coordinate question:

1. `G_src`, the seam-log Markov candidate, and the divided completed
   log-derivative are the same local object.
2. Markov/Pick positivity of that object is still exactly the RH-strength gate
   recorded in `seam-log-markov-pick-rh-equivalence.md`.
3. Carrier language is useful only if it proves the cone condition after the
   division and square-coordinate change above.

Thus the result prevents double-counting the same gate under different names. It
does not move any zero or prove a new sign inequality.

## Source Boundary

This is a bridge theorem and normalization guardrail. It claims no new positivity
and no new zero localization. Its role is to keep the analytic route from
mistaking an identity for the missing source-derived Markov/Stieltjes theorem.

## Gates

- [x] 0 -> 1 in-progress: seam-log derivative and carrier coordinate compared.
- [x] 1 -> 2 fully-proven: chain-rule identity and coefficient dictionary proved.
- [ ] 2 -> 3 formalized: optional power-series and removable-singularity wrapper.

## Log

- 2026-06-24 -- Codex: created under the private anti-theatre pass. The card
  ties the Markov target to the divided completed log-derivative and records that
  this is normalization, not an RH proof.

## 2026-06-24 divided source-split companion

`seam-division-source-split-cancellation.md` records the local source-split residue calculation behind the warning in this card. If `Xi'/Xi=A+P`, with `A` the archimedean/pole log-derivative and `P=zeta'/zeta`, then `(A+P)/w` is holomorphic at `w=0`, but `A/w` and `P/w` have opposite nonzero simple poles.

Thus the seam-log Markov candidate is completed at the level of the divided object. Piecewise Markov/Pick positivity of the divided source summands is not a valid substitute for positivity of the completed sum.
