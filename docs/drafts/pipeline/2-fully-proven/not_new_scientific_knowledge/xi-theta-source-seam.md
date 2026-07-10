# The completed xi theta source is an exact two-sided seam

- **ID:** xi-theta-source-seam
- **Stage:** 2-fully-proven
- **Type:** THEOREM / INTERFACE OBSTRUCTION, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiThetaSourceSeam.lean`

## Source

Mathlib constructs the entire pole-subtracted completion by

`completedRiemannZeta_0(s)=mellin(F,s/2)/2`,

where

`F=(hurwitzEvenFEPair 0).f_modif`.

For `x>1`,

`F(x)=theta(x)-1=2 sum_(m>=1) exp(-pi m^2 x)`.              (1)

The modified-kernel functional equation is

`F(1/x)=x^(1/2)F(x)`.                                       (2)

Define the critical logarithmic normalization

`h(u)=exp(u/4)F(exp u)`.                                    (3)

## Theorem A `[PROVED]`: exact reflection constraint

For every real `u`,

`h(-u)=h(u)`.                                                (4)

### Proof

Apply (2) with `x=exp(u)`:

`F(exp(-u))=exp(u/2)F(exp u)`.

Multiplication by `exp(-u/4)` gives (4).

This is the completion constraint in physical coordinates: the source is fixed by reflection,
not propagated by a flow.

## Theorem B `[PROVED]`: the source is genuinely two-sided

For every `u!=0`,

`h(u)!=0`.                                                   (5)

### Proof

For `u>0`, (1) is a convergent sum of strictly positive terms, hence
`F(exp u)>0`; the prefactor in (3) is positive.  For `u<0`, apply (4) to `-u>0`.

At `u=0`, the strong FE-pair convention defines `F(1)=0`, so `h(0)=0`.

## Theorem C `[PROVED]`: canonical one-sided seam split

Let

`h_+(u)=1_(0,infinity)(u)h(u)`,

`h_-(u)=h_+(-u)`.

Then, pointwise on the whole real line,

`h(u)=h_+(u)+h_-(u)`,                                       (6)

and `h_-` is exactly the negative-half truncation of `h`.

Moreover

`HasAELowerSupport h_+ 0`.                                  (7)

### Proof

For `u>0`, `h_+(u)=h(u)` and `h_-(u)=0`; for `u<0`, (4) gives
`h_-(u)=h(-u)=h(u)` and `h_+(u)=0`; at `u=0` all terms vanish.  Equation (7) is immediate from the
indicator definition.

Thus the existing lower-support Prop is discharged for the positive half without any chosen
defect data.  Its reflected complement is forced by the target's functional equation.

## Theorem D `[PROVED]`: the full source satisfies no lower-support interface

For every finite real `tau`,

`not HasAELowerSupport h tau`.                               (8)

### Proof

Choose an open interval `(a,b)` with `b<min(tau,0)`.  If lower support held, `h=0` almost everywhere
on this interval.  The source is continuous on the negative half-line, so equality almost
everywhere on the open interval forces pointwise equality there.  This contradicts (5).

## Attack and consequence

- `[FALSIFIED]` Feed the full completed theta source into the Sonin lower-support transfer.
  Equation (8) rules this out unconditionally.
- `[PROVED]` The positive half is a genuine lower-supported source and the negative half is its
  exact reflection.
- `[PROVED OBSTRUCTION]` The reflected half cannot be declared a small or optional defect: it is
  nonzero everywhere on the negative half-line and is forced by (4).
- `[OPEN CORE]` Construct a coefficient coordinate on `h_+` and compute the reflected half's exact
  contribution to negative-line contour transport.  Any completed proof must carry both halves.

## Novelty and significance gates

- **NOVEL:** the result identifies the target's exact project-native seam at the level of the
  already formalized Mellin source and proves the full source fails the precise support interface
  used by the Perron transfer.
- **SIGNIFICANT:** scalar reciprocal-Gamma decompletion was ruled out in the parent theorem; this
  theorem supplies the surviving source-side replacement and localizes its unavoidable obstruction
  to the reflected theta half.

## Gates

- [x] 0 -> 1: target source and support question isolated.
- [x] 1 -> 2: evenness, nonvanishing, split, Prop discharge, and universal support failure proved.
- [x] 2 -> 3: formalized and axiom-audited.
- [ ] 3 -> 4: requires the half-source coefficient and reflected-charge theorem.
