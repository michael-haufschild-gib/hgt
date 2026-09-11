# PW-B skew-source endpoint and forced ground correction

- **ID:** PW-B-GAMMA-SKEW-SOURCE-ENDPOINT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** For every complex z, the literal corrected skew-source expression has leading quotient -2 relative to Q(x)*log(x). It cannot equal a scalar multiple of the unchanged arithmetic field. A scalar equation with a logarithmic ground correction requires its coefficient to equal one.

## Complete source limits

Let M_z be the original coefficient-deformed Gamma/Möbius source,
E_z its admitted logarithmic current, Q the original Gamma source,
H the existing weighted Frullani generator, and R its source-fixed
inverse-gain reflection. Lean proves for every complex z:

`M_z(x)/Q(x)->1`,

`E_z(x)/Q(x)->0`,

`R(H(R M_z))(x)/Q(x)->B_z`

as x tends to infinity. B_z is the absolutely convergent endpoint
series in the [complete arithmetic endpoint theorem](pw-b-gamma-arithmetic-reciprocal-endpoint.md).

The first two limits retain the entire signed series. Each normalized
atom is its value at x=1 times exp(-(n-1)*(x-1)); for x>=1 this factor
is at most one for n>=1. The zero atom vanishes. Existing absolute
admission at x=1 supplies the common summable bound. Only the n=1
source atom survives the limit, and its logarithmic current vanishes.
The third limit uses the actual inverse-gain reflection and the proved
right-endpoint limit, retaining both source factors.

## Exact logarithmic obstruction

The literal expression tested is

`K_z(x)=E_z(x)-R(H(R M_z))(x)-2*log(x)*M_z(x)`.

It is the proposed corrected skew formula on the unchanged source;
this theorem does not assert an arbitrary-domain adjoint or closure.
The three complete source limits imply

`K_z(x)/(Q(x)*log(x))->-2`.

For every complex scalar lambda, the quotient
`lambda*M_z(x)/(Q(x)*log(x))` tends to zero. Therefore no pair z,lambda
can satisfy K_z(x)=lambda*M_z(x) throughout the positive ray. This
excludes precisely that unchanged-source scalar ansatz. It does not
exclude PW-B, a different source field, a corrected equation, or
distributional occurrence.

## Positive survivor: unique leading ground correction

For every complex c, the complete corrected expression obeys

`(K_z(x)+2*c*log(x)*Q(x))/(Q(x)*log(x))->2*c-2`.

Consequently the explicit scalar equation

`K_z(x)+2*c*log(x)*Q(x)=lambda*(M_z(x)-c*Q(x))`

on the positive ray forces c=1. The right side has zero quotient at
this scale, so the left limit must vanish. Cancellation of the nonzero
factor2 gives the unique coefficient. At c=1 the leading logarithmic
quotient vanishes for every z. That is the sharp surviving boundary,
not existence of a scalar solution or a selective spectral condition.

The [failed unchanged-source ansatz](../5-failed/pw-b-raw-gamma-skew-occurrence.md)
records this positive result. The [continuing pairing attack](../1-in-progress/pw-b-gamma-reversible-pairing.md)
retains the full cutoff transposition, physical domain, corrected
source equation, actual Xi occurrence and source-forced Ward balance
as open obligations. RH is unproved.

## Verification

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaSkewSourceEndpoint.lean`.
All8 public declarations pass the final scratch with only propext,
Classical.choice and Quot.sound. Exact passing bodies are promoted and
one RHTower umbrella import is wired. The targeted leaf build passed
in211s, building only this leaf. Index passed (two changed entries,
zero removals); all8 public source and API declarations are unique and
exact passing scratch bodies were verified. Final repository formal
lint passed. Scratch and build report only redundant-tactic style
warnings in this leaf. All owned Lean and research processes are
terminal; no full or umbrella build, numerical experiment, added axiom,
commit or push was used.
