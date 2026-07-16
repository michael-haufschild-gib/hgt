# Inverse-Gamma source puncture and scalar Laurent cover

- **ID:** `inverse-gamma-source-puncture-laurent-cover`
- **Stage:** 3-formalized
- **Type:** GENERAL HT BRIDGE / SOURCE-PURE LAURENT COORDINATE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [BRIDGE] [NOT AN RH RESULT]`
- **Parent:** `../../1-in-progress/hypertranscendental-laurent-horizon-residue-field.md`

## Statement

Let `I_n` be any sufficiently late inverse-Gamma sheet on the common exterior and lift that
exterior through

```text
y(z)=-exp(-z).
```

Then the source-defined puncture coordinate and its opposite are

```text
t(z)=exp(z)=-1/y(z),
t(z)^(-1)=exp(-z)=-y(z).
```

They multiply to one, and deck translation by `2*pi*i` fixes `y`, `t`, `t^(-1)`, and the actual
inverse sheet.  On the exterior chamber,

```text
Gamma(I_n(y(z)))=y(z).
```

For a general exponent `s`, the fractional section `t^(-s)` has holonomy

```text
t(z+2*pi*i)^(-s)=exp(-2*pi*i*s)t(z)^(-s).
```

No divisor point, zero table, positivity hypothesis, or RH-equivalent measure enters the
construction.

## Proof

The common inverse collar already proves `Gamma(I_n(y))=y` on the exterior.  The remaining
identities follow from `exp(z+2*pi*i)=exp(z)`, `exp(z)exp(-z)=1`, and direct substitution into the
fractional exponential section.  Lean checks these identities on the actual inverse-Gamma sheets.

## Contribution boundary

This is a source-pure bridge, not new scientific knowledge.  It closes the source-puncture and
scalar-negative-mode parts of the Gamma Laurent-horizon program.  It does not identify those
scalar modes with the negative `A2` current action, pull back the affine residue cocycle, construct
the Xi Plucker packet, or prove source positivity.  Replacing the holonomy by the identically
defined Xi-Hurwitz character is not counted as a theorem or a proof-chain advance.

## Lean certificate

- `formal/GaloisForLFunctions/HTGeometry/GammaPunctureLaurentCover.lean`
- umbrella import: `formal/GaloisForLFunctions/HTGeometry.lean`
- no `sorry`, `admit`, new axiom, `opaque`, or `unsafe` declaration

## Gates

- [x] actual inverse-Gamma source sheet used
- [x] source puncture derived without an Xi zero
- [x] positive and negative scalar Laurent coordinates proved inverse
- [x] deck invariance proved
- [x] fractional holonomy proved
- [ ] negative `A2` current action identified
- [ ] affine residue cocycle pulled back
- [ ] Xi prime packet constructed
- [ ] positive level proved
