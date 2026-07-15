# Homogeneous multiple elliptic gamma scale gauge

- **ID:** `homogeneous-multiple-elliptic-gamma-scale-gauge`
- **Stage:** 3-formalized
- **Type:** BRIDGE / CARRIER CORRECTION
- **Scientific status:** `[FORMALIZED] [STANDARD HOMOGENIZATION] [NOT A NOVELTY CLAIM]`
- **Statement:** Restoring the implicit base period of the normalized additive multiple elliptic
  gamma product produces an exact simultaneous nonzero-scale symmetry.

## Statement

The repository's actual additive multiple elliptic gamma product is normalized as

```text
G(z;tau_i)
```

with implicit base period `1`.  Define

```text
G_hom(omega_0,omega,z)=G(z/omega_0; i |-> omega_i/omega_0).
```

Then for every nonzero complex `c`,

```text
G_hom(c*omega_0,c*omega,c*z)=G_hom(omega_0,omega,z).
```

Choosing `omega_0=1` recovers the normalized product exactly.

## Significance boundary

Homogenization by an explicit base scale is standard and is not new scientific knowledge.  The
important correction is negative: scaling only the normalized displayed parameters is not a
symmetry.  Any affine Ward or cosmological interpretation that omits `omega_0` is false.

The result supplies the honest value-level carrier for the pretemporal affine
hypertranscendence-horizon theorem.  Differentiating the scale identity into an Euler derivation on
a multivariable meromorphic field and transporting actual elliptic-gamma translation
hypertranscendence remain separate obligations.

## Lean realization

File:
`formal/GaloisForLFunctions/HTGeometry/HomogeneousMultipleEllipticGamma.lean`

Declarations:

- `homogeneousMultipleEllipticGammaProduct`
- `homogeneousMultipleEllipticGammaProduct_one`
- `homogeneousMultipleEllipticGammaProduct_scale`

The targeted cached module build passes.  The axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`; there is no project-local proof debt.

## Gates

- [x] actual multiple elliptic gamma product used
- [x] missing base period explicit
- [x] normalized chart recovered
- [x] nonzero scale symmetry unconditional in Lean
- [x] novelty explicitly disclaimed
- [ ] Euler Ward derivation on the multivariable meromorphic carrier
- [ ] actual homogeneous elliptic-gamma hypertranscendence horizon
