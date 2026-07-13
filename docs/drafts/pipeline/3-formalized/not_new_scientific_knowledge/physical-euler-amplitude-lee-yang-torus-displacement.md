# The physical Euler square-root amplitude displaces the Lee--Yang torus

- **ID:** `physical-euler-amplitude-lee-yang-torus-displacement`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[NO-GO] [POSITIVE INTERACTION TARGET] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeEulerLeeYangAmplitudeNoGo.lean`
- **Consumer:** `../../1-in-progress/prime-source-ferromagnetic-ising-lee-yang-limit-rh.md`

## Theorem

In the centered coordinate `XiC(z)=xi(1/2+Iz)`, the source-native character

```text
u_p(z)=exp(-log(p) I z)
```

has unit norm on `Im z=0`.  The physical local Euler monomial carries the additional amplitude
`p^(-1/2)`.  Lean proves

```text
|p^(-1/2)u_p(z)|=exp(log(p)(Im z-1/2)),
|p^(-1/2)u_p(z)|<1  <-> Im z<1/2,
|p^(-1/2)u_p(z)|=1  <-> Im z=1/2.
```

Hence the physical local field is strictly contractive on the centered critical line and reaches
the unit circle only at the original strip boundary `Re s=0`.  Raw Euler monomials cannot be the
field variables of a Lee--Yang proof of RH.

## Positive successor

The no-go separates the two roles of a local Euler term:

```text
centered character exp(-log(p) I z)   -> Lee--Yang field variable,
square-root amplitude p^(-1/2)        -> interaction or completed normalization.
```

A live construction must derive the amplitude from nonnegative spin interactions, an admissible
Lee--Yang single-site measure, or a separately proved zero-free archimedean normalization.  It may
not insert the physical monomial directly and then claim that the critical line is the unit torus.

## Formal certificate

The module proves:

- `norm_physicalCenteredEulerLeeYangField`;
- `norm_physicalCenteredEulerLeeYangField_lt_one_iff`;
- `norm_physicalCenteredEulerLeeYangField_eq_one_iff`;
- `norm_physicalCenteredEulerLeeYangField_criticalLine_lt_one`.

## Gates

- [x] physical centered local field defined
- [x] exact radial coordinate proved
- [x] displaced unit-torus locus classified
- [x] direct raw-Euler Lee--Yang substitution excluded
- [x] positive interaction/normalization target isolated
- [x] exact Lean build
