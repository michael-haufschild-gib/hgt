# Finite von Mangoldt--Gamma aperture orientation floor

- **ID:** `finite-von-mangoldt-gamma-aperture-orientation-floor`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), SOURCE-SIDE ORIENTATION PRODUCER
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `VonMangoldtGammaOrientedAnomaly.lean`

## Theorem

For a positive Gamma depth `N`, real source coordinate `x`, and nonempty natural aperture `M`, let

```text
A_(M,N)(x)
  = finiteVonMangoldtGammaAnomaly M x N 1 evaluated in coordinate zero.
```

Every resolved source term has weight

```text
Lambda(n)/n >= 0
```

and positive rate `log n`.  The preceding atom theorem proves that all nonzero terms have the same
alternating Taylor-tail orientation.  The new finite-aperture theorem proves the exact sum law

```text
A_(M,N)(x)
  = sum_(p : Fin M)
      singletonExponentialGammaAnomalyAtom
        (Lambda(p+2)/(p+2)) (log(p+2)) x N.               (1)
```

Consequently

```text
0 < (-1)^(N+1) Re A_(M,N)(x).                            (2)
```

More strongly, the first prime gives a lower floor independent of `M`:

```text
0 < b_N(x) <= (-1)^(N+1) Re A_(M,N)(x),                  (3)

b_N(x)
  = (-1)^(N+1) Re singletonExponentialGammaAnomalyAtom
      (Lambda(2)/2) (log 2) x N.
```

Thus the finite Euler aperture cannot lose orientation through aggregation, at any positive Gamma
depth.  Composite non-prime-power coordinates contribute zero; prime-power coordinates contribute
nonnegatively; the prime `2` makes the result strict and supplies the common floor.

## RH impact

This is an unconditional source producer, but it is not yet the critical producer required for RH.
The theorem is before canonical continuation, inverse-tilted normalization, and subtraction of the
completed prime--Gamma quadrature/counterterm.  It proves that the resolved Euler atoms and their
finite aggregation are not the source of a sign failure.

The remaining orientation problem is now localized to one exact comparison:

```text
finite oriented Gamma-anomaly aperture
  --completed critical renormalization-->
inverseTiltedPrimeGammaSourceTrace / prime--Gamma Hankel form.          (4)
```

A valid continuation theorem must transport a renormalized form of `(3)`.  Merely taking an
unrenormalized cofinal limit is invalid at the critical coordinate: the positive Euler sum need not
converge there, and the completed counterterm can carry the cancellation.  The next source theorem
must therefore express the counterterm itself as a boundary component of the same oriented defect,
or prove a lower estimate after the subtraction has already been made.

## Formal certificate

Module:

- `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaFiniteApertureOrientation.lean`

Principal declarations:

- `finiteExponentialGammaAnomaly_real_zero_apply_eq_sum`
- `singletonExponentialGammaAnomalyAtom_oriented_re_nonneg`
- `finiteVonMangoldtGammaAnomaly_zero_apply_eq_sum`
- `finiteVonMangoldtGammaAnomaly_zero_oriented_re_pos`
- `firstVonMangoldtGammaAtom_le_finiteAnomaly`
- `finiteVonMangoldtGammaAnomaly_uniform_firstAtom_floor`

## Anti-theatre gate

- The theorem adds a source-side sign and a cutoff-independent floor, rather than an RH-equivalent
  target kernel.
- It does not claim that finite aperture orientation survives critical renormalization.
- Taylor remainder orientation and closure of a positive finite sum are standard parent
  mathematics, so no scientific-novelty claim is made.
- Its useful residue is the exact localization of the open sign: the completed counterterm seam.

## Verification

- [x] direct module check
- [x] exact cached module build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration introduced
- [x] no numerical computation
- [ ] completed critical renormalization transports the floor
- [ ] normalized prime--Gamma Hankel orientation
- [ ] RH
