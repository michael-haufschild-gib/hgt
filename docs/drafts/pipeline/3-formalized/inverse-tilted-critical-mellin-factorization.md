# The complete inverse-tilted prime source is the regularized critical-Mellin defect

- **ID:** `inverse-tilted-critical-mellin-factorization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / Connes critical-Mellin source identification / `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT AN RH PROOF]`
- **Parent theories:** Euler logarithmic derivatives, pole-filled zeta, Mellin convolution,
  and meromorphic continuation

## Main theorem

Let

```text
Z_*(t) = (t - 1) zeta(t), with Z_*(1) = 1,
D_tilde(u) = 1 / (u + 1) + Z_*'(u + 1) / Z_*(u + 1).
```

On `Re(u) > 0`, this agrees with the convergent polar--prime critical-Mellin channel

```text
1 / u + 1 / (u + 1) + zeta'(u + 1) / zeta(u + 1).
```

For the complete inverse-tilted dyadic source `Scal_-` and its aperture
`M_-(s) = A_(log 2)(s)`, define

```text
C_-(s)
  = D_(3/2) N_-(s)
    - 2 M_-(s) / (s - 1/2)
    - 2 H_-(s).
```

Then, identically on the complex plane,

```text
Scal_-(s) = 2 M_-(s) D_tilde(s - 3/2) + C_-(s).
```

The correction `C_-` is analytic on `Re(s) > 1/2`, while `M_-(s)` is nonzero there.
Consequently

```text
Scal_- analytic on Re(s) > 1
  iff D_tilde analytic on Re(u) > -1/2,
```

and the complete-divisor source theorem gives

```text
RH iff D_tilde is analytic on Re(u) > -1/2.
```

## Positive Connes obligation

The inverse-tilted source and the critical-Mellin defect are not independent carriers.  A viable
Connes or Connes--Consani construction must force the actual pole-filled polar--prime defect to
continue holomorphically across the strip

```text
-1/2 < Re(u) <= 0.
```

Equivalently, it must force the complete prime-source divisor onto its critical polar line.  No
additional source-completeness theorem is missing.

## Formal proof surface

The unconditional Lean module is

```text
GaloisForLFunctions.RHTower.CCM.CCMInverseTiltedCriticalMellinFactorization
```

Its declarations are:

- `regularizedCriticalMellinDefect_eq_continued`
- `inverseTiltedDyadicContinuedSource_eq_criticalMellinDefect_add_correction`
- `analyticAt_inverseTiltedCriticalMellinCorrection`
- `inverseTilted_source_analytic_rightOne_iff_regularizedCriticalMellin_analytic_rightNegHalf`
- `riemannHypothesis_iff_regularizedCriticalMellinDefect_analytic_rightNegHalf`
- `inverseTiltedCriticalMellinFactorization_capstone`

It reuses the stronger aperture theorem
`inverseTiltedDyadicMellin_ne_zero_of_re_pos`; hence the stated nonvanishing on
`Re(s) > 1/2` is formalized without duplicating a weaker lemma.

## Scientific-status boundary

The theorem is a direct algebraic and analytic bridge between two already established source
coordinates.  It materially sharpens the route architecture but does not clear the novelty gate.
The remaining holomorphy statement is exactly RH, so the theorem is not an RH proof.

## Completion

`[LEAN-PROVED]` This card is complete as an unconditional factorization and RH-criterion bridge.
The Connes/Sonin holomorphy mechanism and RH are downstream open problems, not unproved obligations
inside this theorem.

## Formalization gates

- [x] source/defect identity is global and exact
- [x] correction analyticity on the full source continuation half-plane
- [x] zero-free Mellin aperture on the required half-plane
- [x] exact translated holomorphy equivalence
- [x] exact critical-Mellin RH criterion
- [x] unconditional Lean proof without project axioms
- [x] classified as bridge infrastructure

## Downstream open problems

- [ ] unconditional Connes/Sonin theorem forcing defect holomorphy on `Re(u) > -1/2`
- [ ] RH
