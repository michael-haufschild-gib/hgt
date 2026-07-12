# Prime--archimedean polar-seam removal

- **ID:** `prime-arch-polar-seam-removal`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]`
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/PrimeArchPolarSeamRemoval.lean`

## Statement

Let

\[
P(s)=-\frac{\zeta'(s)}{\zeta(s)}-
  \frac{d}{ds}\log\!\left(\frac{s(s-1)}2\,\Gamma_{\mathbb R}(s)\right).
\]

Although the two displayed terms are singular at `s=1`, on a punctured neighbourhood of `1`
their difference agrees with the completed flux

\[
\Omega(s)=-\frac{\xi'(s)}{\xi(s)}.
\]

The function `Omega` is analytic at `1`.  Moreover, it is the unique analytic completion of the
punctured source germ: if `g` is analytic at `1` and `g=P` on some punctured neighbourhood, then
`g=Omega` on a full neighbourhood of `1`.

## Formal declarations

- `analyticAt_seamFluxCochain_one`;
- `primeArchPolarFlux_eventuallyEq_seamFluxCochain_one`;
- `exists_primeArchPolarFlux_analyticCompletion_one`;
- `primeArchPolarFlux_analyticCompletion_unique_one`.

The axiom audit for all four declarations is exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Proof

The completed function `xi` is entire and nonzero at `1`, so `-xi'/xi` is analytic there.  In a
sufficiently small neighbourhood, `xi` stays nonzero and the real part stays positive.  On the
punctured neighbourhood the factorization

```text
xi = archFactor * riemannZeta
```

shows that `riemannZeta` is nonzero as well.  The existing continued-source identity then gives
`P=Omega`.  If another analytic germ has the same punctured restriction, the analytic identity
theorem makes it locally equal to `Omega`.

## Top-down consequence

The prospective determinant-orientation chain no longer needs to assume a prime--Gamma
completion across the polar seam:

```text
strict Euler orientation at a safe source point
  + zero winding of every finite completed-source Hankel determinant
      along a fixed continuation detour
  -> positive central leading determinants
  -> RH.
```

The polar removal is unconditional Lean.  The surviving open problem is to define the finite
source determinant family with a proved positive safe endpoint and then prove zero winding along
the detour.  Nonvanishing alone is insufficient because the determinant is complex away from the
real source axis.

## Scientific status

This is standard removable-singularity and identity-theorem machinery specialized to the completed
zeta source.  Its value is architectural: it discharges one exact source interface and isolates the
remaining orientation transport.  It is not claimed as new scientific knowledge.

## Gates

- [x] exact theorem statement
- [x] unconditional Lean proof
- [x] no placeholders or project axioms
- [x] imported by the RHTower umbrella
- [x] scientific classification recorded
