# Completed-seam compact Thorin carrier rigidity

- **ID:** `completed-seam-compact-thorin-carrier-rigidity`
- **Stage:** 3-formalized
- **Type:** EXACT SOURCE-WALL RIGIDITY / HTGEOMETRY-TO-RHTOWER TRANSFER
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [SOURCE-PURE] [AXIOM-CLEAN]`
  `[NO COMPUTATION] [NOT RH] [NOT CLAIMED NOVEL]`
- **Formal target:** `RHTower.CompletedSeamCompactThorinRigidity`

## Result

Let `mu` and `nu` be finite positive Borel measures on the real line.  Suppose each is compactly
supported in `[0,B]` and `[0,C]`, respectively, and each produces the exact normalized completed
Cassini source exponent near the origin:

```text
E_Xi(z) = integral K(x,z) dmu(x)
        = integral K(x,z) dnu(x),

K(x,z) = -log(1-xz)/x,   K(0,z)=z.
```

Then

```text
mu = nu.
```

Thus the missing compact Thorin carrier, if it exists, is canonically determined by the
prime--Gamma source.  It is not an auxiliary measure that can be tuned after the fact.

More sharply, every witness is the already formalized canonical atomic Xi measure

```text
mu_Xi = sum_j lambda_j delta_(lambda_j),
```

where `lambda_j` is the positive reciprocal-square thermal coordinate of the `j`-th Xi zero.
Indeed a witness implies RH; under RH `mu_Xi` has the same complete moment sequence; compact
determinacy then gives `mu=mu_Xi`.

## Proof

On a disk around zero, differentiation under either compact integral gives the Markov transforms

```text
E_Xi'(z) = integral (1-xz)^(-1) dmu(x)
         = integral (1-xz)^(-1) dnu(x).
```

The existing exact Cassini source identity identifies `E_Xi'` with
`completedSeamMomentGerm`.  Differentiating `n` times at zero gives

```text
n! normalizedPrimeArchMoment(n)
  = n! integral x^n dmu(x)
  = n! integral x^n dnu(x).
```

Cancel `n!`.  Compact support gives integrability of every power.  Apply HTGeometry's theorem
`measure_eq_of_moments_eq_of_one_carried`: equality of all moments and compact carriage of one
representative force equality of the measures.

## Why this matters

This closes one genuine ambiguity in the Thorin route.  Abstract positive-measure construction
cannot choose among multiple compact carriers: there is at most one, and its full moment sequence
is forced coefficientwise by the completed source germ.  Future producer attempts must therefore
construct this canonical measure or prove its positivity; changing carrier, radius, or
representation cannot evade the critical-seam sign wall.

The canonical-carrier classification makes the source challenge exact: any proof advertised as a
prime--Gamma construction of a different compact Thorin law must fail.  A valid source proof must
reconstruct the same atomic Xi-divisor pushforward without using zero locations, or establish an
equivalent source-only positivity theorem that forces it.

## No-go and positive survivor

- **No-go:** generic HTGeometry measure-existence machinery does not itself prove critical-seam
  positivity.  It consumes a positive functional or positive moment form.
- **Positive survivor:** compact determinacy does apply after source identification and yields the
  canonical-carrier rigidity theorem above.  This is exact source-wall information not previously
  stated in RHTower.

## Audit status

- [x] exact paper proof
- [x] no RH or zero-location input
- [x] no numerical input
- [x] Lean theorem drafted
- [x] `lake env lean GaloisForLFunctions/RHTower/CompletedSeamCompactThorinRigidity.lean`
- [x] wired into `RHTower.lean`
- [x] targeted final build:
  `lake build GaloisForLFunctions.RHTower.CompletedSeamCompactThorinRigidity`
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] formal lint scanned this module cleanly; global lint was blocked only by three unrelated
  concurrently added modules missing from their umbrellas
- [x] moved to `3-formalized/not_new_scientific_knowledge`
