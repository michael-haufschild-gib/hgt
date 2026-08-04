# Route R finite adelic Gamma naturality cannot produce physical non-erasure

- **Status:** `[FAILED AS RH PRODUCER] [POSITIVE SURVIVOR FORMALIZED]`
- **Killed mechanism:** derive fixed-ideal non-erasure from finite-place Fourier/Gamma naturality,
  finite-prime chain maps, or finite-stage source equivariance.
- **Positive survivor:**
  `../2-fully-proven/new_scientific_knowledge/ccm/fixed-trace-ideal-gamma-cofinal-normalizer-law.md`.

## Proposed mechanism

The rational-adelic source has literal prime scaling, Fourier/Gamma reflection, a retained
ordinary-prime relative class, a period-one Stokes regulator, and a strict resolved Xi chain map.
One might try to transport finite-place Gamma naturality through the fixed physical quotient and
deduce that its two reflected coefficient classes have equal survival status.

## Killing theorem

Let `I=ell1(P)` in the full prime-sequence module.  Every transformation supported on a finite set
of ordinary primes differs from the identity by a finitely supported sequence.  Therefore it
induces the identity on `S/I` for every centered grade.  Every finite-prime Fisher truncation is
also zero in this quotient.

The full all-prime multiplier behaves differently.  In `|t|<1`,

```text
C_t(I) subset I     <-> 0<=t,
C_(-t)(I) subset I  <-> t<=0,
both                 <-> t=0.
```

Thus finite-place naturality contains no selective information.  Selection appears only after a
singular cofinal passage over all ordinary primes.  Claiming that finite compatibility extends to
a two-sided action on the fixed ideal inserts the critical-line conclusion.

The sharp obstruction is now an explicit class rather than a category label:

```text
beta_t=[F_(-t)]-[F_t].
```

Every finite-prime approximation to `beta_t` is zero in `S/I`, while the full class is nonzero
exactly for `t!=0`.  At an actual Xi divisor the difference of the two physical landings of the
same retained source class is its nonzero leading Xi jet times `beta_(t_rho)`.  Hence any proposed
finite-stage proof must explain how it creates this invisible cofinal class; compatibility alone
cannot do so.

## Strongest positive survivor

The retained rational-adelic Stokes class is globally orientation-complete: at every actual Xi
divisor at least one of its two fixed physical Gamma landings is nonzero.  Away from the critical
line exactly one landing is erased.  Hence no total loss occurs, but simultaneous retention is
still the RH-bearing cofinal theorem.

Formal module:

```text
formal/GaloisForLFunctions/RHTower/
  PrimeFirstTraceGammaCofinalNormalizerFrontier.lean
```

## Exact successor

Construct a literal infinite-prime source boundary or regulator whose definition is not a limit
of continuous finite-support quotient actions, prove it controls the fixed `ell1` subobject in
both Gamma orientations, and prove it annihilates the explicit `beta_(t_rho)` class without
assuming its vanishing.  It must also fail on off-line generalized-prime carriers.  A bounded
similarity, transported norm, variable ideal, or finite adelic action is excluded by the theorem
above.
