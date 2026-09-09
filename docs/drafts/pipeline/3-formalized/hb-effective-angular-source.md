# HB: exact evaluation of the complete angular source

Status: formalized. RH remains unproved.

For every actual Xi copy rho with Re(rho)>1/2, the complete angular
coefficient in its physical response residue is

```text
A_eff = Lambda(5rho/2-1) Lambda(rho/2)^2 Lambda(1-3rho/2)/2.
```

Here Lambda is the original `reflectedCompletedLambda`, namely
`pi^(-s/2) Gamma(s/2) zeta(s)`. This evaluates the actual
`physicalSelfSourceCoefficient`; no pairing or normalization is assigned.
All three cutoff corrections are included before cancellation.

## Original source and cutoff identity

The [complete Laurent audit](hb-physical-self-response-laurent-coefficient.md)
identified the physical response as `A_eff U(1)+B`, where B is analytic
at both same-copy fundamental QNMs and

```text
A_eff=A-sum_(i=0..2) C_i A_i/delta_i.
```

A is the original residual angular integral. C_i are the actual scalar
cutoff periods, A_i the original principal half-square coefficients,
and delta_i the nonzero original angular gaps. The corpus's
`ThetaCuspHawkingBMNativePhysicalPairing` already identifies A at the
physical testing parameter for strict-right copies, including the
reflected cutoff correction. That result is used here in full.

Write `delta=1-rho/2`, `k=principalExponent_i`, and `v=k-rho/2`.
The existing cutoff boundary theorem gives

```text
C_i=Lambda(rho-1)[(k-delta)4^v-delta_i B(delta,k)].
```

The original bulk integral is
`B(delta,k)=integral_1^4 y^(delta-2) cutoff(y)y^k dy`.
Its integrand is continuous on this positive compact interval.
The cutoff is zero below 2 and one above 3. Splitting the same integral
at 2 and 3, with the whole transition retained, proves

```text
B(delta,k)=transitionMoment(v)+(4^v-3^v)/v
          =4^v/v-nativeCutoffMellinContinuation(v).
```

The actual gap factors as `delta_i=(k-delta)v`. Its previously proved
nonvanishing gives v!=0 for each of the three original powers. Therefore
the boundary and bulk terms combine exactly to

```text
C_i/delta_i = Lambda(rho-1) nativeCutoffMellinContinuation(k-rho/2).
```

This is valid for every Xi copy; no strict-right condition is used in
the cutoff quotient theorem.

## Complete three-power assembly

The existing native Mellin expansion orders its three powers as
`[2-2rho,1,2rho]`, while the physical response orders them as
`[2rho,1,2-2rho]`. Their coefficients are the same original two squared
Weyl coefficients and cross term. Exact reordering proves

```text
sum_i C_i A_i/delta_i
  =Lambda(rho-1) nativePrincipalMomentContinuation(-rho/2).
```

The source-identified physical residual period, for Re(rho)>1/2, is

```text
A=Lambda(5rho/2-1) Lambda(rho/2)^2 Lambda(1-3rho/2)/2
   +Lambda(rho-1) nativePrincipalMomentContinuation(-rho/2).
```

Subtracting the proved full correction gives the displayed A_eff.
Individual terms depend on the cutoff; their assembled difference is
exactly the four-Lambda value. No separate correction is set to zero.

## Exact remaining incidence

All three displayed arguments are nonreal. Away from 0 and 1,
`xi(s)=s(s-1)Lambda(s)/2`, and the prefactor is nonzero here. Functional
reflection gives `xi(1-3rho/2)=xi(3rho/2)`. Thus Lean proves

```text
A_eff=0 iff xi(5rho/2-1)=0 or xi(rho/2)=0 or xi(3rho/2)=0.
```

Combining this with the already proved scalar Laurent classification,
the full physical response has a nonremovable pole at either original
fundamental frequency, at fixed t<0, exactly when

```text
xi(5rho/2-1)!=0 and xi(rho/2)!=0 and xi(3rho/2)!=0
and clearedReducedGreen(w_star,physicalChi,physicalRate,a,t)!=0.
```

This is an exact criterion, not a proof that these four quantities are
nonzero. The radial moment, full physical retarded/advanced adjoint
identification, spin-two/AIME reconstruction and source-level extinction
remain open. The source value and criterion use the proved strict-right
domain of the original residual-period identification. No result outside
that domain is asserted for the complete A_eff formula.

## Lean surface and audit

Four RHTower leaves, prefixed `ThetaCuspHawkingBM`:

- `CutoffBulkMellinValue`
- `CutoffMismatchMellin`
- `PhysicalAngularSourceValue`
- `PhysicalAngularSourceXi`

They contain 14 public theorems in 266 lines; the largest leaf has 77
lines. Each passed a `lake env lean` scratch check and an individual
final `lake build <exact-module>` check without warnings. Only these
14 new declarations were axiom-audited; each uses exactly `propext`,
`Classical.choice`, and `Quot.sound`. No added axiom or computational
certificate is used. All 12 installed source/olean/ilean artifacts match
the audited files by SHA-256, and four unique umbrella imports are wired.
No umbrella or full build was run. The frontier map remains read-only.

The generated index and `scripts/formal_tools.py lint --check-generated`
pass with 141 existing large-file warnings. `git diff --check` passes.
The frontier map's SHA-256 is unchanged.
