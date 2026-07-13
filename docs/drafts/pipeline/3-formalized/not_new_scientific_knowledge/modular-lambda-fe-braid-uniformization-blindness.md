# Modular-lambda braid uniformizes every FE orbit and therefore does not select RH

- **ID:** `modular-lambda-fe-braid-uniformization-blindness`
- **Stage:** 3-formalized
- **Type:** `[PROVED] [LARGE-DETOUR NO-GO] [POSITIVE SUCCESSOR]`
- **Scientific status:** not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/ArakelovModularLambdaFE.lean`
- **Inputs:** `ArakelovW.lean`, `Bottcher/ModularLambdaCovering.lean`

## Claim

For `rho` outside `{0,1}`, put

```text
w_rho = 1 - 1/rho.
```

Then functional-equation reflection is inversion,

```text
w_(1-rho) = w_rho^(-1),
```

and the critical line is the unit circle,

```text
|w_rho| = 1 iff Re(rho)=1/2.
```

The modular lambda map is onto `C minus {0,1}`.  Its anharmonic braid word `S*T*S` also acts by
inversion.  Therefore every nonexceptional `rho` admits `tau` in the upper half-plane with

```text
lambda(tau) = w_rho,
lambda((S*T*S) tau) = w_(1-rho).
```

This holds equally when `Re(rho) != 1/2`; in that case `|lambda(tau)| != 1`.

Lean proves the universal lift and its off-unit corollary as

```text
exists_modularLambda_lift_FE_braid
exists_modularLambda_lift_FE_braid_off_unit
```

## Large detour and attack

The tempting chain was

```text
Xi functional equation
  -> Arakelov reciprocal orbit
  -> modular-lambda lift
  -> anharmonic braid relation
  -> modular rigidity
  -> unit-circle orbit
  -> RH.
```

The modular-rigidity arrow is false.  Surjectivity of the Hauptmodul shows that the same braid
diagram exists over every point of the punctured plane.  In particular, the holomorphic modular
data explicitly realizes every off-critical reciprocal pair.  The braid relation records the
functional equation but adds no unitary or real-structure constraint.

This is stronger than saying that the route has a missing estimate: the proposed holomorphic
constraint has the full off-critical plane as a family of exact countermodels.

## Positive successor

The modular lift identifies the missing datum exactly.  A live modular detour must add an
**antiholomorphic compatibility**, not more holomorphic modularity.  In the Arakelov coordinate it
must prove

```text
w_(1-rho) = conjugate(w_rho).
```

Since the left side is `w_rho^(-1)`, this is equivalent to `|w_rho|=1`, hence to the critical
line.  On an upper-half-plane lift, the required statement is that the modular braid image and the
Schwarz-reflected lift agree modulo the `Gamma(2)` fibre relation.

That condition closes to RH, but it cannot be postulated after choosing a zero: it must be derived
from a source-defined real structure on the completed theta/Mellin object.  Ordinary modular
lambda covering, the `S_3` action, properness, and the braid relation do not supply it.

## Two-ended closure audit

- `[PROVED]` every Xi zero lies outside `{0,1}` and has an Arakelov coordinate;
- `[PROVED]` FE reflection becomes inversion;
- `[PROVED]` every such reciprocal pair has a modular-lambda braid lift;
- `[PROVED NO-GO]` the same lift exists for every off-critical point;
- `[OPEN CORE]` derive braid--Schwarz fibre compatibility from the completed source before reading
  zero location;
- `[PROVED CONSUMER]` that compatibility gives `w^(-1)=conj(w)`, hence `|w|=1` and RH.

The positive result is a complete modular uniformization of FE orbits.  Its no-go consequence is
that any RH-bearing modular route must be genuinely real/polarized, not merely holomorphic.
