# Prime-power centered-mark finite-monodromy route to RH

- **ID:** `prime-power-centered-mark-finite-monodromy-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [RH ROUTE] [LARGE OUTLANDISH DETOUR]`
- **Source:** the degree-one Euler prime-power ray, local Adams dilation, completed
  prime--Gamma constraint, and finite-monodromy/torsion infrastructure
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimePowerCenteredMarkRH.lean`

## Claim

For one fixed integer `p>1`, put

```text
u_p(rho) = exp(log(p) * (1/2-rho)).
```

This coordinate is source-native: it is the centered version of the actual degree-one Euler
exponential.  It has three exact properties:

```text
|u_p(rho)| < 1  iff  Re(rho)>1/2,
|u_p(rho)| = 1  iff  Re(rho)=1/2,
u_(p^m)(rho) = u_p(rho)^m.
```

Therefore it is enough to prove that, at every hypothetical right-half Xi zero, two distinct
levels of one fixed prime-power ray are identified:

```text
u_p(rho)^a = u_p(rho)^b                 for some a<b.
```

A nonzero complex number of norm strictly between zero and one has pairwise distinct natural
powers.  The collision is impossible, hence no right-half Xi zero exists, and the functional
equation closes the result to RH.

`[PROVED LEAN]` The complete right endpoint, the critical-circle law, reflection inversion, and
the unconditional base-Adams identity are formalized.  Lean also proves the circularity audit

```text
XiRightPrimePowerMarkCollision p <-> RH.
```

The reverse direction is vacuous under RH.  Thus the predicate is not evidence for RH by itself;
only an independently defined source construction producing its collision can advance the proof.

## Two-ended chain

```text
degree-one Euler source at the ray p,p^2,p^3,...
  -> exact centered base-Adams marks u_(p^m)=u_p^m
  -> a source finite quotient / monodromy / completed incidence identifies two levels
       [OPEN CORE]
  -> one finite power collision at each hypothetical right-half Xi zero
  -> contraction makes that collision impossible
  -> no right-half Xi zero
  -> RH.
```

This removes the coordinate mismatch in the Arakelov power-orbit route.  Bare prime Adams does not
send `w(rho)=1-rho^-1` to `w(rho)^m`, but it sends the centered prime mark to its `m`-th power
exactly.  No global self-map of the Xi divisor and no orbit of new zero locations are required.

## Attack and firewalls

1. **The base-Adams identity alone is not a collision.**  The prime-power levels are naturally
   distinct.  A completed source theorem must identify two of them before inspecting zero
   location.
2. **Finite-dimensionality alone gives only a linear recurrence.**  Cayley--Hamilton on a local
   divisor jet does not make an eigenvalue orbit finite.  The missing input must be finite
   monodromy, torsion, a finite source quotient, or an exact level identification.
3. **An external quotient is vacuous.**  Declaring the level labels equal by hand proves nothing.
   The identification must be induced by the completed Euler--Gamma constraint, a canonical
   semilocal descent, or a source incidence law.
4. **Known on-line zeros need not have finite mark orbit.**  The premise is deliberately required
   only on hypothetical right-half zeros.  It is not a global periodicity assertion about the
   actual divisor.
5. **This is not the all-power reflection-energy criterion.**  That route asks the completed source
   to beat the universal off-line energy floor `1/2`.  The present route instead asks for one exact
   finite-monodromy collision.  Either producer would close RH; neither presently implies the other.
6. **Ordinary prime clocks do not supply the collision.**  Vertical translation by
   `2*pi/log(p)` fixes a single mark; it does not identify two distinct base-power levels.
7. **The bare collision certificate is exactly RH-equivalent.**  It cannot be promoted by renaming
   it a source condition.  A producer must be stated without quantifying over Xi zeros or must be
   proved from a completed-source object whose construction is independently available at every
   spectral fibre.

## Positive source targets

The no-go audit leaves four concrete producer families:

1. a source-canonical finite quotient of the degree-one Euler ray on which base Adams acts;
2. an all-prime semilocal monodromy representation with finite orbit on the hypothetical
   right-half completed fibre;
3. a torsion-sector projection that isolates the scalar zeta component rather than the full
   Dirichlet-character packet;
4. a good-reduction theorem in which bounded Frobenius orbit at infinitely many arithmetic
   places lifts to an exact complex level collision.

The fourth is the longest detour.  Its correct endpoint is now explicit: it need not prove
algebraicity of a zero, preserve the whole Xi divisor, or construct an operator with the zeros as
spectrum.  It only has to identify two centered prime-power marks at the same hypothetical fibre.

## Gates

- [x] source-native centered prime mark defined
- [x] critical-line unit-circle law proved
- [x] functional-equation reflection acts by inversion
- [x] base Adams acts by exact powering
- [x] one finite collision at each right-half zero proved sufficient for RH
- [x] bare right-half collision certificate proved equivalent to RH
- [ ] completed source produces a finite level collision without divisor-location input
- [ ] compose the source producer with the formal endpoint and audit axioms
