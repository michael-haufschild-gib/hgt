# Prime-power centered-mark finite-monodromy route to RH

- **ID:** `prime-power-centered-mark-finite-monodromy-rh`
- **Stage:** 5-failed
- **Type:** `[FALSIFIED] [RETIRED RH ROUTE] [LEAN-PROVED NO-GO]`
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
- [x] completed source producer classified: source-first and faithful collision is impossible
- [x] route retired by the source/receiver terminal certificate

## PPM-NG1 source/receiver terminal conjecture (2026-08-29)

**Exact chain attacked.** The remaining PPM chain is

```text
centered Euler ray
  -> divisor-independent finite quotient or finite monodromy
  -> equality of two actual centered-mark powers on a hypothetical right Xi fibre
  -> right-half contraction contradiction
  -> RH.
```

**Conjecture.** For every integer base `p > 1`:

1. the complete power orbit `a ↦ u_p(s)^a` is injective at every right-half spectral label;
2. any quotient that identifies two such powers is necessarily non-faithful to the actual
   centered marks, so its quotient collision cannot supply the scalar equality required by the
   RH endpoint;
3. the canonical Big-Witt Frobenius orbit is already injective on every hypothetical right
   completed-Xi fibre;
4. after restricting collision to right Xi fibres, the statement is exactly RH and is vacuous
   in the RH direction.

The positive survivor is global collision rigidity: one genuine equality
`u_p(s)^a = u_p(s)^b`, with `a < b`, forces `Re(s)=1/2`.

**Dependency-closed paper proof.** `u_p(s)` is a complex exponential and hence nonzero. Equality
of its `a`th and `b`th powers gives equality of the corresponding norm powers. For a positive
real radius different from one, natural powering is injective, contradicting `a < b`; therefore
`|u_p(s)|=1`. The proved exact norm law then gives `Re(s)=1/2`. On the strict right half-plane the
norm is strictly below one, so all natural powers are pairwise distinct. If an injective quotient
map identified two powers, injectivity would recover the forbidden scalar equality; hence every
collision-producing quotient loses precisely the faithfulness needed by the endpoint. The
existing Big-Witt comparison proves the same injectivity for the canonical dyadic Frobenius
orbit, while `XiRightPrimePowerMarkCollision p <-> RH` proves that zero-restriction imports the
entire unresolved theorem.

**Novelty audit.** Internal corpus searches for centered-mark collision, Big-Witt Frobenius
preperiodicity, finite monodromy, reflection, and quotient faithfulness found the endpoint and the
canonical orbit-injectivity theorem, but no theorem closing the producer/receiver fork. External
search found Putnam-type nonperiodicity and work on zeta values or zeros on vertical arithmetic
progressions, but no centered Euler-mark/Big-Witt source--receiver classification. Novelty remains
subject to expert review; the formal claim is the route-level terminal classification above.

## No-go closure

- **Exact killing theorem/mechanism:** `primePowerCenteredMark_source_receiver_terminal` proves
  the exhaustive PPM fork. Actual centered-mark power orbits are injective at every right-half
  label. An injective quotient cannot identify levels; any quotient collision therefore destroys
  the exact scalar faithfulness required by the RH endpoint. Canonical Big-Witt Frobenius is also
  injective on every hypothetical right completed-Xi fibre. Restricting the collision assertion to
  Xi zeros yields `XiRightPrimePowerMarkCollision 2 <-> RiemannHypothesis`, so that alternative is
  a receiver, not an independent source producer.
- **Strongest positive survivor:** `centeredPrimeMark_re_eq_half_of_pow_eq` classifies every genuine
  finite collision: for any `p > 1`, equality of two distinct natural powers of the centered mark
  forces `Re(s)=1/2`.
- **New insight:** finite monodromy cannot be obtained by quotienting the source-correct Adams ray
  while retaining the mark equality that makes PPM work. Any viable successor must introduce a
  different source invariant and a new RH endpoint; it is no longer PPM.
- **Status:** dependency-closed paper proof and Lean proof complete in
  `GaloisForLFunctions.RHTower.PrimePowerCenteredMarkSourceReceiverNoGo`. Targeted build passed;
  all new theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Repository lint reports
  unrelated pre-existing umbrella reachability failures, none involving this module.

## Log

- 2026-08-29 — PPM retired after source/receiver and quotient-faithfulness classification.
