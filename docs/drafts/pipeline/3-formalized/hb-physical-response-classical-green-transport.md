# HB: actual classical response and complete-source Green transport

Status: formalized. RH remains unproved.

The original physical response now has two classical interior derivatives,
a global spatial bound, and an exact finite-interval Green representation
with the complete projected source. This does not yet identify its outgoing
endpoint continuation or its physical residue.

## Exact objects and result

Fix Xi source and target copies q,r, the original branch and onset parameter,
and `3/2 < Re(w) < 2`, `Im(w) != 0`. Let

```text
P(t) = physicalCuspProfile(q,r,branch,w,a,...)(t)
F(t) = continuedAngularSourceProjection(q,branch,u,a,w)(t)
u = physicalAngularParameter(r)
lambda = u^2 - 1/4
chi = -i*u
h(t) = sech(t)^2.
```

Here P represents the actual physical contraction of the original complete
causal response. Its zero extension and original Dirichlet trace are already
proved. The new theorem `physicalCuspProfile_equation` gives, for every t<0,

```text
w^2 P(t) - P''(t) - lambda h(t) P(t) = F(t).
```

Both derivatives are actual derivatives of this same P. The complete source
is the literal angular integral, with its exact decomposition into one
reduced residual coefficient and all three continued cutoff coefficients.

The radial parameter is the original physical angular momentum:
`chi = thetaCuspHawkingTopologicalBlackHoleAngularMomentum(xiSpectralPoint r)`.
Its exact match is `1/4 + chi^2 = -lambda`. The Xi strip bound gives
`|Im(chi)| < 1/2`; hence the original connection coefficient is nonzero on
the response overlap.

Let H and N be the existing horizon and normalizable tortoise modes at
(w,chi), and c their original connection coefficient. Their proved
Wronskian is `H N' - H' N = -c`. Define currents using P's actual jets:

```text
J_H = H' P - H P'
J_N = N' P - N P'.
```

The new capstones prove

```text
J_H' = H F,       J_N' = N F,
c P = N J_H - H J_N,

c P(t) = N(t) [J_H(s) + integral(s..t, H F)]
       - H(t) [J_N(s) + integral(s..t, N F)]    (s <= t < 0).
```

This is Green transport for the actual complete physical response. Neither
the response nor its jet constants are supplied as hypotheses.

## Closed proof chain

1. Existing continued principal derivative theorems give continuity of
   each cutoff radial coefficient on t<0, including totalized values at
   connection zeros. Exact four-channel assembly then gives continuity
   of F. Its existing L2 class has that same representative.
2. Conjugation preserves the original compact radial core. Testing the
   Hilbert equation with the conjugate core cancels the test-slot
   conjugation, including both derivatives and the real squared weight.
   All source pairings are integrable by their actual L2 admission.
3. A reusable local regularity theorem extends a continuous density from
   a smaller closed interval by clamping, applies the existing continuous
   weak-second-derivative theorem, and restricts back to the original
   interval. It requires no endpoint continuity of the density. Applied
   to `w^2 P - lambda h P - F`, this proves both classical derivatives.
4. The physical profile equals the original zero extension almost
   everywhere on the whole line. The existing H1 domain result therefore
   gives whole-line L2 admission and a uniform spatial bound for this
   selected continuous representative.
5. Match the original mode coefficient to the physical angular eigenvalue.
   Differentiate the actual currents: homogeneous terms cancel and all
   of F remains. Integrate on compact interior intervals. The original
   Wronskian reconstructs P and gives the displayed Green formula.

## Lean surface and audit

One HTGeometry leaf:

- `ContinuousWeakSecondLocalRegularity`

Six RHTower leaves, with prefix `ThetaCuspHawkingBM`:

- `CompleteAngularSourceContinuity`
- `PhysicalResponseWeakIntegral`
- `PhysicalResponseClassical`
- `PhysicalResponseBounds`
- `PhysicalRadialModeMatching`
- `PhysicalResponseGreenTransport`

The seven leaves contain 22 public theorems and four supporting definitions.
Each passed `lake env lean <scratch-file>` and a separate final
`lake build <exact-module>` in an isolated cache-backed audit project.
All seven final builds were warning-free. A scratch-only `#print axioms`
audit of the 26 new public declarations reported exactly `propext`,
`Classical.choice`, and `Quot.sound`; no new axiom or computational
certificate was introduced. All 21 installed source/olean/ilean artifacts
were matched by SHA-256 to the audited artifacts. New imports are wired
into both affected umbrellas; neither umbrella was built.
`scripts/formal_tools.py index`, `scripts/formal_tools.py lint --check-generated`,
and `git diff --check` passed. The static lint retained 141 existing
large-file warnings; none of the new leaves exceeds 111 lines.

## Current endpoint and continuation scope

The endpoint currents, complete-source integral admission, and equality
with the original endpoint Green integral are proved in the
[endpoint identification](hb-physical-response-endpoint-green-identification.md).
That result applies on the original positive-frequency overlap and uses
this finite transport formula with its actual constants.

The same-copy complete response now has a [continuation to both fundamental QNMs](hb-physical-self-response-continuation.md).
Physical adjoint residue, complete-source pole survival, spin-two/AIME reconstruction,
and independent Hawking-clock extinction remain open. The frontier map
is read-only.
