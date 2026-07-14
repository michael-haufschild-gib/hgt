# Projective jet-horizon stabilizer law

- **ID:** `projective-jet-horizon-stabilizer-law`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT THEOREM / DIFFERENTIAL-BIRATIONAL RIGIDITY
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED]`
- **Formal owner:** `formal/GaloisForLFunctions/HTGeometry`
- **Primary lane:** nature of hypertranscendental functions; static jet-horizon geometry
- **Secondary audit:** possible RH-coordinate consequence only; not an RH route
- **Statement:** For a hypertranscendental differential-field element, the first derivative-tail
  field is preserved by a nondegenerate projective change of generator exactly when that change is
  affine with constant slope.

## Goal

Give the derivative tower of one hypertranscendental element an intrinsic, non-flow geometry.  The
candidate structure is the decreasing family of static tail fields

```text
T_n(f) = K(delta^n f, delta^(n+1) f, ...).
```

The theorem asks whether the first horizon `T_1(f)` distinguishes a point at infinity in the
projective freedom of the generator.  If so, the full projective symmetry of the generated field is
broken to the stabilizer of that end.

## Exact theorem

Let `K` be an ordinary differential field of characteristic zero, let `L/K` be a differential-field
extension, and let `f in L` be hypertranscendental over `K`.  Put

```text
T_n(f) = K(delta^n f, delta^(n+1) f, ...).
```

For `a,b,c,d in K` with `Delta = ad-bc != 0`, define

```text
z = (a f + b)/(c f + d).
```

The candidate equivalence is

```text
T_1(z) = T_1(f)
iff
c = 0 and delta(a/d) = 0.
```

When the right side holds, `a/d` is a nonzero constant and `b/d in K`, so

```text
z = alpha f + beta,
delta^n z = alpha delta^n f + delta^n beta  for n >= 1,
```

and in fact `T_n(z)=T_n(f)` for every `n >= 1`.

## Medalist lens

Hypertranscendence itself says that the jets are algebraically independent.  That definition is
not new knowledge.  The proposed residue is a symmetry classification: although a Möbius change
preserves the whole generated differential field and preserves HT, it need not preserve which
information lies beyond the first derivative horizon.

The physical/topological statement is exact: the HT jet object is a projective line with a
distinguished end, and the horizon-preserving gauge group is the parabolic subgroup fixing that
end, with the additional differential constraint that its dilation have zero derivative.

No time parameter, evolution equation, transport, semigroup, or carrier is introduced.  Derivative
order indexes nested information constraints only.

## Competing moves and verdicts

1. `[BRIDGE; RETIRED]` HT is equivalent to one transcendence unit across every derivative-tail
   boundary.  This is too close to the standard definition of a differential indeterminate.
2. `[PROJECT COLLISION; RETIRED]` A comeagre pointwise constraint-free phase is already the active
   `countable-point-finite-constraint-completeness` lane.
3. `[FALSE AS A UNIVERSAL DESCRIPTION]` Natural-boundary or singularity topology cannot describe
   all HT functions; Gamma is meromorphic with an elementary pole divisor.
4. `[FAILED ROUTE]` Wheeler--DeWitt, BRST, positive master constraints, and cosmological three-face
   defects already exist in the corpus and do not supply a new source-pure invariant.
5. `[SELECTED CONJECTURE]` Classify exactly the projective changes preserving the intrinsic
   derivative horizon.

## Paper proof plan

Hypertranscendence gives two algebraic facts:

```text
f is transcendental over T_1(f),
delta f is transcendental over K.
```

The first derivative of `z` is

```text
delta z =
  ((delta a)c-a(delta c)) f^2
  + ((delta a)d+(delta b)c-a(delta d)-b(delta c)) f
  + ((delta b)d-b(delta d))
  + Delta delta f
  ---------------------------------------------------------- .
                     (c f+d)^2
```

Assume `delta z in T_1(f)`.  Clearing the denominator gives a quadratic polynomial over `T_1(f)`
annihilating `f`.  Since `f` is transcendental over that tail, all three coefficients vanish.

If `c != 0`, the quadratic coefficient expresses `delta z` as an element of the embedded base
field `K`.  The constant coefficient then expresses `Delta delta f` as an element of `K`, contrary
to the transcendence of `delta f` over `K`.  Hence `c=0`.

Now write `z=alpha f+beta`, where `alpha=a/d != 0` and `beta=b/d` lie in `K`.  Then

```text
delta z = (delta alpha) f + alpha delta f + delta beta.
```

Membership in `T_1(f)` and transcendence of `f` over that tail force `delta alpha=0`.  This proves
necessity.  The displayed higher-derivative formula proves sufficiency and equality of every
positive tail.

## Attack

1. **Hidden flow.**  None occurs: the fields `T_n` are simultaneous subfields of one fixed
   differential field.  No `n -> n+1` propagation constructs `f`.
2. **Exponential boundary.**  For `f'=f`, `T_1(f)=T_0(f)` and the horizon collapses; such an `f` is
   DA, so the theorem correctly does not apply.
3. **Polynomial boundary.**  The tail reaches the base after finitely many derivatives; again the
   element is DA.
4. **Projective inversion.**  For `z=1/f`, `delta z=-(delta f)/f^2`; the theorem predicts that the
   first tail changes even though `K<z>=K<f>` and HT is preserved.  This is the sharp counterexample
   to treating the whole generated field as the topology.
5. **Parent-theory attack.**  Differential-indeterminate and differential-Lu-roth theory supply
   the rational jet field and intermediate-field background.  The scientific residue is only the
   exact horizon-stabilizer classification.  If this classification or an equivalent filtered
   automorphism theorem is found in the literature, the card must be downgraded to `[BRIDGE]`.
6. **Promptability attack.**  The bare tail-transcendence law fails this gate.  Promotion requires
   the necessity classification, the all-positive-tail equivalence, and an exact literature audit.

## RH-impact audit

`[CONJECTURE]` The theorem would impose a coordinate-invariance firewall on RH-facing uses of an HT
source such as a completed logarithmic derivative.  Any selector stated only in the whole generated
differential field is blind to projective inversions that preserve HT but change the derivative
horizon.  A horizon-native selector must therefore either:

1. be invariant only under constant-slope affine gauges; or
2. carry extra source data that canonically marks the projective point at infinity.

This is a requirement on admissible formulations, not progress toward RH and not a zero-localizing
mechanism.

## Preliminary literature boundary

`[SEARCH; PRELIMINARY]` Standard sources and primary papers located in the first pass define a
differentially transcendental element by algebraic independence of all derivatives, identify
`K<f>` with the rational field in those jets, and develop differential Lu-roth and Kolchin-dimension
theory.  No source found in that pass states the exact derivative-tail stabilizer classification.
The search is not yet sufficient for a scientific-novelty verdict.

## Gates

- [x] source-pure static object and exact claim isolated
- [x] hidden-flow and project-collision attacks applied
- [x] complete paper proof reduced to two algebraic coefficient-separation lemmas
- [ ] paper proof written with every field-intersection and derivative identity discharged
- [ ] parent-theory and primary-literature audit completed
- [ ] significance and scientific-novelty verdict completed
- [ ] unconditional Lean theorem under `HTGeometry`
- [ ] targeted Lean module check, lint, and axiom audit; no full build

