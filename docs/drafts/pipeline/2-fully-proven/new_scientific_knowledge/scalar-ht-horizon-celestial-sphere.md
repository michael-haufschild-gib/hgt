# The scalar HT horizon family is a hyperbolic celestial sphere

- **ID:** `scalar-ht-horizon-celestial-sphere`
- **Stage:** 2-fully-proven
- **Type:** RANK-ONE HYPERBOLIC BOUNDARY / DIFFERENTIAL-FIELD COMPLEMENTARITY
- **Scientific status:** `[PROVED CONSEQUENCE] [NOVEL IDENTIFICATION CANDIDATE]`
- **Parents:** `projective-horizon-building-schwarzian-complementarity`,
  `projective-ht-horizon-symmetric-space-boundary`
- **Statement:** Over complex constants, the projective derivative horizons of one HT scalar form
  the visual two-sphere at infinity of hyperbolic three-space. Every hyperbolic geodesic has two
  endpoint horizons, and those two fields reconstruct the complete HT source.

## Set-up

Let `x` be hypertranscendental over `C`, let

```text
F=C<x>,
I=C<S(x)>,
```

where `S(x)` is the Schwarzian derivative. For each `p in P^1(C)`, choose a Möbius transformation
`M_p` taking `p` to infinity and define

```text
mathcal H_p=C<(M_p x)'>.                                  (1)
```

The scalar projective-horizon theorem proves that `(1)` is choice-independent and that for
`p != q`,

```text
mathcal H_p != mathcal H_q,
mathcal H_p mathcal H_q=F,
mathcal H_p intersection mathcal H_q=I.                   (2)
```

## Hyperbolic boundary theorem

There are canonical identifications

```text
H^3 congruent PSL_2(C)/PSU(2),
boundary_visual H^3 congruent P^1(C) congruent S^2.        (3)
```

Under `(3)`, the map

```text
p |-> mathcal H_p                                         (4)
```

is a `PGL_2(C)`-equivariant injective realization of the conformal sphere at infinity by
differential subfields of `F`.

For every complete hyperbolic geodesic `gamma subset H^3`, let `(p_-,p_+)` be its two endpoints.
Then

```text
mathcal H_(p_-) mathcal H_(p_+)=F,
mathcal H_(p_-) intersection mathcal H_(p_+)=I.            (5)
```

Conversely, every ordered pair of distinct horizon fields is the endpoint pair of a unique
oriented hyperbolic geodesic. Thus source reconstruction by two incompatible derivative horizons
is exactly parametrized by the geodesic space of `H^3`.

## Proof

The orientation-preserving isometry group of `H^3` is `PSL_2(C)`, acting on the visual boundary by
Möbius transformations of the Riemann sphere. The scalar horizon construction is equivariant under
the same Möbius action, and distinct boundary points give distinct fields, proving `(4)`. A complete
geodesic in a rank-one hyperbolic space is uniquely determined by its two distinct endpoints.
Substitution into the field complementarity and exact Schwarzian meet law `(2)` proves `(5)`.

## Visual topology versus Tits metric

The rank-one Tits metric places distance `pi` between any two distinct boundary points, so its
incidence building is zero-dimensional. The visual/conformal topology is instead the ordinary
sphere topology on `P^1(C)`. Equation `(4)` uses that visual topology transported to the horizon
family. These are two compatible but different boundary structures and must not be conflated.

## Further exact geometry

- the stabilizer of one horizon is a parabolic subgroup, the stabilizer of one boundary point;
- the stabilizer of an ordered complementary pair is the diagonal Cartan subgroup, the stabilizer
  of the corresponding oriented geodesic;
- ordered triples of distinct horizons are projective frames on the celestial sphere;
- the cross-ratio of four horizon labels is their complete Möbius invariant and the shape
  parameter of an ideal hyperbolic tetrahedron.

The meet/join lattice alone does not recover the cross-ratio: all distinct pairs have the same
meet and join. Cross-ratio geometry uses the labelled `P^1(C)` family and its projective action.

## Physical interpretation

Hyperbolic three-space is Euclidean `AdS_3` up to curvature normalization. Hence the scalar HT
horizon family is mathematically a conformal celestial boundary of an observer-frame bulk:

```text
one HT scalar -> S^2 family of boundary horizons,
two boundary endpoints -> full source reconstruction,
all boundary observers share Schwarzian curvature.        (6)
```

This is a precise kinematic holographic pattern. It is not an AdS/CFT duality and does not supply
a bulk quantum theory, gravity, entropy, a Lorentzian time, or a black-hole solution. The
hyperbolic bulk is the symmetric space of projective observer metrics.

## Novelty and significance gate

- The boundary model `(3)` and geodesic endpoint theorem are classical hyperbolic geometry.
- The projective horizon complementarity and exact Schwarzian meet are the parent candidate-new
  differential-field content.
- The new identification is that their parameter sphere and recovery pairs are exactly the visual
  boundary and geodesics of `H^3`.
- No checked source attaches this celestial-sphere/geodesic reconstruction geometry to HT
  derivative horizons.

## Lean status

The field-theoretic half of `(5)` is formalized in
`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonComplementarity.lean`: Lean verifies
two-chart reconstruction and common Schwarzian membership. Exact equality of the meet and the
hyperbolic boundary geometry remain paper-level; no placeholder encodes them.

## RH impact audit

`[POTENTIAL GEOMETRIC LANGUAGE; NOT RH PROGRESS]` If a completed-zeta scalar were proved HT and
its projective horizon family were analytically natural, `(6)` would provide a celestial-sphere
organization of its derivative charts. Neither premise currently advances zero location.

## Gates

- [x] 0 -> 1: rank-one visual boundary separated from the higher-rank Tits topology
- [x] 1 -> 2: equivariant sphere and geodesic recovery identification proved
- [ ] 2 -> 3: differential reconstruction core formalized; exact meet and `H^3` geometry remain
- [ ] 3 -> 4: external audit in differential algebra and Kleinian/hyperbolic geometry

## References

- The classical identification of the orientation-preserving isometry group of `H^3` with
  `PSL_2(C)` and of its visual boundary with the Riemann sphere.
- W. Thurston, hyperbolic three-manifolds and Möbius boundary geometry.

## Log

- 2026-07-15 — identified the scalar projective horizon sphere with `boundary_visual H^3` and
  complementary horizon pairs with hyperbolic geodesic endpoints.
