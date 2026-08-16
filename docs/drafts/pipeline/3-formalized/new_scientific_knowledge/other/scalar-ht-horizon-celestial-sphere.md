# The scalar HT horizon family is a hyperbolic celestial sphere

- **ID:** `scalar-ht-horizon-celestial-sphere`
- **Stage:** 3-formalized
- **Type:** RANK-ONE HYPERBOLIC BOUNDARY / DIFFERENTIAL-FIELD COMPLEMENTARITY
- **Scientific status:** `[PROVED CONSEQUENCE] [LEAN FORMALIZED] [NOVEL IDENTIFICATION CANDIDATE]`
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

`[UNCONDITIONAL, AXIOM-CLEAN]`  Three modules carry the whole theorem.

`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonCelestialSphere.lean`

```text
jetTailField_mobiusObservable_one_eq_rowHorizon   -- (1) choice independence
rowHorizon_eq_iff                                 -- exact classification of horizon equality
rowHorizon_ne                                     -- (2) H_p != H_q for p != q
rowHorizon_sup_inf                                -- (2),(5) exact join and exact meet
rowHorizon_mobiusObservable                       -- (4) fractional-linear equivariance
celestialHorizon_injective                        -- (4) injective realization of P^1(C)
celestialHorizon_sup_inf                          -- (5) at every ordered pair of P^1(C)
celestialHorizon_infinity_fixed_iff               -- parabolic stabilizer of one horizon
celestialHorizon_pair_fixed_iff                   -- diagonal Cartan stabilizer of a pair
existsUnique_orientedGeodesic                     -- unique oriented geodesic through a pair
hypertranscendentalOver_celestialSphere_realization
hypertranscendentalOver_celestialSphere_realization_prime  -- prime-field instance, no constants
                                                            hypothesis
```

`formal/GaloisForLFunctions/HTGeometry/HyperbolicThreeSpaceBoundary.lean` builds `H^3` itself as
the unimodular positive-definite Hermitian complex `2x2` matrices and proves `(3)`:

```text
HyperbolicThreeSpace.symmetricSpace_model   -- H^3 = SL_2(C)/SU(2): transitivity by an explicit
                                            -- Cholesky factor, and isotropy = unitary part
exists_eq_lightMatrix                       -- every future light ray is a rank-one form v v^H
lightMatrix_smul_iff                        -- light rays modulo positive scale = P^1(C)
lightMatrix_mulVec                          -- the symmetry action on rays is the Moebius action
```

`formal/GaloisForLFunctions/HTGeometry/ScalarHorizonCelestialBoundary.lean` welds the two:

```text
lightRayHorizon_eq_iff       -- two light rays give one horizon iff they are the same boundary point
lightRayHorizon_sup_inf      -- distinct rays: exact join and exact meet
scalarHorizon_celestialSphere_realization
```

`#print axioms` on every capstone returns only `propext`, `Classical.choice`, `Quot.sound`.

The base of constants enters as the standing hypothesis `hconst : forall t, t' = 0`, which is the
definition of "over complex constants"; `hypertranscendentalOver_celestialSphere_realization_prime`
discharges it outright over the prime field of constants.

## RH impact audit

`[POTENTIAL GEOMETRIC LANGUAGE; NOT RH PROGRESS]` If a completed-zeta scalar were proved HT and
its projective horizon family were analytically natural, `(6)` would provide a celestial-sphere
organization of its derivative charts. Neither premise currently advances zero location.

## Gates

- [x] 0 -> 1: rank-one visual boundary separated from the higher-rank Tits topology
- [x] 1 -> 2: equivariant sphere and geodesic recovery identification proved
- [x] 2 -> 3: full unconditional Lean formalization — choice independence, exact meet, exact join,
  equivariant injective `P^1(C)` realization, the `SL_2(C)/SU(2)` model of `H^3`, its light-ray
  boundary, and the unique oriented geodesic through each ordered pair of distinct horizons
- [ ] 3 -> 4: external audit in differential algebra and Kleinian/hyperbolic geometry

## References

- The classical identification of the orientation-preserving isometry group of `H^3` with
  `PSL_2(C)` and of its visual boundary with the Riemann sphere.
- W. Thurston, hyperbolic three-manifolds and Möbius boundary geometry.

## Log

- 2026-07-15 — identified the scalar projective horizon sphere with `boundary_visual H^3` and
  complementary horizon pairs with hyperbolic geodesic endpoints.
- 2026-08-16 — formalized unconditionally in Lean: the celestial-sphere realization, the exact
  meet and join at every boundary pair, fractional-linear equivariance, the parabolic and Cartan
  stabilizers, the hyperbolic three-space model `SL_2(C)/SU(2)` with its light-ray visual
  boundary, and the unique-oriented-geodesic law. Card promoted to stage 3.
