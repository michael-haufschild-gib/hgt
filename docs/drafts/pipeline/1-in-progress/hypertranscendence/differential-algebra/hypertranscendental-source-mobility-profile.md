# Hypertranscendence and source mobility are independent capacities

- **ID:** `hypertranscendental-source-mobility-profile`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL SCOPE CORRECTION / CONSTRAINT DEFORMATION THEORY
- **Scientific status:** `[CONJECTURAL CLASSIFICATION] [MAXIMAL-MOBILITY THEOREMS LEAN-FORMALIZED] [NOVELTY UNVERIFIED]`
- **Parents:**
  - `clock-descent-anomaly.md`
  - `source-mackey-clock-interval.md`
- **Statement:** Hypertranscendence measures algebraic independence of the ambient differential
  clock. It does not imply that deformations preserving a chosen source constraint can realize
  arbitrary finite jets. Constrained HT sources require a second invariant: their finite source
  mobility profile.

## The scope error

For a hypertranscendental element `x`, the fields

```text
F(x,delta x,...,delta^(N-1)x)                              (1)
```

have the full expected transcendence degree. This is **ambient algebraic clock capacity**.

Now choose a source constraint presentation `S` selecting `x`, linearize it at `x`, and let `W_x`
be the homogeneous source tangent. For a finite observation map

```text
q_N : W_x -> O_N,                                         (2)
```

hypertranscendence of `x` does not imply surjectivity of `(2)`. Adding normalization or boundary
data can make a source rigid without creating a differential-algebraic equation for `x`.

Therefore the slogan

```text
hypertranscendence = arbitrary finite source variation
```

is false without an additional source-mobility hypothesis.

## Mobility profile

For finite-dimensional `O_N`, define

```text
R_x(N)=range(q_N|W_x),
d_x(N)=dim(O_N/R_x(N)).                                    (3)
```

For general finite observation objects, retain the quotient

```text
D_x(N)=O_N/R_x(N)                                         (4)
```

instead of its dimension. Call `(D_x(N))_N` the **source mobility profile**.

The profile depends on the source deformation problem, not only on the function. Two source
presentations are equivalent only if their deformation functors identify the profiles and the
global constraint class. Artificially adding normalization can change `(4)` and must not be
mistaken for a new invariant of `x`.

## Exact finite theorem

Let `T_N : O_N -> O_N` be a proposed finite shadow which exactly intertwines the source constraint
on `W_x`. Then

```text
R_x(N) subset ker(T_N).                                   (5)
```

Hence `T_N` factors through the mobility defect `D_x(N)`. In the maximal-mobility case
`D_x(N)=0`, every exact finite shadow vanishes. More generally, all finite shadow information is
supported on the mobility defect rather than on the freely variable part of the clock.

The already Lean-formalized descent-anomaly identity proves the extremal case and identifies the
positive residue: on source solutions, the anomaly is `T_N q_N`, so the part of `T_N` seen on
`R_x(N)` is exactly comparison failure.

## Conjectural phase diagram

1. **Differentially algebraic:** ambient algebraic clock capacity itself becomes finite or obeys a
   finite recurrence.
2. **HT but source-rigid:** ambient capacity is infinite, while `D_x(N)` grows because the chosen
   source deformation problem has few or no variations.
3. **HT with finite-visible source constraints:** both capacities are infinite, but some
   `D_x(N)` are nonzero.
4. **Corona-pure constrained HT:**

   ```text
   D_x(N)=0 for every finite N,
   but the global source constraint is nonzero.             (6)
   ```

   Every finite clock window is free, while the constraint survives only in the source topology
   or corona.

The Gamma shift source before asymptotic normalization is the current model of `(6)`: periodic
Fourier variations realize arbitrary finite jets, while translation supplies an infinite
conormal. Gamma with a rigid normalization illustrates why the source presentation must be part
of the datum.

## Foundational conjecture

**[CONJECTURE]** There is a presentation-invariant deformation category of nonlocal source
constraints on HT functions. Its tangent functor canonically determines `(D_x(N))`, and its
derived boundary at infinity determines a global corona class. The pair

```text
(finite mobility profile, global corona class)             (7)
```

is invariant under source-presentation equivalences and separates finite-visible, source-rigid,
and corona-pure HT behavior.

This is the minimum data required before asking for a universal topology or spectrum.

## Attack

- If the source category is allowed to contain arbitrary normalization constraints, `(7)` is not
  invariant. A valid theory must specify a minimal or Morita-invariant source presentation.
- Hypertranscendence alone supplies no preferred source category. The source must come from an
  independently given functional, arithmetic, geometric, or boundary constraint.
- The dimensions `d_x(N)` alone lose extension and topology data; the quotient system `D_x(N)`
  and its transition maps are primary.
- A zero profile does not imply a nonzero corona. Unconstrained formal differential
  indeterminates have maximal mobility but no thin boundary. Condition `(6)` requires both parts.

## Gates

- [x] hypertranscendence/source-mobility conflation identified
- [x] maximal-mobility finite-shadow no-go Lean-formalized
- [x] Gamma maximal-mobility source model available
- [ ] general factorization through `D_x(N)` formalized
- [ ] minimal source-presentation equivalence defined
- [ ] profile invariance under presentation equivalence proved
- [ ] one source-rigid HT and one finite-visible HT example classified
- [ ] corona-pure class proved nonempty beyond Gamma
- [ ] independent novelty/significance audit
