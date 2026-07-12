# Cauchy-constraint Schubert law for positive HT capacity

- **ID:** `cauchy-constraint-schubert-ht-capacity-law`
- **Stage:** 5-failed / retired as a new-science route
- **Type:** THEOREM (finite packet) / CONSTRAINT-TRANSVERSALITY BRIDGE
- **Lane:** general hypertranscendence; constraint geometry; positive Cauchy carriers
- **Scientific status:** `[FINITE CORE PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For positive reweightings of an infinite-support Herglotz measure subject to
  finitely many linear constraints, the exact loss of attainable finite Cauchy-jet dimension is the
  incidence dimension between the constraint-normal space and the rational Cauchy-jet trace space.
  Inside every finite constraint palette, the constraints that reduce jet capacity form explicit
  Schubert varieties. `[CONJECTURE]` Avoidance of all relevant incidence varieties is sufficient
  for residual full-translation differential independence inside the constrained positive cone.

## Why this is the next object

The retired constraint--orientation paper failed because it placed independent encodings side by
side. The stronger question is interactive:

> Which constraints actually remove hypertranscendental degrees of freedom from a positive Cauchy
> carrier, and by exactly how much?

The answer at every finite observation packet is an intersection law. The relevant geometry is not
the origin of the constraints but their position relative to the Cauchy-jet trace plane.

## Retirement verdict

The exact codimension formula is annihilator duality, and the capacity strata are standard Schubert
incidence varieties. The global residual promotion uses the same constrained transversality engine
as the measure-universal Herglotz theorem. It therefore fails the parent-theory and anti-theatre
gates as a new-science route.

Its surviving role is infrastructure for
`indeterminate-moment-fiber-maximal-translation-ht.md`, where **every** moment is fixed and the
Nevanlinna fiber produces an exact all-order flat coset with residual maximal HT. That theorem
contains the genuinely stronger nonperturbative interaction.

## Setup

Let `nu` be a positive measure with infinite support and let

```text
V = L-infinity(nu;R).
```

Fix distinct upper-half-plane nodes `zeta_1,...,zeta_m` and jet depths. Splitting real and imaginary
parts, let `W_J` be the resulting finite-dimensional real jet space and define

```text
T_J : V -> W_J,
T_J(v) = ( integral v(t) kappa_(j,r)(t) dnu(t) )_(j,r),       (1)

kappa_(j,r)(t) = r!/(t-zeta_j)^(r+1),                       (2)
```

with the regularized value kernel used when the measure is not finite. Infinite support and the
upper/lower pole separation argument imply that `T_J` is surjective.

Let `psi_1,...,psi_k in L-one(nu;R)` be constraint normals and put

```text
E = intersection_a ker(v |-> integral v psi_a dnu).          (3)
```

Let `C` be the real span of the `psi_a` in `L-one(nu)`, and let

```text
R_J = range(T_J^*) subset L-one(nu;R)                        (4)
```

be the rational Cauchy-jet trace space.

## Exact finite-packet incidence theorem `[PROVED HERE]`

Assume the constraint normals are linearly independent in `L-one(nu)`. Then

```text
codim_(W_J) T_J(E) = dim_R(C intersect R_J).                  (5)
```

Equivalently, the allowed positive-density directions retain complete local Cauchy-jet control if
and only if

```text
C intersect R_J = {0}.                                      (6)
```

### Proof

Because `T_J` is surjective, its transpose `T_J^*:W_J^* -> V^*` is injective. The annihilator of
`T_J(E)` consists exactly of those `ell in W_J^*` for which

```text
T_J^*(ell) in E-perp.                                       (7)
```

For the finite family of `L-one` constraints, `E-perp` inside the represented `L-one` functionals
is exactly `C`. Therefore `T_J^*` identifies the annihilator of `T_J(E)` with

```text
C intersect range(T_J^*) = C intersect R_J.                 (8)
```

The dimension of the annihilator of a subspace of the finite-dimensional space `W_J` equals its
codimension. This proves (5), and (6) follows. `QED`

The theorem is unchanged if one replaces `L-infinity` by any real Banach parameter space for which
the constraint and Cauchy-jet functionals have the displayed dual realization.

## Schubert geometry `[PROVED HERE]`

Fix a finite-dimensional real palette `A subset L-one(nu;R)` of dimension `n`, and vary a
`k`-dimensional constraint-normal space `C` in the Grassmannian `Gr(k,A)`. Put

```text
r_J = dim(A intersect R_J).                                  (9)
```

The capacity-loss locus

```text
Sigma_J = {C in Gr(k,A) : C intersect R_J != {0}}            (10)
```

is the standard Schubert incidence variety of `k`-planes meeting the fixed `r_J`-plane
`A intersect R_J`. If `k+r_J<=n`, its codimension is

```text
codim Sigma_J = n-k-r_J+1;                                  (11)
```

if `k+r_J>n`, every `k`-plane meets `A intersect R_J` and `Sigma_J=Gr(k,A)`.

This is the universal overlap profile for finite constraint palettes. Higher capacity losses are
the nested Schubert strata

```text
Sigma_(J,d) = {C : dim(C intersect R_J)>=d}.                 (12)
```

Equation (5) says that their incidence depth is exactly the lost real Cauchy-jet dimension.

## Moment-transversality corollary `[FINITE CORE PROVED]`

Assume the required moments are finite and take

```text
C_q = span_R{1,t,...,t^q}.                                  (13)
```

Then `C_q intersect R_J={0}`. A polynomial agreeing `nu`-almost everywhere with a real Cauchy-jet
rational trace agrees on the infinite support. Their difference is a rational function with
infinitely many zeros and hence is identically zero. The Cauchy trace has upper/lower nonreal
poles unless all its coefficients vanish, while a polynomial has none. Thus every coefficient and
the polynomial vanish.

Consequently, fixing any finite collection of ordinary moments removes no finite Cauchy-jet
direction from the positive density cone.

## Global promotion `[CONJECTURE]`

Let `rho_0` be a positive bounded density bounded away from zero, and work in the affine constrained
slice

```text
rho_0 + E,
```

restricted to a small positive `L-infinity` ball. Suppose `C intersect R_J={0}` for every finite
upper-half-plane Cauchy-jet packet `J` used by the translation-relation detector.

`[CONJECTURE]` For every prescribed countable translation palette, a residual set of densities in
this constrained positive slice has differentially algebraically independent translates over
`C(z)`. With the rank-defect codimension and parametric-transversality argument of the
measure-universal theorem, the same should hold for the full complex translation configuration.

### Open proof obligations

1. Formulate the constrained slice as a Baire parameter space without silently replacing it by its
   completion at the positivity boundary.
2. Prove simultaneous local submersion on the constraint kernel `E` from (6), including regularized
   value coordinates for infinite measures.
3. Re-run the rank-defect stratification uniformly on compact configuration patches.
4. Check that nonlinear log-density coordinates do not bend the fixed linear constraints; use
   additive positive densities for the exact theorem.
5. Audit whether the Schubert-incidence formulation exists in constrained holomorphic
   transversality or inverse-moment literature.

## Positive RH-route consequence `[CONJECTURAL UNTIL GLOBAL PROMOTION]`

Finite moment constraints are transverse to every finite Cauchy-jet plane. Therefore, if the global
promotion holds, a positivity or spectral route cannot obtain an RH selector from any fixed finite
moment packet, even when that packet is imposed exactly inside the positive measure cone. A viable
route must instead supply a cofinal constraint whose normal space accumulates onto the Cauchy trace
geometry, or an equivalent nonlocal source marking.

Positively stated:

> An HT carrier is restricted only by constraints aligned with its Cauchy trace planes; an
> RH-capable carrier must therefore contain a cofinal Cauchy-aligned constraint, not merely finitely
> many moments or generic finite observables.

This does not exclude moment, Weil, de Branges, Hilbert--Polya, or explicit-formula routes. It
identifies the geometric condition their completed constraint system must satisfy.

## Anti-theatre gate

- The finite incidence identity (5) is exact but follows from annihilator duality.
- The Schubert codimension (11) is standard Grassmannian geometry.
- The candidate-new content is their use as a complete local capacity law for constrained positive
  Cauchy HT carriers and the global residual promotion.
- No novelty or significance score is assigned until the global theorem is proved and parent
  literature is audited.

## Gates

- [x] exact finite-packet interaction law proved
- [x] finite-palette Schubert stratification identified
- [x] finite moment constraints proved transverse
- [ ] global countable-translation residual theorem proved
- [ ] full-complex-translation promotion proved
- [ ] parent-literature and rediscovery gates passed
- [ ] complete theorem formalized unconditionally in Lean

## Log

- 2026-07-12 -- Opened after the referee repair and repository containment audit retired the
  constraint--orientation product and its countable positive-Cauchy special case.
- 2026-07-12 -- Proved the exact annihilator-intersection formula, extracted the Schubert capacity
  strata, and verified that every finite polynomial-moment constraint space is transverse.
