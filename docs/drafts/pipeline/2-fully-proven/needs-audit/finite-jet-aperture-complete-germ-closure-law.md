# Finite jets retain maximal HT; one complete germ closes the boundary modulus

- **ID:** `finite-jet-aperture-complete-germ-closure-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / ANALYTIC SELECTION THRESHOLD LAW
- **Lane:** general hypertranscendence; indeterminate moment carriers; analytic constraints
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parents:** `nevanlinna-boundary-bauer-retract-maximal-ht.md`,
  `moment-polynomial-blind-resolvent-complete-boundary-splitting.md`
- **Statement:** In the canonical Nevanlinna boundary simplex of any indeterminate Hamburger
  moment problem, fixing any finite packet of finite-centre Cauchy jets leaves an
  infinite-dimensional positive level chart. Within that exact finite-jet level, with spectral
  type fixed, maximal full-complex translation hypertranscendence is residual. By contrast, the
  complete Taylor germ at one regular nonreal point determines the entire boundary probability
  law. Rigid analytic selection therefore has a sharp finite-jet / complete-germ threshold.

## Goal

The preceding geometry distinguishes moment data at infinity from resolvent data at finite centre.
The present theorem determines how much finite-centre data is needed. It rules out no route by
negation; it supplies the positive necessity law:

> **A rigid selector on an indeterminate HT carrier must contain infinitely coherent analytic germ
> data or an equally strong global constraint. Every finite local jet retains a positive maximal-HT
> aperture.**

The theorem concerns hypertranscendental functions in general. The RH consequence is a later
specialization.

## Setup

Let `T=RP^1(R)`, let `mu_tau` be the `N`-extremal family of a fixed indeterminate normalized
Hamburger sequence, and let

```text
m_tau(z)=m_infinity(z)-1/[C(z)^2(tau-q(z))].               (1)
```

Fix an infinite-support boundary probability `eta_0`, a positive radius `0<delta<1`, distinct
nodes `z_1,...,z_J in C minus R`, and finite jet depths `d_j>=1`. Write

```text
F_(j,r)(tau)=partial_z^r m_tau(z_j),
0<=r<d_j.                                                  (2)
```

The finite-jet level chart about `eta_0` is

```text
X_(eta_0,J,delta)={w in L-infinity(eta_0;R):
  ||w-1||_infinity<delta,
  integral_T w d eta_0=1,
  integral_T w F_(j,r)d eta_0
    =integral_T F_(j,r)d eta_0 for all (j,r)}.             (3)
```

Every `w` in `(3)` is strictly positive. Hence `eta_w=w eta_0` is equivalent to `eta_0`, and its
extremal barycenter `Beta(eta_w)` has the same complete Hamburger moments and the same transported
spectral type as `Beta(eta_0)`.

## Every finite jet level has infinite positive aperture `[PROVED HERE]`

The real tangent space of `(3)` is

```text
E_J={v in L-infinity(eta_0;R):
  integral_T v d eta_0=0,
  integral_T v F_(j,r)d eta_0=0 for all (j,r)}.            (4)
```

Real and imaginary parts turn `(4)` into finitely many real continuous linear constraints on the
infinite-dimensional Banach space `L-infinity(eta_0;R)`. Because `eta_0` has infinite support,
that Banach space is infinite-dimensional. Thus `E_J` has finite codimension and is
infinite-dimensional.

For every nonzero `v in E_J`, sufficiently small real `epsilon` gives two distinct points

```text
w_+=1+epsilon v,
w_-=1-epsilon v                                            (5)
```

in `(3)`. More generally, every finite-dimensional subspace of `E_J` has a small positive ball in
the chart. Hence a finite Cauchy jet does not merely fail to select uniquely: it leaves
arbitrarily large finite-dimensional positive apertures inside one exact moment and spectral-type
class.

## Jet controllability after the finite jet is frozen `[PROVED HERE]`

Fix a second finite packet of nonreal evaluation nodes `zeta_k` and derivative depths `e_k` such
that the parameter poles

```text
q(zeta_k), conjugate(q(zeta_k))                            (6)
```

are pairwise distinct and disjoint from all fixed poles

```text
q(z_j), conjugate(q(z_j)).                                 (7)
```

Such packets exist in arbitrary finite size because `q` is nonconstant and holomorphic.

On `E_J`, consider the new packet map

```text
T_(J,zeta)(v)_(k,l)
 =integral_T v(tau) partial_z^l m_tau(zeta_k)d eta_0(tau),
0<=l<e_k.                                                  (8)
```

This map is onto the complete finite complex target as a real-linear map.

### Proof

Suppose a real target functional annihilates `(8)`. The annihilator of the finite-codimensional
space `(4)` is the real span of the constant function and the real and imaginary parts of the
fixed functions `(2)`. Therefore a real combination of the target functions in `(8)` equals such
a fixed combination `eta_0`-almost everywhere.

After adjoining reflected conjugates, both sides are rational functions of `tau`. Their difference
vanishes on the infinite support of `eta_0`, so it is a rational identity. The target side has
principal parts only at `(6)`; the fixed side has principal parts only at `(7)`. The pole sets are
disjoint. Descending from the highest pole order at each point in `(6)` forces every target
coefficient to vanish. Hence the annihilating functional is zero, proving surjectivity. `QED`

The conclusion is stable if the second packet is enlarged: frozen finite-centre information costs
only finitely many parameter-pole directions and leaves all disjoint packets fully controllable.

## Residual maximal translation HT in an exact finite-jet level `[PROVED HERE]`

There is a dense residual subset

```text
G_(eta_0,J,delta) subset X_(eta_0,J,delta)                 (9)
```

such that, for every `w in G_(eta_0,J,delta)` and every finite tuple of distinct complex shifts
`h_1,...,h_m`, the functions

```text
m_(eta_w)(z+h_1),...,m_(eta_w)(z+h_m)                     (10)
```

are differentially algebraically independent over `C(z)`.

### Proof

Fix one differential-relation support. Refine the distinct-shift configuration space into
countably many sufficiently small compact patches. On each patch choose more auxiliary evaluation
rows than the complex rank-defect codimension requires, with all translated parameter poles
pairwise separated and disjoint from the frozen set `(7)` throughout that patch. At a fixed shift
configuration such row choices form a dense open set; separation persists after shrinking the
patch. The aperiodicity of `q` from the parent theorem removes translation stabilizers.

The constrained controllability theorem `(8)` supplies finitely many directions in `E_J` spanning
the complete row-jet target. On their finite real span, the universal
direction--shift evaluation map is a submersion. Parametric transversality makes the chosen
rank-defect preimage empty for a dense set of parameters inside every neighborhood of `(3)`.
Compact-patch normal convergence gives openness.

Intersect over the countable differential-relation patterns and a countable compact cover of all
finite distinct-shift configuration spaces. The resulting set is `(9)`, and clearing rational
coefficient denominators gives `(10)`. If a relation is initially defined only as an upper-end
germ, its terms are meromorphic on the common connected component above the shifted real lines, so
the identity theorem carries it to the chosen high evaluation rows. `QED`

Because every density in `(3)` is equivalent to `eta_0`, `(9)` holds with the exact transported
spectral type fixed. Componentwise normalization can additionally fix any prescribed pure-point /
singular-continuous / absolutely-continuous mass vector, by the same finite-codimension argument.

## Complete-germ closure `[PROVED HERE]`

Now fix one regular point `z_0 in C minus R` with `C(z_0)!=0`. If two boundary laws `eta_1,eta_2`
have the same complete Taylor jet

```text
partial_z^r m_(eta_1)(z_0)
 =partial_z^r m_(eta_2)(z_0)  for every r>=0,              (11)
```

their analytic germs agree. With `rho=eta_1-eta_2`, equation `(1)` gives on a neighborhood of
`z_0`

```text
integral_T 1/(tau-q(z))d rho(tau)=0.                      (12)
```

The open mapping theorem and Stieltjes-transform uniqueness imply `rho=0`, including its mass at
the projective point at infinity because `rho(T)=0`. Hence

```text
eta_1=eta_2.                                               (13)
```

Thus the infinite intersection of all finite-jet level sets at one regular point is a singleton,
although each finite stage contains infinite-dimensional positive charts with residual maximal
translation HT.

## Finite-jet aperture / complete-germ closure law

> **On the canonical boundary modulus of an indeterminate moment constraint, every finite
> finite-centre analytic jet leaves an infinite-dimensional positive aperture and a residual
> maximal full-translation HT phase, even at fixed spectral type. The coherent complete Taylor
> germ at one regular point closes that modulus to one boundary law. Analytic rigidity begins at
> germ completeness, not at any finite jet order.**

This is a phase threshold, not a claim that “finite data are insufficient” in the abstract. It
identifies the surviving positive geometry at every finite stage and proves exact closure at the
limit.

## Exact scope via Pick defect `[PROVED IN COMPANION]`

The companion `pick-defect-finite-selector-maximal-ht-phase-law.md` gives the global correction to
the chart theorem. A finite analytic packet can select uniquely when its reduced confluent Pick
matrix is singular; the unique solution then has a rational inner parameter and is finite-order
canonical. Otherwise the Pick matrix is positive definite, a free Schur parameter remains, and
maximal full-translation HT is dense residual in the entire exact level set.

The infinite-support boundary mixtures used here necessarily lie in the positive-defect phase. If
their finite data had singular Pick matrix, classical uniqueness would make their Pick parameter
rational inner and their moment solution finite-order canonical, contradicting the nontrivial
boundary mixture. Thus the aperture theorem above is exactly the nonsingular branch of the general
Pick-defect dichotomy, not an overstatement about singular boundary data.

## General HT consequence

For hypertranscendental carrier problems built from moment or Herglotz constraints, finitely many
normalizations, values, or derivatives cannot create differential rigidity while the Nevanlinna
boundary aperture remains. A successful constraint must do one of two positive things:

1. impose a complete coherent analytic germ, which determines the boundary law by `(11)`--`(13)`;
2. impose a genuinely global constraint whose tangent destroys the parameter-pole controllability
   used in `(8)`.

This supplies a practical route test: freeze the proposed finite source data and compute whether a
disjoint finite Cauchy-jet packet remains onto. If it does, maximal translation HT remains residual
inside the proposed carrier class.

## Lean status

Formalization is complete only relative to the exact classical Nevanlinna and finite-dimensional
parametric-transversality interfaces already isolated by the carrier stack.

- `CauchyJetControllability` proves real-linear finite Cauchy-jet surjectivity and arbitrarily
  small positive finitely supported perturbations.
- `InfiniteSupportPositiveAperture`, `PositiveHilbertCubeEmbedding`, and
  `AtomlessProjectivePositiveAperture` prove the infinite-dimensional positive aperture and the
  closed embedded Hilbert-cube refinement under the stated support hypotheses.
- `AnalyticNevanlinnaCarrierBridge`, `NevanlinnaPositiveCarrierCapstone`, and
  `AnalyticNevanlinnaCarrierRelationFree` identify the abstract frozen tangent with actual
  weighted Nevanlinna-carrier jets and prove the dense residual all-finite-pattern
  hypertranscendental phase inside the exact positive chart.
- `CompleteCauchyGermClosure` proves canonical closure at `i` and `-i`, equality from all finite
  prefixes, affine transport of the complete derivative sequence, and
  `measure_eq_of_completeCauchyJet_eq` at every nonreal point. Thus the complete germ determines
  the carrier probability law with no canonical-node restriction.
- The boundary barycenter is a closed embedding in `NevanlinnaBoundaryKernel`; therefore equality
  of the selected carrier laws also identifies their boundary probability laws.

All project-specific deductions on this card are represented in Lean, but the classical
Nevanlinna source theorem and the general proper-projection/Whitney-parametric-transversality
theorem remain theorem parameters.  Until those inputs are constructed in Lean, the residual-HT
half of the card is not unconditional and the card does not clear Stage 3.

## Positive RH-carrier consequence

Any RH route using only finitely many local values, derivatives, normalizations, Hankel minors, or
finite resolvent samples leaves the positive aperture `(3)` whenever its underlying moment carrier
is indeterminate. Such a route must be completed by an all-order coherent analytic constraint or a
global orientation law.

The current Xi/Hedenmalm route crosses the selection threshold: the complete pointed Taylor germ
of the normalized prime--archimedean source determines the germ, source trace, `XiC`, and local
Bezoutian. The remaining RH-bearing obligation is not another finite jet. It is the global
Hermitian orientation sign of the reconstructed kernel.

## Parent-theory and novelty attack

1. `[SEARCH]` Finite-codimensional kernels in `L-infinity`, analytic germ uniqueness, and
   Stieltjes-transform uniqueness are standard.
2. `[BRIDGE]` Parameter-pole controllability and full shift-configuration transversality are the
   engines of the parent moment-fiber HT theorem.
3. `[PROVED HERE]` Freezing an arbitrary finite Cauchy jet only adds a finite set of parameter poles;
   disjoint principal-part elimination restores complete controllability on the constrained
   tangent.
4. `[PROVED HERE]` Residual maximal full-translation HT therefore survives inside every exact
   finite-jet positive level at fixed spectral type.
5. `[PROVED HERE]` The complete coherent Taylor germ closes the same boundary modulus to a point,
   producing an exact finite/infinite analytic selection threshold.
6. `[CANDIDATE RESIDUE]` Preliminary exact searches found no theorem combining this threshold with
   residual full-complex translation differential independence in an exact complete-moment fiber.
7. The theorem remains `[NOVELTY UNVERIFIED]` pending review by specialists in moment problems,
   differential algebra, transversality, and operator theory.

No numerical experiment and no RH assumption enter the theorem.

## Honest significance score

The combined route is now an internal **90/100 candidate**, with a deliberately wide **72--94**
range pending specialist proof and priority review. This is the first point at which the route has
a plausible 90 case, not a verified field-level score.

- **Why it creates the plausible 90 case:** the theorem classifies the analytic selection
  threshold itself. It proves both sides: residual maximal HT in every exact finite-jet level and
  uniqueness at the complete-germ limit. This is a reusable law for constrained HT carriers, not
  only a description of one convex fiber.
- **Why 90 is not yet verified:** the mechanism still synthesizes classical moment theory with the existing
  transversality engine; priority is unaudited; no explicit source-canonical maximally HT member is
  constructed; the theorem is not formalized in Lean; and the Xi orientation sign remains open.

## Formalization audit

The complete-germ closure `(11)`--`(13)`, finite Cauchy-jet controllability, positive Hilbert-cube
aperture, Nevanlinna carrier bridge, and all project-specific Baire deductions are formalized.
The remaining blockers are the construction of the classical analytic Nevanlinna family from an
arbitrary indeterminate Hamburger sequence, the proper-projection/Whitney stratification theorem,
and the finite-dimensional stratified parametric-avoidance theorem.  The current residual-HT
capstone takes the last two as values of `ClassicalComplexProjectiveIncidenceGeometry` and
`ClassicalStratifiedParametricAvoidance`; therefore it is not yet unconditional.

## Gates

- [x] arbitrary finite Cauchy-jet level defined
- [x] infinite-dimensional positive aperture proved
- [x] exact moment and spectral-type preservation proved
- [x] disjoint-pole controllability on the constrained tangent proved
- [x] residual maximal full-translation HT in the exact finite-jet level proved
- [x] complete-germ uniqueness proved
- [x] finite-jet / complete-germ threshold law extracted
- [x] scope corrected and completed by the singular/free Pick-defect companion
- [x] concrete Xi/Hedenmalm consequence scoped
- [x] local prior-research collision search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [ ] unconditional Lean formalization of the entire exact theorem

## Log

- 2026-07-12 -- Froze an arbitrary finite packet of finite-centre Cauchy jets in the boundary
  density chart. Proved that the constrained tangent remains infinite-dimensional and controls
  every disjoint jet packet, yielding residual maximal full-translation HT at fixed spectral type.
  Proved that the complete Taylor germ at one regular point uniquely determines the boundary law.
