# Gravity is clocks disagreeing about which moment comes first

- **ID:** `gravity-is-clock-order-disagreement`
- **Stage:** 0-backlog
- **Type:** NORTH-STAR PHYSICAL CONJECTURE / TIME / CAUSALITY / GRAVITY /
  HYPERTRANSCENDENCE
- **Source:** canonical hypersurface-deformation algebra crossed with
  `../4-publication-ready/riemann-orientation-boundary-fracture/main.tex`
- **Status:** headline accepted; physical novelty and HT bridge open

## Headline

> **Gravity is clocks disagreeing about which moment comes first.**

Sharper scientific form:

> **The spatial metric is the rule that converts the order-dependence of local time steps into
> spatial displacement.**

Possible holographic form:

> **Gravity is the boundary record of time steps performed in opposite orders.**

These are candidate interpretations, not results of the Riemann-orientation paper.

## Known gravitational parent

For lapse profiles \(N,M\), canonical general relativity has the hypersurface-deformation
relation

```text
{H_perp[N], H_perp[M]}
  = H_a[q^{ab}(N partial_b M - M partial_b N)].                  (1)
```

Thus two infinitesimal normal deformations performed in opposite orders differ by a tangential
displacement

```text
v^a_(N,M) = q^{ab}(N partial_b M - M partial_b N).               (2)
```

The inverse spatial metric is a structure function, not a constant. In a local coordinate chart,
take the first lapse profile to be constant and the second to be the coordinate profile \(x^j\).
Then

```text
v^i_(1,x^j) = q^{ij}.                                           (3)
```

Equation (3) is the exact seed of the headline: the metric components can be read from the
oriented composition defect of local time deformations. This is a direct consequence of the
known Dirac--Teitelboim algebra and receives no novelty credit by itself.

## What the Riemann orientation paper contributes

The paper proves a carrier lesson that is absent from the bare gravitational slogan.

1. **Orientation must be retained before scalarization.** The unsquared normal current
   `J_a = partial_a |Xi(b-ia)|^2` retains a sign whose threshold is exactly divisor width.
2. **Regular positive scalar carriers can fail.** No finite local constant-coefficient Gram
   carrier represents the oriented current; the natural translation-stable positive source form
   collapses to a singular nonclosable divisor rigging.
3. **Complete HT differential data can still be orientation-charge blind.** Every real-aperture
   differential matroid is unchanged by arbitrary inserted quartet multiplicity.
4. **A marked noncompact boundary restores the missing integer.** Its Ward mass is exactly
   `8 pi N`, even when its density escapes every bounded window.

The transferable principle is:

```text
all local scalar clock data
  need not determine oriented composition charge;

source-marked boundary data
  can retain the charge lost by scalarization.                              (4)
```

This is an exact theorem for the Riemann source. It is not yet a theorem about spacetime.

## Candidate new physical law

Let a bounded gravitational region carry localized clock deformations \(U_N(\epsilon)\). Define
the order holonomy

```text
Omega_(N,M)(epsilon)
  = U_N(epsilon) U_M(epsilon)
    U_N(epsilon)^(-1) U_M(epsilon)^(-1).              (5)
```

Its infinitesimal antisymmetric channel is the clock-order defect. The target law has three
parts.

### G1 — Metric tomography

The complete family of order defects for a coordinate-generating set of lapse profiles uniquely
reconstructs \(q^{ab}\). A finite operational version must specify probes, errors, and the number
of order-interference experiments needed to recover the metric.

### G2 — Boundary visibility

On a closed physical constraint surface the tangential displacement is gauge. For a subregion
with an observer-marked boundary, the same displacement is represented by a gravitational edge
charge. The measurable carrier of clock-order disagreement is therefore a boundary mode.

### G3 — HT orientation fracture

A physical source-selected HT clock family should exhibit a strict analogue of (4):

```text
complete scalar differential clock geometry
  is blind to a finite order charge,

marked antisymmetric boundary holonomy
  recovers that charge injectively.                              (6)
```

Only G3 would make hypertranscendence essential. The Riemann theorem proves that this fracture can
occur; it does not prove that gravitational clocks realize it.

## Experimental thought-protocol

Use a quantum-controlled ordering of two weak, spatially patterned clock couplings.

1. One control branch applies \(U_N U_M\); the other applies \(U_M U_N\).
2. Interference reads the antisymmetric order channel rather than separate scalar clock rates.
3. Vary the lapse profiles to tomographically recover the induced shift \(v^a_{N,M}\).
4. Invert (2) to recover \(q^{ab}\), or detect failure of the classical hypersurface-deformation
   law.

The decisive observable is not ordinary gravitational redshift. It is an order-sensitive
interference phase or displacement. A viable paper needs a concrete weak-field model and a
finite-resolution signal estimate.

## Direct prior-art collision

This route begins inside established theory:

- hypersurface-deformation algebra already places \(q^{ab}\) in the commutator of normal
  deformations;
- quantum reference-frame work already studies superpositions of proper times and indefinite
  temporal localization;
- gravitational edge modes already carry diffeomorphism boundary charges;
- Giesel--Kabel--Wieland explicitly relate gravitational edge modes and geometrical clocks in
  linearized gravity.

Therefore “clock commutators contain the metric” or “clocks relate to edge modes” is not enough.
The publication claim must be the operational reconstruction theorem plus the HT-specific
orientation fracture and a prediction not contained in those parents.

## Exact kill conditions

Retire the Nature claim if any holds:

1. G1 reduces entirely to choosing coordinate lapse profiles in (1), with no new invariant,
   protocol, stability theorem, or prediction.
2. The boundary clock-order observable is gauge-equivalent to an already known edge charge with
   no HT-dependent sector.
3. Every proposed G3 uses the Riemann source only as analogy and has no physical HT clock.
4. HT is replaceable by an arbitrary faithful probe without changing any conclusion.
5. Quantum-controlled order adds no observable beyond ordinary metric/redshift tomography.
6. The phase disappears under allowed clock, lapse, or boundary-frame recalibration.

## Research sequence

1. State the classical clock-order tomography theorem with all gauge and phase-space-dependent
   smearing subtleties explicit.
2. Derive the group-commutator signal through second nontrivial order without treating a
   dynamical clock field as an external lapse.
3. Pass from closed constraints to a bounded region and identify the exact edge charge.
4. Audit Giesel--Kabel--Wieland and gravitational corner-symmetry literature for theorem
   equivalence.
5. Find a standard physical HT clock source whose scalar family is charge-blind but whose
   antisymmetric boundary channel is not.
6. Produce one falsifiable weak-field or analogue-gravity protocol.
7. Only after G1--G3 survive, prove the mathematical package on paper and formalize it
   unconditionally in Lean.

## Typed frontier after gravity and quantum-gravity audit

The headline currently crosses six different mathematical types. They must not be identified.

| Layer | Exact carrier | What it determines | What it does not determine |
|---|---|---|---|
| hypersurface kinematics | first normal--normal HDA bracket | inverse spatial metric and signature convention | Riemann curvature |
| spacetime gravity | connection-corrected infinitesimal holonomy or clock-compass gradients | Riemann tensor | quantum character |
| clock coordinates | brackets of chosen geometrical reference fields | gauge-dependent frame data | invariant noncommutativity |
| bounded-region physics | corner/edge charge | observable remnant of a diffeomorphism at a marked boundary | a new HT sector by itself |
| quantum-order protocol | coherent control of two operations | an order-sensitive amplitude | a uniquely gravitational witness |
| HT source | differential transcendence of a physical response | exclusion of every finite differential closure | curvature, quantumness, or time orientation by itself |

Consequences:

1. The first HDA bracket is nonzero in flat Minkowski spacetime. Calling it curvature is false.
2. Riemann curvature requires the connection-corrected commutator
   `nabla_X nabla_Y - nabla_Y nabla_X - nabla_[X,Y]` on a vector/tensor frame, or an equivalent
   clock-compass reconstruction. Scalar covariant derivatives commute.
3. Giesel--Kabel--Wieland show that geometrical clocks in linearized gravity can be Abelianized
   order by order by adding constraint terms. Bare clock noncommutativity is therefore not an
   invariant gravitational observable.
4. On a closed constraint surface the HDA displacement is gauge. A marked boundary or relational
   reference is required before the order defect can carry a physical charge.
5. An indefinite-order interference signal is not uniquely gravitational. The optical and
   gravitational quantum switches have the same operational causal-order observable in the known
   comparison.
6. HT excludes a finite differential model, but a classical continuum can also be HT. It is not a
   quantum witness without an independent nonclassicality theorem.

## Exact local survivor: space is the span of clock-order defects

At a point of a spatial slice, write

```text
B_q(N,M) = q sharp (N dM - M dN).
```

For the constant lapse `1` and every local coordinate function `x^j`,

```text
B_q(1,x^j) = q sharp(dx^j).
```

Therefore the span of all local clock-order defects is exactly `im(q sharp)`. In particular:

```text
q nondegenerate
  iff local clock-order defects span the complete spatial tangent space;

all local time steps commute
  iff q sharp = 0.
```

This is the strongest correct version of the first half of the headline:

> **Space is exactly what local time steps can disagree into.**

It is a metric-reconstruction theorem, not yet a new law of gravity. The next original target is a
gauge-invariant bounded-region theorem in which variation of this order map reconstructs curvature
and its marked edge charge.

## Schwarzschild HT source pressure test

Solon's all-order Schwarzschild response supplies a genuine physical HT source:

```text
tau_ret(eta) = L + 2(psi(1-eta) + gamma_E).
```

It fails the naive G3 interpretation for two independent reasons.

1. Its zeta tower is generated in the far zone by the universal Newtonian/Coulomb `1/r` phase,
   not uniquely by horizon geometry.
2. With `tau_adv(eta)=tau_ret(-eta)`, digamma reflection gives

```text
tau_ret - tau_adv
  = 2(psi(1-eta)-psi(1+eta))
  = 2 pi cot(pi eta) - 2/eta,
```

so the time-antisymmetric dressed-log sector is differentially algebraic. The time-symmetric sum
remains hypertranscendental. Equivalently, for the Gamma carriers

```text
P(eta) = Gamma(1+eta) Gamma(1-eta),
Q(eta) = Gamma(1+eta) / Gamma(1-eta),

tau_ret - tau_adv = -2 logDeriv(P),
tau_ret + tau_adv = DA constant + 2 logDeriv(Q).
```

The integral-shift product `P` is DA; the quotient `Q` and its logarithmic derivative are HT.
Thus the irreducible HT content is shared by the two time orientations rather than being their
difference. This rules out using the Schwarzschild far-zone scalar alone as the oriented
clock-order charge.

The exact proof is tracked in
`../../../3-formalized/new_scientific_knowledge/schwarzschild-time-orientation-ht-split.md`.

## Revised live conjecture

The surviving route is no longer “an HT scalar clock is gravity.” It is:

> **In a bounded gravitational region, the image of the clock-order map is spatial geometry; its
> connection-corrected variation is curvature; and a source-selected HT obstruction to globally
> Abelianizing this map is carried by an observer-marked edge mode.**

Three obligations are independent:

1. prove the local image/rank tomography and curvature reconstruction;
2. prove invariance under allowed clock redefinitions and constraint additions;
3. find a physical two-direction HT source whose antisymmetric boundary sector, not merely a
   scalar scattering phase, survives those redefinitions.

No current corpus theorem discharges obligation 3.

## Current verdict

**PROMISING HEADLINE; OPEN SCIENCE.** The Riemann paper supplies a nontrivial warning and design
principle: orientation can survive before scalarization while every local, regular, and even
maximally HT scalar carrier misses the relevant charge; a marked boundary can restore it. General
relativity independently says that clock-order composition contains the inverse metric. Their
intersection is intellectually sharp, but the exact gravitational HT carrier and distinct
prediction do not yet exist.

## Primary sources for the current boundary

- T. Thiemann, *Non-degenerate metrics, hypersurface deformation algebra, non-anomalous
  representations and density weights in quantum gravity*,
  <https://arxiv.org/abs/2207.08299>.
- K. Giesel, V. Kabel, and W. Wieland, *Linking Edge Modes and Geometrical Clocks in Linearized
  Gravity*, <https://arxiv.org/abs/2410.17339>.
- L. Freidel, E. R. Livine, and D. Pranzetti, *Gravitational edge modes: From Kac--Moody charges
  to Poincare networks*, <https://arxiv.org/abs/1906.07876>.

## Log

- 2026-07-28 — opened after direct audit of the publication-ready Riemann orientation-carrier
  paper. Recorded exact conceptual payload, immediate GR identity, prior-art collision, and
  missing HT-specific physical theorem.
- 2026-07-28 — completed typed GR/QG pressure test. Separated metric from curvature, gauge clock
  brackets from boundary charge, and order interference from a quantum witness. Identified the
  exact local image/rank survivor and ruled out the Schwarzschild far-zone dressed log as a direct
  orientation carrier: its time-antisymmetric sector is DA while its time-symmetric sector is HT.
