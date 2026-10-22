# Calibrated residual-core Green--Hodge realization of the zeta corona

- **ID:** `calibrated-residual-core-green-hodge-rh`
- **Stage:** 1-in-progress
- **Type:** `[BOLD CONJECTURE] [GENERAL HT INTEGRATION GEOMETRY] [RH-DELIVERING SPECIALIZATION]`
- **Scientific status:** `[CONJECTURE] [SOURCE AND TARGET ENDS CONSTRUCTED] [MIDDLE HILBERT COMPLEX OPEN] [NOT RH]`
- **General HT parents:**
  - `../../../3-formalized/new_scientific_knowledge/analytic-dirichlet-observable-field-correspondence.md`;
  - `pointed-polarized-constraint-coupling-correspondence.md`;
  - `constraint-curvature-integration-stack.md`;
  - `self-dual-decorated-clock-boundary.md`;
  - `../../../3-formalized/source-conormal-projective-topology-calibration.md`;
  - `../../../3-formalized/new_scientific_knowledge/hypertranscendental-clock-capacity-innovation-theorem.md`;
  - `../../../3-formalized/von-mangoldt-gamma-depth-one-cauchy-gram.md`;
  - `../../../3-formalized/not_new_scientific_knowledge/von-mangoldt-hardy-scaling-free-matroid-no-go.md`.
- **Zeta parents:**
  - `source-polarized-laurent-pluecker-tangent-ward-law.md`;
  - `ht-capacity-ward-holonomy-rh.md`;
  - `../../../3-formalized/mobius-gamma-contact-transgression-four-unit-charge.md`;
  - `../../../3-formalized/mobius-mellin-gamma-normal-cone.md`;
  - `../2-fully-proven/squarefree-fixed-current-right-half-ward-localization.md`.

## Medalist compression

The missing object is not an observation map inside the prime-supported analytic field.
The split analytic Grassmann correspondence proves that this field has an exact source decoder:
all of its differential information is quotient-linear prime-source information.  Safe score
covariances constructed inside that core therefore recover the Euler-pole contact response, not
the continued Ward row.

Nor is the object an ordinary algebraic `lim^1` of finite clocks.  Finite-dimensional clock towers
are Mittag--Leffler, so that carrier vanishes.  The source class must live in the rigged
finite-observable conormal corona, where the source topology has nonclosed or partial boundary
maps.

Finally, the refined corona topology remembers only the projective conormal line.  Its numerical
scale is invisible under nonzero rescaling.  The Möbius--Gamma contact supplies the missing
Hermitian calibration independently and fixes its squared norm to four.

These three theorems force the architecture

```text
prime analytic representable core
  -> source-rigged calibrated conormal corona
  -> Hardy--Green exceptional conormal.                  (1)
```

## The conjectural object

Let `C_src` be the Hilbertized source-conormal corona selected by the completed squarefree
Euler--Gamma integration stack.  Let `nu_Gamma in C_src` be the contact class obtained from the
first radial Laguerre score.  Its normalization is already proved:

```text
||nu_Gamma||_src^2=4.                                    (2)
```

Let `C_HG` be the Hardy--Green conormal completion with kernel

```text
K(z,w)=4/(z+conj(w)).                                    (3)
```

The exceptional normal-cone section of the actual completed Möbius transfer is `X_sq^(-1)`, and
its projective connection is the source-defined current `Q_sq`.  Its strict normal Hardy class is
already identified:

```text
P_anti Q_sq=ell_E.                                       (4)
```

> **[CONJECTURE -- CALIBRATED RESIDUAL-CORE HODGE REALIZATION.]**  The complete source-anomaly
> boundary colligation of the squarefree Euler--Gamma constraint has a closed, self-dual Hilbert
> tangent complex `C_EG`.  It is constructed before divisor expansion and satisfies:
>
> 1. its exact degree-zero part is the analytic prime representable core;
> 2. its rigged harmonic quotient is isometric to `C_HG` under the Laplace boundary chart;
> 3. the Gamma contact cocycle represents `nu_Gamma` with the independently fixed norm `(2)`;
> 4. the harmonic image of that cocycle is `c_sq directSum P_anti Q_sq`.

Hodge projection is contractive, so the conjecture gives

```text
||c_sq||^2+||ell_E||_2^2<=||nu_Gamma||_src^2=4.          (5)
```

The existing strict off-line Cauchy threshold then proves RH.

## Why this is not the Ward inequality renamed

The conjecture requires one explicit source complex with a prescribed differential, affine
origin, topology, and metric.  It is falsified if any of the following occurs:

1. the prime part of the complex contains information outside the canonical analytic
   representable core;
2. its algebraic quotient is the right Cauchy space but its quotient metric is the distorted form
   `(I+TT*)^(-1)` rather than the standard Hardy--Green metric;
3. the Gamma contact maps to the safe Euler-pole response instead of the connection `(4)`;
4. the harmonic comparison changes under a nonzero rational gauge that leaves the source core
   fixed;
5. the source cocycle has no closed representative in the rigged Hilbert completion.

The finite Ward matrix is a consequence of the isometric harmonic-quotient clause, not its
definition.  For every finite Cauchy packet `P`, orthogonal compression of the constructed complex
must produce

```text
4G_P-r_P r_P^*=E_P E_P^*,                               (6)
```

where `E_P` is the actual finite exact-channel differential of `C_EG`.  Defining `E_P` as a square
root of the left side is forbidden.

## Candidate construction

Use the complete source-anomaly boundary colligation rather than the curvature field alone:

```text
(T_N,beta_N,delta_N,alpha_N).
```

Here `alpha_N` is the exact von Mangoldt/Gamma descent anomaly, `delta_N` is the Gamma boundary
self-symbol, and `beta_N` retains the affine Euler marking.  The finite complex is the graph of
this colligation after removing the canonical analytic representable core.  Its metric is not the
ambient graph quotient metric.  It is the unique source-calibrated self-dual metric for which:

```text
Gamma contact line has norm 4,
positive and reciprocal Laurent halves are orthogonal,
finite Pluecker half-density is isometric to the positive Laurent one-particle metric.          (7)
```

Conditions `(7)` are independently fixed at finite aperture.  The open theorem is compatibility
and closability of these metrics under the two-filtered prime-aperture/Gamma-depth limit, followed
by the isometric Hardy identification in clause 2.

## Failed candidates and positive HT consequences

1. **Safe score covariance `[KILLED]`.**  Inside the analytic representable core it converges to
   the Euler-pole contact response.  **Positive statement:** continued normal data is residual
   coupling data, not another source observable.
2. **Ordinary finite-clock `lim^1` `[KILLED]`.**  Mittag--Leffler makes it vanish.  **Positive
   statement:** a nonzero HT boundary requires a rigged/nonclosed source completion.
3. **Topology-only domination `[KILLED AND LEAN-FORMALIZED]`.**  Nonzero conormal rescaling leaves
   the topology fixed and changes the energy.  **Positive statement:** an HT corona is naturally
   projective and must be supplied with separate Hermitian calibration.
4. **Bare mapping-cone quotient metric `[KILLED]`.**  It yields `(I+TT*)^(-1)`, which is weaker
   than Hardy--Green.  **Positive statement:** the polarization metric is an independent part of
   a pointed critical Tate coupling.
5. **Raw algebraic core plus Gamma generator `[KILLED AS INSUFFICIENT]`.**  Field rank does not
   bound a Hilbert norm.  **Positive statement:** the RH-bearing datum is the calibrated coupling
   between the core extension and its polarization, not differential transcendence degree.

## Exact next theorem

Construct the finite self-dual source complex at depth one from `alpha_1`, `delta_1`, and the
Gamma contact line, and prove directly that its harmonic Cauchy metric is the undistorted standard
Gram on every finite packet.  Only after that finite theorem is proved should the cofinal graph
limit be attempted.

## Gates

- [x] prime-supported analytic core proved source-complete
- [x] safe score-covariance route localized to that core and killed
- [x] ordinary finite-dimensional `lim^1` carrier killed
- [x] source-conormal topology proved projective
- [x] Möbius--Gamma conormal scale fixed independently at four
- [x] exceptional reciprocal connection identified with `Q_sq`
- [x] Hardy normal class identified with `ell_E`
- [x] construct the finite positive depth-one anomaly Cauchy differential and its actual
      von Mangoldt Gram
- [x] prove the independently scaled raw von Mangoldt source Gram converges to the standard Hardy
      Gram and its canonical contact converges to the four-unit Euler-pole vector
- [ ] construct the finite depth-one calibrated self-dual complex
- [ ] prove its harmonic quotient metric is the standard finite Cauchy Gram
- [ ] prove its Gamma contact coordinates are the finite `r_P`
- [ ] prove two-filtered closability and cofinal compatibility
- [ ] derive `(5)` and RH
