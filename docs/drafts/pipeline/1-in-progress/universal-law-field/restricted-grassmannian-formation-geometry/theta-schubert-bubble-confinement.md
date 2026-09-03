# Theta--Schubert bubble confinement

- **ID:** ULF-TSBC-001
- **Stage:** 1-in-progress
- **Type:** CONJECTURE · frozen after preliminary hostile audit
- **Source:** `ULF-RPGT-001` · `ULF-BGCA-001` · `MUST-138`
- **Statement:** Literal Gaussian Euler--continuum formation admits a coefficient-native
  Bott-suspended pseudoholomorphic sewing in the restricted Grassmannian; every off-line Xi
  multiplicity is a positive determinant-line Schubert bubble, and source graph-cap area is its
  total energy budget.

## 0. Big-picture interpretation

`[CONJECTURE]` RH is not primarily a statement that zeros occupy a line.  It is a no-bubbling
theorem for arithmetic formation after graded Euler--continuum reduction.

The literal prime source forms a holomorphic positive graph cap of determinant-line area `<1`.
The full pre-reduction field is the four-leg Krein superconnection `ULF-ETRS-001`, because theta
completion subtracts a continuum current and the corpus forbids a nonzero invariant positive form.
After quotienting the universal continuum leg, completion can fail to stay in the reduced big
graph cell only by emitting an integral Schubert bubble.
Every positive bubble has area at least one.  Therefore a correctly sewn source cap cannot emit
one.

The critical line is the fixed real/Lagrangian wall of functional-equation reflection.  A zero on
that wall creates no transverse Schubert bubble.  An off-line quartet is the observable shadow of
a positive bubble emitted when the zero-free Euler formation leaves the determinant big cell.

The proposed universal law is

```text
E_source = E_residual + sum_j m_j,                    (TSBC.1)
sum_j m_j = Tr mathsf T_D,
0 <= E_source < 1,
E_residual >= 0.
```

`ULF-DLLA-001` identifies the structural meaning of `(TSBC.1)`.  Determinant holonomy sees
`exp(2*pi*i*E_source)` and is unchanged when an integer bubble is removed.  The cubic trace must be
the deck translation between the Euler principal lift and the theta residual lift:

```text
Tr mathsf T_D
  = Lift_Euler(det holonomy)-Lift_theta(det holonomy). (TSBC.1d)
```

Thus phase equality is information-neutral by design.  Selection comes only from the lifted
action filtration.

Here `mathsf T_D=(U_D* P U_D-P)^3` is the already-constructed integral--nuclear boundary defect.
The higher object is not a new receiver.  It is a stable formation surface whose bulk
determinant-line class transgresses to that cubic boundary character.

## 1. Corpus audit before conjecture

Searches:

```text
scripts/formal_tools.py research "tateTheta_nodeCharge_eq_boundaryWinding"
scripts/formal_tools.py research "weldFEReflectionLinear_reverses_area"
scripts/formal_tools.py research "offLineXiDivisor_descentAnomalyBubbleLaw"
scripts/formal_tools.py research "criticalHorizonSchubertCell"
scripts/formal_tools.py research "RoutePPrimitiveBurnolBaseNuclearSynthesis"
scripts/formal_tools.py research "RoutePPrimitiveBurnolMatrixCompleteColligation"
scripts/formal_tools.py research "Grassmannian determinant Kähler graph cap Schubert bubble"
```

### Exact shadows already proved

1. `[CORPUS]` `routePPrimitiveBurnolBaseSynthesis` is literal all-prime, pre-divisor, and
   Hilbert--Schmidt.  Its covariance is nuclear and its trace mass is `B_base<1`.
2. `[CORPUS]` Matrix-complete Burnol colligation preserves cross-prime Gram entries and decomposes
   lost source energy into positive boundary/cocycle channels.
3. `[CORPUS]` `mathsf T_D=(U_D*PU_D-P)^3` is the first critical-grade displacement that is at once
   nuclear, reflection-odd, and integral.  Its trace is strict-right multiplicity.
4. `[CORPUS]` `tateTheta_nodeCharge_eq_boundaryWinding` identifies escaping divisor charge with
   limiting boundary winding.  `eventually_tateTheta_divisor_avoids_compact` proves the complete
   divisor escapes every compact subset.
5. `[CORPUS]` `weldFEReflectionLinear_reverses_area` proves functional-equation reflection is
   anti-symplectic for the canonical weld area.
6. `[CORPUS]` `offLineXiDivisor_descentAnomalyBubbleLaw` identifies an off-line divisor with a
   nonzero normalized descent anomaly and a source-matched escaping Ward bubble carrying the same
   multiplicity.
7. `[CORPUS]` `card_criticalHorizonSchubertCell` already makes critical-horizon multiplicity a
   Schubert-cell count, but does not connect it to the literal Euler source.
8. `[CORPUS]` Critical `H^(1/2)` loss is quantized by escaping Möbius profiles; positive winding
   requires at least one unit of one chiral loss.
9. `[CORPUS]` Fixed-support Quillen normalization cancels the determinant response; rectangular
   Evans Plücker data have no canonical determinant line; bounded dense-core landing is zero.
10. `[CORPUS]` Berry holonomy does not determine winding action; closed determinant observation
    can retain open lifted history; periodic phase quotient can hide nonzero integral carry.

### What the shadows mean

The corpus has separately computed the four faces of one stable-map mechanism:

```text
source Hilbert--Schmidt mass  -> Kähler cap energy,
completion escape            -> bubbling at graph-cell boundary,
boundary winding             -> integral bubble charge,
functional equation          -> anti-symplectic real structure.
```

The restricted `S_2` condition was not only a summability threshold.  It is the tangent class of
the restricted Grassmannian.  The cubic trace is not an arbitrary third-order trick.  It is the
odd boundary transgression of the quadratic determinant-line/Schwinger curvature in the bulk.

### Why a curved two-parameter field is forced

Fresh corpus audit closes the naive Paley--Wiener/characteristic-function shortcut.
`HardyPaleyWienerTransport` already gives the exact unitary half-line-to-Hardy transport and
rank-one Cauchy intertwining.  Nevertheless
`not_exists_apertureIntertwiner_primitive_to_strictRight` proves that no linear operator commuting
with aperture translation can carry a primitive Burnol conormal to a strict-right completed Xi
conormal.  The obstruction is not boundedness: it holds for arbitrary linear, radius-nonlocal
maps.

The positive survivor is exact.  If a landing changes a cubic radial rate from `z` to `w`, its
aperture-covariance defect has infinitesimal jet

```text
lim_(c->0) CovarianceDefect(c)/c^2 = 2*(w-z).          (TSBC.C1)
```

This is `tendsto_apertureCovarianceDefect_div_sq`.  It retains the full complex displacement, not
only its norm.  Therefore the missing theta transport cannot be a flat characteristic-function
model.  It must carry a nonzero polar--Gamma connection whose curvature pays exactly this rate
change.

The coordinate-free candidate is a determinant differential character over the formation
quadrant

```text
Q = {(c,x) | c>=0, x>0},                              (TSBC.C2)
```

where `c` is Burnol aperture time and `x` is Gaussian theta heat.  Its restricted-Grassmannian
bundle has:

```text
horizontal edge: graph(S_c A_base),
vertical edge:   Gaussian Euler--continuum completion Phi_x,
mixed curvature: failure of damping and theta completion to commute,
boundary class:  Tr(U_D* P U_D-P)^3.                  (TSBC.C3)
```

The continuum heat term is not optional.  It subtracts the universal non-trace-class metric
anomaly before determinant curvature is integrated.  After subtraction, TSBC asserts that the
remaining curvature current is positive and its total mass is exactly the Burnol graph action.
Thus `(TSBC.1)` is a covariant Stokes law on `Q`, not equality of unrelated source and target
scalars.

## 2. Source cap: closed theorem

`ULF-BGCA-001` proves that, for the literal Burnol synthesis `A_base` and
`K_base=A_base* A_base`,

```text
Gamma_base(z) = graph(z A_base),
E_base = integral_D Gamma_base^* omega_det
       = Tr(K_base(I+K_base)^(-1))
       <= Tr K_base
        = B_base < 1.                                  (TSBC.2)
```

This is already a nonzero, pre-divisor, prime-mixed formation object.  It is not a scalar ghost:
the full graph and `K_base` retain all cross-prime matrix coefficients.  It is not a completion
landing: no Xi projector or zero horizon is its target.

## 3. Required sewing theorem

Let `Gr_res,2` be the **reduced positive** restricted Grassmannian of the additive Hardy
polarization obtained from `ULF-ETRS-001`, and let
`Sigma_det` denote its determinant Schubert divisor.  Let `tau` be the anti-holomorphic,
anti-symplectic involution induced by functional-equation reflection.

`ULF-BGAF-001` strengthens the source input.  Forward Burnol damping gives a canonical monotone
graph path `Gamma_(A_c)` with determinant-line action `E_base(c)` decreasing from `<1` to zero.
Its interval losses are nonnegative, additive, and matrix-complete.  The missing completion map is
therefore not an arbitrary sewing: it must be a **filtered continuation correspondence** from this
one-sided source action to the Hardy/Schubert boundary charge.

`[OPEN CORE]` Construct directly from the Gaussian Euler--continuum current and the matrix-complete
Burnol colligation a family of stable maps

```text
F_(x,D) : (S_(x,D), boundary S_(x,D))
          -> (Gr_res,2, Fix(tau))                     (TSBC.3)
```

with the following five properties.

### TSBC-A — coefficient-native formation

`F_(x,D)` is defined before any Xi zero, divisor list, inner factor, or zero ordinate.  On the
source chart it is `Gamma_base` up to the explicit Gaussian Mellin subordination and universal
continuum anomaly subtraction.  Every finite matrix coefficient agrees with the Burnol
colligation, including distinct-prime entries.

Equivalently, construct the restricted-Grassmannian determinant differential character described
in `(TSBC.C2)`--`(TSBC.C3)`.  Its mixed curvature must reproduce `(TSBC.C1)` on every finite
rate-changing packet and the exact matrix-complete Burnol defect on every horizontal interval.

### TSBC-B — canonical Bott suspension

The boundary loop of the source graph cap is carried by an explicit Bott suspension to the Hardy
projection-pair path `R_D=U_D*PU_D`.  The construction must prove, not assume, that the scalar
rotation `zA_base` is the suspension parameter of the completed boundary phase.

This clause is essential: `Tr mathsf T_D` is a `pi_0` relative index, whereas a Schubert bubble is
a `pi_2` class.  Identifying them without a canonical suspension is type confusion.

### TSBC-C — positive Schubert compactification

Every loss of compactness is a finite stable collection of pseudoholomorphic spheres meeting
`Sigma_det` positively.  If their multiplicities are `m_j`, then

```text
m_j in Nat,
area_det(bubble_j) >= m_j,
sum_j m_j = Tr mathsf T_D.                             (TSBC.4)
```

No signed cancellation is allowed after reflection; the real structure pairs bubbles but retains
their positive determinant-line degree.

### TSBC-D — exact source energy splitting

The sewing obeys

```text
E_base = E_residual(D) + sum_j area_det(bubble_j),
E_residual(D) >= 0.                                   (TSBC.5)
```

The weaker inequality

```text
0 <= Tr mathsf T_D <= E_base                          (TSBC.5')
```

is sufficient for RH, but it must be derived from the matrix-complete surface, not asserted as a
scalar comparison.

Equivalently, using the closed source filtration of `ULF-BGAF-001`, every completed target event
must satisfy the monotone continuation law

```text
Action_target(event) <= Action_base(source interval). (TSBC.5f)
```

This is the proposed arithmetic Floer law.  It is an energy identity for a canonical relation,
not a bounded map between source and completed Hilbert spaces.

### TSBC-E — target identification

The boundary transgression of determinant-line curvature is the same cubic restricted Chern
character already computed by `mathsf T_D`:

```text
SchubertDegree(F_(x,D))
  = Tr(U_D* P U_D-P)^3
  = wind(u_D)
  = enclosed strict-right Xi multiplicity.            (TSBC.6)
```

The final equality may use the existing source-current contour theorem.  The construction of
`F_(x,D)` may not use the divisor it later counts.

Equivalently, with the common determinant framing required by `ULF-DLLA-001`, TSBC-E says

```text
Tr mathsf T_D
  = q(Euler graph filling, theta residual filling).    (TSBC.6d)
```

The common holonomy is insufficient; this equality must identify the lifted deck integer.

## 4. Exact RH closure

Assume TSBC-A--E.  For every admissible strict-right rectangle `D`, `(TSBC.2)`, `(TSBC.4)`, and
`(TSBC.5)` give

```text
0 <= Tr mathsf T_D <= E_base < 1.
```

The trace is an integer, hence zero.  Existing contour conservation says every such rectangle
contains zero Xi zeros.  Exhausting the strict-right half of the critical strip and applying the
functional equation excludes the strict-left half.  Therefore every nontrivial Xi zero lies on
`Re(s)=1/2`.

No amplification, density estimate, supplied zero, or positivity of a zero ledger occurs.  The
integer is killed directly by one pre-divisor bound below one.

## 5. Why this is not the retired landing

The retired `ULF-INHD-001` asked a bounded source operator to retain a completion horizon.  Such a
map vanishes on the dense finite formation core; singular alternatives lose the source norm.

TSBC instead changes topology before completion:

```text
source operator A_base
  -> moving graph surface Gamma_base
  -> determinant-line curvature/area
  -> stable-map compactification
  -> integral boundary transgression.
```

Only a cohomology class and its positive energy are sewn.  No finite source vector is mapped to a
zero projector.  Finite formation is nonzero as a graph cap even though its boundary index is
zero.  A completed index appears as a bubble degree, not as the value of a bounded landing.

## 6. Hostile audit

### Falsifier 1 — arbitrary symplectic sewing

An arbitrary symplectic surface can carry positive and negative charge with no quantized energy
lower bound.  TSBC survives only with a compatible complex structure, pseudoholomorphic bubbles,
and positivity of intersection with `Sigma_det`.

### Falsifier 2 — unsuspended component/bubble identification

Relative index lives in a component group; bubbles live in second homotopy.  The claim is false
unless TSBC-B constructs the Bott suspension from the actual formation loop.  Formal analogy is
not enough.

### Falsifier 3 — scalarization

`E_base<1` alone is another imported budget.  If the proposed sewing sees only `Tr K_base` or the
Fredholm determinant and cannot reproduce every finite cross-prime Gram entry, it is killed by
the matrix-completeness requirement.

### Falsifier 4 — divisor-defined map

If `F_(x,D)` is built from Xi inner factors, its Schubert divisor, or an off-line zero, `(TSBC.6)`
is RH rewritten.  Coefficient-native construction is non-negotiable.

### Falsifier 5 — fixed-support Quillen response

If completion changes only a charge while holding support/subspace fixed, corpus cancellation
removes the Quillen term.  The graph support itself must move and the coupling must be
nonseparable before determinant-line integration.

### Falsifier 6 — rectangular Plücker scalar

If determinant data are taken in the Evans excess target, the exterior power is not a line and a
Gram norm forgets orientation.  Only the canonical determinant bundle over `Gr_res,2` has the
right integral curvature and boundary orientation.

### Falsifier 7 — infinite-dimensional bubbling gap

Finite Grassmannians have unit Schubert area and ordinary Gromov compactness.  The restricted
Grassmannian is noncompact and weakly symplectic.  TSBC needs uniform trace-class tightness that
prevents energy from leaking through infinitely many rank directions without a finite Schubert
bubble.  If such diffuse leakage exists at energy `<1`, the conjecture fails.

### Falsifier 8 — boundary rotation mismatch

The loop `theta -> graph(e^(i theta)A_base)` is canonical but contractible in the big cell.  It
does not automatically encode arithmetic height or the completed Xi phase.  TSBC-B must derive
the correct suspension from Gaussian Mellin/theta formation.  This is presently the sharpest
failure risk.

### Falsifier 9 — flat characteristic-function shortcut

Paley--Wiener transport and a stationary contraction characteristic function cannot be the
completion map.  Exact aperture-intertwining no-gos force nonzero covariance work, with jet
`2*(w-z)`.  Any model whose connection is flat in Burnol time is already falsified.  The
polar--Gamma anomaly must appear as mixed curvature before the determinant-line action is taken.

## 7. External theory audit

- `[LITERATURE]` Restricted Grassmannians provide determinant bundles, the Schwinger cocycle, and
  Kähler/weak symplectic curvature.  Tahiri--Tumpach cover the `S_p`, `1<=p<=2`, orbit geometry.
- `[LITERATURE]` Graph charts model bounded operators as the big cell; recent
  Andruchow--Recht--Varela work makes unbounded closed graphs part of the completion boundary.
- `[LITERATURE]` Positive holomorphic spheres in finite Grassmannians have integral
  determinant-line area, and a nonconstant bubble has area at least one in the normalization used
  here.
- `[LITERATURE]` Standard Gromov compactness supplies stable bubbles in finite-dimensional compact
  targets.  It does not supply the coefficient-native infinite-dimensional sewing or tightness
  required here.
- `[CORPUS-SPECIFIC]` No located source constructs an Euler/Poisson formation surface whose
  determinant-line bubble degree equals Xi contour multiplicity and whose energy is the Burnol
  `<1` budget.

Closest parents explain ingredients, not the arithmetic law.  Novelty is not used as a truth
criterion; it only locates the missing theorem.

## 8. Risky prediction

`[CONJECTURE]` After the canonical Bott suspension is constructed, all three corpus escape models

```text
one Möbius H^(1/2) profile,
one Tate-theta node charge,
one strict-right Xi multiplicity copy
```

represent the same positive generator of the determinant-line Schubert class and cost exactly one
unit.  This can be falsified first on a rank-one finite formation model, before any RH claim.

## 9. Freeze verdict

`SURVIVES PRELIMINARY ATTACK`, Stage 1 only.

Reasons to keep:

1. It uses an unconditional nonzero source object with an exact `<1` energy theorem.
2. It explains, rather than merely combines, the corpus's Möbius bubbles, Tate charge escape,
   anti-symplectic FE law, Schubert counts, and cubic integral trace.
3. It evades bounded landing by transporting a positive geometric current/class, not vectors.
4. It exposes one falsifiable construction problem.

Reason not to advance:

```text
[OPEN CORE] Build TSBC-B--D coefficientwise as a filtration-nonincreasing continuation from the
Burnol graph action to the Hardy/Schubert boundary charge, and prove infinite-rank stable-map
tightness.  No current corpus theorem supplies this correspondence.
```

## 10. Next attack

Do not begin with general infinite-dimensional Gromov compactness.  First solve the finite-rank
rank-one consistency square:

```text
Burnol graph cap
  --Gaussian Mellin/theta suspension--> Hardy projection loop
      |                                      |
determinant-line area                    cubic trace
      |                                      |
unit Schubert intersection  <---------- boundary transgression.
```

Required outputs:

1. explicit finite-rank suspension map using unsquared Euler coefficients;
2. exact equality between its determinant-line boundary holonomy and cubic projection trace;
3. cross-prime two-column test showing nonseparable Gram terms survive;
4. uniform trace-class estimate allowing rank limit without diffuse energy loss.
5. monotone continuation identity showing target action cannot exceed the exact Burnol interval
   action.

Failure of any item retires TSBC and leaves `ULF-BGCA-001` as the strongest positive survivor.

## Log

- 2026-09-03 — corpus audit, graph-cap theorem, literature boundary, and hostile audit completed;
  conjecture frozen at the Bott-suspended coefficient-native sewing.
