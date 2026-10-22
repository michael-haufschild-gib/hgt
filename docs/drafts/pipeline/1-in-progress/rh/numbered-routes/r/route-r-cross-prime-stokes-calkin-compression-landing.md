# Route R cross-prime Stokes curvature Calkin/compression landing

- **ID:** `route-r-cross-prime-stokes-calkin-compression-landing`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / FIXED OPERATOR LANDING
- **Parent:** `route-r-cross-prime-stokes-homotopy-curvature-polarization.md`
- **Status:** `[PAPER-PROVED] [PRE-QUOTIENT SOURCE LIFT PROVED]
  [CORONA/BOUNDED DESCENT IMPOSSIBLE] [LEAN-PROVED RECEIVER AND FIXED-ATOM NO-GO]
  [COMPACTNESS OPEN] [NOT RH]`
- **Statement:** The forward/reflected two-prime Stokes curvature has a canonical landing as the
  orientation commutator of the fixed Sonin-compressed Euler source.  Its Calkin distance is
  bounded below by the exact degree-six physical polar energy, so compactness of this one explicit
  operator annihilates the Route R carrier.

## Goal

Remove the operator-choice ambiguity left after the scalar curvature theorem.  The receiver must
be the existing archimedean Sonin projection and the literal prime Euler multipliers, not a
rank-one operator manufactured from the desired scalar after specialization.  The construction
must retain the ordered primes `2,3`, both Gamma orientations, and the exact physical modular
square.

## Construction

Let `a` be a free real modular grade.  Write

```text
Omega(a) = Omega_23(a),
Delta(a) = Omega(a) - Omega(-a),
u_a      = (Omega(a), Omega(-a)) : Fin 2 -> C,
p        = (2,3) : Fin 2 -> Nat.
```

The continuous formula from the parent card defines both entries at `a=0`; no division by a
vanishing character defect remains.  Let `P_A` be the fixed Sonin boundary-carrier projection at
any aperture `A>0`, and let

```text
M_u = finiteArchimedeanEulerSource p u,
M_1 = finiteArchimedeanEulerSource p 1.
```

Define the fixed compressed-curvature operator

```text
C_A(a) = (P_A M_u P_A)(P_A M_1 P_A)
           - (P_A M_1 P_A)(P_A M_u P_A).
```

The precompression multipliers commute.  The existing constraint-orientation identity therefore
gives

```text
C_A(a) = -finiteArchimedeanEulerOrientationGram A p u_a.       (1)
```

Thus this is not an arbitrary realization: it is the commutator created by the fixed physical
Sonin constraint from the two source curvature orientations.

## Exact Calkin theorem

Let `w=(1/2,1/3)` be the reciprocal-prime weight.  The rescaling which transports the literal
Euler Gram to the even Sonin dilation model sends its orientation matrix to

```text
A_ij = sqrt(w_i*w_j) * (u_a(i)-u_a(j)).                        (2)
```

This is exactly `finiteWeightedDifferenceMatrix w u_a`.  Since there are two indices,

```text
finiteWeightedDifferenceEnergy w u_a
  = 2*(1/2)*(1/3)*|Omega(a)-Omega(-a)|^2
  = |Delta(a)|^2/3.                                           (3)
```

Unitary transport preserves operator norm and compactness.  Applying the corpus theorem
`sqrt_half_finitePrimeDifferenceEnergy_le_norm_primeGram_sub_compact` to `(2)` gives, for every
compact operator `K`,

```text
|Delta(a)|/sqrt(6) <= ||C_A(a)-K||.                            (4)
```

Equivalently,

```text
essentialNorm(C_A(a)) >= |Delta(a)|/sqrt(6).                   (5)
```

The parent scalar theorem proves

```text
Delta(a)^2 = 36*g_23(a)^2*M_6(a),
M_6(a) = -Phi_a(B_6)*Phi_(-a)(B_6) >= 0,
g_23(a) > 0.                                                   (6)
```

Combining `(5)` and `(6)` yields the quantitative fixed-compression landing

```text
essentialNorm(C_A(a))^2 >= 6*g_23(a)^2*M_6(a).                 (7)
```

The existing finite-prime Calkin injectivity theorem supplies the sharp zero classification:

```text
C_A(a) is compact
  <-> u_a(0)=u_a(1)
  <-> Delta(a)=0
  <-> a=0
  <-> M_6(a)=0.                                                (8)
```

At `a=0`, `M_u` is a scalar multiple of `M_1`, so the commutator is literally zero, not merely
compact.

## Proof audit

1. Equation `(1)` is `finiteArchimedeanEulerOrientationGram_eq_neg_compression_commutator` with
   the fixed packet `(2,3)`.
2. `finiteEulerGramRescale` multiplies entry `(i,j)` by
   `1/sqrt(p_i*p_j)`, exactly the reciprocal-prime square-root weight in `(2)`; its two minus
   signs cancel.
3. Only the two off-diagonal terms survive in the ordered energy sum, proving `(3)`.
4. The general Calkin lower bound gives `(4)` on the even model; unitary push and negation carry it
   to `C_A(a)`.
5. Equations `(6)` are the parent Stokes-curvature polar identity.  Squaring `(4)` gives `(7)`.
6. `finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff` reduces compactness
   to equality of the two coefficients.  Parent positivity of `g_23` then gives `(8)`.

No Xi zero, critical-line placement, RH, source-dagger identity, same-fibre norm identity,
physical cyclic descent, or assumed compactness is used.

## Conjecture / proof-or-failure loop

### C1 -- represent the scalar by an arbitrary rank-one operator

`[REJECTED]`.  This would manufacture an operator from the desired answer and would not land on
the fixed physical compression.

### C2 -- use the two oriented Stokes curvatures as coefficients of the literal Euler source

`[PROVED]`.  Compression of the commuting source pair creates exactly the orientation Gram `(1)`.
No operator parameter remains after choosing the already fixed aperture.

### C3 -- ordinary or extended cyclic trace annihilates the commutator and therefore its energy

`[FALSIFIED]`.  Linear trace is blind to the zero-diagonal orientation matrix even when the
operator is noncompact.  The physical datum lives in Calkin distance or a positive quadratic/
absolute-value functional, not in the signed linear trace of the commutator.

### C4 -- source Stokes flatness makes `C_A(a)` compact

`[OPEN, RH-BEARING]`.  Local Stokes exactness concerns the uncompressed relative differential.
The fixed Sonin projection creates the noncompact cross-boundary Gram.  Proving compactness now
requires a genuine multi-place Poisson/compression theorem; by `(8)` it cannot be obtained from
the grade-parametric Stokes identities alone.

## Frontier effect

The operator-lift burden is no longer “find a positive operator realizing the scalar anomaly.”
The operator is explicit and fixed, and its Calkin class quantitatively dominates the physical
degree-six polar square.  Remaining Route R theorem is the single source statement

```text
for every Xi divisor rho and one/every A>0,
  IsCompactOperator (C_A(2*Re(rho)-1)).                        (9)
```

Together with `(8)`, `(9)` closes the existing unconditional RH endpoint.  This card does not
assert `(9)`.

The literal arithmetic comparison has now been classified.  The actual finite Calderon--Witt
cross-prime source span maps coefficient-faithfully to this Calkin class before quotienting, but
the comparison cannot factor through the singular corona: that quotient kills every finite
source atom, including `(2,3)`, while the Calkin image is nonzero off-neutral.  Density also rules
out every continuous Hausdorff descent, and infinite Calkin injectivity rules out cancellation by
an operator-norm summable all-prime tail.  Hence existing source exactness cannot prove `(9)`.
Full proof: `route-r-cross-prime-stokes-calkin-prequotient-comparison.md`.

## Lean realization

`RHTower/RouteRCrossPrimeStokesCalkinPolarHandoff.lean` now supplies the regularized scalar
curvature, its exact odd normal form, degree-six BV--Green modular-square identity, literal
`Fin 2` packet, fixed Sonin commutator, exact compactness classification, quantitative essential
norm lower bound, and global-compactness/RH equivalence.  The fixed arithmetic-atom lift and its
singular-corona no-factorization are formalized in
`RHTower/RouteRCrossPrimeStokesCalkinPrequotientNoGo.lean`.

The realization reuses:

- `SemilocalCompressedEulerOrientation` for `(1)` and compactness classification;
- `SoninPrimeGramCompression` for `(3)`--`(5)`;
- `SoninEulerFiniteGramLower` for rescaling and unitary transport;
- the parent scalar-curvature module for `(6)`.

Remaining Lean content is not receiver construction.  It is an independent theorem proving
compactness from a genuinely renormalized, non-corona, non-norm-summable multi-place source law.

Topology and tightness are now classified completely. Every bounded operator, including the
nonneutral receiver, is a pointwise strong limit of explicit compact Hilbert-basis truncations.
For an arbitrary operator topology, compact approximation can imply compactness only when the
compact ideal is closed; therefore no topology alone can both approximate the nonneutral receiver
and preserve the desired conclusion. The exact positive survivor is compact escape: the canonical
truncations' unit-ball images escape every common compact subset at every nonzero grade, while a
common compact envelope exists exactly at grade zero. Hence no hidden strong/weak/intermediate
topology or collective-tightness argument remains. C4 must prove physical compactness directly
from divisor-sensitive source structure.

## Log

- 2026-08-11 -- C1 rejected; C2 fixed-compression landing and quantitative Calkin bound proved;
  C3 linear-trace shortcut falsified; C4 isolated as sole RH-bearing compactness producer.
- 2026-08-11 -- pre-quotient arithmetic lift proved; singular-corona, bounded-completion, and
  norm-summable-tail descents dependency-closed impossible.  Compactness must come from a new
  cutoff-dependent/unbounded multi-place Poisson self-product law.
- 2026-08-13 -- Explicit polar receiver, essential-norm bound, compactness/RH equivalence, literal
  `(2,3)` arithmetic lift, and exact/mod-compact singular-corona no-factorization formalized;
  targeted builds and axiom audits green.
- 2026-08-13 -- `RouteRNormConvergentCalkinCoefficientRigidity.lean` removes absolute summability
  from the all-prime no-cancellation theorem: every coherent rectangular exhaustion with compact
  operator-norm limit has zero coefficient matrix.  Any surviving producer must use a genuinely
  non-operator-norm-convergent renormalization.
- 2026-08-13 -- arbitrary operator topology and collective compactness classified in
  `RouteROperatorTopologyCompactnessDichotomy.lean` and
  `RouteRStrongApproximationCompactEscape.lean`.  Nonneutral canonical truncations escape every
  common compact unit-ball envelope; targeted builds and axiom audits green.
