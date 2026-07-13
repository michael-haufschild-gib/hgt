# Xi reciprocal-square self-adjointness criterion

- **ID:** `xi-reciprocal-square-selfadjoint-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** top-down whole-corpus RH sweep
- **Statement:** The square of the compact reciprocal Xi divisor operator is self-adjoint if and
  only if RH holds; more sharply, it is enough that its quadratic values be real only on the
  algebraic continued prime--Gamma Cauchy source span.

## Goal

Weaken the terminal Hedenmalm operator condition from self-adjointness of the reciprocal Xi
operator itself to self-adjointness after squaring:

```text
IsSelfAdjoint (R_Xi comp R_Xi)
  -> reciprocal-square Xi coordinates are real
  -> every Xi zero lies on the critical line
  -> RiemannHypothesis.
```

The all-carrier premise admits the source-restricted replacement

```text
quadratic values of R_Xi^2 are real on the algebraic continued-Cauchy source span
  -> the relation extends to each exact divisor fiber by unconditional Cauchy closure
  -> every reciprocal-square Xi coordinate is real
  -> RiemannHypothesis.
```

This is a genuine weakening at the operator interface: a general complex operator can have a
self-adjoint square without being self-adjoint, for example multiplication by `i`, whose square is
`-1`.  For the actual centered Xi divisor, the open-strip geometry removes precisely this square
ambiguity.

## Existing interfaces

- `xiReciprocalOperator_single`: the basis eigenvalue of `R_Xi` is
  `(xiSpectralPoint q)⁻¹`;
- `xiZeroCopyReciprocalSquare_eq`: its square is the centered coordinate
  `-((rho - 1/2)⁻¹)^2`;
- `xiCentralReciprocalSquare_im_eq_zero_iff`: that coordinate is real exactly when the divisor
  point has real part `1/2`;
- `xiSpectralPoint_real_of_rh`: RH makes every centered spectral point real;
- `xiReciprocalOperator_isSelfAdjoint_of_rh`: RH makes `R_Xi` self-adjoint.

## Proof attack

Let `e_q` be the `q`th unit vector.  The diagonal action gives

```text
(R_Xi comp R_Xi) e_q = (xiSpectralPoint q)⁻² e_q.
```

If the square is self-adjoint, symmetry at `(e_q,e_q)` makes this eigenvalue equal to its complex
conjugate.  The existing reciprocal-square identity and exact imaginary-part criterion then force
the underlying Xi divisor point onto the critical line.  Conversely RH makes `R_Xi`
self-adjoint, hence its square self-adjoint.

## Non-circularity and positive source obligation

The operator is indexed by the actual Xi divisor, so this theorem is a terminal bridge, not an
unconditional RH proof.  Its positive content is that an operator construction no longer has to
control the sign/orientation of each reciprocal eigenvalue.  It only has to produce a
source-derived involutive symmetry for the even operator `R_Xi^2`.

A non-circular continuation must prove square self-adjointness from a prime--Gamma, theta, Weil,
or other source constraint without assuming real zeros, Weil positivity, a positive spectral
measure equivalent to RH, or first-order self-adjointness of `R_Xi`.

The formal source-core theorem makes the smallest current obligation more precise.  One need not
prove an all-carrier operator identity: it suffices to prove

```text
inner (R_Xi^2 v) v = inner v (R_Xi^2 v)
```

for finite algebraic packets of continued Cauchy source vectors.  The existing closure theorem
supplies every multiplicity fiber automatically.  What remains open is an exact prime--Gamma value
formula or source symmetry for this reciprocal-square quadratic packet value.  Scalar trace
moments alone cannot provide it: conjugate divisor pairs make those moments real unconditionally,
whereas the packet relation must retain fiberwise orientation.

## Lean theorem surface

The module
`formal/GaloisForLFunctions/RHTower/XiReciprocalSquareSourceCore.lean` proves:

- `xiReciprocalOperator_apply`;
- `xiReciprocalSquareOperator_apply` and
  `xiReciprocalSquareOperator_fiberIndicator`;
- `xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis`;
- `xiZeroCopyReciprocalSquare_star_eq_of_continuedCauchyQuadraticReal`;
- `riemannHypothesis_of_xiReciprocalSquareContinuedCauchyQuadraticReal`;
- `xiReciprocalSquareContinuedCauchyQuadraticReal_iff_riemannHypothesis`.

The formal proof uses the unconditional theorem
`xiWeilFiberIndicatorLp_mem_continuedCauchyHilbertSubspace`; no density axiom, enumeration of zeros,
or RH assumption enters the difficult implication.

## Formal verification

- `lake build GaloisForLFunctions.RHTower.XiReciprocalSquareSourceCore` passes;
- the module contains no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration;
- both RH capstones print only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1 in-progress: exact cross-corpus interfaces and proof attack identified
- [x] 1 -> 2 fully-proven: complete proof with square-ambiguity exclusion
- [x] 2 -> 3 formalized: Lean operator and source-core equivalences
- [ ] 3 -> 4 publication-ready: only if square self-adjointness is obtained source-side
