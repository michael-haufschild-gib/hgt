# Route A source-derived trace-Hankel final verdict

- **ID:** `route-a-source-trace-hankel-final-verdict`
- **Stage:** 3-formalized / not-new
- **Type:** ROUTE VERDICT (paper synthesis), `[BRIDGE]`
- **Statement:** Route A is closed as an independent RH mechanism.  The prime--archimedean source
  trace and the Xi trace-Hankel target are exactly identified, but every surviving way of extracting
  the sign from the current source data is either locally/topologically blind, horizontally blind
  in the only nonzero coefficient corona, nonquantized as a singular graph defect, or the full Xi
  divisor followed by an RH-equivalent positivity test.  Reopening Route A requires a genuinely new
  source object, not another representation of the existing trace or divisor.

## What is and is not being closed

This verdict does not prove or disprove RH.  It does not assert that a positive decomposition of the
Xi trace-Hankel form is logically impossible: if RH holds, the zero-side atomic Gram decomposition
exists.

The closed object is the current proposed route:

```text
continued Euler--Gamma source trace
  -> source-side reformulation or corona incidence
  -> manifest trace-Hankel positivity.                  (1)
```

The first arrow has already been made exact.  The route supplied no independent mechanism for the
second arrow, and the complete audit below proves that every mechanism currently supported by the
source, coefficient-tail, corona, and residue-graph interfaces collapses to a no-go or to the target
itself.

## Gates

- [x] exact target: central trace-Hankel positivity is equivalent to RH in Lean
- [x] exact source: the continued prime--archimedean trace equals the Xi relative resolvent in Lean
- [x] exact moment bridge: reciprocal-square moments and the finite Hankel expansion are in Lean
- [x] local-germ route attacked through the complete FE-odd critical-centre germ space
- [x] joint weighted coefficient/germ route attacked through `M_0`
- [x] complete nonlinear Euler-ray corona reduced to grade one
- [x] finite algebraic and norm-holomorphic corona constructions classified
- [x] singular linear corona--residue incidence classified
- [x] higher-dimensional singular refinement reduced to divisor reconstruction
- [x] final noncircularity audit completed
- [x] critical-centre FE--Schwarz completeness, nonlinear Euler-unit orbit density, the one-point
  continuous quotient, normalized trace-moment inversion, and analytic Hankel-cone instability are
  now formalized unconditionally in Lean; this strengthens the negative route verdict but does not
  itself prove RH
- [x] closed synthesis capstone `routeASourceTraceHankelFinalVerdict_unconditional` packages exact
  source/target, moment, density, quotient, corona, and singular-residue conclusions without
  assuming RH or any route premise

## Lean formalization

Fully formalized in
`GaloisForLFunctions.RHTower.RouteASourceTraceHankelFinalVerdict`.

`RouteASourceTraceHankelFinalVerdictPackage` states the literal theorem interfaces used by this
verdict: continued prime--archimedean source equals Xi relative resolvent on its natural domain;
trace-Hankel positivity is equivalent to RH; reciprocal-square and finite Hankel moment identities;
normalized trace inversion; nonlinear cofinite Euler-orbit completeness; one-point continuous
quotient collapse; compact-open Hankel-cone instability; higher Euler-grade vanishing; finite
FE--Schwarz algebraic corona blindness; scalar residue-graph fibre dichotomy; and exact residue
closability criteria.  The no-argument theorem
`routeASourceTraceHankelFinalVerdict_unconditional` constructs the entire package from existing
kernel-checked results.

Verification on 2026-08-23:

- `lake env lean GaloisForLFunctions/RHTower/RouteASourceTraceHankelFinalVerdict.lean` passed;
- targeted `lake build GaloisForLFunctions.RHTower.RouteASourceTraceHankelFinalVerdict` passed;
- `#print axioms RHTower.routeASourceTraceHankelFinalVerdict_unconditional` reported only
  `propext`, `Classical.choice`, and `Quot.sound`;
- module is imported by `GaloisForLFunctions.RHTower`.

## 1. Exact source and exact target

The Lean tree proves:

```text
continuedPrimeArchSourceRelativeTrace
  = xiRelativeResolventTrace,                            (2)

XiCentralTraceHankelNonnegative
  <-> RiemannHypothesis.                                 (3)
```

Pairing the relative resolvent under the functional equation gives

```text
-xiRelativeResolventTrace(z)/z
  = sum_(n>=0) M_n z^(2n),                               (4)
```

where `M_n` is the centred reciprocal-square moment with exact divisor multiplicity.  For every
real polynomial `p`, the trace-Hankel form is the finite square-coefficient pairing against this
moment sequence.

Thus “construct the source moments” is complete.  The only missing statement was their all-order
Hankel positivity, which is exactly (3).

## 2. Local and complete-jet mechanisms are closed

`critical-center-euler-unit-trace-hankel-instability.md` proves on paper that cofinitely many actual
FE-paired Euler-unit tangents are dense in the complete odd holomorphic germ space at `s=1/2`.
After division by the centred coordinate, the finite-unit orbit is dense in the real even
trace-moment germ space.

The all-order Hankel-positive cone in that germ space is closed with empty interior.  Consequently
no compact-open continuous local property of

- the source trace;
- its complete Taylor jet;
- a triangularly equivalent Markov, Pick, Jacobi, continued-fraction, or cumulant coordinate; or
- a continuous local Gram factorization

can be the finite-unit-stable source reason for (3).

This is not a finite-jet objection.  Every Taylor order is retained.

## 3. Weighted coefficient memory through `M_0` is closed

`weighted-euler-tangent-global-graph-decoupling.md` proves that finite Euler tangents are jointly
dense in

```text
M_0 x O(Q_+)_R,                                         (5)
```

where `M_0` is the full logarithmic Marcinkiewicz vanishing-tail layer and the second factor is the
complete FE--Schwarz regular flux on the off-line fundamental quadrant.

At the actual source the affine closure is

```text
(one+M_0) x O(Q_+)_R.                                   (6)
```

Hence retaining the whole weighted vanishing tail jointly with the whole continued strip field
does not create a continuous incidence invariant.

The complete nonlinear prime-power Euler ray does not repair this.  By
`critical-all-grade-euler-corona-grade-one-reduction.md`, all grades `m>=2` lie in the vanishing
layer.  The sole continuous coefficient datum left is

```text
[one] in Q_log=M_log/M_0.                               (7)
```

## 4. Finite algebraic and holomorphic corona mechanisms are closed

`fe-schwarz-prime-corona-horizontal-grade-collapse.md` classifies every finite algebraic expression
in the normalized prime characters of an off-line FE--Schwarz quartet.

If such an expression belongs to `M_log`, its corona class is exactly its horizontal-grade-zero
part.  That part is independent of the displacement `Re rho-1/2`.  In particular,

```text
tau_rho tau_(1-rho) tau_(conj rho) tau_(1-conj rho)=one. (8)
```

Every complete quartet therefore produces the same symmetric multiplicative corona class.

The boundary phase orbit is not an analytic replacement.  For `t!=u`,

```text
||[p^(-it)]-[p^(-iu)]||_(Q_log)=4/pi.                   (9)
```

It is norm-discrete and has no nonconstant norm-continuous or holomorphic parameterization.

Thus finite polynomial/Laurent constructions, multiplicative FE--Schwarz symmetrization, and
norm-holomorphic corona families are horizontally blind.

## 5. Singular linear corona incidence is closed

The canonical residue graph on `M_0` already gives

```text
R_res(tau_z)=-ord_z(zeta).                              (10)
```

For a right-strip point `z`, multiplication by `tau_z` is a bounded map

```text
S_z : M_log -> M_0.                                     (11)
```

Therefore a continuous pairing that descends through `Q_log` annihilates every shifted unit source
and detects no zero.

Using the singular residue graph instead gives the exact bivariate kernel

```text
K_res(z,w)=-ord_(z+w-1/2)(zeta).                        (12)
```

This is the zeta divisor after translation.  Its closability filtration is the ordinary zero-free
half-plane filtration, and its limiting closability statement is RH.

Nonclosability does not supply the proposed integer charge.  The vertical fibre of the closure of
the graph of a scalar linear functional is a complex linear subspace of `C`; it is `{0}` when the
functional is closable and all of `C` otherwise.  A single off-line zero therefore erases residue
magnitude, multiplicity, and count in the graph closure.

The singular linear corona proposal is consequently one of:

```text
continuous and zero;
canonical and exactly divisor evaluation;
nonclosable and nonquantized.                            (13)
```

## 6. Higher-dimensional refinement is the target divisor

One can avoid the scalar vertical-fibre collapse by retaining the whole residue function

```text
z |-> R_res(tau_z)=-ord_z(zeta).                         (14)
```

But (14) is precisely the complete right-half divisor with multiplicity.  The family of translated
values (12), as the base point approaches the critical line, reconstructs the same function.

Thus every higher-dimensional singular refinement strong enough to retain the desired integer
multiplicities has crossed to the target side.  Applying reciprocal-square moments, a Hankel form,
a Herglotz representation, or an off-line count after (14) is one of the existing RH-equivalent
criteria.  It is not a source-derived sign mechanism.

## 7. Candidate moves and terminal attacks

### Completed nonlocal Gram

`[ATTACKED]` A source Gram would prove RH only after its moments are identified with `M_n`.  The
existing positive Sonin residual Gram has a different coefficient law; identifying it with `M_n`
is the whole missing theorem.  A Gram built after (14) is the zero-side atomic Gram and is circular
for Route A.

### Positive Euler weights

`[ATTACKED]` Individual FE-even frequency kernels and atom-displacement tangents fail pointwise
Hankel positivity.  Positive source weights alone cannot force the combination-mode Hankel cone.
At the critical line the literal positive Euler atom sum is not the finite continued source trace;
renormalization and the archimedean correction carry the unresolved sign.

### Corona--divisor charge

`[ATTACKED]` Finite algebra is horizontally blind, continuous descent is zero, the canonical
singular kernel is divisor evaluation, and scalar graph defect is nonquantized.

### Complete source image

`[ATTACKED]` The all-order coefficient and continuation classifier recovers the unique von Mangoldt
source, but the same source occurs at every zeta zero.  Source membership does not select the
critical line.

No candidate leaves a residue that is both source-defined before divisor reconstruction and
stronger than the RH-equivalent positivity target.

## 8. Final verdict

`[ROUTE CLOSED AS AN INDEPENDENT MECHANISM]`

Route A connected the cleanest exact source identity to the cleanest exact RH criterion, but that
connection is now complete and contains no intervening sign principle.  The remaining sentence

```text
the fixed Euler--Gamma source forces trace-Hankel positivity
```

is not a research mechanism; it is RH itself with the exact source coordinate substituted.

This verdict closes Route A in the current RHTower programme.  It may be reopened only by supplying
a genuinely new mathematical object satisfying all of the following:

1. it is constructed from the fixed Euler--Gamma--theta source before reading the Xi divisor;
2. it is not continuous through the compact-open germ or `M_0` product topology;
3. it is not a finite algebraic or norm-holomorphic expression in corona characters;
4. it retains a quantized sign or multiplicity before graph closure;
5. it does not reconstruct the divisor and then apply an RH-equivalent criterion; and
6. its unconditional source law is independently provable and Lean-formalizable.

Introducing such an object would constitute a new route, not unfinished plumbing in Route A.

## Scientific status

This terminal verdict is `[BRIDGE]`, not new scientific knowledge.  It synthesizes one provisional
candidate-new completeness theorem with classical moment, quotient, exponential-polynomial, and
operator-graph arguments.  The scientific contribution produced while closing the route is the
paper theorem `critical-center-euler-unit-trace-hankel-instability.md`; its novelty remains
provisional pending independent expert review.
