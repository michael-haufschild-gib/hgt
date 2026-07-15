# Library ticket: Xi narrow-sector Schur norm-gap law

- **Date:** 2026-07-15
- **Owner:** unassigned
- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/xi-radial-jensen-schur-capacity-rigidity.md`
- **Target areas:** `formal/GaloisForLFunctions/HTGeometry`,
  `formal/GaloisForLFunctions/RHTower`
- **Status:** strengthened paper theorem complete; formalization deferred; no build run

## Requested reusable infrastructure

Add an `HTGeometry` theorem for an absolutely summable complex atom family `(u_i)`.  Put

```text
M = sum_i u_i,
A = sum_i |u_i|^2.
```

Assume

```text
M is positive real,
|u_i| <= R < 1,
2*A <= (1-R)*M.
```

For every disk-Schur function `f`, prove

```text
|sum_i u_i*f(u_i)| <= M.
```

The proof should use Schwarz--Pick at `f(0)`.  After a unimodular rotation, write `c=f(0)` and
`t=|c|`; then

```text
|f(z)-c| <= |z|*(1-t^2)/(1-t*|z|)
```

and the balance assumption makes the remainder no larger than `(1-t)*M`.  The constant function
`1` proves equality of the functional norm with `M`.

Do not introduce Montel compactness or a phase-interpolating extremizer.  The strengthened theorem
is pointwise and does not need normal-family passage.

## RHTower specialization

Use the existing declarations

```text
xiZeroCopyReciprocalSquare
summable_xiZeroCopyReciprocalSquare
xiZeroCopy_fortyOne_div_two_lt_im_sq
xiThermalNode_pos
xiThermalOrientationTerm_le_one_over_eightyFour_node_sq
xiCentralPolynomialMoment_eq_sourceMomentFunctional
xiCenteredRadialJensenMass_eq_hermitianMass
xiGlobalReflectionDefectEnergy_eq_mass_sub_source
```

to prove, with `R=2/41`,

```text
diskSchurCapacity normalizedPrimeArchMoment = primeArchCentralCurvature,
xiCenteredRadialJensenMass-diskSchurCapacity normalizedPrimeArchMoment
  = xiGlobalReflectionDefectEnergy/2.
```

The atom estimates needed on paper are

```text
|u_q| <= 2/41,
(84/85)*|u_q| <= Re(u_q),
sum_q |u_q|^2 <= (2/41)*sum_q |u_q|.
```

This specialization should replace the earlier upper-saturation/normal-family ticket.  Do not
mark the Schur capacity as an open source producer: its exact value is already the central source
curvature.

## Operator specialization

Connect the result to

```text
xiReciprocalSquareOperator
traceNorm
opTrace
```

by proving the diagonal identities

```text
Tr(D_Xi) = primeArchCentralCurvature,
traceNorm D_Xi = xiCenteredRadialJensenMass,
Tr(D_Xi * P(D_Xi)) = xiCentralPolynomialMoment P.
```

The desired capstone is

```text
2*(traceNorm D_Xi-analyticFunctionalNorm D_Xi)
  = xiGlobalReflectionDefectEnergy.
```

`xiReciprocalSquareOperator` is already a product of two Hilbert--Schmidt operators, and the trace-
norm library already proves such products are Schatten class one.  The missing reusable work is
the diagonal trace-norm evaluation and the bounded analytic-functional wrapper, not trace-class
existence.

## Boundary-duality follow-up

For

```text
g_Xi(e^(it)) = sum_(n>=0) normalizedPrimeArchMoment(n) e^(-int),
```

identify the exact quotient norm

```text
||[g_Xi]||_(L^1/H^1_0) = primeArchCentralCurvature.
```

Only add this after the Hardy-space predual is proved rather than postulated.

## Finite coefficient follow-up

Formalize the Caratheodory--Fejer prefix capacity

```text
S_N = sup { |sum_(k=0)^N m_k*a_k| : ||T_N(a)||_op <= 1 }
```

and the corrected convergence bound

```text
0 <= S_N-primeArchCentralCurvature
   <= xiCenteredRadialJensenMass*(2/41)^(N+1)/(1-2/41).
```

The finite trace-norm dual optimum converges to central curvature.  Do not retain the superseded
target in which those norms were supposed to converge to radial Jensen mass.

`HTGeometry/BernsteinSzegoReconstruction.lean` supplies moment Toeplitz/OPUC infrastructure, but
its `circleToeplitzGram` is not the lower-triangular analytic coefficient Toeplitz matrix needed
for Caratheodory--Fejer.  Add the latter explicitly.

## Verification constraint

No Lean build, lint, numerical test, or scratch computation was run while producing this paper
theorem, following the active user instruction.  Formalization must be verified later with narrow
file-level checks only.

## Existing formal reuse boundary

Reuse the abstract `absOp`, polar decomposition, trace norm, and Hilbert--Schmidt product
infrastructure.  The present tree does not contain a source theorem identifying
`|xiReciprocalSquareOperator|-Re(xiReciprocalSquareOperator)` with a positive prime--Gamma object.
The continued-Cauchy quadratic-reality files and the thermal reverse-norm files are terminal
RH-equivalent consumers, not providers for this step.  Do not discharge the requested capstone by
importing one of those equivalent hypotheses.
