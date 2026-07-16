# Finite geometric CDD constraint and crossing laws

- **ID:** `finite-geometric-cdd-constraint`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / FACTORIZING-QFT ALGEBRAIC CORE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/GeometricCDDConstraint.lean`
- **Parent program:**
  `../../1-in-progress/geometric-cdd-hypertranscendental-local-qft.md`
- **Statement:** Finite truncations of the geometric CDD product satisfy the exact scale
  constraint, divisor-avoiding inversion, rapidity unitarity, and crossing-period inversion.

## Exact theorem

For a field `K`, define

```text
B_k(q,t) = ((1-q^k t)/(1+q^k t))^2,
P_N(q,t) = product_(0<=k<N) B_k(q,t).
```

Lean proves

```text
B_(k+1)(q,t) = B_k(q,qt),
P_(N+1)(q,t) = B_0(q,t) P_N(q,qt).                         (1)
```

Away from the finite zero and pole divisor it also proves

```text
B_k(q,-t) B_k(q,t) = 1,
P_N(q,-t) P_N(q,t) = 1.                                   (2)
```

For the physical crossing coordinate

```text
t_C(theta) = -i sinh(theta)/C,
```

the module proves

```text
t_C(-theta) = -t_C(theta),
t_C(theta+i pi) = -t_C(theta),                             (3)
```

and transports `(2)` to finite rapidity unitarity and crossing-period inversion.

On the real rapidity axis, Lean defines the unwrapped finite scattering phase

```text
delta_N(theta)=pi+4 sum_(0<=k<N) arctan(q^k sinh(theta)/C)    (4)
```

and proves its exact derivative

```text
delta_N'(theta)=
  4 sum_(0<=k<N)
    (q^k cosh(theta)/C)/(1+(q^k sinh(theta)/C)^2).           (5)
```

For `q>0`, `C>0`, and `N>0`, `(5)` is strictly positive.  Thus every nonempty finite
approximation already has a monotone real-axis phase reporter; this is not inferred from a plot or
numerical sample.

## Exact boundary

This is the finite algebraic core.  It does not claim convergence of the infinite product,
uniform boundedness on an enlarged strip, hypertranscendence, modular nuclearity, construction of
local observables, or asymptotic completeness.  Those analytic and QFT interfaces are stated and
audited separately in the parent program card.

The finite identities are standard CDD-product algebra.  Their value is to prevent the physical
candidate from resting on informal sign and crossing manipulations; they are not new scientific
knowledge.

## Lean surface

- `geometricCDDStep`
- `geometricCDDTruncation`
- `geometricCDDStep_succ_eq_scale`
- `geometricCDDTruncation_succ_constraint`
- `geometricCDDStep_neg_mul`
- `geometricCDDTruncation_neg_mul`
- `geometricCDDCrossingCoordinate`
- `geometricCDDCrossingCoordinate_neg`
- `geometricCDDCrossingCoordinate_add_pi_mul_I`
- `geometricCDDTruncation_rapidity_neg_mul`
- `geometricCDDTruncation_rapidity_crossing_mul`
- `geometricCDDTruncationPhase`
- `geometricCDDTruncationPhaseSlope`
- `hasDerivAt_geometricCDDTruncationPhase`
- `geometricCDDTruncationPhaseSlope_pos`
- `deriv_geometricCDDTruncationPhase_pos`

## Verification

- [x] direct touched-file Lean check passed
- [x] exact cached module build passed in one foreground process
- [x] axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [x] no numerical computation used
- [x] imported by the HTGeometry umbrella
