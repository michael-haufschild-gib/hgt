# Completed source Green primitive for reflected-Gaussian horizon

- **ID:** `deninger-meyer-reflected-gaussian-completed-source-green`
- **Stage:** 3-formalized
- **Type:** SOURCE COMPLETION / UNITARY GREEN EXTENSION / EXPLICIT PRIMITIVE
- **Status:** `[LOCAL-RESEARCH] [PAPER PROOF COMPLETE] [LEAN-PROVED]`
- **Parent:** `../1-in-progress/deninger-meyer-gaussian-green-resolvent.md`
- **Predecessor:** `deninger-meyer-reflected-gaussian-green-range-wall.md`
- **Lean module:**
  `../../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianCompletedSourceGreen.lean`

## 1. Frontier closed

The range-wall theorem proves that the reflected-Gaussian admitted residue is a limit of current
compact-source Green vectors but is not itself one: current compact source contains only finite Xi
jets.  The source Gelfand triple supplies a canonical nonlocal Hilbert middle

```text
H_source,2 = ell^2(multiplicity-exact Xi jets),
```

with dense finite source jets.  This result constructs the unique continuous extension of finite
oriented Green reflection to `H_source,2` and gives the admitted residue an explicit source
primitive there.

## 2. Completed source Green operator

For `a in H_source,2`, define

```text
(Ghat a)(q) = epsilon(q) a(Rq),
```

where `R` is functional-equation reflection and `epsilon(q)` is the existing odd orientation.
Equivalently,

```text
Ghat(a) = -J(star(a)),
```

the composition of Riesz conjugation with odd Hodge reflection.  Both constituent maps are
conjugate-linear isometries, so `Ghat` is complex-linear and isometric.  The orientation identities
give

```text
Ghat^2 = -1.                                                     (1)
```

Hence `Ghat` is surjective, with inverse `-Ghat`.

On every finite source jet `a`, coefficient calculation gives

```text
Ghat(a) = J_finite(a).                                          (2)
```

Because finite jets are dense, (2) uniquely determines `Ghat` among continuous linear maps.  If
`ell` is a class in current compact-support dual, its Hilbert source coordinate is the conjugate of
its Riesz representative, and

```text
Ghat(star(Riesz(ell))) = G_c(ell).                              (3)
```

Thus this is an actual extension of the existing comparison-model source Green map, not an
unrelated automorphism of another Hilbert copy.

## 3. Explicit reflected-Gaussian primitive

Let `h_ref` denote the admitted reflected-Gaussian residue vector.  Define

```text
u_ref = -Ghat(h_ref).
```

Equation (1) gives

```text
Ghat(u_ref) = h_ref.                                             (4)
```

Coefficientwise, reflection invariance of `h_ref` gives the explicit source formula

```text
u_ref(q) = -epsilon(q) h_ref(q).                                 (5)
```

Every coefficient is nonzero.  Isometry makes the primitive in (4) unique.  Applying completed
Calderon--Witt incidence and then resolved Hellinger--Gamma provenance sends (4) exactly to the
previously constructed admitted incidence and resolved class.

## 4. Hostile audit

### Renaming the target carrier

Rejected.  Source Hilbert middle, dense finite-test embedding, compact Riesz embedding, and finite
Green action predate this result.  Equations (2), (3), and uniqueness prove that `Ghat` is the
forced continuous extension of source transport.

### Claiming a global arithmetic Green complex

Rejected.  This is still the canonical Xi-jet comparison model supplied by the source Gelfand
triple.  It closes completion and primitive existence inside that model.  It does not construct an
independent global arithmetic complex or identify its range with prime-normal source geometry.

### Claiming RH

Rejected.  Surjectivity of `Ghat` makes every completed vector a Green output and therefore cannot
force the RH-bearing resolved defect to vanish.  New arithmetic input must identify a smaller
compatible source range and prove Hermitian domination there.

## 5. New scientific content and remaining frontier

The earlier operator-range question now splits cleanly:

```text
compact source range membership: false;
canonical Hilbert-completed source primitive: constructed uniquely;
arithmetic compatible-range membership: open.
```

Therefore neither more Green completion nor another choice of primitive can move Route L.  Exact
remaining theorem is a source--divisor intertwiner identifying the compatible part of this
completed resolved range with the independently closed adaptive prime-normal range, followed by
Hermitian Gram domination.  This is where ordinary-prime arithmetic must enter.

## 6. Lean certificate

Headline declarations:

- `deningerArithmeticSourceJetHilbertEquivCompleted`
- `deningerArithmeticSourceJetTestToCompleted_dense`
- `deningerArithmeticCompletedSourceGreenIsometry`
- `deningerArithmeticCompletedSourceGreen_apply`
- `deningerArithmeticCompletedSourceGreen_sq`
- `deningerArithmeticCompletedSourceGreen_surjective`
- `deningerArithmeticCompletedSourceGreen_finite`
- `deningerArithmeticCompletedSourceGreen_unique`
- `deningerArithmeticCompletedSourceGreen_extends_compact`
- `reflectedGaussianHorizonCompletedGreenPrimitive`
- `reflectedGaussianHorizonCompletedGreenPrimitive_green`
- `deningerArithmeticCompletedSourceGreen_eq_admittedResidue_iff`
- `reflectedGaussianHorizonCompletedGreenPrimitive_incidence`
- `reflectedGaussianHorizonCompletedGreenPrimitive_resolved`

All statements are unconditional.

## Log

- 2026-08-03 -- Constructed isometric completed source Green extension and proved odd square,
  surjectivity, finite compatibility, compact compatibility, and uniqueness.
- 2026-08-03 -- Constructed unique reflected-Gaussian completed source primitive and transported it
  to actual incidence and resolved provenance.
