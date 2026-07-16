# Finite skew-Green trace positivity

- **ID:** `finite-skew-green-trace-positivity`
- **Stage:** 3-formalized
- **Type:** `[CONSTRAINT GEOMETRY]`, `[POSITIVE SOURCE INFRASTRUCTURE]`, `[BRIDGE]`
- **Scientific status:** `[PROVED LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/MatrixTracePowerMoment.lean`;
  `formal/GaloisForLFunctions/HTGeometry/SkewAdjointGreenSquare.lean`;
  `formal/GaloisForLFunctions/RHTower/SeamSuspensionTrace.lean`.
- **Parent:**
  `../1-in-progress/prime-gamma-reflection-decimation-defect-resolvent-rh.md`.
- **Statement:** A finite skew-adjoint constraint with a left inverse canonically produces a
  positive inverse-square Green operator whose shifted trace powers are a reflection-positive
  Hankel sequence.  A finite graded Hodge compression becomes an ordinary trace exactly after a
  positive harmonic-parity identity is supplied.

## Exact finite algebra

Let `C` and `G` be finite complex square matrices with

```text
C^*=-C,   GC=I.                                          (1)
```

Taking adjoints makes `-G^*` a right inverse of `C`.  The mixed inverse identity therefore proves

```text
G^*=-G.                                                   (2)
```

Consequently the Green square

```text
A=G^*G=-G^2                                              (3)
```

is positive semidefinite.  Define

```text
m_A(k)=Re Tr(A^(k+1)).                                    (4)
```

The matrix seminorm induced by `A` makes the power orbit `A^i` a reflected Hankel Gram:

```text
<A^i,A^j>_A = m_A(i+j).                                  (5)
```

Thus, for every real polynomial `p`,

```text
L_(m_A)(p^2)>=0.                                         (6)
```

This proves the finite positivity mechanism required by an inverse centered scale generator.  It
does not construct that generator from a prime--Gamma source and does not compare `(4)` with the
canonical prime--Gamma moments.

## Exact parity firewall

Suppose a finite graded complex has grading `Gamma`, harmonic projection `P`, odd differential
`d`, homotopy `h`, and a commuting observable `R`, with

```text
I-P=dh+hd.                                               (7)
```

The existing Hodge compression gives only

```text
Str_Gamma(R)=Str_Gamma(PR).                              (8)
```

Lean now records the exact positive-sector discharge:

```text
Gamma P=P  ->  Str_Gamma(PR)=Tr(PR).                    (9)
```

Combining `(8)` and `(9)` turns the compressed supertrace into an ordinary trace.  Therefore the
remaining sign problem is not hidden in trace cyclicity or Hodge cancellation.  It is precisely
the source theorem `Gamma P=P` (or an equivalent effectivity statement).

## Consequence for the RH route

The finite algebra forces the following division of labor:

```text
source-built skew centered constraint + positive harmonic parity
  -> positive Green trace-power Hankel packet
  -> source trace comparison with normalized prime--Gamma moments
  -> RH.                                                  (10)
```

Only the first arrow's matrix algebra is closed here.  Assuming an arbitrary positive matrix with
the desired traces would merely restate the positive-moment criterion.  The productive theorem
must construct `C`, `G`, and `P` before reading the target moments.

## Lean certificate

The formal modules prove:

- `matrixTracePowerMoment`;
- `trace_matrixPower_eq_matrixTracePowerMoment`;
- `matrixTracePowerMoment_nonnegative`;
- `matrixGreenSquare`;
- `matrixGreenSquare_posSemidef`;
- `leftInverse_conjTranspose_eq_neg_of_skew`;
- `inverse_matrixGreenSquare_eq_neg_sq`;
- `matrixGreenTracePowerMoment_nonnegative`;
- `gradedMatrixTrace_compression_eq_trace_of_positiveParity`;
- `gradedMatrixTrace_hodgeCompression_eq_trace_of_positiveParity`.

The modules are wired through the HTGeometry umbrella; `SeamSuspensionTrace` is already wired
through RHTower.  Direct checks and exact targeted builds pass.  The displayed declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] positive finite matrix trace-power Hankel theorem formalized
- [x] inverse of a skew-adjoint finite constraint proved skew-adjoint
- [x] positive Green square identified with the negative inverse square
- [x] positive harmonic parity proved sufficient to remove the grading
- [x] modules wired and targeted checks pass
- [x] axiom audit passes
- [ ] construct the finite centered constraint from prime--Gamma source incidence
- [ ] prove source-specific positive harmonic parity
- [ ] compare the resulting trace powers with normalized prime--Gamma moments
- [ ] RH
