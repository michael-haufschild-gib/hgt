# Simplex effective harmonic positive parity

- **ID:** `simplex-effective-harmonic-positive-parity`
- **Stage:** 3-formalized
- **Type:** `[FINITE HODGE MODEL]`, `[EFFECTIVITY BOOKKEEPING]`, `[BRIDGE]`
- **Scientific status:** `[PROVED LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/SimplexEffectiveHarmonic.lean`.
- **Parent:**
  `../../1-in-progress/prime-gamma-reflection-decimation-defect-resolvent-rh.md`.
- **Statement:** Removing the augmentation from a finite full-simplex descent complex retains
  exactly one constant degree-zero harmonic class.  Its normalized harmonic projection has trace
  one, is positive semidefinite, and lies in positive grading; the complementary zero-form
  Laplacian has an explicit positive Green operator.

## Exact finite model

For a nonempty finite vertex type of cardinality `n`, let `J` be the all-ones matrix and put

```text
P = n^(-1) J,
L = n I-J,
G = n^(-1)(I-P).                                        (1)
```

Lean proves

```text
P^2=P,       P^*=P,       P>=0,       Tr(P)=1,          (2)
LP=PL=0,     LG=GL=I-P,   L>=0,       G>=0.             (3)
```

The range equation

```text
Px=x  iff  x is a constant section                         (4)
```

identifies the surviving harmonic line intrinsically.  Assigning degree zero positive grading
gives `Gamma P=P` exactly.

## Consequence and firewall

This discharges only a finite bookkeeping question: positive harmonic parity is consistent and
canonical for an unaugmented simplex source-selection block.  It does not identify any
prime--Gamma source complex with this block, does not compare `G` with the centered scale Green
operator, and does not imply positivity of a continued source.  Source-effectivity alone cannot
close RH; the missing input remains an explicit source-produced positive value identity.

## Lean certificate

The wired module proves:

- `simplexEffectiveHarmonicProjection_sq`;
- `simplexEffectiveHarmonicProjection_posSemidef`;
- `trace_simplexEffectiveHarmonicProjection`;
- `simplexEffectiveHarmonicProjection_mulVec_eq_self_iff`;
- `simplexZeroLaplacian_mul_green` and `simplexZeroGreen_mul_laplacian`;
- `simplexZeroLaplacian_posSemidef` and `simplexZeroGreen_posSemidef`;
- `simplexEffectiveHarmonicProjection_positiveParity`.

The module is imported by `formal/GaloisForLFunctions/HTGeometry.lean`.  Its direct check and exact
targeted build pass.  The displayed declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] construct the unique effective harmonic line
- [x] prove positive projection and trace one
- [x] construct the complementary Hodge Green operator
- [x] prove positive grading of the harmonic line
- [x] wire, target-build, and audit axioms
- [ ] identify an actual completed prime--Gamma source-selection complex with this finite model
- [ ] prove a source-produced positive value identity
- [ ] RH
