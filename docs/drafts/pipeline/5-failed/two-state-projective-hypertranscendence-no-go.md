# Failed route: applying the regular quantum classification directly to physical braid scattering

- **ID:** `two-state-projective-hypertranscendence-no-go`
- **Stage:** 5-failed
- **Type:** FAILED PHYSICAL INFERENCE / QUANTUM--BRAID CONVENTION ERROR
- **Scientific status:** `[PHYSICAL CONSEQUENCE FALSIFIED BY EXISTING TWO-SPECIES PROJECTIVE-HT LOCAL QFT]`
  `[POSITIVE RESIDUE: NONREGULAR SCALAR-IDENTITY QUANTUM SLICE IS THE EXACT OPEN SURFACE]`
- **Parents:**
  - `../2-fully-proven/needs-audit/projective-wigner-smith-nonabelian-ht-separation.md`
  - `../2-fully-proven/not_new_scientific_knowledge/06-integrable-qft-yang-baxter/diagonal-projective-ht-local-qft.md`
- **Failed inference:** A proposed classification corollary says that every analytic regular
  difference-form `4 x 4` **quantum** Yang--Baxter family has differentially algebraic projective
  field.  The failed step inferred from this that an operator-algebraic factorizing two-state
  S-matrix can be HT only in a common scalar factor, and hence that projective HT requires at least
  three one-particle states.  The quantum classification corollary is not falsified here; its use as
  a theorem about the adjacent-braid scattering convention is.

## Exact failure

The complete classification theorem concerns a quantum Yang--Baxter matrix `R`, satisfying the
`R_12 R_13 R_23` convention.  The operator-algebraic diagonal-QFT construction used here is in the
adjacent braid convention.  The conversion is

```text
R(theta)=P S(theta),                                          (0)
```

not `R=-S`.

For the already proved physical two-species control,

```text
S(theta)=P diag(h(theta),-1,-1,-1),
S(0)=-P,
R(theta)=diag(h(theta),-1,-1,-1),
R(0)=-I,                                                      (0a)
```

where `h` is HT.  Thus the adjacent braid family is regular at `-P`, but its quantum conversion
is **nonregular** with scalar-identity anchor `-I`.  It has projective differential-transcendence
degree one and reconstructs a compact-local asymptotically complete QFT.  This is a direct
counterexample to the claimed physical consequence, not to a statement confined to regular
quantum `R`-matrices.

The regular classification of quantum matrices with `R(0)=P` says nothing about `(0a)`.  The
invalid step below was the assertion that multiplying the physical braid matrix by `-1` placed it
in that regular quantum class.  A scalar sign does not convert the Yang--Baxter convention; the
tensor flip does.

The positive residue is exact.  The live two-state question is the positive-unitary,
Lorentz-difference, crossing-symmetric part of the **nonregular quantum scalar-identity slice**.
The diagonal projective-HT control lies in that slice.  What remains open is whether intrinsic
mixing can coexist with those physical conditions there.

## Invalid route, isolated

Let `K=C(theta)` with `D=d/dtheta`, and define the scalar-gauge-invariant projective field of a
matrix family `S` by adjoining all nonzero entry ratios to `K`.  The attempted proof set

```text
R=-S,
```

and then applied the classification of regular quantum-Yang--Baxter solutions with `R(0)=P`.
This is invalid before any differential-algebraic argument begins: a scalar sign preserves the
equation already satisfied by `S`; it does not change the adjacent braid equation into the
quantum `R_12 R_13 R_23` equation.  The required conversion is `R=P S`.

The subsequent inspection of the regular difference-form representatives was therefore an audit
of the wrong classification stratum.  Its rational, exponential, trigonometric, and elliptic
representatives may indeed be projectively DA, but that fact cannot imply a no-go for physical
two-species braid scattering.

## Direct falsifier of the physical inference

The diagonal two-species control displayed in `(0a)` has a nonconstant HT entry ratio.  Its
projective differential field therefore has positive differential-transcendence degree, while the
model satisfies the adjacent-convention two-species factorizing-scattering hypotheses and has a
rigorous compact-local QFT reconstruction.  Hence both of the following physical claims are false:

```text
all physical two-state projective scattering is DA;
projective HT physical scattering requires at least three one-particle states.
```

No weakened wording about “regularity” repairs the intended physical conclusion unless the
Yang--Baxter convention, regularity convention, and the `P` conversion are stated explicitly.  The
separate regular-quantum projective-DA corollary remains a classification audit, not a result of this
failed card.

## Positive residue

Multiplying the correct conversion by a harmless scalar gives

```text
R_tilde(theta)=-P S(theta),
R_tilde(0)=I.                                                  (1)
```

Thus the relevant complete-classification surface is the analytic nonregular quantum family with
scalar-identity anchor, further intersected with:

1. Lorentz difference form;
2. positive-metric unitarity and Hermitian analyticity;
3. crossing symmetry;
4. one constant one-particle basis as the admissible physical gauge.

The diagonal HT model survives this intersection, so projective HT itself is not excluded.  The
strictly narrower open question is whether the same intersection admits **intrinsic mixing**:
failure of simultaneous diagonalisation of `P S(theta)` by one constant product basis.

Parameter-dependent local similarities are a critical unresolved point.  They are valid
classification equivalences in parts of the Yang--Baxter literature, but they are not automatically
physical basis changes; their derivative produces a noncentral connection and can manufacture
apparent projective complexity.  Any new no-go must control this explicitly.

## Anti-theatre and novelty verdict

- The proposed physical no-go and the minimum-three-state consequence are withdrawn, not “almost
  proved.”
- The regular `4 x 4` classification remains parent mathematics and cannot be advertised as an HGT
  result.
- The exact scalar-identity nonregular slice is a useful search reduction, not yet a theorem.
- The surviving intrinsic-mixing question must be checked against the complete 2026 nonregular
  classification before it is promoted to a conjecture.
- No Lean theorem is justified from this failed route.

## Primary literature

- M. de Leeuw, A. Pribytok, and P. Ryan, *Classifying integrable spin-1/2 chains with nearest
  neighbour interactions*, <https://arxiv.org/abs/1904.12005>.
- L. Corcoran and M. de Leeuw, *All regular `4 x 4` solutions of the Yang--Baxter equation*,
  <https://arxiv.org/abs/2306.10423>.
- M. de Leeuw and V. Posch, *Solving the `4 x 4` quantum Yang--Baxter equation*,
  <https://arxiv.org/abs/2411.18685>.
- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.

## Gates

- [x] direct corpus counterexample identified
- [x] quantum versus adjacent-braid convention error isolated
- [x] false no-go and minimum-state consequence withdrawn
- [x] correct scalar-identity nonregular quantum surface identified
- [ ] complete 2026 nonregular classification audited on that surface
- [ ] difference form, unitarity, crossing, and admissible-gauge intersection classified
- [ ] surviving intrinsic-mixing statement proved or falsified
