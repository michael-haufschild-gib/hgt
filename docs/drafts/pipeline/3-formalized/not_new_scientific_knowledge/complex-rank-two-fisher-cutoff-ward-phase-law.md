# Complex rank-two Fisher cutoff Ward phase law

- **ID:** `complex-rank-two-fisher-cutoff-ward-phase-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / GENERAL HT OPERATOR LAW
- **Scientific status:** `[LEAN-FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent card:** `../../2-fully-proven/mobius-fisher-contact-commutator-ward-budget.md`
- **Statement:** The cutoff-commutator energy of the canonical rank-two Fisher connection over a
  complex Hilbert space is controlled by the full truncated Gram matrix, including a nonnegative
  phase defect omitted by the phase-blind real formula.

## Exact theorem

Let `P` be a self-adjoint idempotent, `Q=1-P`, and let `psi,chi` be orthogonal vectors in a complex
Hilbert space.  Define

```text
X=2^(-1/2)(|chi><psi|+|psi><chi|),
a=||P psi||^2,
b=||P chi||^2,
C=||chi||^2,
N=||psi||^2,
c=<P chi,P psi>.
```

Then

```text
||[X,P]||_HS^2
 =(C-b)a+(N-a)b-2 Re(c^2)                              (1)
 =(C-b)a+(N-a)b-2|c|^2+4(Im c)^2.                     (2)
```

Consequently the phase-blind formula

```text
||[X,P]||_HS^2=(C-b)a+(N-a)b-2|c|^2                   (3)
```

holds if and only if `Im c=0`.

## Paper proof `[PAPER-PROVED]`

Put

```text
L=QXP=2^(-1/2)(|Qchi><Ppsi|+|Qpsi><Pchi|).
```

Since `X` is self-adjoint, the opposite corner is `L*`, the two same-direction corners have zero
product, and

```text
||[X,P]||_HS^2=2||L||_HS^2.                            (4)
```

The two diagonal rank-one energies in `L` are `(C-b)a/2` and `(N-a)b/2`.  Rank-one
Hilbert--Schmidt polarization gives the cross pairing

```text
<|Qchi><Ppsi|,|Qpsi><Pchi|>_HS
 =<Qchi,Qpsi><Pchi,Ppsi>.
```

Orthogonality of `psi` and `chi` and the orthogonal decomposition `1=P+Q` imply

```text
<Qchi,Qpsi>=-<Pchi,Ppsi>=-c.
```

Thus the real cross contribution to `2||L||_HS^2` is `-2 Re(c^2)`, proving `(1)`.  Writing
`c=x+iy` gives `Re(c^2)=x^2-y^2=|c|^2-2y^2`, which proves `(2)`.  The difference between `(2)`
and `(3)` is `4(Im c)^2`, so equality in `(3)` holds exactly when `Im c=0`.

## Hostile audit and positive survivor

The inherited complex formula used `-2|c|^2`.  It is false without a real-overlap hypothesis.
For example, in `C^2`, take `P` to be the first-coordinate projection,
`psi=(1,1)/sqrt(2)`, and `chi=(i,-i)/sqrt(2)`.  Then `psi` and `chi` are orthogonal and
`c=-i/2`; the phase-blind right side is zero while `(1)` gives energy one.

- **Exact killing mechanism:** complex rank-one cross polarization produces `Re(c^2)`, not
  `|c|^2`.
- **Strongest positive survivor:** equations `(1)`--`(2)` classify the missing energy as the
  nonnegative orientation defect `4(Im c)^2`.
- **Representation lesson:** the truncated state--tangent Gram entry carries a phase orientation;
  passing to its magnitude before forming the Ward curvature loses a genuine boundary value.
- **Möbius specialization:** the squarefree state, Fisher tangent, and clock cutoff have real
  coordinates, so `Im c=0` is discharged and the original arithmetic profile survives.

## Parent-theory and novelty audit

Projection-commutator Hilbert--Schmidt energy is an instance of skew-information/operator-variance
geometry.  The exact phase decomposition here is elementary rank-two polarization and is treated as
a reusable bridge, not a scientific novelty claim.  Relevant parents include Wigner--Yanase skew
information and later quantum Fisher/covariance decompositions.

## Gates

- [x] exact complex formula
- [x] phase-defect decomposition
- [x] equality classification
- [x] counterexample to the phase-blind overgeneralization
- [x] squarefree real-overlap survivor identified
- [x] exact Lean theorem
- [x] ordinary-axioms audit

## Lean certificate

- `formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtRankOne.lean` proves the reusable
  rank-one Hilbert--Schmidt norm and polarization laws.
- `formal/GaloisForLFunctions/HTGeometry/RankTwoFisherCutoffWard.lean` proves equations `(1)` and
  `(2)`, and proves that the phase-blind formula holds if and only if the cutoff overlap is real.
- `formal/GaloisForLFunctions/HTGeometry/LpCoordinateProjection.lean` supplies unconditional
  coordinate idempotence, self-adjointness, mass, overlap, and real-phase interfaces.
- `formal/GaloisForLFunctions/RHTower/MobiusCriticalFisherCutoffWard.lean` discharges those
  interfaces on the squarefree carrier and identifies the cutoff mass with the existing critical
  clock CDF.
- Targeted module checks and `#print axioms` succeeded.  The theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Complement-reflection and total-energy addendum (2026-07-19)

The generic Lean law now also proves that cutoff complementation exchanges the two boundary
corners, reverses the commutator, and preserves its squared Hilbert--Schmidt energy exactly.  The
same module computes the total pointed-connection energy

```text
||X(psi,chi)||_HS^2
 =||chi||^2 ||psi||^2+Re(<chi,psi>^2),
```

with orthogonal and unit-source specializations.  The squarefree consumer identifies this total
energy with `squarefreeMobiusCriticalProjectiveFisherEnergy` and proves exact equality of the lower-
and complementary-window commutator energies.  These are unconditional value-reflection laws;
they do not supply the open prime--Gamma/Sonin completed graph transport.

## Projector-tangent inertia addendum (2026-07-20)

The pointed connection is exactly the positive normalization of the pure-state projector tangent:

```text
X(psi,chi)=2^(-1/2) T(psi,chi).
```

If `Delta=||psi||^2||chi||^2-|<psi,chi>|^2`, the form matrix of `X` on `(psi,chi)` therefore
satisfies

```text
det G_X = -(1/2) Delta^2.
```

For a complex-linearly independent state--tangent pair, `Delta>0`; hence `G_X` is Hermitian,
nonsingular, and neither it nor its negative is positive semidefinite.  This connects the positive
Hilbert--Schmidt energy law above to its sharp ambient-order negative control: Fisher energy is not
positive-operator order.  The general determinant reflection is formalized in
`HTGeometry/PureStateProjectorTangentInertia.lean`, and the normalized Fisher consumer is in
`HTGeometry/PointedFisherConnectionInertia.lean`.  This remains a `[BRIDGE]` in standard
pure-state quantum geometry.

For the completed squarefree Möbius source, this independence premise is now discharged rather
than exposed to callers.  Positivity of normalized mass on every squarefree coordinate makes the
signed weights at `n=1` and `n=2` nonzero.  A vanishing centered logarithmic tangent would then
force its center to equal both `log 1` and `log 2`, impossible because `log 2>0`.  Together with
the existing unit-source and orthogonality laws, this proves state--tangent independence for every
`sigma>1` and hence the exact mixed signature of the actual arithmetic Fisher compression.  The
source discharge is formalized in `RHTower/MobiusCriticalFisherConnectionInertia.lean` and adds no
RH or positivity hypothesis.
