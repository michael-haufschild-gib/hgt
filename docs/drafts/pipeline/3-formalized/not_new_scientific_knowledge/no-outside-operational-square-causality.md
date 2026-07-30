# No-outside operational square--causality law

- **ID:** `no-outside-operational-square-causality`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE OPERATIONAL BRIDGE / THEOREM
- **Status:** `[PAPER-PROVED] [LEAN-PROVEN] [REDISCOVERED MATHEMATICS]`
- **Physical parent:** `../../1-in-progress/no-outside-witness-self-unfolding-law.md`
- **Hermitian source parent:** `../../3-formalized/not_new_scientific_knowledge/triangle-source-hermitian-lift.md`
- **Headline:** **The future is what reality can add without subtracting any possibility.**
- **Compressed law:** **Quantum probability and causal time are two readings of the same square.**

## Exact setting

Let
\[
\mathcal E_m=M_{m,2}(\mathbb C),\qquad
\Gamma_m(X)=X^\dagger X\in H_2(\mathbb C)_+.
\]
For positive records \(A,B\in H_2(\mathbb C)_+\), define
\[
A\preceq B
\quad\Longleftrightarrow\quad
B-A\succeq0,
\tag{1}
\]
and for a two-channel witness \(\psi\in\mathbb C^2\) define its unnormalised Born weight
\[
w_A(\psi)=\psi^\dagger A\psi\in\mathbb R_{\ge0}.
\tag{2}
\]
Write
\[
\Phi(t,x,y,z)=
\begin{pmatrix}
t+z&x+iy\\
x-iy&t-z
\end{pmatrix}.
\tag{3}
\]

## Theorem: one square, four operational readings

For all positive records \(A,B\), the following are equivalent:

1. \(A\preceq B\).
2. There is a finite event \(Y\in M_{3,2}(\mathbb C)\) such that
   \[
   B=A+Y^\dagger Y.
   \tag{4}
   \]
3. Every two-channel witness is monotone:
   \[
   w_A(\psi)\le w_B(\psi)\qquad(\psi\in\mathbb C^2).
   \tag{5}
   \]
4. If \(B-A=\Phi(\Delta t,\Delta x,\Delta y,\Delta z)\), then
   \[
   \Delta t\ge0,\qquad
   \Delta t^2-\Delta x^2-\Delta y^2-\Delta z^2\ge0.
   \tag{6}
   \]

Moreover, independent event composition is not an added matrix operation. If
\[
X\in M_{m,2}(\mathbb C),\qquad Y\in M_{n,2}(\mathbb C)
\]
are stacked on the direct-sum left carrier, then
\[
\Gamma_{m+n}(X\boxplus Y)=\Gamma_m(X)+\Gamma_n(Y).
\tag{7}
\]
Thus `(4)` is exactly the public record of adding another independent event.

For the antilinear spin complement
\[
\psi^\perp=(-\overline{\psi_1},\overline{\psi_0}),
\tag{8}
\]
one has
\[
\psi\psi^\dagger+\psi^\perp(\psi^\perp)^\dagger
=\|\psi\|^2I_2.
\tag{9}
\]
Consequently every unit spinor gives a complete binary alternative and
\[
w_A(\psi)+w_A(\psi^\perp)=\operatorname{tr}A.
\tag{10}
\]
If \(\operatorname{tr}A=1\), the two nonnegative weights in `(10)` are probabilities summing to
one. They are exactly the two-outcome Born rule.

The theorem therefore supplies the finite operational identification:

```text
independent physical succession
  = add another event square
  = Loewner-positive increment
  = Lorentz-future increment
  = non-decrease under every pure quantum witness.
```

## Proof

### Direct-sum composition

For \(u\in\mathbb C^2\),
\[
\|(X\boxplus Y)u\|^2=\|Xu\|^2+\|Yu\|^2.
\]
Polarising, or multiplying the stacked matrix directly, gives `(7)`.

### Positive increment and event factor

`(2) -> (1)` follows because every Gram square is positive semidefinite. Conversely, a
positive-semidefinite \(2\times2\) matrix \(B-A\) has a positive square root \(R\). Embedding
\(R\) in the first two rows of a \(3\times2\) matrix \(Y\) gives
\[
Y^\dagger Y=R^2=B-A.
\]
Hence `(1) <-> (2)`.

### Order detected by every quantum witness

If \(B-A\succeq0\), then
\[
w_B(\psi)-w_A(\psi)=\psi^\dagger(B-A)\psi\ge0,
\]
so `(1) -> (3)`. Conversely \(A\) and \(B\) are Hermitian. If `(5)` holds for every \(\psi\),
then every quadratic evaluation of \(B-A\) is nonnegative, which is exactly positive
semidefiniteness. Thus `(3) -> (1)`.

### Positive cone equals Lorentz future

The determinant of `(3)` is
\[
\det\Phi=\Delta t^2-\Delta x^2-\Delta y^2-\Delta z^2
\]
and its eigenvalues are
\[
\Delta t\pm\sqrt{\Delta x^2+\Delta y^2+\Delta z^2}.
\]
Both are nonnegative exactly under `(6)`. This proves `(1) <-> (4)`.

An elementary proof avoiding spectral language uses the \(2\times2\) principal-minor criterion.
Condition `(6)` implies \(\Delta t\pm\Delta z\ge0\) and \(\det\Phi\ge0\). If
\(\Delta t+\Delta z>0\), completing the square gives a nonnegative quadratic form. If
\(\Delta t+\Delta z=0\), the determinant condition forces the off-diagonal entry to vanish and
the remaining diagonal entry is nonnegative.

### Binary Born normalization

Direct expansion proves `(9)`. Taking the trace after multiplying by \(A\) gives `(10)`.
Positivity of \(A\) makes both terms nonnegative. Trace-one normalization therefore turns the
source-generated quadratic evaluations into a probability pair.

## What is closed

The finite Hermitian/operational lift no longer remains an unspecified analogy. Starting from the
source-forced \(M_{3,2}(\mathbb C)\) carrier and its unique positive Gram record, the same record
now has exact, mutually equivalent composition, quantum-evaluation, positive-order, and
Lorentz-causal readings.

The strongest exact sentence is:

> **A record is later precisely when it is the earlier record plus another possible event; this is
> equivalent to every quantum witness assigning it at least as much unnormalised weight.**

No causal cone or Born matrix formula is separately inserted after the Gram record. Both are
forced mathematical readings of its additive positive order.

## What is not closed

This theorem does **not** establish that observed physical histories use these source records.
That empirical bridge cannot be proved from finite algebra alone. It also does not yet provide:

- local event incidence or tensor composition of separated systems;
- a continuum limit or topology of spacetime;
- clocks, a tetrad, a connection, curvature, Einstein dynamics, or gravity;
- general POVMs, sequential state update, or interacting quantum field theory;
- Standard Model dynamics or a new quantitative prediction.

Calling \(w_A\) “probability” additionally uses trace-one preparation and complete-alternative
normalization. A general uniqueness theorem for all POVMs requires an effect-additivity premise,
as in Busch/Gleason reconstruction. The binary pure-alternative statement above is exact and
assumption-visible.

## Novelty audit

The components are occupied:

- the positive \(2\times2\) Hermitian cone as the Minkowski future cone and its qubit
  interpretation are explicit in P. Arrighi and C. Patricot,
  *A Note on the correspondence between Qubit Quantum Operations and Special Relativity*,
  arXiv:quant-ph/0212135;
- positive-effect additivity forcing the density-operator probability rule is established by
  P. Busch, *Quantum states and generalized observables: a simple proof of Gleason's theorem*,
  arXiv:quant-ph/9909073;
- a qubit POVM Gleason theorem is established by C. M. Caves, C. A. Fuchs, K. Manne and
  J. M. Renes, *Gleason-Type Derivations of the Quantum Probability Rule for Generalized
  Measurements*, arXiv:quant-ph/0306179;
- direct-sum Gram additivity, Loewner order, self-duality of the positive cone, and spinor
  completeness are standard finite linear algebra.

Therefore the theorem is `[REDISCOVERED MATHEMATICS]`, not a Nature-level discovery. Its research
value is closure: it prevents the root program from treating “Born” and “causal” as two unrelated
interpretive declarations. Novel physics can begin only if source-complete succession selects
this operational record in nature and its varying comparison law yields continuum curvature and a
falsifiable prediction.

## Lean realization

Module:
`formal/GaloisForLFunctions/HTGeometry/NoOutsideOperationalSquareCausality.lean`.

Central declarations:

- `eventStack`;
- `eventSquare_eventStack_eq_add`;
- `twoRecordPrecedes`;
- `twoRecordWitnessWeight`;
- `twoRecordPrecedes_iff_exists_colorEvent_increment`;
- `twoRecordPrecedes_iff_forall_witnessWeight_le`;
- `lorentzHermitianMatrix_posSemidef_iff`;
- `twoRecordPrecedes_iff_lorentzFuture_of_difference_eq`;
- `noOutside_operationalSquareCausality_fourWay`;
- `higgsSpinorEventMatrix_add_spinFlip_eq_smul_one`;
- `twoRecordWitnessWeight_add_spinFlip`;
- `twoRecord_binaryBorn_probabilities`.

The Lorentz-cone converse is not delegated to a spectral oracle: Lean checks an explicit
completed-square proof and separately discharges the singular null-boundary case.

## Gates

- [x] dependency-closed paper proof
- [x] primary-source novelty audit
- [x] unconditional Lean formalization
- [ ] axiom audit
- [x] umbrella reachability
- [ ] generated API index
- [x] physical and empirical boundary explicit
