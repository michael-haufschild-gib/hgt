# Reciprocal squares conserve every positive trace moment

- **ID:** reciprocal-square-moment-conservation
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / SPECTRAL BRIDGE
- **Parent:** `source-odd-positivity-square-law.md`
- **Statement:** For every finite rectangular transfer \(D\), the two positive reciprocal squares
  \(D^\dagger D\) and \(DD^\dagger\) have equal trace moments at every positive order.
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/ReciprocalSquareMomentConservation.lean`

## Goal

Upgrade equal-rank reciprocity to the strongest basis-free positive data accessible through power
traces. Determine whether higher incompatibility records can be organized as one shared spectral
moment sequence rather than unrelated tensors.

## Gates

- [x] dependency-closed paper proof `[PROVED HERE]`
- [x] unconditional Lean theorem `reciprocalSquare_trace_pow_succ_eq`
- [x] final target build and axiom audit
- [ ] generated index and project-wide lint
- [ ] source derivation of the transfer and its calibration
- [ ] continuum moment problem and physical observable

## Theorem

`[PROVED HERE]`

Let \(D\in M_{m,n}(\mathbb C)\), and set

\[
H_{\rm in}=D^\dagger D,\qquad
H_{\rm out}=DD^\dagger.
\]

For every \(k\ge1\),

\[
\boxed{
\operatorname{tr}(H_{\rm in}^k)
=
\operatorname{tr}(H_{\rm out}^k).
}                                                             \tag{RMC1}
\]

### Proof

For \(r\ge0\), associativity gives

\[
(D^\dagger D)^{r+1}
=D^\dagger(DD^\dagger)^rD.                                   \tag{RMC2}
\]

Taking trace and cycling the rectangular factors,

\[
\begin{aligned}
\operatorname{tr}\left((D^\dagger D)^{r+1}\right)
&=\operatorname{tr}\left(D^\dagger(DD^\dagger)^rD\right)\\
&=\operatorname{tr}\left(DD^\dagger(DD^\dagger)^r\right)\\
&=\operatorname{tr}\left((DD^\dagger)^{r+1}\right).
\end{aligned}
\]

This proves `(RMC1)`.

## Scientific meaning

Equal rank is only the zeroth support shadow. `(RMC1)` says the two sides share every positive
spectral moment:

```text
same transfer D
  -> same nonzero singular values
  -> same complete positive moment sequence
  -> two different coefficient-side laws.
```

In finite dimension, the full moment sequence determines the multiset of nonzero eigenvalues.
That standard spectral fact is parent mathematics; the Lean theorem here certifies the exact
moment identities.

## Lean certificate

`[LEAN-PROVED]`

Declarations:

- `reciprocalDomainSquare_pow_succ`
- `reciprocalSquare_trace_pow_succ_eq`

No `sorry`, `admit`, axiom declaration, opaque declaration, unsafe declaration, or unproved
hypothesis occurs.
Final audit:

```text
lake build GaloisForLFunctions.HTGeometry.ReciprocalSquareMomentConservation
✔ Built GaloisForLFunctions.HTGeometry.ReciprocalSquareMomentConservation
Build completed successfully (3183 jobs).
```

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Hostile novelty audit

This is classical rectangular trace cyclicity/singular-value theory, equivalent to the spectral
pairing of supersymmetric partner Hamiltonians. Door grade: `[BRIDGE]`.

It becomes physics only if a source theorem independently identifies and calibrates the two
coefficient sides as quantum/gauge and gravity/causal responses. That theorem is open.

## Strongest positive survivor

The source-calibrated singular spectrum can be represented without choosing eigenvectors by the
moment sequence

\[
m_k(e)=\operatorname{tr}\left((D_e^\dagger D_e)^k\right)
=\operatorname{tr}\left((D_eD_e^\dagger)^k\right),\qquad k\ge1.
\]

This provides a concrete candidate for higher scalar records extracted from the complete
incompatibility nerve.

## Hypertranscendence bridge

`[CONJECTURAL PHYSICAL INTERPRETATION]`

A fixed finite matrix has a finite atomic spectral measure and a rational resolvent/moment
generating function. Complete hypertranscendent history therefore cannot be encoded by one fixed
finite reciprocal square. If Hypertranscendence is physical, it must enter through:

- an infinite spectral measure;
- event-to-event change of the transfer/category;
- non-finitely-closing ternary composition; or
- a generating function not reducible to one finite event spectrum.

This is a research direction, not a theorem proved in this card.

## Candidate physical law

`[CONJECTURE — NOT SCIENTIFIC KNOWLEDGE]`

> **Gravity and quantum law have the same hidden spectrum, seen from opposite sides of an
> event.**

Operational falsifier: after source-derived calibration, one nonzero clock/gravity response
spectrum must pair with one quantum/charge spectrum through all moments. No such observable map
has yet been derived.

## Log

- 2026-07-29 — proved all reciprocal positive power traces agree.
- 2026-07-29 — upgraded rank reciprocity to complete finite spectral-moment reciprocity.
- 2026-07-29 — connected higher source records to a candidate common moment sequence.
- 2026-07-29 — final target build and axiom audit passed.
