# Noncompact boundary carrier alone unlocks selection — failed

- **ID:** ULF-FLPM-FAIL-2
- **Stage:** 5 — failed
- **Type:** FAILED HIGHER MECHANISM / POSITIVE SURVIVOR EXTRACTED
- **Status:** `[FALSIFIED] [EXACT COUNTERMODEL] [PAPER-PROVED SURVIVOR] [LEAN PENDING] [NOT RH]`

## Conjecture attacked

> Once a source-derived archimedean or boundary operator is noncompact with positive essential
> norm, it supplies the missing global formation/properness mechanism.

## Exact killing theorem

Let `H=H_1 direct-sum H_2` with both summands infinite-dimensional and let `R` be the orthogonal
projection onto `H_1`. Then

\[
 \operatorname{dist}(R,\mathcal K(H))=1,
 \]

so `R` is maximally visible in the Calkin algebra. But `ker R=H_2` is infinite-dimensional. For
every compact `A:H->Y`, the combined map `(A,R)` is not bounded below: choose an orthonormal
sequence `e_n in H_2`; then `Re_n=0` and `Ae_n->0`.

Therefore positive essential norm detects existence of a surviving cofinal direction, not coverage
of all source directions. It is insufficient for global properness and selection.

## Strongest positive survivor

The exact replacement is

```text
cofinal transducer R has closed range and finite-dimensional kernel
  + compact local formation A is injective on ker R
  iff
combined formation (A,R) is bounded below.
```

Moreover the source is reconstructed by the explicit left inverse

\[
 \mathcal L(y,z)=Sz+J(y-ASz),
\]

and selection must be represented by a separate defect `delta R`; retaining `R` preserves
properness while `delta R` is compact exactly at `delta=0`.

Full proof:

`docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-laplacian-properness-mechanics/compact-formation-semifredholm-transduction-joint-recovery-and-carrier-defect-bifurcation-law.md`.

## New insight

The missing invariant is not essential norm but **essential coverage**: closed range, finite kernel,
or equivalently a positive essential minimum modulus. For a family of Calkin partial isometries,
this becomes a frame-coverage condition on their initial support projections.

This changes the Sonin frontier. Existing exact essential norms prove survival but not coverage.
The next theorem must show that a source-generated family of shell supports covers the identity, or
else exhibit an adaptive uncovered sequence.

## Formal status

The countermodel is elementary and the positive survivor is dependency-closed on paper. Lean
formalization is pending; this failed card is not closed as formally certified until the survivor
module is built.

## Log

- 2026-08-12 — noncompactness/essential-norm conjecture killed by infinite-kernel projection;
  semi-Fredholm transduction and carrier--defect bifurcation extracted.
