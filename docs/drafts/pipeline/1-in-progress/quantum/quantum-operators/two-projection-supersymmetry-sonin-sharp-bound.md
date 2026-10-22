# Two-projection supersymmetry and the sharp Sonin formal-complement bound

- **ID:** two-projection-supersymmetry-sonin-sharp-bound
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper + source-level Lean formalization)
- **Source:** [BRIDGE] quantum spectral projections / two-projection supersymmetry
- **Lean targets:**
  - `formal/GaloisForLFunctions/HTGeometry/TwoProjectionSupersymmetry.lean`
  - `formal/GaloisForLFunctions/RHTower/SoninTimeBandHilbertSchmidt.lean`
  - `formal/GaloisForLFunctions/RHTower/SoninSemilocalTraceObstruction.lean`

## Goal

Replace the triangle estimate for the formal physical/Fourier complement by the exact
two-projection value relation, then propagate the sharper value through every live consumer.
The transfer is useful only if it removes a premise or improves a theorem already used by the
corpus; novelty is not a gate.

## Exact physics relation

Let `P,Q` be self-adjoint projection operators and set

`A = P-Q`,

`B = 1-P-Q`.

Then

`A^2+B^2=1`,

`AB+BA=0`.

The first identity is the anticommutative Pythagorean theorem for two quantum projections.  It
has the positive master-constraint form

`A†A+B†B=1`

and hence the statewise value law

`||A psi||^2+||B psi||^2=||psi||^2`.

Therefore both `A` and `B` are contractions, without any commutativity assumption on `P,Q`.

Primary mathematical-physics provenance:

- B. Simon, *Tosio Kato's work on non-relativistic quantum mechanics: part 1*, equations
  (5.5)--(5.6), defines `A=P-Q`, `B=1-P-Q` and records both identities as the supersymmetric
  approach to quantum spectral projections:
  <https://par.nsf.gov/servlets/purl/10057632>.
- J. E. Avron, R. Seiler, and B. Simon, *Charge Deficiency, Charge Transport and Comparison of
  Dimensions*, applies pairs of Fermi projections to electron charge deficiency and transport:
  <https://math.caltech.edu/SimonPapers/228.pdf>.
- B. Simon, *Twelve tales in mathematical physics*, recounts the same `A^2+B^2=1` and
  `AB+BA=0` mechanism in the projection-index argument:
  <https://math.caltech.edu/SimonPapers/R67.pdf>.

## Proof

`[PROVED HERE]` Idempotence gives `P^2=P` and `Q^2=Q`.  Direct noncommutative expansion yields

`(P-Q)^2+(1-P-Q)^2=1`

and

`(P-Q)(1-P-Q)+(1-P-Q)(P-Q)=0`.

If `P†=P` and `Q†=Q`, both `A` and `B` are self-adjoint, so the square identity is exactly
`A†A+B†B=1`.  Pairing with any state gives the norm-square partition.  Dropping either
nonnegative summand proves the two contraction bounds.

## Corpus application

`[FORMALIZATION DRAFT / UNCOMPILED]` The general HTGeometry file now contains:

- `twoProjection_difference_sq_add_complement_sq`;
- `twoProjection_difference_anticommutes_complement`;
- `quantumMasterConstraint_twoProjection_partition`;
- `norm_twoProjection_difference_sq_add_complement_sq`;
- `norm_twoProjection_complement_le_one`;
- `norm_twoProjection_difference_le_one`.

This is general hypertranscendental constraint infrastructure, not a zeta-only declaration.

For the Sonin physical and Fourier forbidden projections, the formal complement is exactly
`B=1-P-Q`.  The relation replaces

`||centralSoninFormalComplement a|| <= 3`

by

`||centralSoninFormalComplement a|| <= 1`.

Propagating only this sharper value through existing proofs gives:

- principal dilation-corner operator norm: `24 -> 4`;
- dilation-residual Hilbert--Schmidt energy: `80 ||C||_HS^2 -> 16 ||C||_HS^2`;
- every weighted prime-power residual uses `16` instead of `80`;
- the semilocal relative-linear-cross energy constant: `184320 -> 1024`.

No new analytic hypothesis is introduced.  The existing semilocal source-trace no-go remains a
no-go, but with a substantially sharper uniform response bound.

## Direct-application audit

- **General HTGeometry:** direct positive master-constraint partition and automatic contraction
  theorems for arbitrary pairs of bounded quantum projections.
- **RHTower:** directly strengthens four live quantitative theorem surfaces and all their
  prime-power summability consumers.
- **Coupled-Sonin aperture route:** does not prove the remaining aperture Rayleigh comparison;
  it only improves the operator-energy budget available to that route.
- **Projection-correction anticommutator:** corrects the earlier audit.  The identity
  `C^2+C=PQ+QP` did not by itself improve `80`, but the associated two-projection Pythagorean
  relation does improve it by proving the missing sharp norm bound for `1-P-Q`.

## Gates

- [x] 0 -> 1: exact source relation, complete paper proof, direct consumers identified
- [ ] 1 -> 2: independent paper/source review
- [ ] 2 -> 3: targeted Lean check and axiom audit, only when explicitly permitted
- [ ] 3 -> 4: publication integration

## Verification boundary

No Lean invocation, build, lint, numerical script, experiment, or full-tree check was run.  The
Lean additions and propagated constants are source-reviewed only.

