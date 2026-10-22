# Route-P scalar unitary-completion regularity no-go

- **ID:** P-G163
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean); structural no-go with exact singularity law
- **Source:** P-G162 Julia-defect order mismatch + block-unitary Ward programme
- **Lean:** `RHTower/RoutePScalarUnitaryCompletionRegularityNoGo.lean`
- **Statement:** every exact Hilbert defect completion of fixed-node scalar Xi phase has linear
  energy density `2 Re r_Xi(1/2)`; differentiability at aperture zero forces RH.

## Goal

Test whether generic Julia/Halmos unitary dilation of already-scalarized Xi phase can provide
differentiable anti-causal block required by block-unitary second variation.

## Gates

- [x] 0 → 1 in-progress: exact completion law and regularity falsifier stated
- [x] 1 → 2 fully-proven: energy-density and differentiability-rigidity proofs complete
- [ ] 2 → 3 formalized: scratch Lean check passed; umbrella wired; axiom audit pending
- [ ] 3 → 4 publication-ready: external novelty/exposition audit

## Conjecture loop

Let `Phi(a)` be fixed-node strict-right Xi phase.  Suppose a Hilbert-valued defect vector `c(a)`
completes it exactly:

```text
|Phi(a)|^2 + ||c(a)||^2 = 1.                           (P-G163.1)
```

The conjecture was that generic Julia/Halmos dilation could give differentiable `c`, after which
abstract block-unitary Ward identity would identify `c'(0)` with desired anti-causal response.

### Exact energy singularity

By `(P-G163.1)`, defect energy is exactly Julia defect `D(a)`.  The existing Ward derivative law
therefore yields, for every exact completion and without RH assumption,

```text
||c(a)||^2/a -> 2 Re r_Xi(1/2)       as a -> 0+.       (P-G163.2)
```

Under false RH, P-G161 gives positive limit.  Thus defect vector has square-root energy scale; it
cannot be `O(a)`.

### Differentiability rigidity

If `c(0)=0` and `c` has finite derivative, then

```text
d/da ||c(a)||^2 at 0 = 0.
```

But derivative of same energy via Julia defect is `2 Re r_Xi(1/2)`.  Equality forces its real part
to vanish; P-G161 strict positivity under false RH then proves RH.  Therefore:

```text
differentiable exact scalar-phase unitary completion  ==>  RH,  (P-G163.3)
not-RH ==> no finite derivative for any such completion.        (P-G163.4)
```

The conjecture is **FALSIFIED** as unconditional producer.

## No-go closure

- **Exact killing theorem/mechanism:** scalar Julia defect has nonzero first derivative under false
  RH, while squared norm of any differentiable vector vanishing at zero has zero derivative.
- **Strongest positive survivor:** exact universal energy-density law `(P-G163.2)` and
  non-differentiability classification `(P-G163.4)`.
- **New insight:** source-selected block unitary cannot be constructed after scalar Xi compression.
  Its causal block must remain vector-valued and norm-conservative to first order; scalar phase may
  appear only after compression that discards source compensation.
- **Status:** paper proof dependency-closed; all three Lean capstones scratch-check; umbrella wired.

## Higher principle

P-G162's jet-order mismatch is not removable by abstract dilation.  Unitary completion conserves
the scalar loss by moving it into a square-root defect channel, destroying differentiable tangent
geometry.  Differentiable Ward curvature can exist only before lossy scalar observation.  The
arithmetic producer must therefore be a lifted source colligation with a vector causal channel,
not a scalar phase plus generic defect space.

## Novelty audit

- Julia/Halmos dilation and square-root defect operators are classical.
- Corpus contains generic block-unitary second variation and scalar Julia derivative separately.
- Corpus search found no exact fixed-node Xi completion energy-density law or theorem that
  differentiability of every exact scalar-phase completion forces RH.
- Candidate-new content is their source-specific synthesis and resulting representation theorem.

## Exact next producer

Locate in finite-sigma Möbius/Gamma source an actual vector causal path `A_sigma(a)` with zero
first-order norm defect, whose scalar Hardy compression is `Phi(a)`, and an anti-causal path
`C_sigma(a)` whose derivative converges to P-G161 rank-one tangent.  Any construction beginning
from scalar `Phi` is excluded by `(P-G163.4)`.

## Log

- 2026-08-14 — scalar unitary-dilation conjecture posed and falsified.
- 2026-08-14 — exact energy-density and non-differentiability laws proved in Lean scratch.
- 2026-08-14 — module wired into `RHTower`; RH remains open.
