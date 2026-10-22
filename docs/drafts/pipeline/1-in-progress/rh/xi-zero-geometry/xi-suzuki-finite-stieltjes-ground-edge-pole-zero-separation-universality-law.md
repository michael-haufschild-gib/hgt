# Xi--Suzuki finite-Stieltjes ground-edge pole/zero separation universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED]`

## Lean-derived conjecture

One affine-sewn Suzuki exterior can simultaneously have the source-independent Xi-zero normal
form and fail the global Herglotz half-plane condition.  The latter is forced when its central
finite negative-Stieltjes chord mass is identified with a positive ground edge above the
half-curvature floor.

Thus universal pole/zero normalization at every Xi zero does not rescue positivity at the central
chart: local divisor universality and global Herglotz admissibility are separated by an exact
ground-edge inequality.

## Corpus inputs

- `xiZero_suzukiPoleZeroNormalFormUniversalCertificate`
- `not_suzukiFiniteNegativeStieltjes_herglotz_of_groundEdgeIdentification`
- `suzukiOneSidedCenteredShiftParameter_injective`

## New connector

The two terminal Suzuki laws govern the same `suzukiAffineSewnExteriorWeylQuotient` but at
different loci.  Centering the real shift parameters lets the Xi-zero normal-form certificate and
the central finite-Stieltjes/ground-edge obstruction coexist on exactly the same exterior
functions.  The conclusion is not a conjunction of unrelated models.

No numerical computation is used.

## Novelty protocol

No literature search before exact Lean proof.

## Lean target

`formal/GaloisForLFunctions/RHTower/XiSuzukiFiniteStieltjesGroundEdgePoleZeroSeparationUniversalityLaw.lean`

## Exact Lean verification

From `formal/`:

```text
lake env lean GaloisForLFunctions/RHTower/XiSuzukiFiniteStieltjesGroundEdgePoleZeroSeparationUniversalityLaw.lean
```

completed with zero diagnostics.

## Post-proof literature audit

Nearest literature:

- M. Suzuki, *A canonical system of differential equations arising from the Riemann
  zeta-function*, [arXiv:1204.1827](https://arxiv.org/abs/1204.1827), relates shifted Xi
  quotients, meromorphic inner functions, and positive canonical systems.
- M. Suzuki, *Hamiltonians arising from L-functions in the Selberg class*,
  [arXiv:1606.05726](https://arxiv.org/abs/1606.05726), gives canonical-system criteria for
  generalized Riemann hypotheses.
- R. A. Peherstorfer, A. Volberg, P. Yuditskii, *A canonical factorization for meromorphic
  Herglotz functions on the unit disk and sum rules for Jacobi matrices*,
  [published paper](https://www.math.caltech.edu/papers/bsimon/p288.pdf), treats general
  pole/zero interlacing and factorization for meromorphic Herglotz functions.

These sources separately connect Xi shifts to canonical-system positivity and Herglotz
functions to pole/zero structure.  None states the exact separation proved here: the same
centered affine-sewn exterior has the universal Xi-zero order/coefficient certificate while a
finite negative-Stieltjes central flux identified with a positive ground edge above the
half-curvature floor forces failure of the Herglotz condition.  No exact match was found.
