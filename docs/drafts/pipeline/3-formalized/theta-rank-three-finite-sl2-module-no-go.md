# Theta rank-three finite sl2 module no-go

- **ID:** S6F-SL2-FIN-NG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean module:** `GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveFiniteModuleNoGo`
- **Statement:** No linearly independent finite polynomial carrier is closed under the exact
  source-positive theta raising and lowering Lie derivatives while diagonalizing the Cartan action
  with nonnegative weights and at least one positive weight.

## Goal

Kill the finite graded Shapovalov/contravariant-form route to the remaining S6F/TCD determinant
gate. Exact attempted RH chain:

```text
finite graded invariant sl2 module containing D1
  -> positive contravariant form
  -> D1 positive on refined physical cone
  -> global rank-three D1
  -> cofinal/all-order Hankel or completed Bezoutian landing
  -> Weil positivity
  -> RH.
```

The theorem kills the first arrow only. It does not prove or disprove TCD, global D1, or RH.

## Gates

- [x] 0 → 1 in-progress: source-pure exact no-go and explicit RH chain
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: exact Lean theorem, leaf build, and axiom audit
- [ ] 3 → 4 publication-ready: integrate with full S6F/TCD route analysis

## Proof

Let `A = C[U,B,Q]` and let `E,F,H` be Lie derivatives along the exact source-positive
theta `sl₂` fields.

1. In shifted Cartan coordinates `q=Q+3/8`,
   `H(U)=2U`, `H(B)=2B`, and `H(q)=4q`. Polynomial Cartan weights are therefore
   nonnegative, and every nonconstant homogeneous carrier has a positive weight.
2. Lean proves that Lie derivatives represent vector-field brackets and specializes the corpus
   identity `[E,F]=H` to every source-positive polynomial.
3. For a finite linearly independent carrier closed under `E` and `F`, Lean derives its exact
   matrix bracket `EF-FE=diag(w)`.
4. Finite matrix trace annihilates `EF-FE`. The diagonal trace is the sum of nonnegative weights,
   strictly positive because one weight is positive. Contradiction.

No analytic estimate, interval certificate, computation result, RH premise, source-sign premise,
`sorry`, new axiom, `opaque`, or `unsafe` declaration enters the proof.

## Hostile audit

- `[CORPUS]` Exact nonlinear `sl₂` brackets and positive Cartan weights are formal in
  `PolynomialODEJetRankThreeSourcePositiveSl2`.
- `[CORPUS]` D1 is nonconstant: it is negative at a rational seam obstruction and positive at
  the physical modular seam.
- `[LITERATURE]` Searches through 2026-08-29 found general polynomial `SL(2,R)` realizations
  and standard finite-dimensional `sl₂` theory, but no statement for this completed-theta source
  action or D1 route. Method is classical; source-specific no-go is the delta.
- A finite-dimensional quotient is not excluded, but cannot be used as an exact polynomial
  evaluation carrier without a separate evaluation-faithfulness theorem on the physical orbit.

## No-go closure

- **Exact killing theorem/mechanism:** Nonnegative Cartan spectrum contradicts zero trace forced by
  `[E,F]=H` on every nonconstant finite graded polynomial carrier.
- **Strongest positive survivor:** The representation needed by a surviving `sl₂` proof is
  necessarily infinite graded and must prove convergence/evaluation on the physical orbit.
  A direct cross-scale congruence remains viable without a finite invariant module.
- **New insight:** Cross-scale cancellation is structural, not an artifact of failed
  coefficientwise Gram decompositions; exact Cartan action forbids finite nonconstant truncation.
- **Status:** `[LEAN-PROVED]`. Scientific novelty remains source-specific and provisional.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/PolynomialODEJetRankThreeSourcePositiveFiniteModuleNoGo.lean`
- `lake build GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveFiniteModuleNoGo`
- Axiom audit for bracket, matrix no-go, and source carrier capstone:
  `[propext, Classical.choice, Quot.sound]`.
- Wired into `GaloisForLFunctions.HTGeometry`; umbrella not built.
- Repository lint recognizes module as reachable. Unrelated concurrent unwired modules still make
  repository-wide lint nonzero.

## Log

- 2026-08-29 — corpus-derived conjecture admitted with explicit RH chain; paper proof closed by
  Cartan grading plus trace of commutator.
- 2026-08-29 — exact finite graded carrier no-go formalized, leaf-built, axiom-audited, and wired.
