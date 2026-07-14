# Finite cyclic observable twirl

- **ID:** finite-cyclic-observable-twirl
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** [BRIDGE] quantum-information group twirling and constrained-system group averaging
- **Statement:** The finite conjugation-orbit numerator satisfies an exact boundary telescoping law; a finite-period gauge step therefore makes the twirled observable commute with the constraint and preserve its physical kernel.

## Goal

Complete the existing finite cyclic state-average API with the Heisenberg-picture operation on
observables.  The output should be a constructively gauge-invariant/Dirac observable, so existing
physical-state preservation and Ward surfaces no longer require a separately proved commutator
hypothesis.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack identity, direct consumer identified
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem names checked, targeted Lean check green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics relation

For a finite cyclic gauge step `U`, group twirling sends an observable to its conjugation average.
Avoiding inverse notation, define the `N`-term numerator recursively by

`T_0(A)=0`,

`T_(n+1)(A)=U T_n(A) + A U^(n+1)`.

Thus `T_N(A)=sum_(k=0)^(N-1) U^k A U^(N-k)`, and the exact boundary law is

`U T_N(A) - T_N(A) U = U^N A U - A U^(N+1)`.

If `U^N=1`, each summand is the usual conjugate `U^k A U^(-k)` and the right side vanishes.
Hence `T_N(A)` commutes with `U`, with the constraint `U-1`, and preserves `ker(U-1)`.

Physics sources: Marolf, *Group Averaging and Refined Algebraic Quantization: Where are we now?*
(arXiv:gr-qc/0011112), which describes group averaging as a constructive source of observables and
physical inner products; and Hashagen et al., *Real Randomized Benchmarking* (arXiv:1801.06121),
which states the finite-group twirl as the normalized sum and identifies it as projection onto the
commutant.

## Corpus application

- Extend `HTGeometry/FiniteConstraintGroupAverage.lean`, whose current operation averages vectors
  but does not construct gauge-invariant observables.
- Discharge the commutation premise needed to preserve `PhysicalState (U-1)`.
- Expose the identically zero constraint commutator for subsequent Ward consumers.

## Direct-application audit

The result directly consumes the existing physical-state definition and finite-period constraint
surface.  No current RH-equivalent RHTower theorem is parameterized by a finite-period gauge step,
so this is general HTGeometry infrastructure, not an RH premise discharge.

## Verification boundary

Source-level formalization only.  Per user instruction, no Lean process, build, lint, numerical
experiment, or axiom audit is run during this phase.

## Log

- 2026-07-14 — exact boundary telescoping identity and physical-kernel consumer isolated before Lean edits.
- 2026-07-14 — source-level Lean declarations added to `HTGeometry/FiniteConstraintGroupAverage.lean`: recursive conjugation numerator, exact boundary telescoping law, finite-period commutation, normalized twirl, constraint commutation, and physical-kernel preservation.  No computation or build run.
