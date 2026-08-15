# Square-zero compatibility defect

- **ID:** `square-zero-compatibility-defect-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper:** `square-zero-compatibility-defect.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/SquareZeroCompatibilityDefect.lean`

## Certified theorem surface

For an arbitrary bilinear map `B : S →ₗ[R] S →ₗ[R] V` over an arbitrary commutative ring:

1. `bilinearSquare_add` proves exact polarization;
2. `bilinearSquare_add_of_square_zero` identifies the square of a sum with the cross defect when
   both endpoints square to zero;
3. `bilinearSquare_add_eq_zero_iff_compatibilityDefect_eq_zero` proves the exact compatibility
   equivalence;
4. `squareCompatibilityDefect_eq_two_smul_of_symmetric` proves the symmetric defect is twice the
   cross pairing; and
5. `bilinearSquare_add_of_square_zero_symmetric` combines the square-zero and symmetric forms.

The certificate retains characteristic-two behavior and assumes no cancellation of scalar two.

## Audit

- Direct source check:
  `lake env lean GaloisForLFunctions/HTGeometry/SquareZeroCompatibilityDefect.lean` — pass, no
  warnings.
- Final focused build:
  `lake build GaloisForLFunctions.HTGeometry.SquareZeroCompatibilityDefect` — pass,
  `1040/1040`.
- Formal lint:
  `scripts/formal_tools.py lint --check-generated` — pass; only pre-existing large-file warnings.
- Generated `LEAN_API.md`, `LEAN_GAPS.md`, and `LEAN_OVERVIEW.md` refreshed.
- Axiom audit: only `propext` and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or computation-based proof.

## Scientific boundary

This certificate proves a standard algebraic identity. It does not certify any identification of
square-zero elements with quantum possibilities, cross defects with actual events, or target
vectors with spacetime.

## Gates

- [x] dependency-closed paper theorem
- [x] unconditional Lean implementation
- [x] direct check and focused final build
- [x] axiom and formal-lint audits
- [x] umbrella import and generated indexes
- [ ] publication target — intentionally not applicable as new scientific knowledge

## Log

- 2026-07-29 — formal audit completed; retained solely as hostile-test machinery for the frozen
  quantum-incompatibility spacetime conjecture.
