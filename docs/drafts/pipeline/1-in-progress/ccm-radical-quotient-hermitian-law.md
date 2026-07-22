# CCM radical-quotient Hermitian law

- **ID:** `ccm-radical-quotient-hermitian-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL THEOREM / CCM SIMPLE-EVEN HYPOTHESIS REMOVAL
- **Scientific status:** `[CORE PROVED IN LEAN SCRATCH] [CCM CONNECTOR IN PROGRESS]`
  `[NOVELTY AUDIT OPEN] [NOT AN RH PROOF]`
- **Parents:** `ccm-boundary-channel-completion-trichotomy.md`,
  `infinite-semimetric-symmetrization-closed-range-law.md`, Connes--Consani--Moscovici
  *Zeta Spectral Triples*.

## Discovery

Let `B : C^n -> C^r` be surjective, let `R : C^r -> C^n` be any right inverse, and put

```text
T=B* B,                       C=B A R.                    (1)
```

If `A` is self-adjoint for the possibly singular semimetric `T`,

```text
T A=A* T,                                                (2)
```

then `C` is an ordinary Hermitian matrix. Indeed, multiply `(2)` on the left by `R*` and on the
right by `R`:

```text
C=R* B* B A R=R* A* B* B R=C*.                         (3)
```

No simplicity, parity, choice of a kernel generator, or positivity margin occurs. If in addition
`A` preserves `ker B`, then `C B=B A`, so `C` is the honest operator induced by `A` after removing
the full radical of `T`.

## CCM consequence under audit

For every finite CCM Weil matrix `Q` let `mu=min spec(Q)` and `T=Q-mu I>=0`. Existing completion
theorem produces a clock `A` with `(2)` which preserves all of `ker T`, for every dimension and
every parity mixture of the ground space. A full-row-rank Gram factor `T=B*B` therefore produces
an ordinary Hermitian radical quotient `C` by `(1)`. Its characteristic polynomial has only real
zeros.

This removes CCM's simple-even ground-state premise from the finite real-spectrum step. The
one-dimensional even case in *Zeta Spectral Triples* is recovered when `dim ker T=1`; higher or
mixed-parity ground spaces are absorbed by the full radical quotient.

## RH endpoint

For a cofinal family `(lambda_j,N_j)`, if nowhere-zero entire normalizations of the radical-quotient
characteristic polynomials converge locally uniformly to `Xi`, then RH follows by closedness of the
real zero locus. Existing `HermitianDeterminantRH` proves this final transfer. The remaining
source-specific frontier is now only the divisor-preserving convergence of these quotient
determinants; simple-evenness is not part of that frontier.

## Honest route test

The quotient determinant need not equal CCM's original scalar ground-vector Fourier transform
when the radical has dimension greater than one. For an active boundary vector `e`, rank-one
determinant algebra gives the numerator

```text
det(D-sI) eta*(D-sI)^(-1)e,                              (4)
```

while passage to the full radical quotient divides out the characteristic polynomial of the
completion restricted to the residual radical. Proving that this cancelled boundary determinant
has the required cofinal limit is the genuine new analytic problem. Claiming convergence from the
old one-dimensional argument would be circular.

## Kill tests

- `(3)` fails under exact hypotheses `(1)`--`(2)`.
- Existing CCM literature already states and uses arbitrary-radical Gram quotient compression.
- The boundary determinant after residual-radical cancellation has no cofinal normalization that
  can approach `Xi`.
- Constructing the Gram frame or quotient determinant for actual CCM truncations imports RH or
  simple-evenness.

## Formal plan

1. Prove `(3)` for rectangular complex matrices and a supplied right inverse.
2. Prove every zero of `charpoly C` is real.
3. Prove `C B=B A` from full-radical preservation.
4. Add the locally-uniform determinant-to-RH consumer.
5. Connect the existing CCM completion output to `(2)` without assuming a preferred kernel vector.
6. Audit axioms and build only the leaf module, then wire the `RHTower` umbrella.

## Gates

- [x] exact algebraic law discovered
- [x] Hermitian core proved in `/tmp` with project toolchain
- [ ] quotient intertwining formalized
- [ ] real-rooted characteristic polynomial formalized
- [ ] RH convergence consumer formalized
- [ ] actual finite CCM completion connector formalized
- [ ] paper proof integrated without references to Lean
- [ ] external novelty audit
- [ ] quotient determinant convergence
- [ ] RH

