# CCM source--response determinant dichotomy

- **ID:** `ccm-source-response-determinant-dichotomy`
- **Stage:** 1-in-progress
- **Type:** THEOREM / RH ROUTE
- **Status:** `[PAPER PROOF IN PROGRESS] [LEAN IN PROGRESS] [NOVELTY UNDER AUDIT] [NOT RH]`
- **Parent:** `ccm-radical-quotient-hermitian-law.md`

## Frontier

CCM prove real-zero Fourier determinants after assuming that the shifted Weil matrix has a simple,
even ground state.  The radical-quotient theorem removes simplicity only after discarding the
radical and therefore loses the original Fourier determinant when the radical has dimension
greater than one.

The target here is stronger: retain a full-size characteristic determinant and its exact
rank-one/Fourier identity at arbitrary radical multiplicity.

## Candidate theorem

Let `T >= 0` be a nonzero finite CCM scalar shift, let `K = ker T`, let `D` be the injective
diagonal clock, let `eta` be the constant boundary vector, and let `beta` be the odd response
vector.  Put

```text
p_eta  = projection_K eta,
p_beta = projection_K beta.
```

The displacement identity and clock cyclicity imply:

1. `p_eta` and `p_beta` cannot both be nonzero (active-channel exclusivity);
2. they cannot both vanish: otherwise `D K <= K`, while the constant vector is cyclic for an
   injective diagonal clock, forcing `K = 0`;
3. hence exactly one channel is active.

For the active source `alpha` in `{eta,beta}`, define the canonical normalized radical vector

```text
c = p_alpha / ||p_alpha||^2,       <alpha,c> = 1,
A = D - |D c><alpha|.
```

Then `A c = 0`, `A` preserves `K`, and `T A = A* T`.  More strongly, the full characteristic
polynomial of `A` has only real zeros.  Indeed, `A|K` is triangular over
`K = Cc + (K cap c^perp)`, with zero on `Cc` and Hermitian compression of `D` on the quotient;
the quotient by `K` is Hermitian for the positive metric induced by `T`.

The rank-one determinant identity is unchanged by radical multiplicity:

```text
det(A-s) = -s det(D-s) <alpha,(D-s)^(-1)c>.
```

Therefore the polynomial

```text
P_alpha,c(s) = det(D-s) <alpha,(D-s)^(-1)c>
```

has only real zeros.  Reflection makes it even in both branches:

- even/source branch: `alpha=eta`, `c` is even, and `P` is the cardinal numerator of the Fourier
  transform used by CCM;
- odd/response branch: `alpha=beta`, `c` is odd, and `P` is a new response-weighted cardinal
  numerator.

This removes the simple-ground-state premise from the finite real-zero mechanism and replaces the
evenness premise by an exhaustive source/response dichotomy.

## Exact RH interface

For a cofinal family of actual shifted CCM matrices, prove that one channel occurs cofinally and
that its nowhere-zero normalized polynomial converges locally uniformly to `Xi`.  The even branch
is the original CCM Fourier route without simplicity.  The odd branch is a new response route.

No convergence or RH claim is currently made.

## Prior-work audit

- Bovdi--Klymchuk--Rybalkina--Salim--Sergeichuk (2020) classify operators on positive
  semidefinite inner-product spaces.  Generic quotient/radical block decomposition is classical.
- CCM (2025) prove the simple-even rank-one determinant/Fourier identity and identify convergence
  to `Xi` as the remaining program.
- Current corpus contains boundary-channel trichotomy, generic radical quotients, and cyclic
  radical collapse, but no full characteristic-polynomial reality theorem for the canonical
  source projection and no odd response determinant route.

Potential novelty rests only on the exact CCM source/response dichotomy and full determinant
application, not on semidefinite quotient theory, Moore--Penrose inversion, or block triangularity.

## Gates

- [x] exact CCM formulas recovered from primary source
- [x] corpus collision search
- [x] generic semidefinite novelty claim rejected
- [x] numerical sign pre-certification in both channels
- [ ] dependency-closed paper proof
- [ ] Lean theorem for full characteristic-zero reality
- [ ] concrete divided-difference connector
- [ ] hostile external priority audit of exact dichotomy
- [ ] cofinal channel selection
- [ ] locally uniform convergence to `Xi`
- [ ] RH

## Log

- 2026-07-22 -- Derived support-projection completion and vanishing-metric limit idea.
- 2026-07-22 -- Replaced limit proof by stronger exact radical/quotient triangular argument.
- 2026-07-22 -- Observed neutral channel is impossible for injective diagonal clock with constant
  cyclic source.
- 2026-07-22 -- Identified even Fourier and odd response real-rooted polynomial branches.
