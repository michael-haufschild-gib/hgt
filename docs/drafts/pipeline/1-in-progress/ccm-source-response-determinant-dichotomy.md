# CCM source--response determinant dichotomy

- **ID:** `ccm-source-response-determinant-dichotomy`
- **Stage:** 1-in-progress
- **Type:** CORPUS-COLLIDED ROUTE / FORMAL STRENGTHENING AUDIT
- **Status:** `[SIMPLE-EVEN REMOVAL NOT NEW] [SOURCE/RESPONSE EXCLUSIVITY NOT NEW]`
  `[FULL-CHARPOLY RESIDUAL UNDER AUDIT] [NOT RH]`
- **Parent:** `ccm-radical-quotient-hermitian-law.md`

## Frontier

The project already proved the unconditional boundary-channel trichotomy, mutual exclusion of the
active source/response channels, arbitrary-radical completion, and a Hermitian radical quotient.
Therefore removing the simple-even hypothesis from the finite completion mechanism is prior corpus
knowledge and cannot support a novelty claim.

Only the strict residual target survives audit: retain the **full-size** characteristic determinant
and its exact rank-one resolvent identity at arbitrary radical multiplicity, rather than cancelling
the radical in the already-known quotient determinant.

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
- odd/response branch: `alpha=beta`, `c` is odd, and `P` is a response-weighted cardinal
  numerator. No novelty claim is made for existence of this channel.

The source/response dichotomy itself is not new.  The only possible strengthening is that the
specific orthogonal-Riesz completion controls every residual-radical eigenvalue and hence the full
characteristic polynomial, whereas prior corpus proves reality only after radical quotient.

## Exact RH interface

For a cofinal family of actual shifted CCM matrices, prove that one channel occurs cofinally and
that its nowhere-zero normalized polynomial converges locally uniformly to `Xi`.  The even branch
is the original CCM Fourier route without simplicity.  The response determinant is only an
uncollided variant under audit, not established as a new route.

No convergence or RH claim is currently made.

## Prior-work audit

- Bovdi--Klymchuk--Rybalkina--Salim--Sergeichuk (2020) classify operators on positive
  semidefinite inner-product spaces.  Generic quotient/radical block decomposition is classical.
- CCM (2025) prove the simple-even rank-one determinant/Fourier identity and identify convergence
  to `Xi` as the remaining program.
- Current corpus contains boundary-channel trichotomy, generic radical quotients, and cyclic
  radical collapse, but no full characteristic-polynomial reality theorem for the canonical
  source projection and no odd response determinant route.

The source/response dichotomy collides with
`CCMBoundaryChannelCompletion.lean` and the existing boundary-completion manuscript.  Any surviving
novelty rests only on full-characteristic-polynomial reality for the canonical orthogonal-Riesz
completion.  That residual is insufficient by itself for a significant paper or RH progress; it is
retained only if it shortens the genuine cofinal divisor interface.

## Gates

- [x] exact CCM formulas recovered from primary source
- [x] corpus collision search -- simple-even removal and active dichotomy rejected as prior work
- [x] generic semidefinite novelty claim rejected
- [x] numerical sign pre-certification in both channels
- [x] dependency-closed proof of full characteristic-zero reality
- [x] Lean theorem for full characteristic-zero reality
- [x] concrete divided-difference connector
- [ ] hostile external priority audit of exact full-characteristic Riesz-pinning law
- [ ] cofinal channel selection
- [ ] locally uniform convergence to `Xi`
- [ ] RH

## Log

- 2026-07-22 -- Derived support-projection completion and vanishing-metric limit idea.
- 2026-07-22 -- Replaced limit proof by stronger exact radical/quotient triangular argument.
- 2026-07-22 -- Observed neutral channel is impossible for injective diagonal clock with constant
  cyclic source.
- 2026-07-22 -- Identified even Fourier and odd response real-rooted polynomial branches.
- 2026-07-22 -- Hostile corpus audit found the claimed removal of simple-evenness and active
  source/response exclusion already in the formalized boundary-channel trichotomy.  Retracted that
  novelty claim; isolated only full-charpoly reality as a possible strict survivor.
