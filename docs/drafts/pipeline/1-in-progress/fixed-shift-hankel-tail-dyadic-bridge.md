# Fixed-shift Hankel-tail to dyadic RH bridge

- **ID:** `fixed-shift-hankel-tail-dyadic-bridge`
- **Stage:** 1-in-progress
- **Type:** THEOREM / right-to-left RH reduction
- **Lean targets:**
  `formal/GaloisForLFunctions/RHTower/TraceHankelConverse.lean`,
  `formal/GaloisForLFunctions/RHTower/XiShiftedReciprocalHankelTailCriterion.lean`

## Goal

At a fixed nonnegative real Möbius shift `y`, put

```text
w_q = lambda_q / (1 + y lambda_q),
lambda_q = -(rho_q - 1/2)^(-2).
```

For every cutoff `M`, prove that positivity of every finite Hankel quadratic using only shifted
moments from order `2M+1` onward is equivalent to RH.  At `y=1`, identify `w_q` with the existing
fixed-shift squared-Xi seam coordinate.  This gives the exact backward chain

```text
cofinal fixed-shift Hankel cone
  -> every shifted atom is real
  -> power-32 annulus empty AND dyadic tail from power 64
  -> RH.
```

## Paper proof

The map `lambda -> lambda/(1+y lambda)` preserves conjugation, is injective, never vanishes on an
Xi atom, and satisfies

```text
Im(w_q) = Im(lambda_q) / |1+y lambda_q|^2.
```

Thus `w_q` is real exactly when `lambda_q` is real.  The shifted family is trace class because
`|w_q| <= |lambda_q|`, and only finitely many shifted atoms exceed any positive norm threshold.

Fix a hypothetical nonreal atom `alpha=w_q`.  Multiplication by `X^M` does not vanish at `alpha`.
The phase-corrected outer-orbit separator annihilates every atom of modulus at least `|alpha|`
except the `alpha`/`conj(alpha)` fiber, while a radial monomial suppresses the inner atoms.
Dominated convergence leaves a finite sum of strictly negative conjugate-pair contributions,
contradicting nonnegativity on the principal ideal `X^M R[X]`.  Hence every shifted atom is real,
so every Xi reciprocal square is real and RH follows.

Conversely RH makes every shifted atom positive real, hence every tail Hankel quadratic is a sum
of nonnegative atomic squares.

At `y=1`, direct algebra gives

```text
xiShiftedReciprocalSquare 1 q = xiSquaredSeamOneCoordinate q.
```

Therefore the tail criterion supplies both rightmost dyadic interfaces already isolated in
`XiSquaredSeamPowerThirtyTwoAnnulus.lean`.

## Gates

- [x] prior-corpus audit: central principal-ideal converse exists; fixed-shift tail converse does not
- [x] dependency-closed paper proof
- [ ] reusable countable principal-ideal converse in Lean
- [ ] fixed-shift tail criterion in Lean
- [ ] fixed-shift/seam coordinate identity in Lean
- [ ] annulus/tail umbrella connector in Lean
- [ ] axiom, lint, and target-build audit

