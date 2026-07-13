# Moving-fiber prime--Weyl parallelogram

- **ID:** `moving-fiber-prime-weyl-parallelogram`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / LARGE DETOUR / SHORTCUT FALSIFIED
- **Parent:** `dyadic-weld-weyl-multiplicity-route.md`
- **Source:** `PrimeDyadicWeyl.lean`, `SEMEventualSplit.lean`,
  `OrbitwiseSourceDivisorSeam.lean`, `SEMTruncatedJetWeylCharge.lean`

## Candidate chain

The pinned-fiber route fails because a nonzero prime dyadic translation has no fixed spectral
point.  Replace a single fiber by a moving square.  For

```text
t_(p,k) = -2 pi i / (2^k log p),
```

the global translation and Euler multiplier obey

```text
T_t M_p = zeta_k M_p T_t.
```

As `p` grows, `|t_(p,k)|` tends to zero.  A sufficiently small moving isolating annulus can in
principle retain the same finite root cluster along the four vertices of the commutator square

```text
T_t M_p T_t^(-1) M_p^(-1).
```

This bypasses literal fixed-point descent and is the correct large-parallelogram version of the old
compressed-prime-shift idea.

## Attack: why the square alone does not force multiplicity

The four edges are maps between different fibers.  Determinants of the two paths do not cancel as
they do for a commutator inside one finite general linear group.  A groupoid square may carry an
arbitrary scalar holonomy in any rank: even in rank one, choose three edge scalars equal to `1` and
the fourth equal to `zeta_k`.

At the unframed divisor-module level, multiplying a local defining function by a nonzero scalar
does not even change the principal ideal.  Thus the global scalar commutator can become a unit gauge
after passage to the local divisor.  Retaining a framed presentation or determinant line records
the scalar, but then its nontrivial loop holonomy is allowed; it is not forced to be one.

Therefore the tempting chain

```text
moving root cluster + closed prime parallelogram
  -> determinant of a commutator is one
  -> zeta_k^d=1
```

is invalid at its middle arrow.  The loop is a groupoid holonomy, not a commutator of two
endomorphisms of one fixed finite fiber.

## Positive statement from the no-go

The detour identifies an exact additional datum:

> a source-canonical trivialization of the determinant-line transport around the moving square.

With such a trivialization, the loop determinant would be forced to one and the Weyl scalar would
give `zeta_k^d=1`.  Without it, the phase is curvature rather than a multiplicity constraint.

`SEMTruncatedJetWeylCharge.lean` proves that this proposed determinant-line flatness is not a new
gap: its scalar obstruction is exactly the completed-SEM contour charge modulo `2^k`.  Thus the
moving-fiber parallelogram is a valid geometric model of the shared class, but not an annihilation
mechanism.

## Two-ended closure audit

```text
exact global prime Weyl square                         [PROVED]
  -> small moving root-cluster groupoid               [CONJECTURE / plausible analytic transport]
  -> framed determinant holonomy zeta_k^d             [BRIDGE]
  -> source triviality of that determinant holonomy   [OPEN CORE]
  -> zeta_k^d=1 for all k                              [PROVED -> RH]
```

The chain reaches RH on the right.  Its only potentially useful new middle is a source
determinant-line trivialization; ordinary moving-fiber transport is insufficient.

## Gates

- [x] 0 -> 1: moving-fiber square and both endpoints stated; invalid determinant cancellation
  isolated
- [ ] 1 -> 2: construct the moving SEM groupoid and a source determinant-line trivialization, or
  prove no such noncircular trivialization exists
- [ ] 2 -> 3: formalize only after the source trivialization theorem is proved
- [ ] 3 -> 4: requires full RH composition and novelty audit
