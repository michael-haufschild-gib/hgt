# Infinite signed digamma Herglotz pointing

- **ID:** `infinite-signed-digamma-herglotz-pointing`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT NEW IN ISOLATION]`
- **Statement:** The regularized signed Gauss carrier is Herglotz exactly when every residue has
  the positive orientation, including arbitrary infinitely reversed sign sequences.

## Goal

Close the infinite-orientation positivity boundary of the explicit digamma realization.  The
finite chamber theorem does not suffice: after infinitely many reversals, one must prove that the
background obtained by deleting a selected pole remains regular there.

## Theorem

For `epsilon : N -> Bool`, define

```text
w_epsilon(n) = -1 if epsilon(n)=true, and +1 otherwise,

G_epsilon(z)
  = sum_(n>=0) w_epsilon(n)
      [1/(n+1) - 1/(n+z+1/2)].
```

Then

```text
(forall z, Im z>0 -> Im G_epsilon(z)>=0)
  <-> epsilon is identically false.                         (1)
```

Thus the all-positive source is the unique Herglotz point of the full signed Gauss completion.

## Proof

Fix a coordinate `k`.  Delete the `k`th summand.  On the radius-`1/3` disk about
`-k-1/2`, the remaining terms are holomorphic.  On every compact subset, their tail has the
uniform majorant

```text
4 (R+1) / (n+1)^2,
```

because

```text
1/(n+1) - 1/(n+z+1/2)
  = (z-1/2)/[(n+1)(n+z+1/2)].
```

The deleted-pole background therefore converges locally uniformly and is holomorphic at the
selected pole.  Exact summable splitting gives the full carrier as that background plus its one
polar atom.  If the coordinate is reversed, the polar atom has negative upper-half-plane
imaginary part of order `-1/y` and dominates the continuous background on vertical approach.
Conversely, if every coordinate is positive, each Gauss summand has nonnegative imaginary part,
and summability permits termwise passage of the imaginary part.  This proves `(1)`.

## Gates

- [x] 0 -> 1: arbitrary infinite sign sequence and deleted-pole regularity isolated
- [x] 1 -> 2: complete normal-convergence and polar-dominance proof
- [x] 2 -> 3: `signedDigammaBooleanCompletion_nonneg_iff_allPositive`
- [x] narrow module build green
- [x] formal lint passed
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 -> 4: used as one component of the constraint--orientation paper; not standalone

## Formal theorem surface

`formal/GaloisForLFunctions/HTGeometry/ExplicitDigammaOrientationLimit.lean` contains:

- `summableLocallyUniformlyOn_signedDigammaRegular`;
- `differentiableOn_signedDigammaRegular`;
- `continuousAt_signedDigammaRegular`;
- `signedDigammaCompletion_eq_term_add_regular`;
- `signedDigammaBooleanCompletion_eq_regular_sub_atom`;
- `signedDigammaBooleanCompletion_not_nonneg_of_nonempty`;
- `signedDigammaBooleanCompletion_empty_im_nonneg`;
- `signedDigammaBooleanCompletion_nonneg_iff_allPositive`.

## Novelty boundary

Normal convergence of the Gauss series and domination by a single negative residue are classical
analytic mechanisms.  The theorem is recorded as formal infrastructure, not as new knowledge in
isolation.  Its scientific role is to make the explicit source the intrinsic Herglotz pointing of
the paper's full inverse-limit orientation geometry.

## Log

- 2026-07-14 -- proved the deleted-pole normal convergence and exact infinite signed Herglotz law;
  built the module, passed project lint, and audited its axioms.
