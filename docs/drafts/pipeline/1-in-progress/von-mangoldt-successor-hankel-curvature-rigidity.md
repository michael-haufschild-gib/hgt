# Von Mangoldt successor Hankel-curvature rigidity

- **ID:** `von-mangoldt-successor-hankel-curvature-rigidity`
- **Stage:** 1-in-progress
- **Type:** `[UNIVERSAL RIGIDITY]`, `[SOURCE-SPECIFIC FAILED CLASS]`, `[POSITIVE SURVIVOR]`
- **Parent frontier:** `SR-39` in `suzuki-source-realization-knowledge-ledger.md`.
- **Candidate Lean:**
  `formal/GaloisForLFunctions/HTGeometry/ConservativeHankelRigidity.lean` and
  `formal/GaloisForLFunctions/RHTower/VonMangoldtAdditiveLogJetHankelCurvature.lean`.

## Frontier, not endpoint

The live Suzuki arrow asks whether the proved successor Dirichlet carrier and coherent odd
Gamma--Jacobi boundary can be placed in one completed Green--Schur object whose jet matrix is the
prime--Gamma Hankel matrix.  Existing corpus proves positivity, summability, zero constant row,
pointed Ward reconstruction, and strict Gamma Hankel laws.  It does not determine whether an
ordinary Hankel boundary correction can repair the successor carrier.

The containing problem is compatibility of a **conservative carré-du-champ** with a **unital
moment representation**.  A conservative differential kills the unit.  A Hankel form is balanced
under multiplication.  Those two structures may be incompatible except in the zero form.

## Conjecture under test

Let `v_r` be vectors in a real Hilbert space, with `v_0=0`, and let

```text
G(r,s)=<v_r,v_s>.
```

If `G(r+1,s)=G(r,s+1)` for every `r,s`, then every `v_r=0`.  Thus every nonzero conservative Gram
has nonzero Hankel curvature.  For an edge from `b` to `a`, its exact monomial curvature is

```text
(a^(r+1)-b^(r+1))(a^s-b^s)
 -(a^r-b^r)(a^(s+1)-b^(s+1))
 =(a-b)(a^s*b^r-a^r*b^s).                              (1)
```

At adjacent orders `r=s+1`, this is

```text
-(a-b)^2*(a*b)^s,                                      (2)
```

so every nontrivial positive monotone edge contributes the same strict sign.

For the actual successor von Mangoldt carrier, the first curvature should therefore satisfy

```text
G_3(2,0)-G_3(1,1) = -sum_n E_1(n) < 0,                 (3)
```

with strictness already witnessed by the prime atom `n=2`.

## Consequence if proved

For every correction matrix `B` satisfying the ordinary Hankel relation `B(2,0)=B(1,1)`,

```text
(G_3+B)(2,0) < (G_3+B)(1,1).                           (4)
```

Hence no additive ordinary Hankel boundary -- including a boundary supplied only as a raw moment
Gram -- can turn the successor carrier into Suzuki's completed Hankel section.  This kills a
natural class of `SR-39` placements, not the whole Green--Schur lane.

The positive survivor is exact: any viable pointed Gamma/polar boundary must itself be
non-Hankel before completion and solve the curvature equation

```text
B(r+1,s)-B(r,s+1) = -[G(r+1,s)-G(r,s+1)].              (5)
```

The existing adjacent-depth pointed Ward current has precisely the required kind of two-depth
structure; its curvature, rather than another generic positivity estimate, becomes the next
source calculation.

## Falsifiers and controls

1. `G_3(1,1)=0` falsifies source strictness.
2. A Hankel `B` changing the left side of `(4)` falsifies the affine-curvature calculation.
3. A nonzero conservative Gram satisfying all shift identities falsifies universal rigidity.
4. Existing direct-Gram zero-row no-go is a negative control: this card must strictly strengthen
   it from inequality of two matrices to a class-complete additive-boundary exclusion.
5. Existing pointed Ward reconstruction is a positive control: it is not declared dead, because
   it is not merely an additive Hankel correction.

## Novelty discipline

Corpus search found no conservative-Hankel rigidity theorem, no exact successor Hankel-curvature
law, and no additive Hankel-boundary exclusion in `HTGeometry`, `RHTower`, `HilbertMetric`, or the
proven/failed cards.  Generic Gram positivity, moment-Hankel theory, and the successor zero row are
already known and are not novelty claims.  External novelty remains unaudited until the theorem
survives Lean and source-specific comparison.

## Gates

- [ ] prove universal conservative-Hankel rigidity on paper and in Lean
- [ ] prove exact edge curvature laws `(1)`--`(2)` in Lean
- [ ] prove actual von Mangoldt strict curvature `(3)` in Lean
- [ ] prove additive Hankel-boundary exclusion `(4)` in Lean
- [ ] compare `(5)` with actual pointed Ward/Gamma--Jacobi boundary
- [ ] update anti-rediscovery ledgers and promote card

