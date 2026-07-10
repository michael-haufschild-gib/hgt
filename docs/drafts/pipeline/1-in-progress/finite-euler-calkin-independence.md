# Finite Euler dilation corners are Calkin-independent

- **ID:** finite-euler-calkin-independence
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE -> PAPER PROOF IN PROGRESS -> LEAN TARGET]`
- **Source:** one-prime Euler Fredholm seam; concrete Sonin shell carrier
- **Statement:** `[CONJECTURE]` For any finite set of distinct scales `r_j>1`, the lower Sonin
  cross-boundary corners of `U_(r_j)+U_(r_j)*` are linearly independent modulo compact operators.
  Equivalently, every nonzero finite linear combination has a noncompact lower corner.  In
  particular the prime-indexed Euler corners span an infinite-dimensional subspace of the Calkin
  quotient.

## Goal

Rule out finite cancellation as a repair of the one-prime Fredholm obstruction.  The theorem must
use the concrete common physical/Fourier Sonin carrier, not an abstract family of operators with an
assumed separating sequence.

## Proposed theorem

Fix `a>0`, distinct scales `r_1,...,r_m>1`, and complex coefficients `c_j`, not all zero.  Put

```text
W = sum_j c_j (U_(r_j) + U_(r_j)*),
Q = projection onto the central Sonin carrier at cutoff a.
```

Then

```text
(1-Q) W Q
```

is not compact.

Since the positive one-prime Euler Gram has lower corner equal to the nonzero scalar
`-r_j^(-1/2)` times the dilation corner, the same conclusion gives Calkin linear independence of
the one-prime Euler Gram corners after rescaling coefficients.

## Paper proof under attack

Choose an index `k` with `c_k != 0`.  Select `b>a` sufficiently close to `a` that the finitely many
inward scaled shells

```text
r_j^(-1) {x : a < |x| < b}
```

are pairwise disjoint and all lie inside `[-a,a]`.  The outward scaled shells lie outside
`[-a,a]`.  Let `g_n` be the existing orthonormal even shell sequence supported in the shrinking
cells between `a` and `b`, and let `A_k` be the physical cutoff onto the `r_k^(-1)` shell band.

Then, exactly for every `n`,

```text
A_k W g_n = c_k U_(r_k) g_n,
||A_k W g_n|| = |c_k| > 0.
```

The observer `A_k` is contractive and kills the Sonin carrier.  The common Sonin projection
satisfies `Q g_n - g_n -> 0`; boundedness of the finite sum gives

```text
||A_k W Qg_n|| -> |c_k|.
```

The existing weak-null shell theorem then forces `(1-Q)WQ` to be noncompact.

## Attack obligations

- [ ] Prove a single shell width `b>a` simultaneously separates every distinct finite scale.
- [ ] Formalize the scaled even-shell observer and its measurability/contractivity.
- [ ] Prove exact target/self and off-target/zero cutoff identities using the existing normalized
  indicator dilation lemmas.
- [ ] Prove the corrected-shell crossing limit for the finite operator sum.
- [ ] Apply the existing Sonin noncompactness theorem and package the prime/Euler corollary.
- [ ] Run novelty and literature gates before promotion.

## Research classification

`[CONJECTURE]` The result appears unavailable from the current repository and is substantially
stronger than one-prime noncompactness: it identifies an infinite-dimensional essential prime
source, not merely a nonzero local seam.  It still does not itself move the Platt--Trudgian bound;
its significance is to prove that any faithful all-prime index must use genuinely infinite
renormalization rather than finitely many Euler factors or counterterms.

## Log

- 2026-07-10 -- Route opened after formalizing the one-prime invertible/noncompact-commutator
  theorem.  Concrete shell-isolation proof identified; Lean construction not yet complete.
