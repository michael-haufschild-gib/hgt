# Translation positivity is free; reflection positivity is a comparison

- **ID:** reflection-vs-translation
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** The free prime-side Gram is Toeplitz and equals `C² + S²`; the Gram any zero
  criterion needs is Hankel and equals `C² − S²`. The first is a sum of squares and always holds;
  the second is the comparison `S² ≤ C²`, and it fails on a single atom.

## Why this card exists

Three separate no-gos in this programme turned out to have the same shape, and this card identifies
the shape.

- CANNOT-387: square-root cancellation in the modulus aspect is blind to `ζ`, because the
  `ζ`-content sits below the certified accuracy — a **comparison** that fails.
- CANNOT-392: the factorial regularization has off-diagonal entries above the geometric mean of its
  diagonal at every pair — a **comparison** that fails.
- MUST-389/390: every checkable input is free or circular, with no intermediate.

All three are the sign below.

## The theorem

With `C = ∑ u_m cos(mx)` and `S = ∑ u_m sin(mx)`:

`RHTower.translation_form_eq` — `∑_{m,n} u_m u_n cos((m−n)x) = C² + S²`
`RHTower.reflection_form_eq` — `∑_{m,n} u_m u_n cos((m+n)x) = C² − S²`

`RHTower.translation_form_nonneg` — the translation form is nonnegative for **every** weight and
**every** frequency. No hypothesis. This is the entire content of the free prime-side positivity:
the explicit formula is translation covariant, so its Gram depends on `m − n`, so it is a sum of
squares.

`RHTower.reflection_form_nonneg_iff` — the reflection form is nonnegative **iff** `S² ≤ C²`. It is
not a positivity; it is a comparison between the odd and even parts of the weight.

`RHTower.reflection_form_neg_witness` — at `x = π/2` with the weight on the index `1` the reflection
form is `−1`. One atom.

## What it means

The functional equation is a reflection, so the Gram a zero criterion needs depends on `m + n`.
Toeplitz becomes Hankel, and `+S²` becomes `−S²`. A positivity cannot produce a comparison, so:

> **No route that transports the free prime-side positivity into a zero criterion can succeed, and
> the obstruction is visible before any arithmetic is used.**

This subsumes the factorial no-go (CANNOT-392) and the modulus-aspect no-go (CANNOT-387) as
instances, and it explains why the corpus's five lanes all terminated at the same wall
(`five-lanes-one-wall`): they were all trying to derive a comparison from a positivity.

## What to do instead

Supply the reflection positivity as **data**, not as a consequence. A reflection-positive functional
is exactly the datum that reconstructs a Hilbert space carrying a self-adjoint generator, so the
object MUST-390 asked for — a category in which `ζ` is one member and a pairing exists — and the
missing hypothesis are the same thing. The programme's remaining question is therefore not "which
inequality is sharp enough" but "what arithmetic datum is reflection positive".

The identification of Weil positivity with a reflection positivity is not new in the literature.
What is established here is that it is **forced**: it is where the deformation calculus, the
regularization criterion and the modulus-aspect no-go all terminate, and the terminus is one sign.

## Open core

Find an arithmetic construction whose reflection form is nonnegative by construction — i.e. where
`S² ≤ C²` holds because `S` and `C` are the odd and even parts of something with a built-in
domination, rather than because of an estimate. Over a finite field the Weil pairing is exactly such
a construction.

## Log
- 2026-09-25 — created; both forms, the free positivity, the comparison, and the one-atom witness
  proved and formalized. MUST-393.
