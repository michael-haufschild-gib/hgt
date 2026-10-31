# Theta native tail is strictly positive near the seam

- **Stage:** 1-in-progress
- **Parent:** A7, finite-rank native-tail flux domination.
- **Target:** Every finite native tail Hankel matrix is positive definite
  on some neighborhood of the self-dual seam. Together with the audited
  cofinal positivity theorem, this confines any failure to a compact
  interval separated from zero.

## Proof mechanism

The corpus proves

`∫ x^j Φ^(i)(x) dx = (-1)^i j.descFactorial(i) ∫ x^(j-i) Φ(x) dx`

and `∫Φ>0`. If a finite linear combination of source derivatives vanishes,
pair successively with `1,x,…`. At step `j`, lower coefficients have vanished
and higher derivatives integrate to zero. The remaining diagonal is
`(-1)^j j! ∫Φ≠0`. Thus all coefficients vanish.

The seam tail form is exactly the squared integral norm of
`Σ_j v_j (2i)^j Φ^(j)`. A nonzero vector gives a nonzero continuous packet,
so this integral is strictly positive. Entrywise continuity of tail integrals
and openness of positive definiteness give a common center neighborhood
for each finite rank.

## Remaining obligations

Formalize the triangular moment argument, strict Gram positivity, continuity
and the neighborhood statement. This does not prove positivity on the
remaining compact interval and does not close A7.
