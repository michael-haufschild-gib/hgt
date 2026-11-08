# Sharp logarithmic completion of the full torsion form

- **ID:** RIAC-logarithmic-torsion
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md), critical torsion
- **Statement:** The full torsion form is bounded on `ℓ²((1+log n)^α)` exactly when `α>2`; a constant multiple of that diagonal gives a positive completion in precisely that range.

## Candidate mechanism

Write `L(n)=1+log n` for positive conductors and take the Schur reference
sequence `λ(n)=1/(√n L(n)^a)`, with `a=α−1>1`. The off-diagonal torsion
kernel is the sum of the two divisor kernels, with negative sign.
At conductor `n`, the weighted row contributions are

- multiples: `L(n)^a Σ_(t≥2) Λ(t)/(t L(nt)^a)`, at most `K_a L(n)^a`;
- proper divisors: `L(n)^a Σ_(t|n,t>1) Λ(t)/L(n/t)^a`, at most `L(n)^a log n`.

Here `K_a=Σ_(t≥2) Λ(t)/(t L(t)^a)` should be finite for `a>1`.
The divisor identity `Σ_(t|n) Λ(t)=log n` and `L≥1` then bound the entire
row by `(K_a+1)L(n)^α`. Weighted two-variable square completion gives
absolute finite-form control. Since the original tame diagonal is
nonnegative and bounded by `log n`, this also gives an explicit positive
diagonal completion of the full torsion matrix.

At `α≤2`, the conductor-one prime row has square mass comparable to
`Σ_p (log p)²/(p L(p)^α)`, which diverges. The prime-star classification
also excludes every finite constant diagonal compensation in that range.
The exact arithmetic comparisons and the full Schur estimate remain unproved.

## Further consequences to audit

If boundedness is proved, inclusion from exponent `α` into any exponent
`β∈(2,α)` is compact, giving compactness of the original torsion operator.
Even conductors have tame diagonal at least `log 2`; their normalized
diagonal square sum diverges for every finite logarithmic exponent.
Thus this candidate compact operator should never be Hilbert–Schmidt.
These consequences require separate proofs and are not accepted results.

## Positive survivor and scope

The proposed survivor is a sharp completed carrier and an explicit positive
completion on all conductor interactions, extending the prime-star restriction.
The added diagonal is a constructed compensation, not an archimedean height,
product formula or integer arithmetic count. No sign for the uncorrected
critical form or Weil form follows.
