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

The [formalized Mangoldt tail](../3-formalized/riac-logarithmic-mangoldt-tail.md)
gives `K_a=Σ_(t≥2) Λ(t)/(t L(t)^a)<∞` for every `a>1`.
The divisor identity `Σ_(t|n) Λ(t)=log n` and `L≥1` then bound the entire
row by `(K_a+1)L(n)^α`. Weighted two-variable square completion gives
absolute finite-form control. Since the original tame diagonal is
nonnegative and bounded by `log n`, this also gives an explicit positive
diagonal completion of the full torsion matrix. The proposed positive
correction is `(K_a+1)L(n)^α`; the absolute-form bound uses `K_a+2`.
These constants are sufficient bounds. Only the exponent threshold is claimed
to be sharp; minimal full-matrix compensation is not determined.

At `α≤2`, the conductor-one prime row has square mass comparable to
`Σ_p (log p)²/(p L(p)^α)`, which diverges. The prime-star classification
also excludes every finite constant diagonal compensation in that range.
The full finite absolute bound, sharp positive-compensation equivalence and
unique bounded Hilbert completion have complete Lean drafts. The same cost
`K_a+1` compensates every completed probe: the absolute prime pair series
is bounded by that cost times the logarithmic mass, while each original
torsion summand is bounded below by the negative absolute prime summand.
These claims remain unaccepted pending direct checks and axiom audits.

The generic finite weighted Schur test already exists as
`weighted_double_sum_le_weightedRowBound` in `HTGeometry.WeightedSchurTest`.
The required tail reduces to the existing prime reciprocal-log series and
`RHTower.sum_nonprime_vonMangoldt_rpow_le` at exponent one; the latter
uniformly bounds the proper-prime-power mass by `72`. The conversion into
the required summability theorem has passed its production Lean check.

For necessity, the draft embeds every prime-star probe into its actual
integer support `{1}∪S`. A full positive correction with constant `C` restricts
to central diagonal `C` and leaf diagonal `d(p)+C L(p)^α`. The unrestricted
star classification supplies strict leaf positivity and finite payment.
For `α≤2`, eventual growth is at most `(1+4|C|)(log p)²`, contradicting that
finite payment. Thus no sign assumption on the proposed constant is hidden.

## Further consequences to audit

If boundedness is proved, inclusion from exponent `α` into any exponent
`β∈(2,α)` is compact, giving compactness of the original torsion operator.
Even conductors have tame diagonal at least `log 2`; their normalized
diagonal square sum diverges for every finite logarithmic exponent.
Thus this candidate compact operator should never be Hilbert–Schmidt.
The [spectral branch](riac-logarithmic-torsion-spectrum.md) gives the exact
coefficient-preserving factorization and even-prime diagonal argument.
Its complete Lean drafts remain unchecked; these are not accepted results.

## Positive survivor and scope

The proposed survivor is a sharp completed carrier and an explicit positive
completion on all conductor interactions, extending the prime-star restriction.
The logarithmic Hilbert domain is still smaller than unweighted `ℓ²`;
this would not make the original `δ=0` operator bounded.
The added diagonal is a constructed compensation, not an archimedean height,
product formula or integer arithmetic count. No sign for the uncorrected
critical form or Weil form follows.

## Related operator theory

[Brevig–Perfekt–Seip, §3](https://arxiv.org/html/1602.04729v3#S3)
write Dirichlet-series Volterra operators as divisor convolutions followed by
an output logarithmic divisor. This supplies a related established operator
framework. The present matrix has two-sided logarithmic normalization, its
transpose and the original tame diagonal; no operator identification with
that theorem is assumed. The [multiplicative Hilbert matrix](https://arxiv.org/abs/1411.7294)
has entries `1/(√(mn) log(mn))`, a different kernel. Neither comparison
establishes novelty for the candidate torsion threshold. No priority is claimed.
