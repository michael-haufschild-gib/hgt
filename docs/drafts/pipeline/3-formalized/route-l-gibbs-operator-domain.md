# Route L: literal Gibbs operator domain and physical exchange

Status: formalized; scratch, targeted module build, all-theorem axiom audit and repository lint passed.
Date: 2026-09-11.
Module: `GaloisForLFunctions.RHTower.Deninger.DeningerOrdinaryIntegerGibbsOperatorDomain`.

## Exact source and result

Use the existing ordinary-integer sequence endomorphisms: reciprocal Green
operator `Q`, dilation shift `S_n`, backward shift `S_n^*`, and divisibility
projection `P_n`. No new source operator is substituted for them.

For real `sigma`, define `m_sigma(k)=k^(-2*sigma)` on positive integers and

`D_sigma = { T : sum_k m_sigma(k)*k*(T e_k)(k) converges }`.

This is a complex submodule. The displayed sum defines `Trace_sigma` on that
submodule. Normalization by `Z_sigma=sum_k m_sigma(k)` requires an explicit
proof of `sigma>1/2`; the normalized reader is not defined by assigning a
value to a divergent partition sum.

The source Green operator belongs to `D_sigma` **exactly** for `sigma>1/2`.
For every positive integer `n`, the actual admitted operators satisfy

`Reader_sigma(Q)=1`,

`Reader_sigma(P_n Q)=n^(-2*sigma)`,

`Reader_sigma([S_n^*,Q S_n])=1/n-n^(-2*sigma)`.

At `sigma=Re(s)`, the last value equals the already fixed
`deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n s`. For `n>=2`,
it is nonzero throughout the convergence chamber.

The stronger exchange theorem applies to **every** `T in D_sigma`:

`Trace_sigma(S_n^* T S_n) = [n*m_sigma(n)]^-1 Trace_sigma(T P_n)`.

Both operators displayed here belong to the same source domain. The
multiplier is exactly `deningerHalfDensityMateGain n s` when `sigma=Re(s)`;
the normalized reader has that same exchange law. This is a weighted
exchange identity, not an assertion of ordinary cyclicity.

For every `n!=1`, both factors `S_n^*` and `Q S_n` belong to `D_sigma` for
**every** real parameter, but their product belongs exactly for
`sigma>1/2`. Thus factor admission at the critical parameter does not admit
the product. No pair `D_sigma`, `D_(1-sigma)` both admits `Q`.

## Dependency-closed paper proof

The diagonal maps are linear. Summable complex families are closed under
addition and scalar multiplication, and their sums respect those operations,
so they give the stated submodule and linear functional.

On `Q`, reciprocal multiplication leaves precisely `m_sigma(k)`. The
positive-integer p-series criterion gives the sharp admission threshold.
The partition is strictly positive there because every summand is positive.
On `P_n Q`, the same mass is restricted to multiples of `n`. Reindexing by
the injection `j -> n*j` and multiplicativity of real powers proves the
exact multiples law. Linearity on the admitted domain and the existing
operator identity `[S_n^*,Q S_n]=n^-1 Q-P_n Q` give the boundary value.
Writing real powers as exponentials identifies it with the fixed physical
coefficient; the existing classification of that coefficient proves it is
nonzero in the convergence chamber.

For general `T`, the Wold shift sends `e_k` exactly to `e_(nk)`, so
`d_k(S_n^* T S_n)=d_(nk)(T)`. The diagonal of `T P_n` is the restriction of
`d_k(T)` to multiples. An injective subsequence of a summable family and
its indicator restriction remain summable. Reindexing gives the exchange
law with multiplier `[n*m_sigma(n)]^-1`, equal to the fixed physical gain.

When `n!=1`, the two literal chain factors have zero diagonals. Their left
product equals `n^-1 Q`; multiplication by this nonzero scalar preserves
admission, giving its exact threshold. Finally `sigma>1/2` and
`1-sigma>1/2` cannot both hold.

## Novelty, positive survivor and remaining obstacle

The scalar degree-six shell Gibbs formula already exists in
`DeningerGammaSixGreenGibbsPhysicalReader`; it is not claimed as new.
This module constructs the reader on the literal ordinary-integer operator
domain, proves its sharp admission criterion, and derives the physical
exchange multiplier for every admitted operator and every integer dilation.
Its chain-factor admission theorem identifies an actual failure of product
admission at the proposed cyclic parameter.

These are source/domain results with no Xi-zero premise. They do not show
agreement between the existing normalized cyclic reader and the fixed
physical reader at Xi divisors. The new reader instead reads a nonzero
boundary throughout its convergence chamber. A continuation or changed
domain that removes this multiplier while retaining the fixed physical
value remains unproved. RH remains unproved.

## Search and literature audit

Hybrid/deep/method searches and targeted source searches covered Gibbs
readers, divisibility, normal domains, injective trace reindexing and the
full Green remainder. Reported deep coverage was partial. The direct source
identities and mathlib p-series/indicator/injective-sum lemmas support the
proof; unrelated normal-form and finite-matrix hits supply no missing
arithmetic comparison.

Broad recent-paper searches used transgression, anomaly, reciprocity and
excision. The [August 2026 transgression analysis](https://arxiv.org/html/2608.09776v1)
retains endpoint terms and requires local exactness for its cancellation.
The [August 2026 higher Chern--Simons triangle identity](https://arxiv.org/html/2608.19539v1)
also retains a boundary correction. Neither identifies this source reader;
their assumptions are not imported as arithmetic facts. Detailed tests and
other recent-paper exclusions are recorded in the C16 attack ledger.

## Verification

- `lake env lean /tmp/route_l_gibbs_reader.lean` — all 30 theorems passed, no warnings.
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerOrdinaryIntegerGibbsOperatorDomain` — passed; only this new module was built, with existing dependency results replayed. No umbrella build.
- `scripts/formal_tools.py lint` — passed.
- `lake env lean /tmp/route_l_gibbs_operator_axioms.lean` — all 30 theorems use only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms.

The module is imported by `RHTower.lean`. No numerical experiment is used.
