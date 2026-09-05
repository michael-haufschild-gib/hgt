# Arithmetic mean descent of deletion interference

Stage: retired as an RH selector. Positive source-conservation theorem formalized.

## Frozen question

Can complete-period averaging kill literal composite interference while preserving
a nonzero diagonal bracket, and does its factorization law force the half exponent?

## Paper answer

Write `a_p(n)=1-p[p|n]`, `b_pq(n)=a_pq(n)-a_p(n)`, with positive moduli.
Pointwise `a_p b_pq=(1-p)b_pq`. Both deletion channels have bounded
summatory functions, so the arithmetic mean of this interference is zero.
The existing square identity gives means
`mean(a_p^2)=p-1`, `mean(b_pq^2)=p(q-1)`.
Thus the retained positive bracket obeys the exact ordered conservation law
`pq-1=(p-1)+p(q-1)` and its opposite factorization.

For the literal Mellin source `E_p(s,n)=a_p(n)n^(-s)`, stripping its prescribed
Mellin weight before taking this mean returns the same coefficient bracket for
every complex `s`. At multiples, Euler amplitude contributes `p^(2-2 Re s)`,
weight recovery contributes `p^(2 Re s)`, and sampling density contributes `1/p`:
the product is `p`, for every exponent. The quotient exists and retains bracket,
but this normalization erases the exponent rather than selecting `1/2`.

## Scope

This tests one explicit mean/coefficient quotient, not all factorization-graded
or nonlinear source quotients. The ordinary Dirichlet Gram from earlier modules
is different and retains nonzero negative interference. No zero hypothesis,
boundary-index identification, or uniform infinite-prime comparison is supplied.
The argument uses standard periodic averaging and scaling algebra; no priority
or beyond-literature claim. A positive survivor must be the exact mean/source
conservation law, not only a rejection of its RH interpretation.

Periodic coefficient means are classical; for their role as Dirichlet residues see
Chatterjee–Murty, [Non-vanishing of Dirichlet series with periodic coefficients](https://arxiv.org/abs/1405.6982).
The present proof uses finite prefix identities directly, not continuation.

Own leaf: `EulerDeletionMeanInterferenceDescent.lean`. Other tasks own the
factorization-graded carrier and cylinder-reconstruction modules.

## Exact verdict and positive survivor

The mean quotient can annihilate literal interference while keeping a positive
coefficient square mass. It cannot thereby select `Re s=1/2`: its finite recovered
mass prefixes, not only their limits, are independent of `s`. Weight recovery has
changed the observable. In particular the zero mean cannot be substituted into
`tsum_deletionSource_inserted_pair_re_neg`, which evaluates the different,
unrecovered Dirichlet pairing.

Strongest survivor: unconditional, signed, literal-source mean conservation in
both factorization orders, together with exact amplitude/weight/density accounting.
This does not exclude a different source-derived, weight-faithful associated grade.

## Lean evidence

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionMeanInterferenceDescent.lean`.
Namespace: `RHTower.DeletionMeanDescent`.

- `coefficient_mul_inserted`: the exact source overlap identity.
- `tendsto_mean_coefficient_sq`, `tendsto_mean_interference`, `tendsto_mean_inserted_sq`: the three coefficient limits.
- `unweight_mellin_normSq`, `unweight_mellin_pair`: exact weight recovery with signs, for every complex exponent.
- `recoveredMass_source`, `recoveredMass_inserted`: finite-prefix exponent independence.
- `recovered_interference_zero`, `recovered_source_mass_conservation`: literal-source limit certificate.
- `recovered_dilation_factor`: `p^(2-2σ) p^(2σ)/p=p`, without fixing `σ`.

Scratch and published leaf passed, with one informational `ring` hint and no
warnings. Nine principal axiom audits returned only `propext`, `Classical.choice`,
and `Quot.sound`. Umbrella import wired; no full or umbrella build. Global lint
at this cutoff failed only on concurrent unwired `KrejcirikTransverseValuationPseudospectrum`
and `BrizardElasticaHydrodynamicPotentialBounds`; both left untouched. All own
processes finished. No computation or RunPod job was needed. RH remains open.
