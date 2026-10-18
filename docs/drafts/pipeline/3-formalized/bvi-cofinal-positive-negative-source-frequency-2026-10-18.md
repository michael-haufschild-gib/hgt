# Both Möbius-source signs have positive cofinal frequency

Status: formalized, audited, wired, and indexed. Research paused at the
user's explicit request after completing the started Lean work. No further
sign-symmetry or distribution theorem was started. Scope: BVI arithmetic;
no RH, receiver budgets, or numerical experiments.

## Verification

Canonical leaf:
`formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalMobiusPositiveNegativeSourceFrequency.lean`.
SHA-256: `3fe9891b3ed675fddbced02fb04e82fae7dd259fe53b02a734bbe2a606151013`.

- Corrected complete scratch 17558 passed with empty diagnostics.
- Original-source `lake --old env lean -j 1` passed from `formal/`, exit 0,
  empty diagnostics; fresh olean/ilean emitted.
- All six public declarations passed separate `#print axioms` checks, exit 0:
  only `propext`, `Classical.choice`, and `Quot.sound`. Both final checks
  ran serially in session 42402.
- Leaf wired into the BVI umbrella; index 80412 passed.
- Authoritative lint 32437 exited 1 on two unrelated findings: concurrent
  `CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity` reachability
  and existing root `TransHorizonIncidenceMechanics.lean` placement. No owned
  leaf is named; global lint is not claimed clean.
- Evidence, source hash, exact public-declaration audit, research coverage,
  and index/lint logs: `logs/bvi-sign-frequency-2026-10-18-*`.
- Completed temporary proofs, API probes, retrieval files, logs, and audit
  launcher were removed after archive. No owned process remains running.

## Proved theorem

For every fixed natural B, set C=B+1 and M=(B+2)N. Let P_N and D_N count
the k in [1,M] with s_N(k)>0 and s_N(k)<0 respectively. The proved bound is:

    eventually min(P_N,D_N) >= F(C) N / (4 C^2)
                            >= (6/pi^2) N / (4 C^2),

where F is the already formalized cofinal quadratic profile. All B>=0
are included; this parameterization makes the observation ratio at least
two without an extra premise on B. The sharper liminf formulation
`liminf P_N/N, liminf D_N/N >= F(C)/(2C^2)` is deferred; it is not
claimed as a formalized theorem here.

## Paper proof

For every real x with |x|<=C and C>0,

    x^2 + Cx <= 2C^2 * 1_{x>0},
    x^2 - Cx <= 2C^2 * 1_{x<0}.

For the first inequality, if x<=0 then x(x+C)<=0; if x>0, both
x^2 and Cx are at most C^2. The second follows by replacing x with -x.
Apply these inequalities to the literal sieve source. The verified
bounded-band theorem gives |s_N(k)|<=C throughout [1,(C+1)N] for N>=1.
Summation yields

    Q_N(M) + C S_N(M) <= 2C^2 P_N,
    Q_N(M) - C S_N(M) <= 2C^2 D_N.

Divide by N. The two left sides converge to F(C), since the quadratic
profile is F(C) and the first source moment is zero. F(C)>=6/pi^2>0,
so both inequalities eventually give the displayed half-margin bound.
This produces positive frequency of both actual source signs from proved
arithmetic inputs, rather than assuming a sign or variance budget.

## Dependencies and completed checks

- `abs_sieveSeq_moebiusReal_le_band_width` in
  `CofinalLinearWindowMobiusEnergyAndDefectBounds.lean`.
- `tendsto_sieveL2PrefixEnergy_moebiusReal_linear_horizon` and
  `squarefreeDensity_le_cofinalMobiusQuadraticProfile` in
  `CofinalMobiusQuadraticQuotientProfile.lean`.
- First moment is already implied by `UniformCofinalMobiusPrefixDiscrepancy.lean`;
  the r=0 instance of the new all-odd-moment theorem supplies a direct limit.
- Deep field-filtered query `sieveSeq positive negative cardinality quadratic energy`
  completed partially.
  Broadened hybrid query `source sign count` completed without partial retrieval;
  all candidate and
  source-argument lists were inspected. They expose finite quadratic identities
  and the existing source profile, not this sign-frequency producer. Compiler
  coverage includes stale/source-only entries, so applicability is checked in Lean.
  Both queries and coverage are archived in
  `logs/bvi-sign-frequency-2026-10-18-research.json`.
- Finite indicator-to-cardinality identities, zero cutoffs, positivity
  of constants, and the exact shift C=B+1 all passed Lean checking.

This does not assert equal unweighted sign counts, individual sign-class
densities, or a uniform estimate for a growing horizon ratio. Those are
separate targets, deferred at the user's request. Metadata for the two
preparatory follow-up searches is archived in
`logs/bvi-sign-frequency-2026-10-18-deferred-searches.json`; no further
Lean implementation was started.
