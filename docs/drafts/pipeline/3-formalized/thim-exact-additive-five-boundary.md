# Exact additive boundary for the damped unit envelope

- **ID:** thim-exact-additive-five-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Statement:** For every ε≥0 and 2≤k<5(N+1), the damped response has absolute
  value at most one. The universal additive buffer after 5N is exactly four.

## Plan and gates

1. [x] Reread objective and all 311 README lines; inspect current source and corpus.
2. [x] Close paper proof, including zero horizon and unit residual quotient.
3. [x] Formalize sharp tail compression, envelope, additive classification, and transport.
4. [x] Actual-source Lean audit, all axiom closures, wiring/index/lint, ledger/memory, cleanup.

`update_plan` unavailable; this card tracks work. README stays read-only.

## Paper proof [PROVED HERE]

If d divides k and d>N, then d≥N+1. Thus its complementary quotient q=k/d
is at most B whenever k<(B+1)(N+1). Conversely, under BN<k, every divisor
q≤B has k/q>N. Therefore throughout BN<k<(B+1)(N+1), the exact tail is
the sum of c(k/q) over divisors q≤B. This integer bound improves the previous
k≤(B+1)N cutoff without changing the deletion formula.

For k≤5N use the proved envelope. For 5N<k<5(N+1), N=0 gives the empty sum.
For N≥1 the B=4 formula applies. If 4 divides k, write k=4u and absorb the
repeated factor two: response equals that at 2u≤5N. Otherwise the only deletion
channels are 1,2,3. Zero, one, or two distinct prime channels are controlled by
the established terminal/prime/two-prime identities. Their residual u is positive.
Previously stated contraction lemmas required u≥2; the missing u=1 case closes
exactly: single-prime deletion is zero, and two-prime deletion is one since both
the full response and terminal coefficient at one equal one. This covers every
small horizon without numerical evaluation.

For every real b, the universal bound on integer endpoints 2≤k≤5N+b holds
iff b<5. Sufficiency is the strict bound above; necessity uses the existing
cofinal prime family N=6p−1, k=30p=5N+5, response two. For natural buffers b,
this is exactly b≤4. Both classifications hold for literal μ and uniformly over
all ε≥0. At horizons in the counterfamily, 5N+5 is therefore the first offending
endpoint. Radical/power invariance extends the certified endpoint range, and
polarization yields 2D≤−E≤0 for prefixes and rough-start windows. Zero horizon
is handled directly, so transport does not smuggle in N≥1.

## Verification

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ExactAdditiveEnvelopeAndFirstFailure.lean`.
- SHA256: `670e7dc055eccd500f09a491a0d6ab5ebeb382130d13b7754a503139d214ceb3`.
- Full scratch proof and actual-source `lake --old env lean` both exited 0
  without warnings. All 28 public theorems and three private helpers have
  exactly `{propext, Classical.choice, Quot.sound}`; no added axioms or proof gaps.
- `logs/thim-additive-audit.json` passed all 31 closures, 28 baseline docstrings
  and API entries, exact source/dependency hashes and fresh artifacts, unique
  umbrella import, MainTheorems reachability, whitespace and prohibited declarations.
- Evidence: `logs/thim-additive-{lean,axioms,index,lint}.txt`. Final
  `scripts/formal_tools.py lint --check-generated` exits 1 for seven external
  integration findings: one RHTower leaf, one BiScaleUncertainty leaf, four
  BezoutValuationIncidence leaves, and existing THIM root registration. Exact
  errors are retained in the audit JSON. No new-leaf, prohibited-declaration,
  or stale-generated-file finding in the final run.
- First pass found stale API/overview indexes during concurrent work; logs
  preserved as `logs/thim-additive-{index,lint,lint-exit}-first.txt`. One refresh
  and complete lint rerun cleared those findings.
- Nine owned scratch files removed; every owned job terminal. README unchanged.
  No full/umbrella build, numerical experiment, heartbeat override, commit, or push.
- Ledger updated; prior ratio-five and failed-route cards now reference the
  sharp additive survivor. Continuing research goal remains active.

## Baseline and limitations

Classical baseline: exact integer Dirichlet-hyperbola truncation, multiplicative
Möbius deletion, radical invariance, and discrete polarization. The equivalent
classical statement is |Σ_{d|k,d≤N} μ(d)d^(-ε)|≤1 for k<5(N+1).
Classification: New formulation, not an external novelty claim. The identical
truncated Möbius sum and prime deletion recursion appear in Helfgott–Thompson,
[Proposition 3.2](https://link.springer.com/article/10.1007/s40993-022-00408-8).
Observation/shifted-correlation baselines: [TH10](https://arxiv.org/abs/1009.5281),
[CMS16](https://arxiv.org/abs/1612.03136).

Corpus query `sharp additive five horizon buffer endpoint envelope first overflow
five N plus four Mobius` returned partial=false, 74085 inventoried files, zero
pending, generation1454178; compiler coverage mixed/source-only. All 20 candidate
lemmas and 20 source arguments inspected. Prior ratio-five/counterfamily theorems
found; no exact additive envelope found. Exhaustive field-source search agrees.

This sharpens only the endpoint-unit-envelope boundary. It does not establish
positive renormalized defects beyond that boundary, nor the optimal cutoff for
each fixed positive damping exponent. Broader research goal remains active.
