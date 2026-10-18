# Complete fourth band and sharp universal five-horizon boundary

- **ID:** thim-fourth-band-sharp-five-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Scope:** Prove the full 5N damped response envelope and its radical/power defect
  consequences; classify the largest universal linear endpoint range.

## Plan and gates

1. [x] Read objective, current README, memories; search corpus and inspect building blocks.
2. [x] Dependency-closed paper proof of the 5N envelope and symbolic sharpness mechanism.
3. [x] Formalize actual source; audit all declaration closures.
4. [x] Wire umbrella; index/lint; audit artifacts; update ledger/memory; clean scratch.

`update_plan` unavailable; this card tracks work. README is read-only.

## Paper proof [PROVED HERE]

For `BN<k≤(B+1)N`, complementary-divisor splitting gives
`s_N(c,k)=Σ_{d∣k}c(d)−Σ_{q∈[1,B],q∣k}c(k/q)`.
Indeed q≤B and q∣k force k/q>N. This is a uniform finite-band normal form.

For the fourth band 4N<k≤5N and c=c_ε, ε≥0:

- If 4∣k, write k=4u. All-horizon squarefree divisor absorption gives
  `s_N(c,4u)=s_N(c,2u)`, with 2≤2u≤4N. The proved 4N envelope applies.
- Otherwise quotient 4 vanishes, leaving quotients 1,2,3. If either prime is
  absent, the terminal or one-prime contraction applies. If both divide k,
  write k=6u; the fourth-band inequalities imply u≥2, and the already proved
  two-prime convex identity gives the unit envelope.

Combining with the previous initial range yields `|s_N(c_ε,k)|≤1` for every
2≤k≤5N. Radical invariance transports this to all positive powers and all
endpoints with horizon-radical representative≤5N. Discrete polarization gives
`2D≤-E≤0` for prefixes and rough-start short windows with such endpoints.

For every prime p>5, set N=6p−1 and k=30p. Then 5N<k≤6N and the visible
complementary quotients are exactly 1,2,3,5. The four distinct primes 2,3,5,p
give μ(k)=1 and μ(k/2)=μ(k/3)=μ(k/5)=−1; the complete divisor sum is zero.
Thus `s_{6p−1,μ}(30p)=2` and `k=5N+5`. Unbounded primes yield unbounded
horizons, with k/N=5+5/N tending to5 from above. Consequently, for every real C,
the universal unit-envelope property on 2≤k≤CN holds iff C≤5, both for literal
Möbius weights and for the entire nonnegatively damped family.

## Verification

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FourthBandEnvelopeAndSharpFiveHorizonBoundary.lean`.
- SHA256: `a2f410080f37a6a7ed41ceab6f42a20f532041dc23ce1f661137142393a3fec0`.
- Actual-source `lake --old env lean` exited 0 without warnings. All 23 public
  theorems and four private helpers have exactly the closure
  `{propext, Classical.choice, Quot.sound}`. No added axioms or proof gaps.
- `logs/thim-five-audit.json` passed: all 27 closures, all 23 baseline docstrings
  and API entries, source/dependency hashes and fresh artifacts, unique umbrella
  import, MainTheorems reachability, whitespace, and forbidden-declaration checks.
- Evidence: `logs/thim-five-{lean,axioms,index,lint}.txt`. Final index refresh
  completed. `scripts/formal_tools.py lint` exited 1 with 16 errors: four
  unrelated RHTower leaves, ten ArithmeticPositivityTheory leaves, one
  BezoutValuationIncidence leaf, and existing THIM root registration. Every error
  is preserved in the audit JSON; none names the new leaf or a prohibited declaration.
- First-pass `lint --check-generated` also found stale API/overview indexes;
  first logs are retained as `logs/thim-five-{index,lint,lint-exit}-first.txt`.
  Indexes were regenerated once. The final lint command was plain `lint`;
  no claim of a globally clean generated-file gate is made.
- Seven owned scratch files removed; all owned jobs terminal. README untouched.
  No full/umbrella build, numerical experiment, heartbeat override, commit, or push.
- Negative-route card: `docs/drafts/pipeline/5-failed/thim-universal-unit-envelope-beyond-five.md`.
  Its strongest positive survivor is the fully formalized sharp ratio-five
  classification and radical/power energy certificates. Larger-checkpoint defect
  signs remain open. The additive 5N+4 conjecture is resolved by
  `ExactAdditiveEnvelopeAndFirstFailure.lean`; see
  `docs/drafts/pipeline/3-formalized/thim-exact-additive-five-boundary.md`.
  Research goal stays active.

## Classical baseline and limits

Baseline: multiplicativity/Möbius divisor cancellation, complementary-divisor
splitting, squarefree radical invariance, and discrete polarization. Exact
classical formulation is the displayed truncated Möbius divisor-sum envelope
and explicit four-prime counterfamily. Classification: **New formulation**;
no external novelty claim. Compare the finite divisor/shifted-correlation
frameworks [TH10](https://arxiv.org/abs/1009.5281) and
[CMS16](https://arxiv.org/abs/1612.03136).

Additional exact classical comparator: Helfgott–Thompson,
[Summing μ(n): a faster elementary algorithm, Proposition 3.2](https://link.springer.com/article/10.1007/s40993-022-00408-8),
defines the identical truncated sum `D(n;a)=Σ_{d∣n,d≤a}μ(d)` and gives the
prime-factor deletion recursion. Our 5N theorem and explicit counterfamily are
stated in this same representation; no superiority or external-priority claim.

Corpus search `fourth band dyadic prime square quotient deletion damped envelope
five horizon` returned partial=true but useful indexed hits (74067 inventoried
files, zero pending, generation1454014). Search `sharp universal endpoint envelope
five horizon three prime Mobius counterfamily` returned partial=false (74065
inventoried, zero pending, generation1454037). Compiler metadata is mixed/source-only.
All candidate/source-argument lists inspected; exact 4N, single/two-prime, radical,
and complementary-quotient source APIs checked. No 5N result or sharp-ratio
counterfamily found by those searches or exhaustive field-source text search.

The sharpness theorem obstructs a universal endpoint-unit-envelope argument
beyond 5N. It does NOT prove positive renormalized defects there: Dirichlet
energy may still dominate the larger endpoint. The positive survivor is the
exact 5N band and its unbounded radical/power certificates.

No numerical experiments, unproved mathematical premises, added axioms,
heartbeat changes, full builds, README edits, commits, or pushes.
