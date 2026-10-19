# Complete critical prime limit of one factorial source

- **ID:** APT-CRITICAL-PRIME-LIMIT
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** apt-critical-collar-resonance-2026-10-18.md; existing factorial phase and critical prime-admission leaves.
- **Statement:** Determine the full critical physical correlation limit, including every harmonic and prime power, as the actual factorial source scale tends to infinity.

## Goal

Replace the earlier one-harmonic resonance observation by an exact limit of the complete
actual-source prime channel. Track its dyadic sign law and the slow phase retained by the
physical weight. No positivity premise is allowed. This does not assert positivity of the
complete Weil form. Accepted significant contributions remain **0/100** pending the original
novelty and significance gate.

README remains read-only. No numerical experiments, new axioms, heartbeat increases, full
builds, commits or pushes. One owned foreground Lean invocation at a time; use targeted
dependency builds and final actual-file audits. Preserve concurrent source changes.

## Gates and plan

- [x] Exact native source, normalization, and prospective limit specified.
- [x] Corpus search conducted; concrete prior dependencies inspected.
- [x] Complete and independently check every paper-proof step below.
- [x] Formalize the actual-source endpoint and exact dyadic classification.
- [x] Pass targeted builds, actual-file and axiom checks; refresh the public index.
- [x] Run the global lint gate and record its unrelated failures without claiming a pass.
- [ ] Audit significance and external priority before counting any contribution.

## Exact statement and paper argument

Let `Φ_N(v)=P₀(λ_N v)-P₀(Nv)` be the existing actual factorial phase, with `N≥1`.
Write `w_k=χ(k)/k²`, `w_0=0`, where `χ` is 1 on odd integers, -1 on integers
congruent to 2 modulo 4, and zero on multiples of 4. Existing theorems give

`Φ_N(v)=-(2/π²) Σ_(k≥1) w_k [cos(2πkλ_N v)-cos(2πkNv)]`,

with absolute convergence, and `λ_N=N+1/12-e_N`, `0≤e_N≤1/(140N)`.
Define

`K(a)=∫_1^∞ v⁻² cos(2πav)dv`, `J(a)=1-K(a)`,

`C_N(r)=∫_1^∞ v⁻² Φ_N(v) Φ_N(rv)dv` for a positive integer `r`.
The proposed exact limit is

`C_∞(r)=(4/π⁴) Σ_(l≥1) w_(rl) w_l J(rl/12)`.

1. The weight has mass one. Dominated convergence proves continuity of `K`; evenness
   follows from cosine parity. The existing cosine Riemann--Lebesgue theorem gives
   `K(a)→0` as `|a|→∞`, applied to the zero-extended integrable weight. Also
   `0≤J(a)≤2`, and `J(a)>0` for `a≠0`: its nonnegative continuous integrand is
   strictly positive on some interval inside `(1,∞)`.
2. Expand the product of the two cosine differences in harmonics `k,l`. If `k≠rl`,
   every difference frequency is `(k-rl)N+O(1)`, and every sum frequency diverges;
   all eight cosine integrals vanish. If `k=rl>0`, the two same-branch differences
   are zero, the two mixed differences tend to `±k/12`, and all sum frequencies
   diverge. The resulting integral tends to `1-K(k/12)=J(k/12)`.
   Zero harmonics vanish identically.
3. Each harmonic-product integral has absolute value at most 4. The summable
   majorant `4|w_k||w_l|` permits both integration of the full double series and
   interchange of its limit. Reindex the surviving diagonal `k=rl` to obtain the
   displayed formula. This is a full-profile identity, not a harmonic truncation.
4. The existing fixed-source critical prime theorem, specialized to one coefficient,
   gives `|C_N(r)|≤(168+96/N)/r≤264/r`. Hence the complete integrated prime atoms
   are bounded by `264 Λ(r)/r²`, an existing summable majorant. Dominated convergence
   on the prime series therefore gives

   `lim_(N→∞) Σ_(r≥2) Λ(r) C_N(r)/r = Σ_(r≥2) Λ(r) C_∞(r)/r`.

   For `g_N(x)=1_(x≤0)e^(x/2)Φ_N(e^(-x))`, the existing change of variables gives
   `autocorr(g_N)(log r)=r^(-1/2) C_N(r)`. Thus this is exactly the critical prime
   channel in logarithmic coordinates. The formal endpoint must include or reuse
   a public actual-source bridge; it must not rely on an unnamed private identity.
5. The multiplier gives the exact proposed sign classification: `C_∞(r)>0` for
   odd positive `r`; `C_∞(r)<0` when `r≡2 (mod 4)`; and `C_∞(r)=0` when `4|r`.
   For odd `r`, `χ(rl)χ(l)=χ(l)²`. For `r≡2 (mod 4)`, the product is -1 on odd
   `l` and zero on even `l`. The `l=1` term makes the first two signs strict.
   In the prime channel, 2 has the opposite sign to all odd prime powers, and
   every higher power of 2 has zero limiting contribution.

The logarithmic prime coefficient here is `Λ(r)/sqrt(r)` before the correlation
change of variables, hence `Λ(r)/r` afterwards. Losing that additional half power
would change the claimed theorem. The raw boundary Mellin integral and full Weil
positivity remain separate questions.

## Reuse and priority audit

- `FactorialPhaseHarmonicLayers.lean` supplies the exact full Fourier expansion,
  absolute summability, and the profile bound. These are baseline.
- `FactorialAffineClockResonance.lean` supplies the actual defect estimate and
  earlier one-harmonic physical/Bohr limit contrast. It does not itself assert
  this complete correlation or prime-series limit.
- `FactorialCriticalPrimeAdmission.lean` supplies the source-dependent correlation
  bound and absolute prime admission. Its constant specializes uniformly to 264.
- `FactorialPhaseWindowAndPhysicalRieszBounds.lean` already proves window coercivity
  and physical Riesz bounds. New wrappers around those bounds are not significant.
- `RHTower/WeilPhiDoobDivisorEnergy.lean` already reindexes the complete theta-ground
  Doob energy by divisor graphs; its bounded quotient and source hypotheses differ.
- All 41 `factorial Riesz`, 31 APT-filtered `factorial limit`, 47 `periodic averaging`,
  and 86 `Riemann Lebesgue` lexical hits were paginated and screened. The inspected
  `RHTower.tendsto_integral_mul_cos_atTop` requires only an integrable weight.
- Deep affine-scaling retrieval completed with unavailable semantic-coverage metadata;
  many candidates concern unrelated factorial functions. Earlier logarithmic-diagonal
  retrieval was partial. No empty or partial retrieval establishes novelty.
- Generic fast/slow periodic averaging is classical: Allaire, *Homogenization and
  Two-Scale Convergence* (1992), Lemma 1.3 and Section 5,
  https://www.cmap.polytechnique.fr/~allaire/two-scale.pdf. The paper was opened and
  the relevant statements inspected. This mechanism is not new contribution credit.
- Dilated-function Riesz theory and its Dirichlet-series formulation are also prior:
  https://arxiv.org/abs/math/9512211 and https://arxiv.org/abs/1708.08545. Abstracts
  were inspected; neither abstract alone settles priority for the exact native limit.

## Continuation state

The complete all-harmonic correlation limit now passes in `/tmp/apt_critical_limit.lean`
(exit 0, before adding the strict-positivity lemma). It proves actual correlation
integrability, the exact integrated double-series identity, and the full limit via
the existing Tannery theorem; no finite harmonic truncation or unproved public premise
is left in that scratch endpoint. API probes exposed a nonexistent `Real.cos_mul_cos`;
the proof instead uses the verified `Real.cos_add` and `Real.cos_sub`. The generic API
probes need explicit universe levels in this toolchain, now supplied.

The strict positivity lemma also passed. Installed the correlation package as
`formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalCorrelationLimit.lean`
(531 lines), with an APT umbrella import. Added the public
`criticalFactorialSource_correlation_eq` wrapper to the existing critical-admission leaf;
it reuses the private proof and exposes only public source definitions. Both targeted
leaf builds passed; `/tmp/apt_critical_limit_dependencies_build.log` records the result.

The complete prime-series limit and exact dyadic sign law passed in
`/tmp/apt_critical_prime_limit.lean` (exit 0). All nine endpoint axiom probes report only
`propext`, `Classical.choice`, and `Quot.sound`. Installed the proof as
`formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeLimit.lean`
and added its APT umbrella import. Its targeted leaf build passed. Direct actual-file
audits of the new correlation leaf, modified admission leaf, and new prime-limit leaf
all exited 0 with empty diagnostic logs. The actual-import audit checked eleven public
endpoints; every axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`.
The generated index contains all fifteen new declarations/wrappers. Completed scratch
sources can now be removed; diagnostic logs and search JSON remain the evidence.
The broader finite-pattern two-scale conjecture remains in the parent card. Contribution
count is unchanged.

The refreshed hybrid query `factorialCriticalCorrelation` recovered the new source and
the existing physical/logarithmic bridge. All 20 candidate lemmas and 20 source arguments
were screened. Its retrieval completed, but coverage reports an older snapshot and
unmeasured semantic coverage; refresh was deferred to the running background indexer.
These limitations prohibit treating an empty query as evidence of novelty. The four
earlier `prime limit` lexical hits were checked at their exact statements: they are
smoothing-radius limits at fixed arithmetic scale, not the present scale-to-infinity
limit. The focused deep search for prior factorial-scale prime/correlation limits completed
in `/tmp/apt-critical-prime-limit-prior-deep.json`: all twenty candidates and twenty source
arguments were screened. It recovered existing bounds, phase expansions, dyadic
classification, and fixed-scale smoothing work; semantic coverage remains unmeasured.

The broader APT lexical union query `dyadic vonMangoldt divisor harmonic prime --any`
was paginated through all thirteen pages: stable total 241, 241 distinct hits screened.
In particular, `factorialSpanTest_high_scale_weil_coercivity` was checked at its actual
statement: it assumes the archimedean lower bound and concerns the `exp(3x/2)` span test.
It is not an unconditional theorem for the present `exp(x/2)` critical source.

## Verification evidence

- Targeted leaf build: `/tmp/apt_critical_prime_limit_build.log`, exit 0.
- Actual-file audits: `/tmp/apt_actual_FactorialCriticalCorrelationLimit.log`,
  `/tmp/apt_actual_FactorialCriticalPrimeAdmission.log`, and
  `/tmp/apt_actual_FactorialCriticalPrimeLimit.log`; all exit 0, empty logs.
- Actual-import axiom audit: `/tmp/apt_critical_prime_limit_actual_axioms.log`, exit 0.
- Public index refresh: `/tmp/apt_critical_prime_limit_index.log`, exit 0.
- Global lint: `/tmp/apt_critical_prime_limit_lint.log`, exit 1. Only two errors:
  `TransHorizonIncidenceMechanics.FermiHomogeneousEnergyAndPronicComparison` and
  `TransHorizonIncidenceMechanics.FermiPrimeExponentGramBounds` are unreachable from
  their theorem-area umbrella. These concurrent files are outside this task's scope.
- No placeholder proof, new axiom, unsafe declaration, or heartbeat change was introduced.
  Scoped whitespace validation passed.

## Significance decision

This is an unconditional native full-series asymptotic, with a strict arithmetic sign
classification. The averaging mechanism and dominated-convergence machinery are classical;
the corpus supplies the source expansion and prime admission. Neither the full Weil sign
nor a decisive finite-source positivity mechanism follows yet. Hold the significant-result
count at **0/100**. The next candidate is an exact prime/harmonic divisor regrouping and its
sharp coefficient classification; that candidate must pass its own paper and novelty audits.

## Log

- 2026-10-19 — Candidate separated from the verified affine comparison; full-series
  proof mechanism and exact dyadic classification recorded. Contribution count unchanged.
