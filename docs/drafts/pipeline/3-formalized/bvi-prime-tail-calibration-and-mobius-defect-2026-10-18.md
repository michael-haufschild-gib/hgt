# BVI prime-tail calibration and the literal Möbius defect

- **ID:** BVI-PRIME-TAIL-CALIBRATION-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4); all 22 public declarations audited
- **Source:** current BVI route, following RW → TH → MSC → RB → SZ rotation.
- **Statement:** A sharp, explicitly attained tradeoff between prime response and successor energy forces a macroscopic signed defect for the unmodified truncated Möbius source.

## Goal and scope

Audit the tempting proposal that the signed LCM and Bézout remainders can be bounded together at square-root size uniformly through the sieve horizon. Work with the actual coefficients, not arbitrary spectral models. This is a scoped input audit, not retirement of BVI and not a proof of RH. Neither field README nor the frontier map may be edited.

## Plan

- [x] Complete corpus search and paper proof, including an explicit positive survivor.
- [x] Formalize the sharp calibration inequality and its attaining arithmetic weights; connect it to the literal Möbius remainder.
- [x] Check the canonical leaf and all public axiom closures; wire the umbrella; refresh index and run lint. Record exact unresolved checks.

## Paper proof

Write s(k)=Σ_{d≤N,d|k} c(d), Y(e)=Σ_{d≤N,e|d} c(d)/d, and

    E(c)=Q_Sel(c)−Q_Bez(c)=Σ_{e=2}^N (φ(e)−μ(e))Y(e)^2.

Every diagonal weight is nonnegative. Set P={p prime : N<2p and p≤N},
H=Σ_{p∈P}1/p, and R(c)=Σ_{p∈P}s(p)^2/p. For p∈P, its only multiple at most N is p, so Y(p)=c(p)/p. Its only divisors are 1,p, so s(p)=c(1)+c(p). The exact prime eigenvalue is φ(p)−μ(p)=p. Consequently

    E(c) ≥ A(c):=Σ_{p∈P}c(p)^2/p.

For every real t≤1, completing each prime square gives the exact identity

    (1−t)E(c)+tR(c)−t(1−t)c(1)^2 H
      =(1−t)(E(c)−A(c))+Σ_{p∈P}(c(p)+t c(1))^2/p ≥0.

This is sharp for every N≥1 and real a: choose c(1)=a, c(p)=−t a on P, and c(d)=0 elsewhere. All nonconstant coordinates outside P vanish, so

    E=t²a²H,  R=(1−t)²a²H.

This explicitly constructs the full supporting family, including empty P and t=0,1. It gives a quantitative cost for altering the prime response, rather than merely forbidding an approximation.

**Refinement audit:** the initial conjecture restricted t to [0,1]. The Lean draft exposed that t≥0 was unused. Returning to the paper identity shows that only 1−t≥0 is needed; the explicit attaining weights work for every real t. The wider statement therefore also includes negative response weights. The recorded corpus comparison concerns the same reserve/response pair and does not identify this sharp negative-parameter family; search completeness remains limited as recorded below. The canonical theorem drops the unnecessary t≥0 premise. No claim about parameters t>1 is made.

For the actual c=μ, s(k)=1_{k=1} on 1≤k≤N. If N≥2 and 1≤M≤N, both Σ_{k≤M}s(k)^2=1 and Σ_{k≤M}s(k)s(k+1)=0; in the latter sum, k=1 uses s(2)=0, while k≥2 uses s(k)=0, so no unproved condition at N+1 is needed. The existing two exact finite-prefix decompositions therefore give

    signedLcmFractDefect(N,M,μ)+bezoutSawtoothRemainderForm(M,N,μ)
       = M E(μ)−1.

Since μ(p)=−1, R(μ)=0 and E(μ)≥H. Thus the combined signed remainder, even before taking absolute values, is at least MH−1. At M=N, N/p≥1 on P, so it is at least #P−1. This is an arithmetic lower bound with no sign, RH, or cancellation premise.

### Growth and the scoped no-go — paper proof

At N=2n, P is exactly the set of primes in (n,2n]. The existing unconditional theorem `HTGeometry.eventually_primeCount_window_ge` gives, eventually,

    #P ≥ n/(2 log n),
    moebiusCombinedPrefixDefect(2n,2n) ≥ n/(2 log n)−1.

Fix α<1 and any real C. The elementary logarithmic limits give

    ((C(2n)^α+1)log n)/n
      = C·2^α·log n/n^(1−α)+log n/n →0.

Eventually this is less than 1/2, with log n>0. Hence the displayed defect is strictly greater than C(2n)^α. No eventual upper bound C N^α can hold on all natural cutoffs. This proof uses the established PNT window lower bound, not a newly assumed prime-density input. **[PROVED HERE]** on paper and certified in the canonical Lean leaf together with the finite identities.

## No-go closure and positive survivor

- **Scoped obstruction:** a uniform sublinear power bound for the *unrenormalized* combined remainder of the literal Möbius coefficients, including M=N, is incompatible with the displayed prime lower bound and PNT.
- **Positive survivor:** exact, sharp prime-response/successor-energy tradeoff, with explicit attaining weights and literal Möbius specialization. The nonconstant pole-free diagonal reserve survives the negative audit.
- **New insight:** suppressing this reserve costs a quantitatively fixed change in actual prime responses. A BVI cancellation theorem must retain the large deterministic cancellation with its diagonal main term, restrict its horizon, or pay the source modification; separate or combined raw smallness at M=N is a false target.
- **Status:** dependency-closed paper proof and exact Lean formalization complete; all 22 public axiom closures checked. The sharp reserve/response inequality and its explicit attaining weights are the certified positive survivor. BVI and RH remain open.

## Corpus audit and verification

- Read current field READMEs, frontier, STATUS, and relevant BVI memories. External BVI work covers generic moments, prefix duality, reconstruction, and integral prefix lattices; this file has a disjoint source-calibration objective.
- Deep search completed: `scripts/formal_tools.py research "Bézout signed sawtooth remainder Möbius cancellation successor prefix" --mode deep --budget-seconds 300 --json`. Partial result: final successor query/reranking unfinished; all 73,950 inventoried files indexed, no inventory errors; compiler metadata predominantly pending/source-only. The runtime reported a reranking deadline. Candidate lemmas, source arguments, proof ideas and ingredient sets were inspected; they supplied generic Möbius inversion, not this calibration theorem. No semantic completeness claim.
- Follow-up lexical query `"selbergMultiplesCoord" prime` returned no hits. Direct source inspection verified the actual prime eigenvalue and exact finite-prefix identities. Broad text searches were narrowed after output truncation; no exhaustive global novelty claim is made.
- Prior inputs: exact φ−μ diagonal, prime eigenvalue p, exact signed prefix decompositions, and Möbius divisor inversion. Those ingredients are not claimed as new.
- Broadened lexical search (`prime Selberg tail --any --module BiScaleUncertainty`) returned 1,034 hits, with 20 ranked results inspected. Relevant source checks covered the existing generic tail decomposition, its ℓ¹-square upper bound, the Barban–Vehov Selberg pinch, and the von Mangoldt tail bound. Those results concern the Selberg form or a different weight. The current theorem concerns the pole-free successor reserve together with the literal terminal-prime response and an explicitly attaining family; the Möbius lower bound needs no separate estimate on its harmonic mode. Ranked search is not exhaustive novelty certification.
- No numerical experiments, web research, or external novelty claims.

## Log

- 2026-10-18 — Created before Lean implementation; precise finite theorem and asymptotic follow-up separated.
- 2026-10-18 — Completed dependency-closed paper proof, explicit attaining source family, and all-sublinear-power consequence. Drafts: `/tmp/hgt_bvi_prime_proof.lean` and `/tmp/hgt_bvi_prime_growth.lean`.
- 2026-10-18 — Shared build temporarily removed `DirichletEvenThetaAxisKernel.olean`; import probe exited 1. Its external rebuild was observed and left untouched. Copying compiled imports into an owned snapshot before continuing; no proof has yet passed its final Lean audit.
- 2026-10-18 — First complete finite scratch check exited 1 with three local elaboration errors (a substituted binder name, strict/non-strict transitivity, and a remaining conditional in a prime square). Corrected all three. Mathlib API probes in that scratch produced no errors. Combined finite/growth scratch now runs as `/tmp/hgt_bvi_prime_combined.lean`, using `/tmp/hgt-bvi-prime-shared.setup.json` and the stable hard-linked `/tmp/hgt-bvi-prime-shared-cache`. The previous owned copied cache was removed after its Lean process exited. Planned canonical result is one leaf, `PrimeTailCalibrationAndMobiusDefect.lean`; canonical compilation, axioms, umbrella wiring and lint remain pending.
- 2026-10-18 — Combined scratch exited 1 with the finite proof block accepted and growth diagnostics confined to one incorrect namespace plus a redundant tactic. Source inspection found `isLittleO_log_rpow_atTop` at the root namespace. Created the canonical leaf, widened the calibration parameter to every real t≤1, corrected the growth name and removed redundant tactics. A separate mathlib API probe precedes the canonical audit. No canonical success or axiom closure is claimed yet.
- 2026-10-18 — The separate growth API probe exited 0 with an empty diagnostic log. Canonical `lake --old env lean -j 1 --setup /tmp/hgt-bvi-prime-shared.setup.json -o … -i … GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean` is running, with diagnostics in `/tmp/hgt-bvi-prime-final.log`. Its source fingerprint and full command are in `/tmp/hgt-bvi-prime-compile-start.json`. The all-22-public-declaration audit is prepared in `/tmp/hgt_bvi_prime_axioms.lean`. Next fresh research cycle must rotate away from BVI; this cycle ends after certification and bookkeeping.
- 2026-10-18 — Canonical leaf compilation exited 0 with an empty diagnostic log under Lean 4.32.2. Protected its `.olean` and `.ilean`; source hash remained `e9e97c648cc82d37ea8aeec58d3dbae8029ecd1f91931fb1159c0b503c33f7b9`. Wired the finished leaf into the BVI umbrella, preserving the concurrent integral-lattice import. The separate axiom audit is now running via `/tmp/hgt-bvi-prime-axioms.setup.json`, whose module name differs from the leaf. Formal status remains pending that audit and lint.
- 2026-10-18 — Separate axiom audit exited 0: all 22 public declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Checked the actual types of seven capstones, including the wider t≤1 bound and the quantified no-sublinear-budget theorem. Moved this exact result to `3-formalized`. Initial lint found a stale generated overview; refreshed the index. The final lint reports only the unrelated unreachable BVI module recorded below.

## Formal certificate

- Canonical source: `formal/GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean`.
- Canonical `lake --old env lean` audit with `.olean` and `.ilean` output: **exit 0**, empty diagnostic log, Lean 4.32.2.
- Separate `/tmp/hgt_bvi_prime_axioms.lean` audit: **exit 0**, all **22** public declarations inspected; axiom union exactly `propext`, `Classical.choice`, `Quot.sound`.
- Source SHA-256: `e9e97c648cc82d37ea8aeec58d3dbae8029ecd1f91931fb1159c0b503c33f7b9`, unchanged through compilation and audit.
- Umbrella import added; generated API, gaps, overview and search index refreshed. Imports used a stable owned artifact snapshot because shared builds were rebuilding transitive dependencies.
- `scripts/formal_tools.py lint --check-generated`: **exit 1**. Sole error after refresh: `owned module unreachable from theorem-area umbrella GaloisForLFunctions.BezoutValuationIncidence: GaloisForLFunctions.BezoutValuationIncidence.DilatedCellScalingAndSecondOctaveFermiJumpBridge`. This module is outside this contribution. Existing large-file warnings also remain. No clean global-lint claim is made.
- Audit commands, output fingerprints and declaration-by-declaration axiom records: `/tmp/hgt-bvi-prime-audit-manifest.json`. Logs: `/tmp/hgt-bvi-prime-final.log`, `/tmp/hgt-bvi-prime-axioms.log`, `/tmp/hgt-bvi-prime-index-final.log`, `/tmp/hgt-bvi-prime-lint-final.log`.

**Next rotation:** select a different live-route family. This cycle closes the precise raw-Möbius input obstruction and its sharp positive survivor; it does not retire BVI or establish RH.
