# Cofinal arithmetic control of the renormalized BVI defect

- **ID:** BVI-COFINAL-ARITHMETIC-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / source audit
- **Statement:** Develop unconditional estimates for the actual truncated Möbius incidence source, uniform as cutoff and observation horizon grow, without assuming MC/PM receiver budgets.

## Scope and plan

- [x] Read the task attachment and every line of the field README; leave README unchanged.
- [x] Read project instructions and current source-calibration obstruction.
- [x] Search the live Lean corpus; inspect actual source statements rather than README summaries.
- [x] Derive and audit an arithmetic cofinal estimate on paper.
- [ ] Formalize each dependency-closed survivor with no assumed analytic budget.
- [ ] Audit original leaf with `lake --old env lean`; audit public axiom closures, wire umbrella, regenerate index, run lint, clean owned scratch artifacts.
- [ ] Continue conjecturing toward control of the unresolved interior/energy quantity. A boundary-only estimate does not close that target.

## Current authoritative facts

For `s_N(k) = sieveSeq N moebiusReal k`, the established exact identity is

    2 R_N(M) = -sum_{1 <= k <= M} (s_N(k+1)-s_N(k))^2
               + s_N(M+1)^2 - s_N(1)^2,

where `R_N(M) = sieveRenormalizedPrefixDefect N M moebiusReal`.
The raw combined defect has a macroscopic positive term at M=N; bounding it
by a sublinear power without subtracting its reserve is already disproved.
First-octave sign laws do not control all cofinal horizons.

## Conjecture loop

### C1: Uniform arithmetic endpoint control

The positive part of R_N(M) should be controlled uniformly in N by the
square of the number of squarefree divisors of M+1. A divisor-growth theorem
would then give decay after every positive power normalization, uniformly
over arbitrary cutoff schedules. This is a candidate *one-sided* estimate;
it cannot bound the negative energy term and must not be called closure of
the full cofinal cancellation problem.

### C2: Identify the independent interior estimate

After C1, isolate the exact arithmetic quantity still needed for a two-sided
or energy estimate. Reject any conjecture that merely assumes a renamed
MC/PM budget, fixes the cutoff before taking the horizon limit, or averages
over a full lcm period instead of controlling the requested cofinal regime.

### C3: Prime-to-square-zero edges force polynomial-horizon negativity

**Paper mechanism:** for N>=2, every prime p in (N,2N] is odd and satisfies
s_N(p)=1. One of p-1,p+1 is divisible by four, hence has zero Möbius value;
that neighboring response is zero throughout [N,2N]. Choose the edge p-1
when p=1 mod 4, and p when p=3 mod 4. Each selected gradient square is one.
Selected edges are distinct: their residues are respectively 0 and 3 mod 4,
and each branch is injective. All lie between N and 2N-1.

Thus for every M>=2N the accumulated gradient energy is at least the number
of primes in (N,2N], with no periodic averaging or receiver hypothesis.
The corpus already proves that this count is eventually >=N/(2 log N).
Combining this with C1 and the exact polarization law should give, for each
fixed positive integer A, eventually uniformly on 2N<=M<=N^A,

    R_N(M) <= -N/(8 log N).

The endpoint square is O((M+1)^delta); take delta=1/(2A), so it is
O(sqrt N), eventually smaller than N/(4 log N). This is a genuine moving
cutoff/horizon estimate for the literal source. It is a signed coercivity
estimate, not an upper bound for the energy or the interior martingale.
Formalization and precise constants pending. Do not claim this theorem yet.

The deep novelty query `Mobius prime adjacent squarefree zero Dirichlet
energy lower` completed; returned source candidates require direct checking.

### Dependency-closed paper proof of C1 and C3

Write E_N(M)=sum_{k=1}^M(s_N(k+1)-s_N(k))^2 and tau(n)=#divisors(n).
The triangle inequality on the actual divisor sum gives |s_N(n)|<=tau(n),
uniformly in N, for n>=1. Since |s_N(1)|<=1, exact polarization gives

    |2 R_N(M)+E_N(M)| <= tau(M+1)^2+1,
    max(0,R_N(M)) <= tau(M+1)^2/2.

The corpus theorem `RHTower.card_divisors_le_const_mul_rpow` proves, for
each delta>0, tau(n)<=C_delta n^delta with no analytic assumption. Squaring
at exponent delta/2 proves tau(n)^2+1<=C'_delta n^delta. This is classical
arithmetic infrastructure; the uniform transfer to BVI is not by itself a
novelty claim or closure of the interior estimate.

For C3, the selected edge e(p) is p-1 for p=1 mod 4 and p for p=3 mod 4.
In the first branch e(p)=0 mod 4; in the second e(p)=3 mod 4. Each branch
is injective and the images are disjoint. Every selected edge lies in
[N,2N-1], its square increment is 1, and all remaining square increments
are nonnegative. Therefore E_N(M)>=#(primes in (N,2N]) for M>=2N.
The existing unconditional PNT window theorem gives E_N(M)>=N/(2 log N)
eventually, uniformly over all M>=2N.

Fix integer A>=2, set delta=1/(2A), and choose C with
|2R_N(M)+E_N(M)|<=C(M+1)^delta. For 2N<=M<=N^A and N>=2,

    (M+1)^delta <= (2N^A)^delta = 2^delta sqrt(N).

Since log(N)/sqrt(N)->0, eventually C*2^delta*sqrt(N)<N/(4log(N)). Thus
2R_N(M)<-N/(4log(N)), proving the stated -N/(8log(N)) bound uniformly on
the whole polynomial window. All dependencies are already source-proved;
the Lean certificate is pending. **[PROVED HERE] on paper.**

### C4: Replace prime density by odd squarefree density

The edge mechanism does not require primality: any odd squarefree k in
(N,2N] has |s_N(k)|=1 and a neighboring multiple-of-four zero. Distinct
odd k again select distinct edges. The source theorem
`RHTower.Sieve.abs_sum_moebius_sq_Icc_sub_le` gives squarefree density 6/pi^2
with O(sqrt N) error. A positive-density odd-squarefree lower bound should
upgrade E_N(M)>=N/(2log N) to cN, and the polynomial-window bound to -c'N.
The stronger corpus input `RHTower.Sieve.tendsto_window_coprime_squarefree_density`
at p=2 gives the exact odd-squarefree density 4/pi^2 directly. It is proved
by the elementary squarefree divisor expansion with a square-root truncation
error, with no MC/PM receiver. Its source is
`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeSquarefreeDyadic.lean`.

**[PROVED HERE] on paper:** choose the same edge e(k) for every odd squarefree
k in (N,2N]. Now s_N(k)^2=1, while the neighboring multiple of four has
response zero; the selected edge square remains 1 regardless of the sign.
The edge map is injective for all positive odd k, not only primes. Thus

    E_N(M) >= #(odd squarefree k in (N,2N])  (M>=2N).

The count divided by N tends to 4/pi^2. In particular, eventually
E_N(M)>=(2/pi^2)N uniformly in M>=2N. For M<=N^A, the endpoint correction
is O(sqrt N), hence eventually below N/pi^2. Polarization gives

    R_N(M) <= -N/(2pi^2), uniformly for 2N<=M<=N^A.

This supersedes the weaker prime/PNT/logarithmic estimate before publication.
The bound uses arithmetic support alone and is a cofinal signed coercivity
estimate. An upper bound for the accumulated energy/interior remains open.

## Live proof state (for continuation)

### Current checkpoint (supersedes scratch status below)

- Canonical `CofinalMobiusGradientCoercivityAndRenormalizedDefect.lean`
  exists and passed original-source `lake --old env lean -j 1` (session
  86144, exit 0, empty diagnostics). SHA-256:
  `b76bced42e329e2a1e50610d1f752be6b31c6bd82796a234fa38b45398a60765`.
- All 13 public declarations passed separate axiom audit (session 2916,
  exit 0): only `propext`, `Classical.choice`, `Quot.sound`.
- C5 canonical `CofinalLinearWindowMobiusEnergyAndDefectBounds.lean`
  passed original-source session 50481 and all five public axiom audits
  in session 3889, with no diagnostics and only standard axioms.
  Both leaves are wired. Evidence archived under `logs/bvi-cofinal-*`
  and `logs/bvi-linear-cofinal-*`; both result cards are in stage 3.
- C6-C7 canonical `UniformCofinalMobiusPrefixDiscrepancy.lean` passed
  original-source session 6514 and all eight public axiom checks in
  session 84742. No diagnostics, only standard axioms. It is wired;
  index passed; stage-3 card and `logs/bvi-uniform-cofinal-*` archive
  source hash and every gate. No owned Lean process currently running.
- Latest lint errors concern only concurrent BiScale PrimeRawMomentContrasts
  reachability and root TransHorizon umbrella placement. All three owned
  leaves have no reported lint error. Full global gate is not claimed clean.
- Quadratic-profile and multiplicative-density searches completed and
  were inspected (first partial, second complete). Next conjecture C8 is
  tracked in `bvi-cofinal-quadratic-quotient-profile-2026-10-18.md`.
- C8 is complete: two new leaves, both original-source audited and wired,
  all 33 public declarations audited with only standard Lean axioms. Profile
  source check 57054 and axiom check 23187 passed. Index passed; global lint
  has four unrelated findings, archived in the C8 manifest. Completed C8
  scratch files were removed after archive. C8's card is under `3-formalized`.
  The odd-moment conjecture is now active under `1-in-progress`. Scratch
  33012 passed its all-moduli mean-zero and odd-dilation-product foundation.
  Owned Lean session 6385 checks original source
  `CoprimeMobiusCancellationAndOddDilationMeans.lean`; log
  `/tmp/bvi-coprime-mobius-canonical.log`. Re-poll before another Lean command.
  The overall conjecture loop remains active.
- Session 46734 exited with three local elaboration errors, now corrected.
  Session 93140 exited before elaboration because it was launched from the
  repository root; all subsequent Lean commands run from `formal/`.
- The BVI README acquired concurrent foreign edits during this task.
  This task never wrote it. Preserve those edits; do not claim the global
  README diff is empty.
- Completed C1-C7 scratch proofs and API probes were removed after audit;
  historical paths below are no longer live continuation inputs.
- Leaf wired into BVI umbrella; `scripts/formal_tools.py index` passed.
- Lint exited 1 for concurrent unrelated unreachable leaves (three BVI,
  one BiScale) and the existing root TransHorizon umbrella placement.
  No finding names the new cofinal leaf. Preserve other work.
- Search sessions 55383, 57019, 67480, 6869 are terminal. The linear-horizon
  deep query was partial; lexical complementary-quotient search found the
  exact existing compression theorem.

### C5: Matching upper energy bound on every fixed linear horizon

**Dependency-closed paper proof.** For B>=1 and 1<=k<=(B+1)N,
the corpus complementary-quotient identity writes s_N(k), for k>1,
as minus a sum of at most B values mu(k/q). Hence |s_N(k)|<=B.
At k=1 use s_N(1)=1. Therefore for M+1<=(B+1)N,

    E_N(M) <= 4 B^2 M,
    |R_N(M)| <= 2 B^2 M.

The second inequality follows from R=sum s_N(k)(s_N(k+1)-s_N(k)).
Together with C4, for each fixed A>=2 and eventually uniformly
2N<=M<=AN, this gives a two-sided linear-order estimate for the actual
signed defect and the unsigned gradient energy. For the upper bound,
apply the finite estimate with B=A, using M+1<=(A+1)N.
No MC/PM budget, full-period average, or Möbius sign-correlation hypothesis
enters. This settles the order on fixed linear windows, not an upper
energy bound uniform in unbounded M/N or an interior-martingale estimate.

Existing source reused:
`TransHorizonIncidenceMechanics/ComplementaryQuotientAndSecondOctaveLaw.lean`,
`sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail` and
`complementaryQuotientTail_eq_sum_Icc_of_le_mul`.
Exact fixed-band envelopes through five horizons already exist elsewhere;
do not duplicate or claim those as new. The new synthesis is every fixed
linear window plus the C4 positive-density lower bound.

### C6: Uniform sublinear signed discrepancy above the cutoff

**Conjecture, now paper-proof dependency-closed:** for every epsilon>0,
eventually in N, simultaneously for every M>=N,

    |sievePrefixDiscrepancy N M moebiusReal| <= epsilon * M.

This is uniform in the moving cutoff and arbitrary observation horizon;
it does not fix N before taking M to infinity and does not use a period.

Write H_N=sum_{d<=N}mu(d)/d and S_N(M)=sum_{k<=M}s_N(k).
The corpus proves H_N->0 (PNTPlus `mu_pnt_alt`) and
mertensSup(X)/X->0 (`RHTower.Sieve.tendsto_mertensSup_div`).
For M<=(B+1)N, complementary-quotient compression and a finite sum exchange give

    S_N(M)=1-sum_{q=1}^B sum_{N<d<=M/q}mu(d),
    |S_N(M)|<=1+2B*mertensSup((B+1)N)=o_B(N).

Choose fixed B so large that 1/(B+1)<epsilon/2. For
N<=M<=(B+1)N, use L_N(M)=S_N(M)-M H_N and the two limits.
For M>(B+1)N, the direct fractional-part bound |L_N(M)|<=N
already gives |L_N(M)|<epsilon M. This covers all M>=N.

The PNT inputs are proved corpus theorems, not assumed premises. They are
classical inputs and are not claimed new. The new target is their uniform
cofinal transfer through the exact BVI quotient geometry. This is a
qualitative signed first-moment estimate; it does not imply square-root
error, a critical unsigned energy bound, or interior martingale closure.
Deep query `sievePrefixDiscrepancy moebius uniform tendsto` completed;
candidate lemmas and source arguments were inspected, no matching cofinal
theorem found in returned hits. Coverage is predominantly source-only.

### C7: Remove the relative-scale restriction entirely

**Paper-proof dependency-closed.** C6 and full sub-horizon Möbius inversion
give the genuinely joint cofinal statement

    for every epsilon>0 there exists K such that for all N,M>=K,
    |L_N(M)| <= epsilon M and |S_N(M)| <= epsilon M.

When M>=N use C6. When M<N, S_N(M)=1 and
L_N(M)=1-M H_N. Choose K so that 1/M<=epsilon/2 and
|H_N|<=epsilon/2. The source-prefix bound also follows from
S_N(M)=L_N(M)+M H_N, splitting epsilon in half.
No relation between the two growing scales remains. This strengthens
the quantifier domain of the first-moment estimate; it does not bound
unsigned energy or supply square-root cancellation.

C6 scratch session 79190 exited 0 with empty diagnostics. Its first pass
16981 had only a missing direct import and local finite-set/API elaboration
errors, corrected without changing the paper argument. C7 is being added
to the canonical source before the original-source audit.

### Historical scratch state (C1-C4)

- `/tmp/bvi_prime_cofinal_proof.lean`: `lake --old env lean -j 1` exited 0,
  empty diagnostics (tool session 45767). This proves the disjoint prime-edge
  count bound; do not publish it separately as an independent contribution.
- `/tmp/bvi_cofinal_proof.lean`: finite endpoint inequalities checked; last
  diagnostic was a `norm_cast` rewrite in divisor-growth transfer, now
  replaced by `simp only [Nat.cast_ofNat]`. Combined check pending.
- `/tmp/bvi_squarefree_cofinal_proof.lean`: combined stronger C1+C4 proof,
  currently being checked by owned session 15161. Only one owned Lean process
  is running. Re-poll this handle; do not restart on observation timeout.
- Combined first pass (session 28019) found only local elaboration issues:
  positivity did not close `1<=M+1`, two API probes had an extra namespace,
  simplification expanded Möbius before its square identity, and a limit
  needed its exponent type made explicit. Corrected each; no mathematical
  premise was added.
- Draft assembly inputs: `/tmp/bvi_squarefree_section.txt`,
  `/tmp/bvi_linear_cofinal_tail.txt`. Earlier weaker drafts:
  `/tmp/bvi_cofinal_tail.txt`, `/tmp/bvi_prime_cofinal_proof.lean`.
- Intended canonical leaf:
  `formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalMobiusGradientCoercivityAndRenormalizedDefect.lean`.
  It does not exist yet. Add mathematical docstrings, remove scratch API probes,
  run original-source check and all public axiom audits, then wire umbrella.
- New concurrent untracked field file
  `PronicPotentialSelfCancellationAndInteriorGradientConservation.lean` was
  observed during work; preserve it alongside the pre-existing compensated
  harmonic drift file.
- Next conjecture after C4: determine the strongest independent cofinal
  estimate for the interior or accumulated energy, distinguishing source
  support coercivity from sign cancellation. Corpus search results for upper
  mean-square estimates are in `/tmp/bvi-next-energy-research.json`.

## Evidence and tool constraints

- `docs/architecture.md` and `docs/testing.md` absent.
- `update_plan` and `multi_tool_use.parallel` unavailable; this card tracks
  work, and independent tool reads use `Promise.allSettled`.
- Serena symbol extraction rejects Lean: active language is Python. Use
  source reads and patches for Lean, preserving unrelated work.
- Hybrid queries completed with source-only candidates; compiler metadata
  is mostly pending/stale, so search hits are not Lean certificates.
- Deep query `renormalized defect endpoint divisor bound cofinal` running
  under owned tool session 55383; results in `/tmp/bvi-boundary-research.json`.
- Existing untracked `CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget.lean`
  belongs to pre-existing work and is not owned by this task.
- No numerical experiments, full builds, external novelty claims, or commits.

## Log

- 2026-10-18 — Opened this card before proof implementation. Original goal
  remains the full independent cofinal estimate, not completion of C1 alone.
