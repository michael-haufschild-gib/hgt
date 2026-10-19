# Exact gap-chain prefix Gram, coercivity, and clock visibility

- **ID:** bvi-period-reset-profile-coercivity-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Unformalized C14 candidate in
  `bvi-dilation-successor-jump-coupling-2026-10-18.md`; current BVI corpus.
- **Statement:** The actual signed gap-chain prefix Gram is diagonal harmonic
  jump energy minus one endpoint product. It has a uniform half-energy lower
  bound, exact visibility threshold at the valuation clock, and explicit
  coefficient readout at every visible depth after an explicit endpoint
  correction. The forced conditional tail removes the endpoint energy loss
  from the global lower bound.

## Goal

Obtain a lower bound on the actual profile, complementing the corpus's upper
residue-gap bound. This must use the literal primitive, not reverse
Cauchy–Schwarz on signed Möbius summands. Neither signed prime-packet dispersion
nor a global cancellation estimate follows from a pairwise lower bound.

## Paper proof under audit

Write `R > 1`, `q = p+h`, with positive integers `p,h`, and
`A(k) = Re(pmRamanujanPrimitive R k)`. Define

`D(p,q) = (p+q) G(R,R) - 2 sqrt(p) sqrt(q) Phi_R(p/q)`.

Existing `hasSum_scaled_pmRamanujanPrimitive_distance` identifies this with
the sum of `(p A(n/p) - q A(n/q))^2 / (n(n+1))` for `n >= 0`.

For `k=R*t`, `t>=1`, and `k*h<=p`, the interval `I_k=[kp,kq)` has exact
quotients `floor(n/p)=k`, `floor(n/q)=k-1`. Periodicity gives `A(k)=0`;
the coefficient at a multiple of R is `phi(R)`, so `A(k-1)=-phi(R)`.
Consequently the literal difference on this interval is `q*phi(R)`.
The existing reciprocal-pronic interval identity then gives exact cell mass

`sum_{n in I_k} distanceTerm(n) = h*q*phi(R)^2/(p*k)`.

For `1<=t<=K=floor(p/(R*h))`, the selected intervals are disjoint:
`k*q <= (k+1)*p <= (k+R)*p`. Their nonnegative masses sum to

`h*q*phi(R)^2/(p*R) * harmonic(K) <= D(p,q)`.

Proof obligations: verify all interfaces against current Lean; implement
quotient boundaries, reset and preceding value, finite interval mass,
disjoint-cell aggregation, and exact HasSum transfer. No numerical evidence.

## Prior-work and significance audit

- Existing `PronicResidueGapEnergyAndPrimePairDistance` already proves harmonic
  upper/lower bounds for a residue difference. Those are not new.
- Existing `RamanujanDilationProfileResidueGapBudget` proves the actual-distance
  HasSum and an upper bound via the signed residue expansion. Its source was
  read fully; it does not provide this actual-carrier lower bound.
- Existing periodicity, successor, real-coefficient/lag, and divisible-lag
  totient interfaces must be reused.
- Fresh deep corpus query in progress:
  `/tmp/bvi-100-actual-profile-research.json`.
- General periodic-step autocorrelation may already imply related cusp laws.
  Classical novelty is not established. Formalizing a previously open corpus
  candidate alone does not establish the user's significance criterion.
- **Accepted contribution status: not accepted; 0 credit.**

## Gates

- [x] Well-posed candidate and explicit distinction from residue bounds.
- [ ] Fresh corpus / classical-baseline audit completed.
- [x] Complete dependency-closed paper proof, including endpoint cases.
- [x] Exact Lean capstones with data parameters only.
- [x] Original-source check, all public axiom closures, wiring and indexing.
- [x] Significance verdict recorded: not accepted as significant new knowledge.

## Log

- 2026-10-18 — Candidate carried into new programme; no previous completed
  theorem recounted. Field README remains read-only.

## Stronger conjecture exposed by the cell algebra

For every `1<=k<=K`, `K*h<=p`, the first cell `[kp,kq)` has difference
`p A(k)-q A(k-1)` and the second `[kq,(k+1)p)` has difference `-h A(k)`.
Writing `c(k)=A(k)-A(k-1)`, their combined exact mass simplifies to

`h*c(k)^2/k + (h^2/p)*(A(k-1)^2/k-A(k)^2/(k+1))`.

Since `A(0)=0`, summing **all** quotient cells gives the stronger candidate

`sum_{n < (K+1)*p} distanceTerm(n)`
`  = h*sum_{k=1}^K c(k)^2/k - (h^2/p)*A(K)^2/(K+1)`.

This is an exact identity for the original Ramanujan primitive, including its
signed cancellation. It is stronger than selecting period-reset cells.
At `R|K` the endpoint term vanishes. Search the corpus before formalizing;
fresh deep query `/tmp/bvi100-exact-prefix-research.json` is running.
The arithmetic statement and significance require separate audits; count
remains zero. A generic periodic-step cusp alone is insufficient: Balazard–
Martin already analyze multiplicative fractional-part autocorrelation and its
logarithmic modulus (2013, https://arxiv.org/abs/1305.4395, propositions 31–32).

Fresh first deep query completed: partial=false, errors=[], 74,219 inventoried
files; semantic completeness unmeasured, compiler coverage mostly pending or
stale; background refresh incomplete. All 20 candidate and 20 source statements
reviewed. Proposed ingredient chain only repeats the existing upper bound and
does not prove a lower bound. Broad lexical hits mix unrelated harmonic
results; narrowed exact-profile query is used for the next review.

## Signed-chain extension: exact diagonal minus one endpoint square

New conjecture, not yet Lean checked. Use the existing
`ramanujanGapChainPacket r K m offset h a`, with
`P=pronicGapChainLower K m offset h 0`, `R=r+2`, and write

`J_R(K) = sum_{k=1}^K Re(c_R(k))^2/k`,
`V = sum_i a_i^2*h_i`, `B = sum_i a_i*h_i`.

Proposed exact identity at the existing physical cutoff `(K+1)*P`:

`sum_n packet(n)^2/(n*(n+1))`
`  = V*J_R(K) - B^2/P * A_R(K)^2/(K+1)`.

The existing source gives only the upper bound with
`ramanujanDilationResidueBudget(R)*(8*harmonic(K)+2*H/P)*V`.
The proposed identity would remove the cofactor expansion cost and retain
all signed-gap dependence in one explicit endpoint square. It does **not**
bound the later tail or contradict positive mixed-level covariance examples.

Paper mechanism: first transport the two-scale exact identity from cutoff
`(K+1)*p` back to common cutoff `(K+1)*P`. For endpoints `P<=p<=q<=P+H`,
the removed terminal interval has both quotients equal to K, so

`D_prefix(p,q) = (q-p)*J_R(K) - (q-p)^2/P*A_R(K)^2/(K+1)`.

Polarization for ordered disjoint gaps gives cross energy
`-h_i*h_j/P*A_R(K)^2/(K+1)`; the diagonal is
`h_i*J_R(K)-h_i^2/P*A_R(K)^2/(K+1)`. Summing with arbitrary signed a
gives the conjectured packet identity. Empty/zero gaps and K=0 must be audited.

The user reiterated corpus search on this continuation. Two searches are
live: `/tmp/bvi100-packet-cell-research.json` (BVI scoped) and
`/tmp/bvi100-signed-packet-exact-research.json` (whole corpus). Do not infer
novelty from missing names or sample only a few relevant returned statements.
The exact `ramanujanGapChainPacket` lexical search found four declarations;
their definitions and upper-bound interfaces were read directly.

## Verification checkpoint

- `/tmp/bvi100-period-reset-api.lean` exited 0. Current-toolchain interfaces
  checked, including interval sums, natural quotients, `Summable.sum_le_tsum`,
  periodic reset, and divisible-lag coefficient.
- `/tmp/bvi100-exact-prefix-draft.lean` exited 0 with an empty diagnostic log.
  Verified scratch declarations: `ramanujanScaledPrimitiveDistanceTerm`,
  `ramanujanDilationDistance_prefix_eq`, and
  `ramanujanDilationProfile_ge_jump_energy`. The prefix theorem allows any
  requested depth clamped to `floor(p/h)`, includes K=0, and has data only.
  Original-source/axiom/wiring audits remain pending; no acceptance yet.
- The exact signed-chain conjecture remains unformalized. Before extending,
  the whole-corpus lexical `dilation prefix energy` query returned 10 hits in
  six modules; all statements were checked, including the actual
  `finite_prefix_product_eq_jump_kernel`. Its exact reciprocal Green kernel
  provides a second derivation: ordered distinct quotient levels have
  `max(p_i*k,p_j*l)=p_j*l`; the reciprocal part cancels because total endpoint
  coefficient is zero. The common cutoff term is the single endpoint square.
- The first BVI packet search was partial (semantic deadline) and the long
  whole-corpus query was partial with interrupted retrieval. All 20 candidate
  and 20 source statements from each were inspected, but these do not certify
  absence. Shorter query `pronic dilation energy` is the next retrieval pass.
- Additional exact lexical audits: six `gap energy exact` hits and thirteen
  `prefix covariance` hits, all statements checked. Existing residue identities,
  same-level nonpositive covariance, positive mixed-level covariance, Route PM
  square-increment decompositions, and global mean zero are distinguished from
  the proposed exact signed-chain finite-prefix matrix.

## Current proof work and live handles

- The shorter whole-corpus `pronic dilation energy` search finished,
  partial=false/errors=[]; all 20 candidate and 20 source statements inspected.
  Semantic completeness remains unmeasured. The proposed search-engine
  ingredient set only combines unrelated energy scaling/trace inequalities.
  Existing `sum_ramanujanDilationJump`, finite reciprocal kernel, cofactor
  prefix bound and Route PM budget interfaces are the relevant reusable hits.
- `actual_distance_common_prefix` passed Lean: handle 5282 exited 0 with an
  empty `/tmp/bvi100-common-prefix-check.log`.
- Packet handle 53708 exited 1. Four diagnostics reduce to three local
  proof-script issues: qualify `Finset.sum_range_succ` (two uses), remove a
  no-op `dsimp`, and distribute the inner boundary sum with `mul_sum`.
  The common-prefix polarization and diagonal/off-diagonal formulas passed.
- Handle 73363 exited 1 with one remaining boundary-factorization goal:
  simplification expanded the two sums in opposite index order. Replaced
  it with an explicit `Finset.sum_mul_sum` rewrite before distribution.
  Readout and its positivity proof had no diagnostics.
- Handle 43419 exited 1 with local coercivity-proof elaboration issues:
  an ambiguous cast, a rational identity requiring denominator normalization,
  and two tactics running after their goals closed. The exact Gram, reset
  readout, and clock-support argument had no diagnostics. These issues are
  fixed in the promoted source; full verification remains pending.
- Canonical handle 65189 exited 1 on a single untyped `Nat.cast_nonneg`
  argument in `linarith`. Added its explicit real-valued type. No other
  diagnostics remained.
- Source check 23000 exited 0. All nine public theorems and the public term
  definition are verified in the canonical source. One unused trailing `ring`
  warning was removed.
- Handle 71512 exited 0: warning-free canonical-source check, then all ten
  public axiom closures checked. Each uses only `propext`, `Classical.choice`,
  and `Quot.sound`; no `sorryAx` or added axiom.
- Completed sequential commands:
  `lake env lean -o <leaf.olean> -i <leaf.ilean>
  GaloisForLFunctions/BezoutValuationIncidence/RamanujanGapChainExactPrefixGram.lean`, log
  `/tmp/bvi100-canonical-final.log`, followed only on success by
  `lake --old env lean /tmp/bvi100-exact-prefix-axioms.lean` with log
  `/tmp/bvi100-exact-prefix-axioms.log`.
- `/tmp/bvi100-common-prefix-fragment.lean` has been integrated into that draft.
- `/tmp/bvi100-packet-fragment.lean` contains common-prefix polarization,
  chain endpoint arithmetic, exact bilinear/energy identities, intrinsic
  upper bound, and reset orthogonality. It is integrated into the scratch,
  with the existing packet-module import and new mathlib API probes.
  Packet fixes and the readout fragment are integrated; canonical promotion
  remains pending.
- Exact packet proof plan: four common-prefix distances polarize to
  `C(i,j)=-h_i*h_j*A_R(K)^2/(P*(K+1))` for i<j. Diagonal is
  `h_i*J_R(K)-h_i^2*A_R(K)^2/(P*(K+1))`. Expand the packet square, sum
  the diagonal, and factor the remaining double sum into B².
- Stronger native consequence to audit: at `R|K`, the primitive resets and
  **all disjoint gap channels become exactly orthogonal on this common short
  prefix**, without a period for the physical scales. This is part of the same
  contribution, not a separate count.
- Canonical module is
  `formal/GaloisForLFunctions/BezoutValuationIncidence/RamanujanGapChainExactPrefixGram.lean`
  (647 lines). Original-source and axiom audits passed. The leaf is wired into
  the BVI umbrella. Index/lint remain pending;
  no umbrella build is authorized. Programme count remains 0/100.
- `/tmp/bvi100-exact-prefix-axioms.lean` is prepared for all ten public
  declarations. The sequential command 71512 launches it only after source
  checking and writing the leaf `.olean`; one owned Lean process at a time.

### Strongest finite-prefix capability to finish

The packet fragment now proves a proposed **bilinear** identity first, with
`sum_i a_i*b_i*h_i` as diagonal coefficient and
`(sum_i a_i*h_i)*(sum_i b_i*h_i)` as endpoint product. Energy, the intrinsic
upper bound, and the period-reset diagonal law are consequences of that one
mechanism. All belong to one contribution.

At `K=R*(t+1)` and positive gap lengths, the jump energy `J_R(K)>0`: the
term k=R is `phi(R)^2/R>0`. Thus the reset identity supplies exact coefficient
readout from inner products with the individual gap channels, on physical
horizon `(K+1)*P`; it does not wait for the lcm period of the physical scales.
Audit/formalize this native inverse capability after the packet identity.
Reuse the already checked real-coefficient/lag/totient interface rather than
proving a new character-sum identity.

Paper endpoint audit: K=0 gives an empty jump sum and zero primitive; h=0
gives an empty first cell and zero gap channel; m=0 gives an empty packet;
ordered gaps may touch; all denominators requiring nonzero values have
p>=P>=1 and K+1>=1. Signed coefficients are unrestricted. The common-prefix
tail is removed only after Kq<= (K+1)P ensures both quotients equal K.

### Recovery prior-work audit

- Exact lexical `"Ramanujan" "readout"`: four hits, all source statements
  checked in `RHTower/MobiusRamanujanTwoLevelConservation.lean`. They recover
  a weighted Möbius sum from two conductor levels of complete additive Fourier
  readouts; they do not recover coefficients of physical dilation gap packets.
- Exact lexical `"gap" "orthogonal"`: 37 hits across both result pages
  inspected. These concern spectral gaps, Hilbert projections, graph channels,
  or exponential-frequency estimates; no existing actual gap-packet identity.
- The deep recovery query was partial (reranking deadline). All 20 candidate
  and 20 source statements were inspected. Relevant results reuse the existing
  packet, coefficient support clock, cofactor bounds and exact HasSum. The
  proposed Fourier recipe is unverified and does not establish this readout.
- `SharpInitialPrefixObservabilityAndExactGramDeterminants.lean` was checked
  directly: it reconstructs divisor weights from the first N-1 unscaled
  discrepancy values, with a dense conductor-indexed Gram. Its exact Möbius
  inverse and determinant are prior work, not new claims here. The proposed
  gap-channel inverse instead uses a fixed conductor, ordered physical scale
  differences, the pronic measure, and a shared pre-overlap cutoff.
- `/tmp/bvi100-readout-fragment.lean` records the positive-gap inverse theorem
  with data parameters only. It is integrated in the checked scratch.
  The positivity proof reuses the known coefficient at k=R
  and totient positivity, not a new character-sum identity.

### Further conjecture exposed by the exact matrix (not yet formalized)

The endpoint correction cannot destroy most of the intrinsic jump energy:

`(1/2) * J_R(K) * sum_i a_i^2*h_i <= packetPrefixEnergy <= J_R(K)*sum_i a_i^2*h_i`.

Paper proof: weighted Cauchy gives `B^2 <= H*V` and
`A_R(K)^2 <= J_R(K)*K*(K+1)/2`, since `A_R(K)=sum_{k=1}^K c_R(k)`.
Thus the endpoint correction is at most `J_R(K)*V*K*H/(2*P)`, and
`K*H<P` by construction. The empty/K=0 cases give zero on both sides.
This predicts stable recovery without waiting for a primitive reset.

The known exact coefficient support clock then predicts the sharp quotient
visibility boundary: `J_R(K)>0` exactly when `lagVisibilityClock R <= K`
for R>1. Below the clock every coefficient in the prefix vanishes; at the
clock the existing support theorem supplies a nonzero coefficient. Audit
prior work before adding these consequences. They are part of the same
candidate, not additional contribution credit.

The new coercivity and visibility fragment is now integrated and running in
43419. Its proof uses the current mathlib weighted Cauchy interface directly,
and reuses `ramanujanNaturalCoefficient_re_ne_zero_iff_clock`. Exact lexical
audits `prefix coercivity` (four hits) and `clock energy` (one hit), scoped to
BVI, were checked in source: they concern additive sieve-gradient defects or
Buchstab scale steps, not physical gap-chain pronic energy.

Additional visibility audits: `visibility prefix` has no BVI lexical hits;
`recovery clock` has three, all checked. The existing clock wavelet theorem
recovers valuation shells, and the totient observability theorem reconstructs
translation phases. `ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean`
already classifies recovery from full literal translated probes by clock
divisibility. None supplies the proposed finite pronic Gram for many physical
gap channels. The clock itself and its support law are reused prior work.

### External baseline check

[Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation*
(2005 preprint)](https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf)
already uses the exact `1/(n(n+1))` sequence norm and fractional-part carriers,
and discusses full Gram determinants with digamma entries. The pronic Hilbert
space is not new. [Planat's Ramanujan signal-processing
paper](https://perso.ens-lyon.fr/patrick.flandrin/NewOrl2.pdf) uses traditional
period/mean orthogonality for conductor-indexed Ramanujan expansions. Neither
source supplies the proposed shared short-prefix Gram of ordered physical gap
channels. This limited comparison does not establish worldwide novelty.

## New conjecture: exact global conditional-tail completion

Let `N=(K+1)*P`, `A=A_R(K)`, `B_a=sum_i a_i*h_i`, and write F_a for
the existing actual gap-chain packet. Its already proved total pronic mean is
zero. The quotient-cell mean calculation predicts

`sum_{n<N} F_a(n)/(n*(n+1)) = B_a*A/N`.

Thus the conditional mean on `n>=N` is `-B_a*A`. Completing the tail square
cancels the negative endpoint term in the exact head Gram:

`sum_{n>=0} F_a(n)*F_b(n)/(n*(n+1))`
` = J_R(K)*sum_i a_i*b_i*h_i`
`   + sum_{n>=N} (F_a(n)+B_a*A)*(F_b(n)+B_b*A)/(n*(n+1))`.

For a=b this gives the full diagonal jump energy as a global lower bound,
with an exact nonnegative residual tail. This is stronger than dropping the
uncentered tail from the head identity. It uses the existing zero-mean law;
the mean-zero property must not be silently assumed for arbitrary primitives.

Dependency-closed paper mechanism for the head mean: at cutoff `(K+1)*p`,
integer quotient blocks give `sum_{k=1}^K A_R(k)/(k*(k+1))`. The existing
`pmRamanujanPrimitive_reciprocal_partial` rewrites this as
`sum_{k=1}^K c_R(k)/k - A_R(K)/(K+1)`. Removing the final interval to common
cutoff N leaves `sum c_R(k)/k - p*A_R(K)/N`. Subtracting the p+h scale
and summing signed coefficients gives the displayed head mean. Tail mass is
1/N; linear tail mean is minus the head mean. Boundedness of the finite packet
gives all needed pronic summability, so the bilinear expansion is legitimate.

Status: new conjecture under corpus audit; no Lean proof yet. Reuse the
existing `PrimePacketConditionalTailAndCoherentPrefix` methodology or any
generic conditional-tail lemma found by search. Do not count this completion
as a separate contribution from the exact Gram mechanism.

Corpus audit: deep `pronic conditional tail mean energy` returned partial
semantic coverage (deadline); all 20 candidate and 20 source statements
inspected. Relevant existing results are the prime-packet and natural-cutoff
conditional-tail decompositions. Exact lexical `tail mean` in BVI returned
22 declarations across both pages; these include those decompositions,
mean-centered oscillatory primitives, and unrelated adjacent-divisor tail
bounds. General conditional variance is prior work. The new content to prove
is the exact endpoint mean and its cancellation against this gap-chain Gram.

`/tmp/bvi100-global-tail-draft.lean` (282 lines) now contains the block mean,
common-cutoff mean, packet square summability, conditional-tail algebra, and
public exact completion/lower bound. Its first Lean check is running (handle
 **11293**); log `/tmp/bvi100-global-tail-check.log`. No other owned
Lean process is running. Squared summability reuses the corpus lemma
`summable_div_pronicSeq_of_bounded` (exact research query, sole result checked)
and the existing bounded primitive, avoiding an unnecessary new convergence
argument. The prime-specific tail carriers are not substituted for actual
physical gaps; the series algebra is applied to the actual packet.

The same completion predicts the sharper original-profile bound
`h*J_R(min(K,floor(p/h))) <= D(p,p+h)` with no endpoint subtraction.
`/tmp/bvi100-profile-global-fragment.lean` records its unintegrated proof.
The pair's total mean is obtained by realizing it as the existing canonical
one-gap packet at depth zero and offset p-1. The actual head mean and energy
then use the requested clamped depth, including the boundary `T*h=p`.
Integrate only after 11293 terminates; this is part of the same contribution.

### Current global-tail checkpoint

- Scratch handle 11293 exited 1 with two local errors: an untyped natural cast
  in an absolute-value rewrite, and a `ring` after `field_simp` had already
  closed the goal. Head-mean and conditional-tail series proofs had no errors.
- Both errors fixed; the stronger original-profile fragment is integrated.
- New canonical source:
  `formal/GaloisForLFunctions/BezoutValuationIncidence/RamanujanGapChainConditionalTailCoercivity.lean`
  (330 lines). It is not wired yet.
- Handle 7819 exited 1 only on positivity of `(min(K,p/h)+1)*p`; `omega`
  expanded the quotient unnecessarily. Replaced with direct `positivity`.
  The head mean, global decomposition, global lower bound, and all remaining
  profile proof steps had no diagnostics.
- Live foreground handle **6309** runs `lake env lean -o <leaf.olean>
  -i <leaf.ilean> GaloisForLFunctions/BezoutValuationIncidence/RamanujanGapChainConditionalTailCoercivity.lean`.
  Log: `/tmp/bvi100-global-canonical-final.log`, followed only on success by
  `lake --old env lean /tmp/bvi100-global-tail-axioms.lean` into
  `/tmp/bvi100-global-tail-axioms.log`. No other owned Lean process.
- `/tmp/bvi100-global-tail-axioms.lean` is prepared for all four new public
  theorems. The sequential command runs it after source success; then wire,
  index, lint, and clean owned
  scratch files. Do not claim these final gates before observing their output.

### Strongest readout exposed by conditional completion

The new head mean also removes the need to wait for a primitive period reset.
For channel j, let `G_j` be the actual one-gap summand and let `A=A_R(K)`.
The exact bilinear head Gram and head mean give

`sum_{n<N} F_a(n)*(G_j(n)+h_j*A)/(n*(n+1)) = a_j*h_j*J_R(K)`.

The endpoint terms cancel explicitly. For positive h_j and
`K=lagVisibilityClock(R)+t`, the denominator `h_j*J_R(K)` is positive by the
existing nonzero coefficient at the clock. This is an exact finite readout at
every visible depth, including the first one; it uses no tail observations.
At a reset, the correction vanishes and recovers the already formalized
uncorrected readout. This is another consequence of the same mechanism, not
separate contribution credit. Paper proof closed;
`/tmp/bvi100-sharp-readout-fragment.lean` now contains the proposed exact
`ramanujanGapChainPacket_clock_coefficient_readout`, plus positivity at the
first clock depth. It is unintegrated and unverified. The clock/recovery
prior-work audit above applies to the same physical carrier. After 6309
terminates, integrate before the namespace end, regenerate the axiom audit
to include this fifth public theorem, and check the final canonical source.


## Final proof and expanded prior-work checkpoint

The final conditional-tail source, including
`ramanujanGapChainPacket_clock_coefficient_readout`, passed original-source
`lake env lean` with no diagnostics (handle 4334, exit 0). The sequential
`lake --old env lean /tmp/bvi100-global-tail-axioms.lean` also exited 0;
all five public theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The core module's ten public declarations passed the same axiom
closure earlier. Both leaves are now wired in the BVI umbrella. No umbrella
or full build was run. Explicit `scripts/formal_tools.py index` is running
(handle 29441); lint remains pending. No owned Lean process remains.

The user requested another corpus check. The whole-corpus deep query
`physical dilation gap coefficient recovery endpoint correction first visibility clock`
excluded `RamanujanGapChain` modules. It returned partial results because
reranking hit its local deadline. All 20 candidate statements and all 20 source
arguments were reviewed. The only directly relevant hits were the already
used visibility clock and the existing dilation-jump-gap definition. The
proposed ingredient set incorrectly mixed an entire gap series with marked
Xi clock corrections; it does not prove the target and was rejected.
Coverage: all 74,240 inventoried files indexed; 62,405 Lean and 11,835 prose
files; semantic completeness unmeasured, background refresh incomplete, most
compiler metadata pending or stale. These counts are coverage information,
not evidence that no equivalent theorem exists.

Follow-up lexical searches avoided relying on that ranking:

- `pronic recovery`, uncapped by module and excluding our leaves: all five
  hits inspected directly. Four concern the new THIM Fermi boundary sampler:
  odd readings, doubled even readings, exact four-divisible support
  classification, and physical energy comparison. The fifth is elementary
  recovery of coprime factors from a pronic product. Neither is the physical
  fixed-conductor gap-chain Gram or its corrected readout.
- `harmonic jump`, same scope: all 48 hits reviewed across offsets 0, 20, 40;
  relevant statements read directly. Existing local two-cell harmonic-mean
  variance/coercivity and Xi aperture endpoint bounds are generic or use
  logarithmic prime interval carriers. BVI interior-jump centering bounds,
  successor-fiber full-period amplitude selectors, the active-deleted
  diagonal identity, THIM calibrated power sampling, harmonic floor jumps,
  and Chebyshev pronic Abel summation are distinct results. They are prior
  work, not new contribution credit.
- Exhaustive source-text checks additionally inspected the current THIM
  Vasyunin–Fermi pronic Gram bridge. It supplies a reciprocal-cell
  decomposition and multiplicative scaling, not the diagonal-minus-endpoint
  evaluation for ordered physical gaps.

Search artifacts are `/tmp/bvi100-corrected-readout-research.json`,
`/tmp/bvi100-pronic-recovery-crossfield.json`, and
`/tmp/bvi100-harmonic-jump-crossfield{,-page2,-page3}.json`.

External baseline expansion (primary sources): Werner Ehm,
[On certain Gram matrices and their associated series](https://arxiv.org/html/2405.06349),
2024, evaluates full Nyman–Beurling Gram kernels and decomposes their quadratic
forms. Its formulas do not state this finite ordered-gap evaluation.
Vaidyanathan's
[finite-duration Ramanujan expansions](https://authors.library.caltech.edu/records/k3xw5-byr96)
and Tenneti–Vaidyanathan's
[minimum data length work](https://authors.library.caltech.edu/records/tezc8-qaq67)
already establish finite periodic-signal representations and identifiability
bounds. Only their repository abstracts were available here; they are a
baseline warning against claiming finite recovery itself as new. The present
readout uses fixed-conductor primitive dilation gaps and a pronic weight.
No worldwide-priority claim follows from these comparisons.

**Significance checkpoint:** this is a verified exact evaluation for an
existing native carrier, stronger than the previous residue-budget upper
bound. Its consequences form one conceptual package. The underlying
quotient-cell identity and conditional-mean completion are general
piecewise-constant/variance mechanisms. Without a further arithmetic
consequence, the user's stronger demand for a genuinely significant new
mathematical contribution remains unestablished. Accepted count stays
**0 / 100**; do not relabel the fifteen public declarations as fifteen
contributions or claim that proof certification establishes novelty.


### Repository gate outcome

Explicit indexing exited 0 and rewrote the API/gaps/overview artifacts; its
incremental search refresh reported one changed file and no removals. Search
readback finds the new Gram, coercivity, mean and corrected-readout names.
`git diff --check` on the owned tracked changes exited 0.

Formal lint exited 1. Its sole error was:

```
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.TransHorizonIncidenceMechanics: GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiSelectedCoefficientSharpInverse
```

That concurrently-created THIM leaf is outside this work's write scope.
No BVI error or forbidden proof declaration was reported. Global lint has
**not** passed; do not erase that distinction or edit another agent's files.
The mathematical verification of both BVI leaves is complete. Significance
remains insufficient for contribution credit. The next research question is
whether the exact physical-gap formula exposes an additional arithmetic
constraint on actual varying-prime packets, beyond transporting generic
piecewise-constant variance algebra.
