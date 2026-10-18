# Integer jump coupling for rational dilation profiles

- **ID:** bvi-dilation-successor-jump-coupling-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/walls/bezout-wall1-programme.md, problem 2
- **Statement:** Recover additive integer jump incidence and Diophantine spacing inside the existing high-scale Ramanujan dilation profile.

## Goal

Construct an unconditional arithmetic coupling for the existing profile, valid at arbitrary positive integer dilation scales, with its exact finite-horizon and analytic consequences. Research is independent of RH. No numerical experiments, assumed cancellation estimates, new axioms, or heartbeat increases.

## Plan and gates

- [x] Read field context; inspect actual spectral and incidence definitions; search corpus.
- [ ] State successive precise conjectures; prove or refute on paper; retain positive survivors.
- [ ] Formalize dependency-closed survivors, connect to original dilation profile.
- [ ] Audit original Lean sources and axiom closures; wire completed leaves; run lint and refresh indexes.
- [ ] Record exact conclusions, failure boundaries, and next conjecture.

## Evidence and constraints

- Field README read in full. Architecture/testing documents absent at session initialization.
- Existing working tree contains concurrent changes; preserve them.
- `update_plan` and `multi_tool_use.parallel` unavailable; this card tracks steps, independent reads use parallel tool orchestration.
- Deep corpus query `dilation profile Bezout jump Diophantine` started; results pending.
- User requests continuing conjecture/proof/refutation loop, no hgtl7 skill, no RH work, foreground single owned Lean process, no full/umbrella builds, final `lake --old env lean` checks.

## Conjecture log

### C1: finite jump Green representation (paper proof)

Write `A_r(N) = Re(pmRamanujanPrimitive r N)` and `c_r(a) = Re(d4BMRamanujanNaturalCoefficient a r)`. The actual definitions give `A_r(N)=sum_{1<=a<=N} c_r(a)` and `A_pr(N)+A_r(N)=p A_r(floor(N/p))` for primes not dividing r.

For positive integer p,q and horizon H, conjectured exact identity:

`sum_{n=1}^H A_r(floor(n/p)) A_r(floor(n/q))/(n(n+1))`

`= sum_{a=1}^{floor(H/p)} sum_{b=1}^{floor(H/q)} c_r(a)c_r(b) [1/max(pa,qb)-1/(H+1)]`.

Paper proof: expand both finite primitive sums, interchange three finite sums, and telescope `sum_{n=max(pa,qb)}^H 1/(n(n+1))`. No infinite rearrangement. Multiplication by pq identifies the finite four-term prime Gram. The existing bounded-primitive pronic-tail theorem gives error `pq B_r^2/(H+1)` to `sqrt(pq) Phi_r(p/q)`, where `B_r=pmRamanujanPrimitiveBound r`.

### C2: resolve Green representation into additive lag sectors (paper proof)

Group jump pairs by the signed integer `h=pa-qb`. For h=1, pairs are precisely successor incidences `q | n` and `p | n+1`; therefore both dilation moduli and the multiplier indices are coprime. General h enforces `gcd(p,q) | h` and `gcd(a,b) | h`. These restrictions apply at arbitrary scales, not only bounded small divisors. Exact modular solution fibers and quantitative successor-sector control remain to be developed.

### Unsafe extension rejected before use

An unrestricted infinite double sum of `c_r(a)c_r(b)/max(pa,qb)` does not follow from the finite identity. The boundary term and the prescribed common physical cutoff must be retained until convergence is proved. The positive survivor is the finite Green formula with an explicit tail bound; no absolute convergence or cancellation claim is made.

### C3: arithmetic fiber correlation (candidate)

For p,q coprime to r and `pa-qb=h`, unit invariance of Ramanujan coefficients should identify `c_r(a)c_r(b)=c_r(pa)c_r(qb)=c_r(n+h)c_r(n)`. When gcd(p,q)=1, the solution fiber advances n by pq; since gcd(pq,r)=1, one r-step fiber period traverses every residue modulo r. Its exact unweighted mean should be `c_r(h)`, hence `mu(r)` at h=1. Need corpus verification and complete proof before treating this as established. A weighted reciprocal version additionally needs explicit residue-dependent boundary control.

### C4: fixed-lag logarithmic counterterm (candidate exposed by C3)

C3 predicts the unscaled lag-h Green sector grows as `c_r(h)/(pq) log H`, because successive solutions are spaced pq and the Green weight is reciprocal. In particular, isolating h=1 need not produce a finite limit even though the full dilation Gram converges. The candidate positive survivor is a renormalized sector with an explicit arithmetic logarithmic counterterm and bounded residue-dependent remainder. Coherent lag cancellation, not termwise infinite summation, is essential. No divergence theorem claimed before C3 and the weighted remainder are proved.

Sharper next target: choose the first positive successor solution pa=qb+1 with 1<=a<=q and b>=1. Put L=pqr and d_t=pa+pq t for 0<=t<r. Then 1<=d_t<=L. For K+1 complete fiber blocks, the weighted sum is `W_K=sum_t c_r(a+qt)c_r(b+pt) progressionHarmonicSum L d_t (K+1)`. Existing `abs_progressionHarmonicSum_succ_sub_harmonic_div_le` and C3 yield

`|W_K - mu(r)/(pq) harmonic(K)| <= sum_t |c_r(a+qt)c_r(b+pt)|/d_t`.

To identify this with the actual h=1 sector at H=L(K+1), prove the complete positive solution parametrization, then subtract the exact cutoff term `(K+1)r mu(r)/(H+1)`. This would prove the predicted logarithmic obstruction and its strongest positive renormalized survivor without numerical experiments. Current status: argument outlined; finite arithmetic reindexing and Lean proof still required. Do not replace the actual sector with an auxiliary block sum and claim completion.

### Implementation checkpoint

Canonical `ReciprocalJumpKernelAndDilationLagSectors.lean` passed exact original-source `lake --old env lean -j 1 -o ...` (exit 0, no diagnostics); wired into field umbrella. It contains pair reindexing, signed sectors, both gcd support laws and successor coprimality. `/tmp/bvi-dilation-profile-draft.lean` develops a stronger direct Hilbert-to-integer-series bridge for all positive integer scales, independent of prime insertion, with cutoff and quadratic-horizon error bounds; check running, output `/tmp/bvi-dilation-profile-check.log`. That check also prints all 16 public axiom closures from the first leaf. `/tmp/bvi-dilation-fiber-draft.lean` develops unit invariance, actual additive pair transport and full residue correlation. These latter drafts are unverified.

## Corpus audit

Deep query completed (`partial=false`, 74,152 inventoried files); semantic coverage unavailable and compiler coverage mostly source-only. Broad semantic suggestions largely unrelated; no applicability inferred. Lexical followups located actual primitive, prime-insertion, pronic-tail, and finite divisor reindexing declarations. Source definitions read directly. Existing CRT successor-incidence module supplies period spacing; it does not identify the high-scale profile. Serena symbol lookup rejects ignored Lean paths, so source reads/patches are necessary.

## Dependency-closed paper argument for the coupling package

Let r>1, p,q>=1, H>=0 be integers. Let A_r be the actual bounded primitive and B_r its existing proved bound. Define the finite set of jump pairs by 1<=a<=H/p and 1<=b<=H/q. Its signed separation is h=pa-qb.

1. **Finite Green formula.** At a fixed integer n, A_r(n/p) is the sum of c_r(a) over pa<=n. Expanding both factors and interchanging finite sums gives the reciprocal kernel from max(pa,qb) through H. Since pa,qb>=1, telescoping evaluates it to `1/max(pa,qb)-1/(H+1)`. Grouping by h is another finite partition, so no convergence assertion is needed.
2. **Original Hilbert profile.** The actual full-line source is A_r(floor x)/x. Normalized dilation by 1/p has representative `sqrt(p) A_r(floor x/p)/x`. The floor identity gives A_r(floor(floor x/p)). Both dilated sources vanish below one. Their full-line inner product therefore equals sqrt(pq) times the integer-cell series with weight 1/(n(n+1)). Unitarity of dilation identifies the same inner product with the existing Phi_r(p/q). This uses every positive integer p,q, not just primes outside r.
3. **Uniform truncation.** Each unscaled product is bounded by B_r^2. The reciprocal tail sums to 1/(H+1). Thus the error in Phi is at most sqrt(pq) B_r^2/(H+1). Put Q=max(p,q) and H=Q^2; sqrt(pq)<=Q gives error <=B_r^2/Q. The final quantifier is joint in both dilation scales, with r fixed only through its explicit B_r.
4. **Additive support.** Both gcd(p,q) and gcd(a,b) divide pa-qb. At h=1 both pairs are coprime. The h=1 kernel is exactly `1/(qb+1)-1/(H+1)`. These constraints hold for arbitrarily large p,q and act on terms already proved to reconstruct Phi.
5. **Amplitude reciprocity.** If gcd(p,r)=gcd(q,r)=1, the proved gcd formula for c_r implies c_r(pa)=c_r(a) and c_r(qb)=c_r(b). Along pa-qb=h the product becomes c_r(qb+h)c_r(qb). Thus the lag sector carries actual additive correlation, not only a count of admissible pairs.
6. **Full successor fiber mass.** Given pa-qb=1, the solution family (a+qt,b+pt) has product c_r(n_t+1)c_r(n_t), n_t=qb+pqt. Since pq is invertible modulo r, t modulo r runs through every n_t modulo r. Expand each Ramanujan coefficient into its finite sum of primitive additive characters. Summing the product over n annihilates frequency pairs except v=-u. The survivor is r c_r(1)=r mu(r). This is exact for arbitrary starting solution and all admissible dilation scales.

The new connection is the quantitative identification of the original profile with arithmetic lag sectors, together with transport of their amplitudes to actual additive correlations. Finite Fubini, reciprocal telescoping, character orthogonality, unit invariance, and CRT are reused infrastructure, not separately claimed discoveries. No cross-sector cancellation estimate, unsigned absolute jump-series convergence, or bound for an unrelated natural-cutoff quadratic form follows from this package.

## Verification

- `ReciprocalJumpKernelAndDilationLagSectors.lean`: original-source check clean, wired; all 16 public axiom closures use only subsets of `propext`, `Classical.choice`, `Quot.sound`. Raw closures: `logs/bvi-dilation-successor-kernel-axioms.txt`.
- Profile draft first pass found only a square-root/inverse parenthesization error in the a.e. scaling lemma. Corrected. All later declarations elaborated, but their dependency closure remains unverified until corrected helper passes.
- Combined profile/fiber check: `/tmp/bvi-dilation-combined-check.lean`, output `/tmp/bvi-dilation-combined-check.log`. No overall completion claim.
- Combined check confirms the entire all-positive-scale profile identification, finite-lag error bound, successor kernel and unconditional quadratic-horizon capstone elaborate without diagnostics. Remaining errors confined to the separate fiber draft (qualified character lemma, cast of conditional, unit-inverse parentheses); corrected. Canonical `DilationProfileIntegerJumpCoupling.lean` original-source check now running, log `/tmp/bvi-dilation-profile-original.log`.
- `DilationProfileIntegerJumpCoupling.lean` original-source audit completed exit 0, no diagnostics; wired. Original log `logs/bvi-dilation-successor-profile-original.txt` (empty because clean). Current Lean check is `/tmp/bvi-dilation-fiber-draft.lean`, log `/tmp/bvi-dilation-fiber-check.log`; includes all eight profile axiom closures. Deep search for C4 solution parametrization running separately, `/tmp/bvi-dilation-fiber-parametrization-research.json`.

### C3 original-source check completed

`DilationSuccessorFiberReciprocity.lean` passed its original-source `lake --old env lean -j 1 -o ...` check with exit 0 and no diagnostics. All nine public declarations compile. Added its umbrella import. Public axiom audit is queued alongside the C4 scratch check; C4 remains unverified. Original diagnostic log: `logs/bvi-dilation-successor-fiber-original.txt`.

### C3 axiom audit; C4 exact-sector proof

All nine public C3 declarations have axiom closures contained in
`[propext, Classical.choice, Quot.sound]`; saved audit:
`logs/bvi-dilation-successor-fiber-axioms.txt`. The first C4 scratch check
verified `successor_solution_parametrization` and
`ramanujanDilationLagSector_one_eq_seed_sum`. The independent seed-existence
helper had three elementary natural-number proof errors, now corrected and
queued for recheck. No C4 module has yet been added to the tree.

For positive coprime scales `p,q > 1`, choose the unique positive successor
seed `pa=qb+1`, `1≤a≤q`, `b≥1`. The CRT period theorem supplies existence.
Reducing any other positive solution `pc=qd+1` modulo `q` gives
`c≡a (mod q)`. Minimal positivity gives `c≥a`, hence exactly
`c=a+qt`, `d=b+pt`, `t≥0`. At physical horizon `H=pqT`, the two coordinate
bounds are equivalent to `0≤t<T`; this proves a bijection with the complete
finite `h=1` sector, not a selected subfamily.

Write `A_t=c_r(a+qt)c_r(b+pt)` and `d_t=p(a+qt)`. Then
`A_(t+rk)=A_t`, `1≤d_t≤pqr` for `0≤t<r`, and, when `gcd(pq,r)=1`,
`sum_(t<r) A_t=r μ(r)`. With `L=pqr`, `U=K+1`, and `H=LU`, the exact
sector is

```
S_1(H) = sum_(t<r) A_t progressionHarmonicSum(L,d_t,U)
         - U r μ(r)/(H+1).
```

Subtracting `harmonic(K)/L` inside every progression, the existing reciprocal
progression bound and the triangle inequality give

```
|S_1(H) + U r μ(r)/(H+1) - μ(r)/(pq) harmonic(K)|
  ≤ sum_(t<r) |A_t|/d_t.
```

This is a dependency-closed paper proof. The right side is independent of
`K`. The actual sector and its physical cutoff correction both remain
explicit. Formal verification is running. No cross-lag interchange or
uniform high-scale profile conclusion is asserted.

### Next conjecture C5: arithmetic selector for the successor mean

Candidate (paper argument only, corpus/Lean audits pending): for an arbitrary
successor seed, without assuming `gcd(pq,r)=1`, the complete period mass is
`r μ(r)` if `gcd(pq,r)=1`, and zero otherwise. In the Fourier expansion,
a surviving unit-character pair must satisfy `q α+p β=0 (mod r)`.
Because `gcd(p,q)=1`, this forces both scales to be units modulo `r`:
if a prime divides `r` and one scale, it does not divide the other, and
reducing the character equation modulo that prime contradicts unitness.
When both scales are units, C3 gives the mass exactly. This would classify
which successor sectors have a nonzero harmonic mode. It is a new candidate,
not a verified theorem or a new claim about the full dilation profile.

#### C5 corpus audit and improved paper proof

Direct deep search `research 'Ramanujan correlation' --mode deep
--budget-seconds 120 --exclude-module DilationSuccessorFiberReciprocity`
completed with `partial=false`; inventory 74,172/74,172 files. Semantic
coverage was not measured (reporting budget), and returned candidate compiler
status was source-only, so this is not an exhaustive novelty certificate.
Candidate lemmas/source arguments mainly concern Kloosterman-column
correlations, translation diagonalization, and existing primitive moments.
They supply established character-orthogonality patterns, not the successor
scale selector. No proof idea was returned; ingredient grouping was a
Kloosterman main-term identity, not this determinant identity.

A simpler dependency-closed C5 proof avoids prime factorization. For unit
characters `u,v` with `uq+vp=0`, put `w=ua+vb`. The exact successor equation
implies

```
pw=u,  q(-w)=v.
```

Both right sides are units, so `p,q` are units modulo `r`. Consequently,
if either scale is noninvertible, every inner complete character sum vanishes.
If both are invertible, C3 applies. This proves the proposed complete-period
classification on paper. Formal scratch code has been drafted but not run.

### C4–C5 formal checkpoint

The generic exact period-block sector identity and harmonic remainder bound
now pass the scratch check. The remaining C5 failures were explicit
natural-to-`ZMod` coercions; those are corrected in the original source
`DilationSuccessorSectorHarmonicClassification.lean`, currently checking.
This module contains the exact successor parametrization, all-period mass
classification, its finite-sector remainder bound, and a capstone for
`p=n+2`, `q=n+3`, `a=n+2`, `b=n+1`, `r=m+2` with no hypotheses.
It is not wired into the umbrella until that original-source check passes.

### C6: canonical renormalized successor constant (paper proof)

The finite bound suggests a stronger positive survivor than boundedness.
For `1≤d≤L`, set

```
E_d(K) = progressionHarmonicSum(L,d,K+1) - harmonic(K)/L.
C_d = inf_(K≥0) E_d(K).
```

The successive decrement is exactly

```
E_d(K)-E_d(K+1)
  = 1/[L(K+1)] - 1/[L(K+1)+d]
  ∈ [0, (1/L)(1/(K+1)-1/(K+2))].
```

Hence `E_d` decreases, `E_d(K)-1/[L(K+1)]` increases, and the existing
finite bounds give a common finite limit `C_d`. In particular,

```
0 ≤ E_d(K)-C_d ≤ 1/[L(K+1)].
```

An order-only proof of the last bound: the increasing lower sequence at
index `K` lies below every upper-sequence term, using monotonicity on either
side of `K`; it therefore lies below the infimum. Thus no infinite exchange
of unbounded lag sums is required.

For the actual successor sector, let `Gamma=successorSectorMean(r,p,q)`,
`L=pqr`, `d_t=p(a+qt)`, and `A_t=c_r(a+qt)c_r(b+pt)`. Define

```
C_successor = sum_(t<r) A_t C_(d_t) - Gamma/(pq).
```

The already-proved finite block identity gives, at `H=L(K+1)`,

```
|S_1(H) - Gamma/(pq) harmonic(K) - C_successor|
  ≤ (sum_(t<r) |A_t|)/H + |Gamma|/[pq(H+1)].
```

The cutoff contribution follows from the exact identity
`Gamma/(pq) - (K+1)r Gamma/(H+1) = Gamma/[pq(H+1)]`.
This is a dependency-closed paper argument for a canonical renormalized
limit, including an explicit rate. Formal proof and exact convergence/no-go
classification remain pending; no route is retired.

C6 corpus search `research 'periodic reciprocal harmonic remainder
convergence' --mode deep --budget-seconds 120` completed with no partial
stages, inventory 74,175 files. Semantic coverage was not measured;
candidates were source-only. Returned ingredients mostly matched unrelated
periodic or harmonic bounds. The existing arithmetic-progression finite
bound plus Mathlib monotone convergence is the direct applicable mechanism.
A narrower lexical harmonic-limit search is also recorded in session scratch.

### User steering: corpus audit before further extension

User flagged missed existing work and explicitly requested the Lean corpus
search tool. New proof development is paused while the corpus is searched
with narrower queries and matching source statements/proofs are audited.
The C6 draft exists only at `/tmp/bvi-dilation-renormalized-draft.lean` and
has not been run. Do not promote it before checking whether existing
reciprocal-progression, periodic-source, or digamma results subsume it.
Existing C4–C5 original-source verification remains running; no replacement
Lean process has been started. Prior broad deep queries and unavailable
semantic-coverage measurements were insufficient evidence of novelty.

C4–C5 original-source verification completed: exit 0, no diagnostics, all 17 public declarations. Added umbrella import; public axiom audit is next. The C6 standalone convergence draft is superseded by existing `HTGeometry/DigammaGaussSeries.lean`: its absolute-convergence theorem and exact finite Gauss identity already supply the analytic mechanism. Do not run or promote the infimum-based draft. Audit and reuse these results, including `DigammaAsymptotic.digamma_shift_diff_bound`, before constructing the sector-specific bridge.


### Corpus correction audit: exact reuse map (2026-10-18)

User correction: use the Lean corpus search; existing work was being missed.
Ran documented `research` searches for `digamma progression`, `reciprocal periodic`
(deep), `Ramanujan successor`, `dilation jump`, `Ramanujan covariance`,
`digamma shift`, `Ramanujan correlation`, `digamma harmonic` (both pages),
`periodic harmonic`, `dilation profile` scoped to BVI, and the exact Abel helper.
Search JSON retained under `/tmp/bvi-corpus-audit-*.json` during this session.
The hybrid/deep results reported semantic-retrieval deadlines, stale compiler
coverage, and incomplete refresh while the background indexer was running.
These results are discovery aids, not evidence of novelty or verified applicability.
Lexical hits were followed to original source statements and proofs.

Exact existing dependencies:
- `RHTower.sum_gaussDigammaSeriesTerm_eq_digamma_shift`
  (`HTGeometry/DigammaGaussSeries.lean:170`) gives the finite identity.
- `GaloisForLFunctions.HTGeometry.norm_digamma_shift_sub_le`
  (`HTGeometry/GammaDigammaShiftAnchor.lean:56`) gives the stronger bound
  `norm (psi(z+N)-psi(1+N)) <= norm(z-1)/N` for `0 <= re z`, `1 <= N`.
  This removes even the threshold and factor two of the previously noticed
  `RHTower.digamma_shift_diff_bound`.
- `RHTower.hasSum_digamma_sub`
  (`RHTower/DigammaDifferenceSeries.lean:51`) already supplies convergence of
  reciprocal differences; `hasSum_residueClass_recip` specializes to pronic
  progression weights (`RHTower/ResidueClassRecipSeries.lean:33`).
- `abs_sum_range_mul_antitone_le`
  (`OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError.lean:75`)
  is the generic Abel bound. Existing `InteriorJumpOrbitCenteringAndCompensatedBounds`
  applies it to centered sawtooth jump orbits. Do not re-prove this machinery.

Related existing arithmetic, not a literal replacement for the affine successor
sector identity:
- `BiScaleUncertainty.periodCovariance_eq_ramanujanLagWeight_diagonal` concerns
  divisor-sieve covariance over `N!`; its lag-one eigenvalue is already Mobius.
- `RHTower.pmRamanujanResidueCoeff_periodCovariance` concerns covariance of
  primitive residues, with gcd-square weights and a density correction.
- `Sieve.kloostermanCompleteColumnCorrelation_eq_cglRamanujan` concerns
  Kloosterman column correlation, not products of two affine Ramanujan sequences.
The new fiber statements should be described as explicit coordinate bridges,
not discovery of the classical Ramanujan correlation or generic centering law.

Revised C6 paper target (corpus corollary, not new convergence theory): set
`L=p*q*r`, `N=K+1`, `d_t=p*(a+q*t)`, `alpha_t=d_t/L`,
`C_d=-(re psi(d/L)+EulerGamma)/L`, and
`C_successor=sum_{t<r} A_t*C_{d_t}-Gamma/(p*q)`.
Use the natural centering `harmonic N` (not `harmonic K`). The existing finite
Gauss identity gives
`P(L,d,N)-harmonic N/L-C_d = re(psi(d/L+N)-psi(N+1))/L`.
Thus the exact sector remainder is the finite weighted sum of these digamma
shifts plus `Gamma/(p*q*(L*N+1))`. The existing anchor bounds it by
`sum_{t<r} abs(A_t)*norm(alpha_t-1)/(L*N)
 + abs(Gamma)/(p*q*(L*N+1))`.
A least-positive seed gives `0<alpha_t<=1`, hence the simpler numerator
`sum abs(A_t)` is also available. This proves the intended explicit constant
and decay without the superseded standalone infimum/monotone convergence draft.

Verification update: the C4-C5 axiom audit terminated exit 0. All 17 public declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Together with C1-C3, all 50 public declarations in the four completed modules are now individually axiom-audited. Log: `logs/bvi-dilation-successor-classification-axioms.txt`. The scratch also verified the four previously selected Gauss/asymptotic theorem names against the current toolchain. The newly selected stronger anchor remains to be checked in Lean.


Further exact prior-art check: `TrueTranslationPredictionAndExactCompression.lean:57`
already gives the bilinear complete-period Ramanujan diagonal for literal integer
translation; `RamanujanLagCoefficientAndTotientQuotient.lean` supplies the lag
coefficient and normalized Mobius/totient quotient. These confirm that the
underlying additive spectral law is existing work. The new interface concerns
its affine successor fiber inside the original dilation profile, with the actual
reciprocal jump kernel and finite cutoff retained.

C6 implementation is currently scratch-only. The first Lean check found cast
and real-part normalization issues in the short Gauss coordinate conversion;
no issue with the selected corpus theorem statements. The stronger anchor name
resolved. A corrected check includes the sector-specific finite-part identity,
explicit rate, and convergence corollary. Do not claim C6 verified until terminal
source and axiom checks complete.


### C7 candidate: oriented successor mass as adjacent scales coalesce

This is the next sector-specific candidate, pending a complete paper audit and
formalization. Keep C6 verification separate.

Corpus-first audit: deep `research 'successor dilation limit' --module
BezoutValuationIncidence --budget-seconds 300 --per-module 0 --json` completed
with `partial=false`; candidate/source hits include the existing dilation cube,
our finite-horizon bridge, successor prediction, and birth-delayed sawtooth
centering. Lexical `coalesc` scoped to BVI returned no hits. This does not prove
novelty. `pmRamanujanDilationProfile continuous` found the already formalized
`continuousOn_pmRamanujanDilationProfile` and `pmRamanujanDilationProfile_one`
in `RHTower/PMRamanujanNearbyPrimeResonance.lean`. `Ramanujan norm bound` found
`Sieve.norm_cglRamanujanAdditiveSum_le_totient` in
`RHTower/Sieve/StadlmannReciprocalPhaseApplications.lean:206`.
These supply the analytic continuity and coefficient majorant; reuse them.

At the single complete-block horizon H=r*p*q, let S=S_1(H).
For p=q+1 (q>=1), the least seed is (a,b)=(1,1), and the exact finite formula is
`p*S = sum_{t<r} A_t/(1+q*t) - p*sum_{t<r} A_t/(H+1)`.
The t=0 term is mu(r)^2. If `abs(A_t)<=phi(r)^2`, all remaining terms are
O_r(1/q), and the boundary is O_r(1/q); a coarse bound is
`abs(p*S-mu(r)^2) <= r*phi(r)^2/q`.
For q=p+1 (p>=2), the least seed is (a,b)=(p,p-1). Every denominator
`a+q*t` is at least p, giving
`abs(p*S) <= (r+1)*phi(r)^2/p`.
Thus the proposed oriented limits of the actual normalized sector are
`sqrt(p*q)*S_1(r*p*q) -> mu(r)^2` from p=q+1, but `->0` from q=p+1.
The full profile has the same continuous limit Phi_r(1) from both sides, by
existing continuity. The signed complement must carry the corresponding
compensating limits. This would expose orientation-sensitive additive mass
inside a continuous dilation profile; it is not a claim that a single sector
controls the full Gram energy, nor permission to rearrange infinite lag sums.
No C7 Lean theorem has been written or claimed verified yet.


C6 source verification: `DilationSuccessorDigammaRenormalization.lean` now passes
`lake --old env lean -j 1 -o ... -i ... <original source>` with exit 0 and no
diagnostics, after removing one unused tactic. It has 10 public declarations:
the progression finite part and its exact/rate bridges; the sector constant and
tail mass; exact centered-sector identity; quantitative remainder; convergence;
and two no-hypothesis consecutive-scale capstones. Wired into the BVI umbrella.
The README now documents all five completed source modules and explicitly
credits the existing finite Gauss identity and sharp shift anchor.
Log: `logs/bvi-dilation-successor-digamma-original.txt` (empty, clean).
The separate `/tmp/bvi-dilation-digamma-axioms.lean` audits all 10 public
symbols and both imported analytic theorems; its run is still pending at this
checkpoint. `scripts/formal_tools.py index` completed exit 0, regenerating the
three formal index documents and reporting 0 changed/removed search entries
(the background indexer had already ingested the source).


Global lint result: exit 1, with two structural errors outside this work's
source set: `NaturalCutoffMultiDepthCofactorAndConditionalTailBridge` is not
reachable from the BVI umbrella; `TransHorizonIncidenceMechanics.lean` is treated
as a research leaf at package root. Full log:
`logs/bvi-dilation-successor-lint.txt`. Do not claim the global lint gate passed.
The current umbrella diff also contains concurrent imports for
`BirthDelayedInteriorJumpCenteringAndUniformPairBounds` and
`PronicResidueGapEnergyAndPrimePairDistance`; these were preserved.
Our only additions to that diff are the C4-C5 classification and C6 digamma
module imports. Axiom audit of C6 is now running separately.


Additional C7 prior-art audit: corpus query `prime pair distance` found
`PronicResidueGapEnergyAndPrimePairDistance.lean`. Read its quotient-cell setup
and all public results. It already provides an exact pre-overlap harmonic
residue-gap prefix, two-sided gap budgets, the identity between actual
energy-centered prime-mode distance and residue energy minus squared log-mean
difference, and a symmetric prime-pair gap bound. Reuse this for nearby-prime
transport; do not re-prove these estimates. Its variable-modulus residue
energy differs from C7's fixed-modulus, oriented finite successor sector.
C7 remains a candidate; the new corpus theorem names must be checked in Lean
before any use, as with the already verified C6 dependencies.


C6 verification closed: the separate axiom audit terminated exit 0. All 10
public C6 declarations, and the two reused Gauss/shift-anchor theorems, have
exactly the standard axiom set `propext`, `Classical.choice`, `Quot.sound`.
Log: `logs/bvi-dilation-successor-digamma-axioms.txt`.
Across C1-C6, all 60 public declarations in the five source modules now have
original-source compilation and individual axiom audits. No full/umbrella
build was run. The superseded infimum-convergence draft and merged scratch
fragments were removed; canonical sources and audit logs remain.
C7 is still the next candidate, not a verified result. Its prior-work audit
must include the existing profile continuity, CGL totient bound, and the
recent pronic residue-gap/prime-pair distance module recorded above.
The research goal remains active.

Final lint retry followed concurrent repair of the NaturalCutoff umbrella import. It still exits 1 with: error: research leaf module at package root: TransHorizonIncidenceMechanics.lean; move it into an owned theorem area
Log: `logs/bvi-dilation-successor-lint-final.txt`. This remains outside the edited source set. No owned Lean/check/search process remains running at this checkpoint.


### C7 strengthened: least-successor resonance at arbitrary high scales

Previous goal turn: PROGRESS. C6 changed authoritative source state and completed
original-source and axiom checks; it did not close the endless research goal.
Current attachment and worktree rechecked. The adjacent-scale candidate alone
is too narrow for the requested arbitrary large prime pairs. Retain it as a
corollary; prioritize the following all-scale statement.

Current corpus audit: lexical `successor seed` returned four existing C4-C5
interfaces; exact `norm_cglRamanujanAdditiveSum_le_totient` returned the existing
Sieve bound. Deep query describing isolation of the least positive Bezout
solution in the dilation sector returned all 20 candidate lemmas and all 20
source arguments; these were inspected. It reported `partial=true`, unfinished
reranking. Relevant dependencies are the already verified exact period-block
sector identity, gcd exclusion, finite profile coupling, and the CGL totient
bound. No novelty conclusion is inferred from missing hits. Latest related
memories also caution against replacing actual signed rows or natural cutoff
order by a generic covariance bound. C7 preserves the entire signed complement.

Dependency-closed paper argument:
1. Let r>=1 and p,q>1 be coprime. Existing seed existence gives unique least
   positive (a,b), with 1<=a<=q, b>=1, pa=qb+1. Existing parametrization gives
   every positive solution (a+qt,b+pt). Set M=phi(r)^2,
   A_t=c_r(a+qt)c_r(b+pt), H=rpq.
2. Existing complete-period sector identity at one block gives
   `p*S_1(H)=sum_{t<r} A_t/(a+qt)-p*sum_{t<r} A_t/(H+1)`.
   Existing CGL bound gives abs(A_t)<=M.
3. Isolate t=0. For t>=1, a+qt>=q; the r-1 remaining terms cost at most
   `(r-1)*M/q`. The full boundary costs at most
   `p*r*M/(rpq+1)<=M/q`. Therefore
   `abs(p*S_1(rpq)-c_r(a)c_r(b)/a)<=r*phi(r)^2/q`.
4. Choose the existing unique bounded seed intrinsically; set its resonance
   to zero when p,q are not coprime. Existing gcd exclusion makes S_1 zero
   in that case too. Thus the same bound is unconditional for all p,q>1.
   The no-hypothesis capstone uses p=n+2,q=m+2,r=k+2, so it includes all
   sufficiently large prime pairs, rather than assuming a prime-gap theorem.
5. Multiply by sqrt(q)/sqrt(p). The actual profile normalization satisfies
   `abs(sqrt(p)*sqrt(q)*S_1(rpq) - sqrt(q)/sqrt(p)*resonance)
    <= r*phi(r)^2/(sqrt(p)*sqrt(q))`.
6. Combine with the existing finite-lag profile error, keeping every other lag
   signed and at the same physical horizon H=rpq. Replacing only the successor
   term by this intrinsic least-seed resonance adds the above error to
   `sqrt(p)*sqrt(q)*B_r^2/(H+1)`. This is the intended direct arithmetic
   refinement of the original dilation profile, with explicit high-scale error.

Plan: verify existing bound/API names and prove seed-isolation estimate;
package intrinsic seed and actual normalized profile capstone; audit original
source/all public axioms, wire umbrella, refresh index and run lint. Do not
claim signed coercivity or a bound for an entire unmodified prime packet.


C7 implementation checkpoint: initial scratch compiled the existing totient
bound bridge and the exact scaled one-block identity. The only failure in the
seed-isolation estimate was using the three-point `abs_sub_le` lemma with two
arguments; replaced by the already verified `abs_add_le` applied to a negative.
Current scratch `/tmp/bvi-c7-least-seed-draft.lean` additionally contains intrinsic
seed selection (using existing CRT existence), the noncoprime-zero branch,
actual sqrt-normalized estimate, full-profile signed-complement coupling, and
an unconditional uniform capstone at p=k+n+2,q=k+m+2,r=R+2.
The uniform error is `(B_r^2/r+r*phi(r)^2)/(k+2)`.
This is still scratch, not claimed verified. Current owned Lean process:
exec session 56039, `lake --old env lean -j 1 /tmp/bvi-c7-least-seed-draft.lean`,
log `/tmp/bvi-c7-least-seed-draft.log`. Await terminal before any other Lean run.
Merged snippets remain `/tmp/bvi-c7-intrinsic-snippet.lean` and
`/tmp/bvi-c7-uniform-snippet.lean`. The successful prototype APIs include the
CGL totient bound and Finset erase/card identities. On promotion, narrow the
scratch import from DilationSuccessorDigammaRenormalization to
DilationSuccessorSectorHarmonicClassification: C7 uses the finite sector
formula, not C6's digamma analysis. Verify that narrowed original source.

C7 scratch session 56039 terminated exit 1 with three redundant `ring` calls
after `field_simp` had closed the goals, and one reversed use of
`mul_div_assoc`. These were repaired. Replacement owned session 99103 is
checking the same scratch and log; await its terminal result.

### C8 candidate: transport the existing valuation clock to actual jump sectors

Corpus searches `Ramanujan visibility`, `Ramanujan radical`, and
`d4BMRamanujanNaturalCoefficient` located the existing exact support theorem
`ramanujanLagCoefficient_ne_zero_iff` in
`ValuationVisibilityClockAndRamanujanSupport.lean`, and the natural-coefficient
gcd-divisor formula. The deep clock/gap query and hybrid coefficient-bridge
query both completed without partial results; all 20 candidate lemmas and all
20 source arguments in each were inspected. Coverage inventories are complete,
but compiler freshness is mixed and the background indexer is running. Thus
source inspection and Lean checks remain necessary. Broad-query misses are
not evidence of novelty. A targeted joint-clock query is still running.

The hybrid search also exposed the older exact `pm_ramanujan_at_one` theorem
in `PMPowerDampedMobiusRamanujanWeights.lean`; the C3 public wrapper should reuse
that theorem instead of repeating its divisor calculation, once the API is
verified. The existing real lag-coefficient gcd-sum proof is private; expose a
small public interface if needed rather than duplicate its arithmetic proof.

Paper argument for the next bridge, not yet formalized:
1. Identify `Re(d4BMRamanujanNaturalCoefficient a r)` with the existing real
   `ramanujanLagCoefficient r a` using their proved divisor formulas.
2. Existing visibility gives nonzero coefficient iff `r!=0` and `v|a`, where
   `v=lagVisibilityClock r=r/rad(r)`. For nonzero pair amplitude, `v|a` and `v|b`.
3. Put `g=gcd(p,q)`. Since `g|p,q`, divisibility multiplies: `v*g|p*a` and
   `v*g|q*b`, hence `v*g|h=p*a-q*b`. This is a product clock, stronger than
   separately imposing `v|h` and `g|h`.
4. Every forbidden lag sector is exactly zero at every finite horizon. The
   original profile may therefore be coupled to just the finite set of lags
   divisible by `v*g`, with the existing cutoff error unchanged.
5. At `h=1`, any nonsquarefree positive modulus has `v!=1` and therefore the
   whole successor sector vanishes, not merely its period mean. The positive
   survivor is the clock-selected family of higher lags. No claim that an
   allowed sector is nonzero: signed cancellation can still occur.

First close C7 original-source verification. Then verify/reuse the coefficient
bridge APIs and prove C8's exact finite selection and actual-profile capstone.

C7 scratch session 99103 terminated exit 0 with empty log. Promoted its 11 public
declarations to `DilationSuccessorLeastSeedResonance.lean`, narrowing imports to
the finite harmonic-classification module and the existing CGL bound. The
original-source check is now running; log
`logs/bvi-dilation-successor-least-seed-original.txt`. No claim of completion
until that check and its axiom audit terminate.

The targeted C8 query completed (`partial=false`); inspected all 17 lexical
declarations, 20 candidates, and 20 source arguments. It additionally identified
the existing zero-below-clock corollaries in
`NonMarkovianLagOperatorAlgebraAndPrimePowerRevival.lean`. Those are compressed
translation coefficients, not the new physical dilation sectors. The useful
positive refinement of C8 is exact pointwise support: a pair coefficient is
nonzero iff `r!=0` and `lagVisibilityClock r | gcd(a,b)`. On a successor fiber,
existing coprimality makes this equivalent to `Squarefree r`. This is a
pointwise statement; squarefree modes can still have zero signed sector sums.

C7 verification closed: original source and separate `/tmp` axiom audit both
terminated exit 0. All 11 new public declarations, the reused CGL totient bound,
and the older `pm_ramanujan_at_one` have only `propext`, `Classical.choice`,
`Quot.sound`. Logs: `logs/bvi-dilation-successor-least-seed-original.txt` and
`logs/bvi-dilation-successor-least-seed-axioms.txt`. Module wired; README records
the exact least-seed term, uniform bound, and signed-complement limitation.
The older coefficient API was also verified by a `have := @...` probe. The C3
wrapper now delegates to it; its original source still needs rechecking.

C8 scratch is `/tmp/bvi-c8-jump-clock-draft.lean`: 11 prospective public results
cover the real-coefficient bridge, exact pair support, squarefree successor
boundary, product-clock exclusion, finite filtration, and actual-profile
capstone. It awaits Lean checking. The existing private gcd-divisor proof has
a new public all-modulus wrapper `ramanujanLagCoefficient_eq_gcd_divisor_sum`;
its original-source check is running as owned session 84368, log
`logs/bvi-dilation-clock-lag-interface-original.txt`. No second owned Lean job
may start until that session terminates.

C9 exploration only: a deep radical/dilation query completed without partial
results; all 20 candidates and 20 source arguments inspected. It returned
existing primitive residue formulas and prime-power coefficient cancellation,
but no direct radical reduction of the actual profile. A `totient radical`
lexical query returned nine mainly unrelated declarations. Possible next
candidate: `c_r(v*n)=v*c_rad(r)(n)` and its primitive/profile transport, with
`v=r/rad(r)`. This has not received a complete paper or prior-art audit; no
new C9 code or novelty claim. Finish the C8 checks first.

C8 first scratch check (session 60890) terminated exit 0 with empty log. The
public gcd-divisor wrapper's original-source check (84368) also exited 0.
Promoted the 11 clock results to `DilationJumpValuationClock.lean`; original
source is running as session 40120, log `logs/bvi-dilation-jump-clock-original.txt`.
The module is wired and documented. Next: await 40120, recheck the simplified
C3 original source, then run `/tmp/bvi-c8-jump-clock-axioms.lean` to audit all
11 new declarations, the new public divisor interface, the changed C3 wrapper,
and both reused valuation-support results. No concurrent owned Lean process.

Additional C9 search evidence: targeted profile query returned and inspected
all 10 candidates and 10 source arguments in `DilationProfileIntegerJumpCoupling`.
Its existing `pmRamanujanDilationProfile_eq_integerDilationGram` already gives
the exact normalized pronic series. If the coefficient scaling is proved,
the existing `sum_ramanujanDilationJump` transports it to
`A_r(N)=v*A_rad(r)(N/v)`, and the profile formulas at scales `(v*p,v*q)` would
give `Phi_r(p/q)=v*Phi_rad(r)(p/q)` by ordinary scalar algebra. No new analytic
convergence theorem should be needed. The lexical `totient primeFactors`
query found `RHTower.prod_one_sub_inv_primeFactors_eq_totient_div`; inspecting
that source exposed `Nat.totient_mul_prod_primeFactors`, the likely smaller
dependency for the required totient scaling. These APIs still need fresh
scratch verification before C9 implementation, and the coefficient/radical
identification still needs a complete audit.

C8 original source (40120) terminated exit 0 with empty log. C3's simplified
original source is now checking as session 88184, log
`logs/bvi-dilation-successor-fiber-reuse-original.txt`; axiom audit follows it.
Index refresh (47556) exited 0. The quoted exact lexical query for the two new
capstones returned exactly two declarations in their canonical new modules:
`/tmp/bvi-c7-c8-discoverability.json`. Global lint (96659) exited 1 with only
`research leaf module at package root: TransHorizonIncidenceMechanics.lean;
move it into an owned theorem area`; full output is
`logs/bvi-dilation-successor-clock-lint.txt`. No global lint pass is claimed.

### C9 paper candidate refined: radical reduction of the actual rational profile

This is a proposed connection of classical coefficient identities to the
existing physical profile, not a novelty claim for Ramanujan sums. For R>1,
put s=rad(R), v=R/s, and c_R(a)=Re(d4BMRamanujanNaturalCoefficient a R).
1. The distinct-prime product has exactly R's prime factors, is squarefree,
   and divides R. Thus R=v*s, v>0, s>1. Prime membership follows by Euclid's
   product lemma in both directions; squarefreeness follows from distinctness.
2. The existing totient prime-factor product identity at R and s gives
   phi(R)=v*phi(s). Also gcd(R,v*n)=v*gcd(s,n), so the quotient in the existing
   Mobius/totient formula is unchanged. Consequently c_R(v*n)=v*c_s(n).
   C8's support theorem gives zero at every remaining index.
3. Equivalently, c_R(n)=v*ramanujanDilationJump s v n for every n. Sum with
   the existing `sum_ramanujanDilationJump` to obtain A_R(N)=v*A_s(N/v).
4. Substitute into the existing exact integer-dilation Gram formula. Natural
   floor division composes, giving G_R(p,q)=v^2*G_s(v*p,v*q). The ratio of
   the enlarged scales is still p/q and their square-root normalization gains
   a factor v. Therefore Phi_R(p/q)=v*Phi_s(p/q) for all positive p,q.
5. The requested no-hypothesis capstone can use R=r+2,p=n+1,q=m+1, deriving
   v>0,s>1 internally. The rational-scale result already covers all prime pairs;
   no new continuity or convergence argument is needed for this scope.

Before implementing C9, audit existing radical/coefficient interfaces more
precisely and verify each selected API in Lean. C9 remains unformalized.

Potential next finite-horizon refinement, requiring its own corpus audit:
at H=v*(T+1)-1, coefficient support and the reciprocal kernel suggest
`S_(R,v*k)(H)=v*S_(s,k)(T)`. For arbitrary H and T=floor(H/v), retain the exact
boundary defect
`v*(1/(T+1)-v/(H+1))*sum_(gap k at T) c_s(a)*c_s(b)`.
The aligned-horizon formula makes this defect zero. This candidate keeps the
physical cutoff correction explicitly; it is not a proved Lean result.

Final-check checkpoint: C3 original session 88184 terminated exit 0 with empty
log. All four changed/new Lean source files now have successful original-source
checks. The only owned Lean process is axiom-audit session 63671:
`lake --old env lean -j 1 /tmp/bvi-c8-jump-clock-axioms.lean`, log
`logs/bvi-dilation-jump-clock-axioms.txt`. Await terminal before any new Lean
process. Five superseded/merged C7-C8 scratch drafts and snippets were removed;
canonical sources, search evidence, audit scripts and logs remain.

C8 verification closed: axiom session 63671 terminated exit 0. All 11 new
clock declarations, the exported gcd-divisor identity, the changed C3 wrapper,
and both reused visibility theorems have exactly `propext`, `Classical.choice`,
`Quot.sound`. Log: `logs/bvi-dilation-jump-clock-axioms.txt`.
Across C1-C8, the seven pipeline modules contain 82 public declarations with
original-source checks and individual axiom audits; the one newly exported
interface in the pre-existing lag-coefficient module is separately checked
and audited too. No full/umbrella build, heartbeat increase, numerical
experiment, commit, or push was performed. Scoped whitespace check passed.

The final C9 search materially improved the next dependency plan. Exact lexical
lookup of the known Mathlib name returned no hit; switching to a mechanism-based
deep search recovered `Nat.totient_mul_prod_primeFactors`,
`Nat.totient_eq_mul_prod_factors`, and, more directly,
`Nat.totient_eq_div_primeFactors_mul` in
`formal/.lake/packages/mathlib/Mathlib/Data/Nat/Totient.lean:306`:
`phi(n)=(n/prod_(p|n) p)*prod_(p|n)(p-1)`.
All 20 candidates, 20 source arguments, and the proposed two-step ingredient
set were inspected. Search session 31192 terminated exit 0; JSON is
`/tmp/bvi-c9-totient-product-hybrid-research.json`. It reports `partial=true`,
two unfinished expansion queries, and reranking deadline expiry; available
exact hits are useful, not a complete novelty audit. The ingredient set is
explicitly unverified. Verify these names in a scratch file before C9 use.

Current checkpoint: C7 and C8 complete; C9 remains the recorded paper candidate
and next corpus/API audit. No owned Lean, search, index, or lint process remains
running. Global lint's unrelated root-module placement error remains recorded
above. The unbounded research goal remains active.

### C9 active implementation and current-state audit

Previous goal turn: PROGRESS (C7/C8 original sources, axiom audits and corpus
discoverability completed). Attachment reread; no RH work or hgtl7. Current
README was concurrently rewritten to a 134-line thematic guide; read the new
version fully and preserve that structure. The separate active-deleted
remainder memory concerns problem 4, not this task. Architecture/testing docs
remain absent. No plan tool is available; this card tracks the steps.

Fresh deep query `/tmp/bvi-c9-radical-bridge-audit.json` completed with
`partial=false`; all 20 candidates, 20 source arguments and the proposed
ingredient set were inspected. It locates the existing clock support, prime
power clock values, composite wavelet tensor, and original profile identities.
It does not verify the radical-profile bridge. Compiler/semantic coverage
warnings remain; absence of a hit is not a novelty claim.

The first core scratch `/tmp/bvi-c9-radical-core-draft.lean` (69531) exited 0.
It verifies the selected totient/divisibility APIs and proves private radical
positivity, prime-factor equality, radical-times-clock identity, clock
positivity, radical>1 for r>1, and phi(r)=clock(r)*phi(rad(r)). These reuse the
existing `primeRadical` definition and `Nat.totient_eq_div_primeFactors_mul`.
One implicit unused-binder warning was fixed. Added four prospective public
coefficient/primitive transport results to that scratch; current owned Lean
session 84931 is checking it, log `/tmp/bvi-c9-radical-core-draft.log`.
Await terminal before another Lean job. No C9 canonical module exists yet.

Plan: finish exact coefficient/primitive transport; derive the original
rational-profile reduction from the existing integer-dilation Gram identity;
package an unconditional shifted-natural capstone; audit original source and
all public axioms, wire it, refresh index/lint. The subsequent finite-horizon
clock-rescaling candidate must retain its recorded boundary defect.

README correction from corpus evidence: its new non-Markovian warning wrongly
used lag 2 for arbitrary prime-square revival and claimed squarefree support
restores composition. `sieveLagMultiplier_prime_pow_revival_at_clock` puts
revival at the actual clock p^a; `nonMarkovianLagDefect_first_octave_table`
already gives nonzero composition defects for squarefree modes 3 and 6. Both
names passed the scratch probe. Corrected both README mentions, preserving
the concurrent thematic rewrite. No numerical experiment was used.

C9 coefficient/primitive scratch session 84931 terminated exit 0. Added the
integer Gram transport, rational-profile reduction and data-only capstone.
The first extended run 99937 was cancelled by its owned Lean PID 41733 and
confirmed terminal exit 143 after spotting a recursive simplification risk;
the primitive rewrite is now specialized to the original modulus. Current
extended check is session 18144. No competing owned Lean check was started.

### C10 candidate: physical clock sector and its cutoff defect

Write s=rad(r), v=clock(r)>0, T=floor(H/v), and let M_s(k,T) be the finite
signed coefficient mass over the same multiplier pairs as S_s(k,T). The
candidate exact law is

`S_r(v*k,H) = v*S_s(k,T) + v*(1/(T+1)-v/(H+1))*M_s(k,T)`.

Paper derivation: C8 kills all pairs outside v-multiples; C9 changes their
coefficients to v times the s-coefficients. Reindex (a,b)=(v*a',v*b'); the
physical gap becomes v*(p*a'-q*b') and the multiplier horizon becomes H/v.
The exact reciprocal kernel is `1/(v*max(p*a',q*b'))-1/(H+1)`.
Multiplying by v^2 and subtracting v times the kernel at T leaves precisely
the displayed boundary coefficient, independent of the pair. All sums are
finite at one physical cutoff. At H=v*(T+1)-1 this defect vanishes.

This is the positive continuation of C8's nonsquarefree successor obstruction:
the original lag-1 sector vanishes, but the squarefree successor sector can
survive at original lag v. No positivity of its signed sum is asserted.
After formalising the transport, combine with the existing least-seed theorem
at s; keep the full signed complement and the physical cutoff error.

Prior-work audit underway: deep query is `/tmp/bvi-c10-clock-sector-prior-research.json`
(session 81037). Exact lexical search `/tmp/bvi-c10-dvd-reindex-research.json`
completed and returns the existing generic `sum_Icc_filter_dvd_reindex` in
`RHTower/EulerDeletionQuasiShuffleConvergence.lean:95`; its full signature and
proof were read. Reuse it instead of reproving a divisor reindexing bijection.
The broad lexical radical/cutoff query returned 20 ranked and 5 exploration
hits, all inspected; it mainly recovers existing radical products and clock
interfaces, not the finite sector identity.

Concurrent frontier update: newly present
`RamanujanOrderedGapCollectivePrefixEnergy.lean` already transfers ordered
gap-chain prefix energy to the actual Ramanujan carrier and gives a bilinear
prefix bound with signed packet retained. Its header and both public bound
statements were read. This is separate from clock rescaling; do not rederive
that prefix estimate or claim it controls the later signed tail. The current
source explicitly leaves that tail unresolved. No edits to that author's files.

C9 original-source audit completed: session 46401 exited 0 with no diagnostics.
Canonical `RamanujanRadicalDilationReduction.lean` has seven public theorems,
ending in `dilation_profile_radical_reduction` with data parameters only.
The exact result is `Phi_r(p/q)=clock(r)*Phi_rad(r)(p/q)` for every positive
rational scale; all arithmetic helpers reuse the existing radical and totient
interfaces. Umbrella wired; thematic README entry added without replacing its
concurrent rewrite. Log: `logs/bvi-radical-dilation-reduction-original.txt`.
The preceding extended scratch 18144 had no proof errors; its only error was
the universe-unspecified API probe `have := @tsum_mul_left`. That probe is
corrected to `@tsum_mul_left Nat Real` in the next scratch, not in canonical source.

C10 deep search 81037 completed exit 0 with `partial=false`, but declarations
were mostly irrelevant and source arguments were more useful. All 20 candidates,
20 source arguments and the proposed ingredient set were inspected. It returns
our existing pair/sector/cutoff interfaces and the newer signed gap packet
residue expansion. Coverage is source-complete but compiler metadata largely
pending/stale, snapshot older than current generation, semantic coverage not
measured. No novelty conclusion follows from the search's missing sector bridge.

Current owned Lean session: 9516, checking `/tmp/bvi-c10-clock-sector-draft.lean`.
It prints axioms for all seven completed C9 public declarations, verifies the
new arithmetic APIs, and checks C10 weighted-sum reindexing, scaled kernel,
signed boundary formula, aligned-cutoff transport and data-only successor
capstone. Log: `/tmp/bvi-c10-clock-sector-draft.log`. No C10 canonical file yet.
Await its terminal handle before another Lean run.

The aligned-horizon lexical API query had zero hits. Direct installed core
source exposes `Nat.add_mul_div_left` in `Init/Data/Nat/Div/Basic.lean:323`;
its exact signature is used in the scratch probe. A rephrased deep query
`/tmp/bvi-c10-quotient-mechanism-research.json` is running to audit the quotient
mechanism rather than assuming index coverage of that exact name.

### C11 paper continuation: genuine clock-successor resonance in the profile

The concurrent `BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge`
was searched directly (`/tmp/bvi-c11-concurrent-radical-bridge-audit.json`,
two hits, both inspected). Its Tool 2 theorem packages the already established
C2/C7 interfaces, including `dilation_profile_least_successor_seed_uniform`;
the radical-fibre statement concerns a different prefix-defect observable.
Read the Tool 2 proof, which directly invokes C2/C7. No duplicate wrapper needed.

For r>1, p,q>1, s=rad(r), v=clock(r), set T=p*q*s and H=v*(T+1)-1.
After C10, the original physical clock sector obeys

`|sqrt(p*q)*S_r(v,H)-v*sqrt(q/p)*leastSeedResonance_s(p,q)|`
` <= v*s*phi(s)^2/sqrt(p*q)`.

This follows by multiplying the existing
`abs_normalized_successor_sector_sub_leastSeed_le` at the positive modulus s
by v and using the aligned transport, not by a new harmonic argument. Combining
with the original profile cutoff theorem gives the same error plus
`sqrt(p*q)*B_r^2/(H+1)` after retaining the full signed complement
`sum_h S_r(h,H)-S_r(v,H)`.

The seed at the radical is nonzero exactly when p,q are coprime: the existing
least-seed specification supplies the gap-1 pair and positive denominator;
`successor_pair_re_ne_zero_iff_squarefree` and `squarefree_primeRadical` supply
its nonzero numerator. Noncoprime scales use the existing zero-seed branch.
This is an exact positive survivor of the nonsquarefree lag-1 obstruction,
not a claim that the complete profile or remaining signed sectors are positive.
Formalise after C10 is checked; do not infer a global cancellation bound.

C9 axiom audit is closed: session 9516 printed all seven public closures,
each exactly `propext`, `Classical.choice`, `Quot.sound`. The full run exited 1
only because C10's aligned-cutoff proof left `1-1=(T+1)*0` after `field_simp`.
That final normalization was repaired with `ring`. Preserved C9 audit output
in `logs/bvi-radical-dilation-reduction-axioms.txt` and replay commands in
`/tmp/bvi-c9-radical-axioms.lean`; the complete failed scratch log is retained.
All new API probes, including `tsum_mul_left Nat Real`, elaborated successfully.

C10 canonical original-source check 98982 terminated exit 0, no diagnostics.
`DilationClockSectorBoundaryAndSuccessorTransport.lean` has seven public
theorems and one definition. It proves the exact boundary formula and the
data-only physical clock-successor transport. Umbrella and thematic README
wired. Log: `logs/bvi-clock-sector-transport-original.txt`.

The rephrased quotient search 37897 completed `partial=false`; all 20
candidates, 20 source arguments and the proposed ingredient set were inspected.
Useful related source: `Nat.add_div_of_dvd_left`; most returns were unrelated.
The installed core's verified `Nat.add_mul_div_left` is the direct mechanism
actually used. Compiler/semantic coverage caveats remain unchanged.

Next scratch `/tmp/bvi-c11-clock-seed-draft.lean` is now checking C11 and printing
the eight C10 public axiom closures in one owned Lean process. It contains four
prospective public theorems: exact radical-seed nonvanishing iff scale coprimality,
the scaled normalized clock-sector bound, the actual profile with its full signed
complement retained, and a data-only combined capstone. No C11 canonical module
exists yet. Read its terminal output before another Lean process.

Current C11 Lean session is 69379; log `/tmp/bvi-c11-clock-seed-draft.log`.

### Next frontier audit: nonzero seed versus nearby-prime sector size

C11's nonzero radical seed must not be mistaken for a uniform lower bound.
The next corpus audit is `/tmp/bvi-c12-nearby-clock-sector-prior-research.json`:
nearby prime profiles, fixed successor lag, least Bézout seed, and retained
signed complement. Its outcome must be inspected before selecting C12.

Source-derived geometric question: if p*a=q*b+1 and q>p, then a>b and
`(q-p)*a=q*(a-b)-1 >= q-1`. If p>q and p-q>1, then b>a and
`(p-q)*a=q*(b-a)+1 >= q+1`. Thus near-equal scales with gap greater than one
force the least seed denominator large. The difference-one case is essential:
for p=q+1, (a,b)=(1,1) is a genuine fixed seed, so no universal nearby-integer
vanishing claim is valid. Large distinct odd primes avoid this exception.

Combined with the already proved coefficient bound and C11's normalized sector
estimate, this suggests a quantitative smallness bound for the isolated clock
sector at nearby large primes. The existing continuous profile has a positive
value at ratio one, so the positive survivor to audit is an explicit transfer
of the profile to its retained signed complement. No global cancellation or
prime-spacing assumption is to be inserted. A nonvanishing statement alone
does not close this question; check the actual corpus and domain before Lean.

C11 scratch 69379 terminated exit 0. All four new seed/profile proofs passed,
as did all eight C10 public axiom prints; every closure is exactly `propext`,
`Classical.choice`, `Quot.sound`. C10 audit log is
`logs/bvi-clock-sector-transport-axioms.txt`; minimal replay file is
`/tmp/bvi-c10-clock-sector-axioms.lean`.

C11 promoted to `DilationClockSuccessorSeedCoupling.lean` (four public theorems,
139 lines). Its original-source audit is the sole owned Lean session 56350,
log `logs/bvi-clock-successor-seed-original.txt`. C12 prior-work search is
session 90555, still pending. No C12 Lean code exists.

Removed merged C9/C10 scratch drafts and the uninformative owned-process sample;
kept original sources, audit replay files, complete check logs and research JSON.
Scoped whitespace check passed after removing one extra README EOF blank line;
concurrent new thematic entries were preserved.

C12 corpus audit 90555 completed exit 0, `partial=false`. All 20 candidate
and 20 source-argument statements were inspected. Most candidates and the
suggested prime-density ingredient set are irrelevant to the geometric bound;
do not introduce a prime-counting argument from those suggestions. Relevant
existing work is `PMRamanujanNearbyPrimeResonance`: its actual profile is
continuous on positive scales, equals the positive diagonal Gram at 1, and
the prime-insertion Gram has an explicit profile error. Read both relevant
source argument proofs, including the use of existing
`exists_prime_pair_ratio_lt`; do not reprove prime realization or continuity.
Coverage inventory is complete, semantic coverage unmeasured, compiler metadata
mostly pending/stale, and background refresh incomplete.

The focused lexical follow-up `/tmp/bvi-c12-seed-lexical-research.json` returns
14 hits, all inspected. Besides C7/C11 it includes the already formalized
`consecutive_scale_successor_harmonic_coupling`, consistent with the essential
adjacent-integer exception. It does not supply the proposed near-equal prime
seed-size estimate. This is not a corpus-wide novelty claim.

Dependency-closed paper target for C12: let d=abs(p-q), with p,q>1 and either
p<q or q+1<p. For the intrinsic seed (zero when the scales are noncoprime),
`abs(leastSeedResonance_s(p,q)) <= phi(s)^2*d/(q-1)`.
In the coprime branch the geometric inequalities recorded above give
`q-1 <= d*a`; the existing amplitude bound gives
`abs(seed)*a <= phi(s)^2`. Multiply the first inequality by abs(seed), then
use the second and divide by q-1>0. In the noncoprime branch the seed is zero.
Combining this bound with C11 yields an explicit relative-gap plus inverse-scale
bound for the original clock sector and an approximation of the actual profile
by its retained signed complement. For near-equal large primes, the known
positive profile limit prevents this complement from disappearing. This is
the positive survivor to formalize; no route is retired on the negative
single-sector observation alone. No C12 Lean code has been written.

C11 original-source audit 56350 terminated exit 0 with no diagnostics. Module
is wired once into the umbrella, with a narrow thematic README entry. Its four
public axiom prints are the sole owned Lean session 23283, replay file
`/tmp/bvi-c11-clock-seed-axioms.lean`, output
`logs/bvi-clock-successor-seed-axioms.txt`.

Index refresh 45826 terminated exit 0; generated API/gaps/overview refreshed,
cached lexical DB reported 0 changed/removed after background ingestion.
Index log: `logs/bvi-clock-radical-seed-index.txt`. Final guarded lint is
session 55115, log `logs/bvi-clock-radical-seed-lint.txt`. Whitespace and direct
forbidden-declaration scans of all three new sources passed; each import appears
once. Exact quoted-capstone discoverability search 21543 completed exit 0;
JSON: `/tmp/bvi-c9-c11-discoverability.json`.

Discoverability search returned exactly the three new capstones, with canonical
paths/lines: radical reduction 171, clock-successor transport 222, and combined
clock-seed profile coupling 117. All three hits inspected.
Final lint 55115 terminated exit 1, with 381 large-file warnings and exactly the
same unrelated error recorded at C8:
`error: research leaf module at package root: TransHorizonIncidenceMechanics.lean; move it into an owned theorem area`.
No active forbidden-declaration error is reported. The global lint gate has
not passed; no edit to that unowned root module. C11 axiom session 23283 remains
the sole owned process; all search/index/lint jobs are terminal.

C11 axiom session 23283 terminated exit 0. All four public declarations have
exactly `propext`, `Classical.choice`, `Quot.sound`; log
`logs/bvi-clock-successor-seed-axioms.txt`. Removed the merged C11 scratch,
retaining its complete successful log and minimal `/tmp` axiom replay file.

Checkpoint outcome: PROGRESS. C9-C11 add 19 public declarations across three
canonical modules, each original-source checked, individually axiom-audited,
wired, and corpus-searchable. C1-C11 now comprise 101 public declarations in
ten pipeline modules, plus the separately checked existing-module gcd-divisor
interface exported at C8. No owned Lean, search, index, lint, or profiling
process remains. No full build, numerical experiment, heartbeat increase,
commit or push. The global lint placement error remains explicit above.

The unbounded research goal stays active. Next: formalise the C12 seed-size
inequality from the checked paper argument and the positive signed-complement
survivor, reusing the existing actual-profile continuity and prime-pair
realisation. Preserve the consecutive-integer exception. No uniform lower
bound follows from C11 nonvanishing, and no complete signed-complement estimate
has been proved. The current pipeline card, canonical sources, logs, and own
Serena memory are the continuation state.
