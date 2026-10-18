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
