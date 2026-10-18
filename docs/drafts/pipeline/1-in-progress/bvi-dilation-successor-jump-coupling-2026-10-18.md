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
