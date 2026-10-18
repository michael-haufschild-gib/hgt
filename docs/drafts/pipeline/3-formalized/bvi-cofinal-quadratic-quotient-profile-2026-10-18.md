# Cofinal unshifted quadratic profile from complementary quotients

- **ID:** BVI-COFINAL-QUADRATIC-PROFILE-2026-10-18
- **Stage:** 3-formalized
- **Type:** Unconditional arithmetic cofinal asymptotic
- **Scope:** Literal Möbius source, fixed linear observation ratios; no RH
  work, no receiver assumptions, no numerical experiments.

## Target

Let Q_N(M)=sum_{k=1}^M s_N(k)^2, with
s_N(k)=sum_{d<=N,d|k}mu(d). For each fixed integer A>=2, the proved limit is

    Q_N(A N)/N -> F(A),

where F(A) is the following finite arithmetic profile. For q,r in [1,A-1],
put g=gcd(q,r), a=q/g, b=r/g, l=lcm(q,r), and

    D(v)=(6/pi^2) product_{p prime, p|v} p/(p+1).
    F(A)=sum_{q,r=1}^{A-1} mu(a)mu(b) D(ab) (A-max(q,r))/l.

This is unshifted quadratic energy. The neighboring-gradient energy
also contains an additive shifted correlation; no formula for that
correlation is assumed or claimed here.

## Paper mechanism and missing dependency

For 1<=k<=AN and N>=1, complementary quotient compression writes
s_N(k)=1_{k=1}-sum_{q<=A-1,q|k,k>qN}mu(k/q). The tail vanishes at k=1.
Expand the square and exchange finite sums. A q,r pair is supported on
k divisible by l and k>max(q,r)N. Write k=l*n. Then k/q=b*n and k/r=a*n.
Möbius multiplication gives the exact identity

    mu(an)mu(bn)=mu(a)mu(b)mu(n)^2 1_{gcd(n,ab)=1}.

Thus the pair contributes a weighted coprime-squarefree count on

    max(q,r)N/l < n <= AN/l.

Its proposed density is D(ab), and the interval length divided by N
tends to (A-max(q,r))/l. A finite sum then proves the target profile.

The main dependency is squarefree counting density with fixed coprimality
modulus. The paper extension below closes it; its Lean certificate remains
to be constructed. Only squarefree moduli are needed in nonzero quotient
pair terms: a,b are coprime, and a nonsquarefree a or b annihilates the term.

## Candidate way to close the density dependency

Let C_Q(x) count squarefree n<=x coprime to Q. If p is prime and p does
not divide Q, splitting n according to p|n gives exactly

    C_Q(x)=C_{pQ}(x)+C_{pQ}(floor(x/p)).

This follows because squarefree multiples of p are p*m with p not dividing
m, and coprimality to Q is preserved. Given C_Q(x)/x->D(Q), a finite
geometric expansion of this recurrence and the bound 0<=C_{pQ}(x)<=x
force C_{pQ}(x)/x->D(Q)*p/(p+1).

**Closed paper proof of the contraction step.** Set f_Q(Y)=C_Q(floor(Y))/Y,
using the total division convention at zero. For Y<=0 the count is zero;
for Y>0 it lies between zero and floor(Y), so |f_Q(Y)|<=1 globally.
The exact prime recurrence becomes

    f_Q(Y)=f_{pQ}(Y)+(1/p)f_{pQ}(Y/p).

Subtract the same equation at Y/p divided by p. Then

    f_Q(Y)-(1/p)f_Q(Y/p)
      = f_{pQ}(Y)-(1/p^2)f_{pQ}(Y/p^2).

The existing corpus theorem `tendsto_of_div_contraction` at parameter p^2
applies to the bounded f_{pQ}. If f_Q->D(Q), its left side tends to
(1-1/p)D(Q), and the resulting limit is

    [p^2/(p^2-1)](1-1/p)D(Q)=p/(p+1)D(Q).

The base Q=1 follows from the existing square-root error for the global
squarefree count (`abs_sum_moebius_sq_Icc_sub_le`). Strong induction on
squarefree Q, removing its least prime factor, yields the finite Euler
product D(Q). Each quotient pair then has its claimed scaled-window
limit by subtracting the two prefix limits. The finite double sum gives
F(A). This closes the paper argument without a sign-correlation premise.
Exact endpoint and casting details still require Lean verification.

**Positive check:** Q_N(AN)>=Q_N(2N) for A>=2, and first-octave reciprocity
gives Q_N(2N)/N->6/pi^2. Hence the resulting profile must satisfy
F(A)>=6/pi^2. This is a proof consequence, not a numerical experiment.

## Corpus evidence

- `ComplementaryQuotientAndSecondOctaveLaw.lean`: exact compression.
- `CompositeSquarefreeStepAndMultiOctaveL2Energy.lean`: finite two-band
  energy formulas and exact cutoff-step identities, not a general cofinal
  density profile in inspected source.
- `CoprimeSquarefreeDyadic.lean`: prime-deleted dyadic density.
- `CoprimeSquarefreeWindow.lean`: prime-deleted square-root counting error.
- `CoprimeMoebiusSeries.lean`: prime deletion of the inverse-square series.
- Deep query `sieveL2PrefixEnergy asymptotic density` returned only finite
  energy identities among useful hits; query was partial, coverage pending.
- Follow-up deep query `moebius multiplicative correlation coprime
  squarefree density` completed; candidate lemmas, source arguments and
  coverage inspected. It found the existing coprime dilation-product
  identity and prime-deleted squarefree weight, not the target profile.
- `CoprimeLogMoebiusLimit.lean` supplies `tendsto_of_div_contraction`.
  Its minus recurrence handles the plus recurrence after the two-step
  elimination above; no new analytic assumption is needed.

## Status

- [x] Conjecture recorded before new Lean implementation.
- [x] Complete corpus applicability audit; no matching profile found in the inspected results (partial-search coverage recorded; no external novelty claim).
- [x] Close required squarefree-modulus density proof on paper.
- [x] Audit exact quotient-pair reindexing and all endpoint floors on paper.
- [x] Formalize the exact survivor, then original-source and axiom audits.

The three prior cofinal results are already verified and documented in
stage-3 cards. This card does not replace their completed work.

## Exact finite identity and live checkpoint

Set `T(N,q,k)=1_{q|k, qN<k} mu(k/q)`. For positive q dividing k,
`N<k/q` iff `qN<k`, with no rounding error. On `1<=k<=(B+1)N`,
`s_N(k)=1_{k=1}-sum_{q=1}^B T(N,q,k)`. For N>=1 every T at k=1
vanishes, so squaring contributes exactly one unit plus the double sum.

For q,r>=1 set g=gcd(q,r), l=lcm(q,r). The exact common-multiple
substitution is `k=l*n`, with `k/q=(r/g)n`, `k/r=(q/g)n`.
Both band cutoffs reduce to `max(q,r)N<k`. Therefore for
`B*N<=M<=(B+1)*N` the quadratic energy is

    1 + sum_{q,r=1}^B [P_{r/g,q/g}(floor(M/l))
                       - P_{r/g,q/g}(floor(max(q,r)N/l))],

where `P_{a,b}(X)=sum_{1<=n<=X}mu(an)mu(bn)`.
The endpoint floors are natural divisions, so strict lower endpoints
and inclusive upper endpoints agree exactly with prefix subtraction.

The limit will be stated with parameter B>=0 and horizon (B+1)N.
Thus B=0 is included unconditionally, with profile zero; B>=1 gives
the original A>=2 formulation after A=B+1.

Completed original-source check: session 57054, original source
`CofinalMobiusQuadraticQuotientProfile.lean`, emitting matching olean/ilean;
log `/tmp/bvi-quadratic-profile-canonical.log`. Source SHA-256
`c77f3a76d32ceacb04a596bd2d1a2dbdc330a6b08688a5e5f488466ca513b3be`.
Scratch session 44979 passed the complete finite identity, cofinal profile,
monotonicity and first-octave lower bound. Its log
`/tmp/bvi-quadratic-profile-proof.log` also audits all 17 density-leaf public
declarations: only `propext`, `Classical.choice`, and `Quot.sound`.
Both leaves are wired into the BVI umbrella. The profile leaf has 16 public
declarations; axiom audit session 23187 passed for every declaration with
only `propext`, `Classical.choice`, and `Quot.sound`.
Original-source session 98135 passed with empty diagnostics for
`CoprimeSquarefreeDensityAndMobiusDilationMeans.lean`, emitting matching
olean/ilean; log `/tmp/bvi-coprime-density-canonical.log`; source SHA-256
`057bee06cb0e1ed377839cff86f1df31df29e9c48ffa9978e99dcad2a91dce80`.
The combined
scratch session 28245 accepted the density foundation and exited with only
two errors in the finite-profile proof (dependent `if` rewrite and function
composition simplification). Both are corrected in
`/tmp/bvi_quadratic_profile_proof.lean`, which now imports the new density
leaf. The density axiom
audit file is `/tmp/bvi_coprime_density_axioms.lean` (17 public declarations).
Both leaves passed original-source and axiom audits. Index regeneration
passed. Global lint exited 1 for three concurrent foreign unreachable BVI
leaves and the existing root TransHorizon umbrella placement; no finding
names either new leaf. This is not a claim that the global gate is clean.

All 33 public declarations are audited. Source hashes for all five leaves
produced by the wider task still match their audited versions. Evidence is
archived under `logs/bvi-quadratic-profile-2026-10-18-*`, including exact
commands, hashes, all axiom outputs, lint errors, and corpus-search summaries.
Completed C8 scratch proofs, probes, temporary logs, and search JSON were
removed after archiving. Paths in the implementation history above are no
longer continuation inputs. No owned Lean process remains for C8.

Next conjecture is recorded separately in
`docs/drafts/pipeline/1-in-progress/bvi-cofinal-odd-moments-and-sign-symmetry-2026-10-18.md`.

## Mathematical boundary

This is an exact cofinal asymptotic for the unshifted quadratic source
energy on each fixed linear horizon ratio. Common-multiple reindexing
aligns all Möbius factors on one variable, so finite coprime-squarefree
densities suffice. It does not assert an asymptotic for successor gradient
energy, a uniform growing-ratio rate, or an interior critical-energy bound.
Those quantities do not follow merely by renaming this explicit profile.

Earlier sessions 40447 and 53849
exited on a local simplifier failure in the prime-indicator recurrence;
the induction and dilation-limit sections emitted no diagnostics. Session
96509 exposed the same simplification issue for reducible `Nat.Coprime`;
the recurrence now uses explicit iff constructors and staged rewrites.
Session 15302 exposed a dependent-Decidable rewrite failure inside an
indicator. It now uses direct case proofs. The combined check assembles
the density scratch, `/tmp/bvi_quadratic_profile_finite.lean`, and
`/tmp/bvi_quadratic_profile_limits.txt`, including monotonicity and the
positive first-octave lower bound.

Read-only follow-up search on odd coprime dilation products finished as
session 9545, output `/tmp/bvi-odd-dilation-moments-research.json`. No odd
moment theorem is yet claimed or implemented.

Additional deep search `finite sum common multiples lcm quotient dilation
Mobius second moment` completed partially; inspected both candidate and
source-argument lists. It returned lcm/gcd identities, no matching
cofinal profile. Compiler coverage remains mostly pending/source-only.
