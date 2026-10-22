# CTF: signed origin-tail cancellation

Status: started Lean modules completed, checked, and wired. The user cleared
the research goal and requested this bounded completion. The requested
significant CTF advance has not been achieved. The final checkpoint below
governs verification status.

## Task contract

- Use current Lean corpus and its research search; no external search, novelty audit, numerical experiments, or historical research Markdown.
- Frontier map is read-only. Preserve concurrent changes.
- Complete a dependency-closed mathematical proof before formalization. No new axioms, unproved analytic inputs, computational certificates, or heartbeat increases.
- Audit finished leaf modules with `lake --old env lean`; import new leaves into their umbrella without building the umbrella. Run formal lint.

## Original research plan (historical)

1. Establish exact current CTF frontier from Lean source and corpus searches.
2. Conjecture, attack, and revise a source-side cancellation mechanism. Record failures and positive survivors without presenting a receiver as a producer.
3. Prove and formalize a qualifying theorem, then audit its actual contribution to the full route.

## Verified starting evidence

- `ChronologicalRiemannEquivalence`: bounded chronological approximation is already equivalent to RH.
- `ChronologicalDualSamplingCriterion`: dual sampling bound is already equivalent to RH; exchanging pointwise Möbius inversion with arbitrary Hilbert pairing is the missing analytic step.
- `ChronologicalGrowingMomentSource`: unit-bounded rows with a half-length Möbius prefix, zero harmonic charge, and increasing exact moments already exist.
- `ChronologicalGrowingSignedProjection`: their remaining logarithmic boundary window retains signed Mertens and harmonic channels.
- `SignedLcmFractionalDefectAndCompleteFibreCollapse`: exact finite mean square is Selberg diagonal minus signed LCM defect; complete Möbius fibres collapse. Cofinal signed control is not supplied.

## Initial search record

Initial `research "CTF" --exclude-module Mathlib --json` finished: no partial result; compiler metadata mostly pending/stale, so hits are leads rather than validation.

The initial deep whole-corpus mechanism query finished. Its results informed
the source audits below; its temporary output was removed after inspection.

## Completion gate

Not achieved. The auxiliary finite Selberg theorems below are proved;
convergence of a bounded chronological source, or removal of its signed
origin-window obstruction, remains open.

## 2026-10-18: coefficient-mass coercivity — paper proof

Status: dependency-closed paper proof, subsequently verified in Lean. This is an
auxiliary rigidity result, not yet the requested significant CTF advance.

Write `w(n)=μ(n)^2/φ(n)`, `F(n)=n/φ(n)`, and
`Q_N(c)=Σ_{e≤N} φ(e) Y_e²`, where `Y_e=Σ_{e|d≤N} c_d/d`.
For every real finite row, conjectured and now proved on paper:

`(Σ_{d≤N}|c_d|)² ≤ 16384 N² Q_N(c)`.

Proof, including the uniform arithmetic constant:

1. Existing divisor identity: `F(n)=Σ_{d|n}w(d)`. Existing bounds:
   `0≤w≤1`, `Σ_{d≤N}w(d)/d≤4`, `Σ_{d≤N}w(d)/φ(d)≤16`.
2. Put `b(n)=w(n)/φ(n)`. Squarefree multiplicativity and vanishing on
   nonsquarefree products imply `b(dm)≤b(d)b(m)` for all positive `d,m`.
   Divisor swapping gives
   `Σ_{n≤N} b(n)F(n) = Σ_{dm≤N}b(dm)w(d)
    ≤ (Σ_{d≤N}b(d))(Σ_{m≤N}b(m)) ≤256`.
3. Totient supermultiplicativity gives `F(dm)≤F(d)F(m)`.
   If `Σ_{n≤X}F(n)^k≤C X`, divisor swapping gives
   `Σ_{n≤N}F(n)^(k+1) ≤ C N Σ_{d≤N}w(d)F(d)^k/d`.
   Starting at `k=0` produces `ΣF≤4N`, `ΣF²≤64N`, `ΣF³≤16384N`.
4. Existing `σ(n)/n≤F(n)` implies
   `Σ_{n≤N}σ(n)²/φ(n) ≤ Σ_{n≤N}n F(n)³≤16384N²`.
5. Exact finite multiples inversion gives
   `c_d=d Σ_{m≤N/d}μ(m)Y_{dm}`. Triangle inequality and divisor swapping
   give `Σ|c_d|≤Σ_{e≤N}σ(e)|Y_e|`. Weighted Cauchy then gives the claim.

Positive survivor: small Selberg energy forces small mean absolute coefficient
mass, uniformly over cutoff and without a coefficient-budget assumption.
An exact Möbius prefix of fixed positive relative length therefore cannot have
vanishing Selberg energy, using the corpus squarefree-density theorem.
This distinguishes the existing growing-moment half-prefix source from the
Selberg-small-energy strategy. It does not obstruct small chronological L²
error by itself: signed fractional defects still matter.

Additional audited candidates:
- Standard Selberg optimizer and unit coefficient bound: already in corpus.
- Centering at index 1: routine bridge, not significant.
- Centering at the squareful index 4: since the standard Selberg optimizer
  vanishes there, subtracting `4/G_N` preserves the unit box for `G_N≥4`,
  removes harmonic charge, preserves coefficient 1, and costs `4/G_N²` in
  Selberg energy by the optimizer's normal equations. This is a useful source
  normalization, not an origin-window estimate; not claimed as goal completion.
- Oscillatory bounded-tail compactness: no new arithmetic source estimate yet.

Search audit: source, divisor, optimizer, compactness, prefix-mass, and totient
moment searches completed. Source/divisor deep searches reported partial
coverage; optimizer, compactness, prefix-mass, and totient searches completed
without partial status. Retrieved declarations remain source-only leads until
checked against this Lean toolchain. No external search or novelty audit used.

### Stronger finite consequences and a sharp-norm conjecture

The corpus already proves `#{squarefree n≤M}≥M/4` for every cutoff in
`RHTower/SquarefreeLowerDensity.lean`. Thus the preceding mass estimate gives,
without any large-cutoff assumption,
`M²≤262144 N² Q_N(c)` whenever `c_d=μ(d)` for `d≤M≤N`.
For a half-prefix and `N≥2`, it gives `Q_N(c)≥1/2359296`.
This is a dependency-closed strengthening of the same paper proof.

A sharper positive survivor has emerged. Put
`P(e)=Σ_{d|e} d |μ(e/d)|` and `A_N=Σ_{e≤N}P(e)²/φ(e)`.
The exact best constant in `(Σ|c_d|)²≤A_N Q_N(c)` is `A_N`:
finite inversion gives the upper bound, and the Liouville-aligned coordinates
`Y_e=λ(e)P(e)/φ(e)` attain it. Indeed
`μ(m)λ(dm)=λ(d)μ(m)²`, so each inverse row has a common sign and
both triangle inequality and weighted Cauchy are equalities. The resulting
row has total absolute mass `A_N` and Selberg energy `A_N`.
This sharp-norm statement is proved on paper by those identities and verified
in `ChronologicalSelbergSharpMass.lean`. No claim about its
sufficiency for the main CTF goal is made.

### Completed finite-mass formalization

- `Sieve/TotientCubicMean.lean`: full cubic mean proof passed its final Lean
  audit without diagnostics.
- `ChronologicalSelbergCoefficientMass.lean`: uniform mass estimate, all-cutoff
  Möbius-prefix bound, and explicit `growingMomentSource` energy obstruction
  passed Lean without diagnostics.
- `ChronologicalSelbergSharpMass.lean`: exact norm constant and explicit
  Liouville extremizer passed Lean without diagnostics.
- Leaves registered in `RHTower.lean`; no umbrella/full build run.
- No significance/completion claim: actual chronological origin-window
  estimate remains open. The sharp finite coercivity theorem is a positive
  survivor of the incompatible half-prefix/vanishing-Selberg hybrid.

`ChronologicalSelbergCoefficientMass.lean` includes the verified
`not_tendsto_growingMomentSource_selberg_zero`. Axiom and lint results are
recorded in the dated audit below.

`ChronologicalSelbergSharpMass.lean` now passes Lean without diagnostics.
`selberg_mass_inequality_iff` classifies every admissible universal constant;
`sum_abs_selbergMassExtremalRow` and `selberg_selbergMassExtremalRow` verify
attainment by the explicit Liouville-signed inverse. The only rejected draft
issue was an identifier containing Lean's reserved lambda character; it was
renamed. No mathematical premise was added.

Next conjecture, not proved: a sublinear exact Möbius prefix might be compatible
with vanishing Selberg energy through a two-cutoff logarithmic taper.
The present coercivity theorem proves the necessary condition `M_N/N→0`.
A proposed sufficient construction is the normalized difference of two
Barban–Vehov weights. Its uniform moving-cutoff covariance and exact
zero-charge/budget correction still require proof; do not assume either.

## Next producer: logarithmic taper with a squareful charge correction

Research target (not yet formalized): uniformly for `1≤M<N` and sufficiently
large `H=log(N/M)`, construct a supported row `c` with `|c_d|≤1`, exact
`c_d=μ(d)` through `M`, exact harmonic charge zero, and `Q_N(c)≤K/H` for an
absolute constant `K`. Together with the proved mass obstruction, this would
classify feasibility of vanishing Selberg energy with a prescribed Möbius
prefix: the relative prefix length must tend to zero, and that should suffice.
This still would not prove chronological global L² convergence.

The taper already exists in `EulerDeletionCutoffAverage.lean` and
`EulerDeletionAveragedDivisorCovariance.lean`:
`a_d=(BV_N(d)-BV_M(d))/H`, equal to `μ(d)` for `d≤M`, and
`μ(d) log(N/d)/H` for `M<d≤N`. Do not recreate that definition.
The existing mean-square estimate in the latter file is a triangle bound
proportional to `(log N+log M)/H²`; it does not yet cover every `H→∞`.

Proposed proof mechanism, with no numerical experiments:

1. Let `T(Y)=coprimeLogMoebius 1 Y`, zero for `Y<1`. Corpus has uniform
   boundedness and `|T(Y)-1|≤C/log²Y` eventually, in
   `Sieve/CoprimeLogMoebiusOneRate.lean`.
   Enlarge the constant to obtain `|T(Y)-1|≤C/(1+log Y)²` for all `Y≥1`.
2. Prove the uniform harmonic sampling estimate
   `Σ_{d≥1}(T(Y/d)-T(X/d))²/d ≤ C(1+log(Y/X))` for every `0<X<Y`.
   Decompose `T` into the step at 1 plus its error. The step occupies the
   logarithmic interval `(X,Y]`, with harmonic mass at most `1+log(Y/X)`.
   For the error, split `log(X/d)` into unit intervals. Each interval has
   harmonic mass at most 2, and `Σ_{j≥0}(1+j)^(-4)` converges. This gives a
   uniform error-square bound independent of the cutoff. The same applies
   at `Y`; use the elementary square-of-sum inequality. Cases `X<1` or
   `Y<1` are included by the support condition.
3. Corpus exact bivariate Selberg factorization writes the original LCM
   quadratic form as an Euler-correction convolution of principal models.
   `Sieve/SelbergEulerCoefficientIdentity.lean`,
   `Sieve/SelbergDiagonalUpperAsymptotic.lean`, and
   `Sieve/SelbergEulerCorrectionCoefficientMass.lean` provide the identity,
   the principal diagonal collapse, and absolute summability of the correction.
   For the difference of the two logarithmic cutoffs, each principal model is
   `Σ_d ΔT(N/(ad),M/(ad)) ΔT(N/(bd),M/(bd))/d`.
   Cauchy and step 2 bound its absolute value by `C(1+H)`, uniformly in `a,b`.
   Absolute summability of the correction therefore gives `Q_N(a)≤K/H`
   for `H≥1`. Crucial: cancel the two cutoffs BEFORE bounding; no logarithmic
   moment of the Euler correction is needed.
4. Harmonic charge of `a` is `h=(T(N)-T(M))/H`, hence
   `|h|≤C/[H(1+log M)²]` by step 1.
5. Put `b_d=1` when `M<d≤N` and `4|d`, zero otherwise. These are squareful
   slots where `a_d=0`. Its harmonic mass
   `B=(Harmonic(floor(N/4))-Harmonic(floor(M/4)))/4` satisfies
   `B≥(H-log 5)/4≥H/8` for `H≥2 log 5`.
   This follows from the lower harmonic-interval integral bound and
   `(floor(N/4)+1)/(floor(M/4)+1)≥N/(5M)`.
6. Correct `c=a-(h/B)b`. This preserves the exact prefix, kills harmonic
   charge, and stays in the unit box once `H` exceeds an absolute threshold,
   since the altered slots originally had coefficient zero and `|h/B|≤C/H²`.
7. For every `e`, the multiples coordinate of `b` is bounded by `(H+1)/e`:
   discard the squareful restriction and bound the harmonic interval
   `M/e<k≤N/e`. Therefore `Q_N(b)≤(H+1)²(1+log N)` by the existing totient
   diagonal harmonic bound. Consequently
   `(h/B)²Q_N(b)≤C(1+log M+H)/[H²(1+log M)^4]≤C'/H` for `H≥1`.
   Positive quadratic-form Cauchy gives `Q_N(c)≤2Q_N(a)+2(h/B)²Q_N(b)≤K'/H`.

The next audit identified here was to write the uniform harmonic-sampling proof in full, inspect
and instantiate the exact bivariate convolution for two independent cutoffs,
and check all endpoint/floor constants. Those auxiliary steps are now verified
below; the full corrected producer remains unimplemented. The existing tuned-minimum-log files concern a
*different* included detector kernel and are not a proof of step 3.

## Verified audit, 2026-10-18

All three new leaves passed `lake --old env lean` with generated leaf oleans,
without diagnostics on their final runs. No umbrella/full build was run.
`git diff --check` passed for the changed CTF files.
A `/tmp` import-only audit checked seven results: cubic mean, uniform mass,
Möbius-prefix bound, growing-source nonconvergence, sharp universal-constant
classification, and both extremal-row identities. Every axiom list was exactly
`[propext, Classical.choice, Quot.sound]`.

`scripts/formal_tools.py lint` exited 1. Its four errors are outside these CTF
edits; do not misreport the repository lint gate as passing:
- Unreachable from `GaloisForLFunctions.ArithmeticPositivityTheory`:
  `GaloisForLFunctions.arithmetic-positivity-theory.FactorialCollarIrrationalityAndSpacing`.
- Unreachable from the same umbrella:
  `GaloisForLFunctions.arithmetic-positivity-theory.RankOnePoleReadoutAndZeroNullspace`.
- Unreachable from the same umbrella:
  `GaloisForLFunctions.arithmetic-positivity-theory.SourceRelativeSchurMarginAndPerturbationCalculus`.
- Research leaf at package root: `TransHorizonIncidenceMechanics.lean`.
Those areas were already under unrelated work at session start; they were not
modified by this task. The lint output also contained existing large-file
warnings. No prohibited-declaration error was reported for the new leaves.

At this earlier checkpoint the research goal was active and not achieved.
The verified finite norm classification
and half-prefix obstruction are useful positive/negative research results, but
no actual chronological origin-window decay estimate has been established.
The next research step then selected was the logarithmic-taper mechanism
above. Formalization of the finite theorem family does not establish the
requested chronological contribution.

Cleanup: completed search-result JSON files and all owned `/tmp/hgt_ctf_*`
name/axiom scratch files were removed after their relevant results were recorded.
No owned Lean or research process remains running at this checkpoint. Current
leaf oleans were retained for subsequent imports; the final cubic-mean olean
was regenerated after its tactic-style cleanup.

## Continuation: uniform sampling proof

Previous turn classified as progress: three verified leaves and their exact
axiom audit changed authoritative state. The main goal remains unachieved.

The deep harmonic-sampling search completed with `partial=false`; coverage was
an older indexed snapshot and refresh reported `background_indexer_running`.
Candidate lemmas/source arguments supplied harmonic-interval bounds but no
matching uniform sampling theorem. No prose hits were read.

The missing sampling argument has a finite, elementary proof. For `Y>0`,
partition positive integers `d≤Y` by `j=floor(log(Y/d))`. In one fibre,
`d≤Y/exp(j)` and `1/d≤exp(j+1)/Y`. Its cardinality is at most
`floor(Y/exp(j))`, so its harmonic mass is at most `exp(1)`.
Consequently any error envelope `|E(Y/d)|≤A/(1+log(Y/d))` has squared
harmonic mass at most `2 exp(1) A²`, using the existing inverse-square sum
bound after shifting `j` by one. The corpus's stronger log-square rate gives
this envelope globally, after enlarging its constant on a bounded interval.

Write `T(Y/d)=1_{d≤Y}+E_Y(d)`. The difference of the two indicator rows has
harmonic mass at most `2+log(Y/X)`, by the existing harmonic-interval bound
and `floor(X)≥X/2` when `X≥1`; if `X<1`, use the harmonic prefix bound.
The elementary inequality `(u+v+w)²≤3(u²+v²+w²)` now proves the required
uniform two-cutoff sampling bound. This closes the paper sampling gap;
formalization and the independent-cutoff convolution identity are verified below.

`Sieve/LogarithmicHarmonicSampling.lean` now passes its direct Lean check with
no diagnostics. Its window constant is actually `1+log(Y/X)`. The Möbius
specialization in `Sieve/CoprimeLogMoebiusHarmonicDifference.lean` also passed
its final direct check without diagnostics.

The bivariate step can be proved without four separate mixed-cutoff formulas.
For an arbitrary finite weight `w`, set
`F_w(q)=Σ_{u≤N/q} μ(u) w(qu)/u`. Apply the corpus's bivariate hyperbola swap
first to `original = correction * principal`, then to
`principal = diagonal_reciprocal * (μ/n ⊗ μ/n)`. The diagonal collapse gives
the exact finite identity
`Σ_{m,n≤N} original(m,n) w(m)w(n)
 = Σ_{a,b≤N} correction(a,b)
     Σ_{d≤min(N/a,N/b)} F_w(ad) F_w(bd)/d`.
For the existing taper `w=taper M N`, finite filtering gives exactly
`F_w(q)=(T(N/q)-T(M/q))/(log N-log M)`.
Apply the two-cutoff harmonic estimate to real cutoffs `M/a,N/a` and `M/b,N/b`;
`2|uv|≤u²+v²` bounds every principal term uniformly by
`C(1+H)/H²`. The finite absolute correction mass is at most its existing
convergent absolute series. Hence the taper's Selberg form is at most `K/H`
for `H≥1`. This is the dependency-closed paper proof of the moving-cutoff
energy estimate; its exact finite identity and Lean implementation passed
their direct checks. It does not estimate the chronological signed remainder.

### Simpler squareful correction (supersedes steps 5–7 above)

Use only the outer half-annulus: `b_N(d)=1` if `N/2<d≤N` and `4|d`, else zero.
For `N≥16`, its harmonic charge is at least `1/16`: the interval contains
`floor(N/4)-floor(N/8)≥N/16` multiples of four, and each reciprocal is at
least `1/N`. When `H≥16`, the exact prefix lies below this annulus and `N≥16`.
The former follows from `log(N/M)≤1` if `N≤2M`; the latter follows from
`log N≤N-1`. These are elementary inequalities, not numerical experiments.

For every positive `e`, reindex the multiples coordinate by `d=ek` and use
the proved harmonic-window bound. The annulus ratio is at most three after
integer flooring, so `0≤Y_e(b_N)≤3/e`. Hence
`Q_N(b_N)≤9(1+log N)`. This avoids the previous moving-annulus charge formula.

With the uniform rate constant `A`, the taper charge obeys
`|h|≤2A/[H(1+log M)²]`. Put `alpha=h/charge(b_N)` and `c=a-alpha*b_N`.
For `H≥16+32A`, `|alpha|≤1`, so the unit box survives because all altered
slots have original Möbius coefficient zero. The prefix survives and charge
is exactly zero. Writing `L=1+log M≥1`,
`alpha² Q(b_N)≤9216 A²(L+H)/(H² L⁴)≤18432 A²/H`.
Thus `Q(c)≤(2K+36864A²)/H`. All scalar estimates and floor endpoints are now
specified; the correction itself is not yet formalized.

The squareful-charge corpus search returned no matching construction. It was
non-partial but used an older coverage snapshot while indexing continued.
Its candidate/source results were inspected; unrelated correction theorems
and our just-added weighted identity are not substitutes for this proof.

### Physical-norm audit: locate the repair near the prefix

The outer-`N` mask is a valid Selberg construction but is a poor choice for the
original chronological norm: its regularized Bose energy scales like `N`, so
a charge of order `1/H` can incur a large physical cost. Do not silently use
small Selberg cost as evidence of small chronological cost.

Keep the same proved-on-paper mask estimates, but instantiate the mask at
`L=2*max(M,16)` instead of `N`. Its support lies strictly beyond the retained
prefix and is below `N` once `H≥16`. Its harmonic charge is still at least
`1/16`; all changed coefficients are still squareful. Finite support makes
`Q_N(mask_L)=Q_L(mask_L)`. Since `L≤32M`,
`Q_N(mask_L)≤9(1+log L)≤288(1+log M)`.
The same correction coefficient satisfies
`|alpha|≤32A/[H(1+log M)²]`, giving the improved correction cost
`alpha² Q_N(mask_L)≤294912 A²/[H²(1+log M)³]`.
Thus charge repair is lower order in Selberg energy and its chronological
scale depends on the prefix, not on the outer cutoff. Use this location in
the final producer. A quantitative chronological norm bound for this repair
must still be sourced/proved; it is not claimed here as formalized.

Corpus search for the physical repair found exact scaling in
`ChronologicalPositiveAbelTransfer.lean:135`
(`chronologicalL2Norm_dilate_eq`) and
`ChronologicalMobiusSubsetSums.lean:288`
(`chronologicalL2Norm_bose_dilate`). Both give the Bose norm divided by
`sqrt(d)`. The finite triangle inequality and the existing reciprocal-square-
root sum bound therefore give mask norm at most `2*sqrt(L)` times the mother
Bose norm. The inner repair's physical norm is consequently at most
`64*A*sqrt(L)/[H(1+log M)²]` times that fixed norm. This tends to zero under,
for example, `M≤H` and `H→∞`. This estimate is a paper consequence of the
retrieved identities; it is not yet a formal theorem for the new mask.

The same search found `chronologicalZeroChargeRepair_norm_bound` in
`ChronologicalHarmonicCharge.lean:230`; that existing repair changes the first
coefficient, so it does not preserve an exact growing Möbius prefix. Do not
substitute it for the squareful construction. Search was non-partial, with
background indexing and unavailable semantic coverage reported.

## Current formalization checkpoint

Direct leaf checks passed for:
- `Sieve/LogarithmicHarmonicSampling.lean` (band, envelope, window bounds).
- `Sieve/CoprimeLogMoebiusHarmonicDifference.lean` (uniform rate and two-cutoff energy).
- `Sieve/SelbergWeightedConvolutionModel.lean` (exact arbitrary-weight identity).
- `ChronologicalSelbergTaperEnergy.lean`, including
  `exists_selberg_arithmeticCoeff_le_inv_log_span`. Its final source was
  rechecked after removing a tactic-style warning; no diagnostics remained.
- `ChronologicalSquarefulChargeCorrection.lean`: all mask charge/energy
  estimates and cutoff-extension invariance passed without diagnostics after
  making the natural-to-real cardinality cast explicit.
These five leaves are wired into `RHTower.lean`; all eight leaves from this
research work occur exactly once in the umbrella. No umbrella build was run.

The new squareful mask has charge at least `1/16` for `N≥16`, multiples
coordinates between `0` and `3/e` for `N≥2` and positive `e`, and Selberg
energy at most `9(1+log N)` for `N≥2`. Extending the ambient cutoff beyond any coefficient
row's support preserves its Selberg form exactly.
Do not yet claim the full corrected unit-row producer: its final combination,
asymptotic feasibility classification, and physical-norm transfer are pending.
The main CTF origin-window gap remains open. The user cleared the research
goal and requested completion of already-started work; no further research
or corrected-producer implementation is part of this cleanup.

### Final verification and cleanup, 2026-10-18

The four main results from harmonic sampling through taper energy passed an
import-only axiom audit. A separate import-only audit checked all eleven
public theorems in `ChronologicalSquarefulChargeCorrection.lean`. Every
reported axiom list was exactly `[propext, Classical.choice, Quot.sound]`.
All five new leaves passed direct `lake --old env lean` checks without final
diagnostics; the earlier three finite-mass leaves retain their successful
direct checks and axiom audit recorded above. No full or umbrella build ran.

The final `scripts/formal_tools.py lint` run exited 1 with five errors outside
this work, superseding the earlier four-error snapshot:

- Unreachable from `GaloisForLFunctions.BiScaleUncertainty`:
  `GaloisForLFunctions.BiScaleUncertainty.SixthReadoutStability`.
- Unreachable from `GaloisForLFunctions.BezoutValuationIncidence`:
  `GaloisForLFunctions.BezoutValuationIncidence.ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile`.
- Unreachable from the same umbrella:
  `GaloisForLFunctions.BezoutValuationIncidence.CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget`.
- Unreachable from the same umbrella:
  `GaloisForLFunctions.BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation`.
- Research leaf at package root: `TransHorizonIncidenceMechanics.lean`.

These files and their umbrella wiring were not changed by this task. The
remaining lint output consisted of large-file warnings. No lint error names
any of the eight completed CTF leaves. Explicit source checks found no
`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or heartbeat override in them.

Scoped `git diff --check` passed. All seven temporary files from this final
work period (three Lean audits, three research JSON outputs, one lint log)
were removed and their absence verified. All owned Lean/lint processes have
exited. The completed leaves, final oleans, this record, and the cross-session
memory remain; no unfinished Lean stub or unwired leaf from this work remains.
