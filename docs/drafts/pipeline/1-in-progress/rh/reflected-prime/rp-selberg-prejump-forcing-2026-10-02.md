# RP-50: exact Selberg forcing against native prejump work

Status: two unconditional boundary leaves audited; signed payment remains open.
Route: RP, unconditional native history floor.

RP-49 did not bound its signed prejump sum. This attempt tests the exact
Möbius-weighted Selberg forcing against that sum, retaining the terminal
square and ratio-dependent pair kernel. The existing O(N) Selberg remainder
bound admits sublinear power modes and is not a critical input.

Plan: inspect the literal forcing and its previous failed uses; derive a
source-specific signed absorption estimate if possible; formalize only a
new dependency-closed arithmetic result. A product-only convolution or an
assumed critical energy will not be counted as progress.

The exact floor source is F(N)=psiDefect N and
A(N)=sum_(d<=N) F(floor(N/d)). Corpus Tatuzawa gives

    F(N)*log N + sum_(n<=N) Lambda(n)*F(floor(N/n))
      = sum_(n<=N) mu(n)*log(N/n)*A(floor(N/n)).

The hard obligation is cancellation in this actual right side together
with the retained signed delayed products. Its separate absolute bound
does not estimate the critically weighted prejump work.

## RP-50 continuation: boundary cancellation forced by the native source

The Selberg attempt does not close: in n>N/2 its forcing still contains
(2 gamma-1) sum mu(n) log(N/n). The reciprocal-phase estimates retrieved
from the corpus do not bound this weighted Mobius sum. No absorption
estimate or new theorem follows.

New conjecture, grounded in `RoutePCoprimeSquareNative`,
`CriticalAbelRoutePAsymptoticBridge`, `CausalL2LaplaceHolomorphy`, and
`SPEQuantileRieszRoutePSourcePoleResidue`: the native coprime cross work
has nonintegrable negative part at zero damping, hence is negative
arbitrarily late. This does not decide any positive-damping budget or RH.

Paper mechanism:

1. A hypothetical square-integrable literal Route-P ray has a holomorphic
   causal transform on Re z>0. Reconstructing the regularized-zeta
   logarithmic derivative and applying the corpus analytic-rigidity
   theorem identifies this transform with the actual continuation.
2. Cauchy-Schwarz gives sigma*L(sigma+i tau)->0. A literal Hardy zero,
   already supplied by the corpus, forces a nonzero quantized residue
   on this path. Contradiction. No RH premise is needed.
3. Transfer to exp(-t)*H_full(exp t) using an exact all-real full-head/Abel
   identification and the exponentially decaying Route-P correction.
   The full-head identification remains to be written and checked.
4. If exp(-t)*cross_negative(t) were integrable, the admitted combined
   source at every positive damping bounds the native square uniformly
   as damping decreases to zero. Its Mellin mass tends to zero. Fatou
   then contradicts step 3. This avoids assuming admission of the
   combined source at zero damping.

Formal target: actual-source nonintegrability and cofinal negative work,
not merely a generic receiver. The positive survivor is an unavoidable
unbounded critical square-energy budget together with its compensating
negative arithmetic work. Every positive-damping payment remains open.
Status at conjecture formation: paper argument for steps 1-2; steps 3-4
required exact source and measure-theoretic bridges. Subsequent audit
below closes steps 1-3; step 4 remains a paper proof.

The all-real identification has a finite paper proof. For x>1 set
n=floor(x), and choose a finite core containing every prime <=n+1.
`mobiusDivisorContinuousHead_eq_fullHead` identifies its head with H_full
through this interval. `mobiusDivisorContinuousHead_eq_block_affine`
makes the head affine in sqrt(x). At each integer M, expand H_full using
`divisorContinuousUnitHead_dilation`; then
`sum_mobiusDivisorDilationChannel_eq_psiDefect_abel` and
`squareRootSummatoryPrimitive_nat` identify its value with A_critical(M).
`criticalContinuousAbel_between` gives the same affine interpolation, so
agreement at n and n+1 proves agreement throughout. Both heads vanish for
x<=1. No limit over prime cores is used.

For step 4 one can avoid global Fatou machinery: the negative-part
assumption admits each damped endpoint square by domination with the
absolute combined source plus that negative part. Its total integral is
at most I_epsilon+N. Restrict the nonnegative square to [0,T], then let
epsilon decrease to zero by compact dominated convergence. Since
I_epsilon->0, every undamped partial energy is <=N. This contradicts
unbounded partial energy from step 3. This argument retains the complete
native cross term and never assigns a zero-damping integral to the signed
combined source.

Search audit: all six search processes exited 0. Selberg33832 and
Mobius-phase36450 returned partialfalse/no errors; generations
1189720/1189734/1189737 and1189730/1189751/1189752 respectively.
Native-energy56726 returned partialtrue with decomposition and
filter_and_judge unfinished (deadline, malformed JSON, disconnect);
generations1189755/1189770/1189781,64576files,0pending.
Square-pole16838 returned partialtrue with reranking and semantic
retrieval unfinished (disconnect/Qdrant timeout); generations
1189765/1189786/1189787,64578files,0pending.
Source-pole30900 returned partialfalse/no errors, generations
1189835/1189846/1189848,64581files,0pending.
Full-head91821 returned partialfalse/no errors, generations
1189883/1189897/1189905,64585files,0pending. All reported unmeasured
semantic coverage and incomplete background refresh. All candidate,
source-argument, proof-idea and ingredient-set fields were inspected.
Generated recipes did not solve the source identification or absorption;
applicable declarations were inspected in the actual source. Retrieval
alone is not compiler evidence.

First verified advance: `RoutePSourceCriticalSquareNonintegrability.lean`
passes the foreground `lake --old env lean` leaf audit (69078, exit0).
The literal Route-P ray is not square integrable, and its partial square
energy exceeds every fixed budget at arbitrarily late cutoffs.
Scratch/API/axiom audit46678 exited0: all three public declarations depend
only on propext, Classical.choice, Quot.sound. The leaf is wired into the
umbrella without an umbrella build. No heartbeat override was introduced.
The full-head transfer also passes in `RoutePNativeCriticalSquareEnergy.lean`
(foreground leaf audit87829 exit0). Its all-real head identification,
native critical-square nonintegrability, finite-interval admission, and
cofinal partial-energy escape are verified. Scratch audit64016 exited0
with only the same three standard axioms for all seven public theorems.
Both leaves are wired. Lint8491 exited1 with fourteen unrelated unreachable
modules and no error for these leaves. The global gate remains non-green.

No-go closure and strongest positive survivor are recorded in
../../../5-failed/rp-native-undamped-square-budget-2026-10-02.md.
This advances the native zero-damping boundary, not the required
positive-damping payment estimate. Step 4, the actual negative coprime
mass theorem, remains to formalize. It must use the admitted combined
budget without assuming separate endpoint-square admission. The
source-specific positive-damping cross-work bound, both history debts,
and RH remain open. Goal remains active.
