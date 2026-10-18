# MSC: remove the auxiliary logarithmic Hilbert weight

Status: FORMALIZED — exact critical source admission. Canonical, axiom and index
checks passed; global lint reports 9 unrelated unreachable modules. Route candidate MSC;
framework BiScaleUncertainty. Sonin comparison and RH remain open.
Selected after the completed RW-to-TH rotation cycle. RH remains the goal.

## Source and proved statement

`SquarefreeDiscrepancyHilbertTransport.lean` uses the literal source
`h(t)=1_(t>0) E(exp t) exp(-t/2)/(1+t)`, where E is the full squarefree
counting discrepancy. Its fixed clock pair is admitted in L2 and preserves
the MSC partition, derivative, and conormal. The auxiliary logarithmic
weight is paid back in the evaluation vectors; this admission does not yet
provide the critical Mellin/Sonin energy comparison.

The unweighted physical source `U(t)=1_(t>0) E(exp t) exp(-t/2)` belongs to L2.
Its norm corresponds exactly to the finite actual discrepancy energy
`integral_1^infinity E(x)^2/x^2 dx`. The required logarithmic saving is produced
from this corpus's unconditional Mertens estimate; no cancellation bound or RH
premise is left as an assumption. Its natural Hilbert evaluation pairing equals
the original full arithmetic Mellin moment throughout Re(s)>1/2.

## Hostile audit

The existing pointwise envelope `|E(x)|≤4 sqrt(x)` alone gives a divergent
critical energy majorant and cannot prove this conjecture. Hilbert positivity
of the already weighted source cannot replace the Ward four-unit Schur law.
`GammaSewnMobiusXiWardSourceNonexpansiveNoGo.lean` concerns the older literal
source map; applying it unchanged to the new fixed source plane would be an
unproved identification. Exact conormal preservation leaves inverse-overlap
division and complementary-channel subtraction unpaid.

The proposed admission improvement would remove a representation obstacle,
not by itself prove RH. A subsequent Sonin/source-energy landing remains
necessary. Do not write a new RH equivalence in place of an estimate.

## Completed research steps

1. Searched actual arithmetic bounds and source/energy interfaces.
2. Proved the estimate for the full signed discrepancy, retaining both tails,
   exact density and endpoint terms; closed the paper proof before Lean.
3. Audited the Sonin use: admission does not settle inverse-overlap energy sign.
4. Formalized the unconditional producer, finite energy and exact Mellin pairing.
5. Canonical leaf, axiom, import and index checks passed. Formal lint was run;
   its 9 unrelated failures are recorded below. Rotate to another family.

## Current evidence

The prior MSC memories identify the Sonin energy comparison as open. Current
Lean definitions and source identities were inspected directly. Completed deep
search output: `/tmp/hgt-msc-source-rotation-search.json`; partial=false, no
errors, inventory complete, compiler snapshots largely pending/stale, background
indexer prevents a full refresh. Candidate/source-argument lists contained no
ready critical-energy producer. The lexical Mertens search found the actual
unconditional input `Sieve.deningerMertensM_log_pow_rate` in
`Sieve/MoebiusHarmonicArbitraryLogRate.lean`. Its source was inspected: it weakens
the unconditional contour estimate `deningerMertensM_rate`, with no RH premise.

## Dependency-closed paper proof

Write M(r)=sum_(n<=r) mu(n). For an integer D>=1 and delta>=0 such that
|M(r)|<=delta*r for every r>=D, finite Abel summation gives, for R>=D and
nonnegative decreasing w on [D,R],

    |sum_(D<n<=R) mu(n) w(n)|
      <= delta*(2D*w(D) + sum_(D<n<=R) w(n)).

Indeed the exact boundary terms are M(R)w(R)-M(D)w(D), and the remaining
sum is M(n)(w(n)-w(n+1)) over D<=n<R. Taking absolute values and telescoping
the coefficients n yields the displayed bound, including both endpoints.
For w(n)=n^(-2), the reciprocal-square tail is at most 1/D, so passage to
the already absolutely convergent sum gives

    |sum_(n<=D) mu(n)/n^2 - density| <= 3delta/D.

For w(n)=floor(N/n^2), its monotonicity and w(n)<=N/n^2 give

    |sum_(D<n<=N) mu(n)*floor(N/n^2)| <= 3delta*N/D.

The exact squarefree divisor identity, split at D<=N, now gives

    |Q(N)-density*N| <= D + 6delta*N/D.

The head costs D because each fractional part lies in [0,1) and |mu|<=1.
This estimate retains cancellation in both tails; replacing their coefficients
by absolute values would lose the improvement.

Use the corpus's p=2 Mertens estimate |M(n)|<=B*n/(log n)^2 for all n>=K.
For large t, set x=exp(t), N=floor(x), D=floor(exp(t/2)/t). Exponential
dominance gives D>=exp(t/4)>=K, D>=exp(t/2)/(2t), D<=exp(t/2)/t, and D<=N.
Thus log(n)>=t/4 for n>=D, and delta=16B/t^2 is admissible. The bound becomes

    |E(exp t)| <= (1+192B)*exp(t/2)/t + 1.

The final 1 is the real-cutoff density endpoint; 0<=density<=1. Multiplying
by exp(-t/2), and using exp(t/2)>=t eventually, bounds |U(t)| by
(2+192B)/t. On every bounded positive t interval the existing square-root
bound gives |U(t)|<=4. U is measurable, vanishes on t<=0, and has square
bounded by an integrable compact part plus C/t^2 on a positive tail.
Therefore U belongs to L2. The substitution x=exp(t) gives finite literal
discrepancy energy integral E(x)^2/x^2 dx on (1,infinity).

This proof removes the auxiliary Hilbert weight using an unconditional
arithmetic producer. It supplies no sign for the inverse-overlap Sonin or Ward
comparison; that remains open. No numerical experiment or external source was
used. Lean checked the complete proof, including all 15 public declaration
axiom lists: only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Exact framework landing

`abs_squarefree_count_sub_le_of_mertens` is the finite arithmetic transfer;
`eventually_abs_error_exp_critical_le` instantiates its premise from the proved
Mertens saving. `memLp_unweightedSourceFunction` admits the fixed, literal
source U; `integrableOn_discrepancy_critical_energy` and
`integral_discrepancy_critical_energy_eq` identify its actual arithmetic energy.
`inner_unweightedSource_evaluation` pairs U with the natural column
`1_(t>0) exp(-(s-1/2)t)` and returns the same full moment for Re(s)>1/2.
Thus neither side of this pairing pays an auxiliary `(1+t)` factor.

The bound is finite-energy admission, not the four-unit Ward bound. Dividing
by the partition overlap and controlling the complementary Sonin energy are
still unpaid. No source norm bound in this package establishes that comparison.
After these audits, rotate to another family rather than refining constants
or extending this same admission result.

## Lean checkpoint

Owned sources:

- `formal/GaloisForLFunctions/BiScaleUncertainty/SquarefreeCancellationTransfer.lean`:
  3 public transfer theorems; canonical direct audit passed, exit 0, empty log
  `/tmp/hgt-msc-transfer-final.log`; `.olean` and `.ilean` produced.
- `formal/GaloisForLFunctions/BiScaleUncertainty/SquarefreeCriticalLogEnvelope.lean`:
  actual unconditional Mertens saving instantiated at the exponential cutoff.
  Combined scratch found only a redundant `dsimp` in this leaf; fixed.
  Canonical audit passed with exit 0; `.olean` and `.ilean` produced.
  Log `/tmp/hgt-msc-envelope-final.log` contains an internal tactic suggestion,
  no error or warning diagnostic.
- `formal/GaloisForLFunctions/BiScaleUncertainty/SquarefreeUnweightedHilbertSource.lean`: L2 admission, finite
  discrepancy energy, exact energy identity, and natural Mellin pairing;
  combined scratch audit finished with coercion and beta-reduction issues;
  corrected in the source. Final canonical check passed with exit 0; log
  `/tmp/hgt-msc-hilbert-final.log`. Objects produced. Four harmless warnings
  report redundant trailing `ring` tactics after goals were already closed.
  Diagnostic log: `/tmp/hgt-msc-remaining-scratch.log`.

All three imports are wired into the BiScale umbrella. All source hashes were
unchanged across canonical checks and the public axiom audit (15 declarations).
Audit `/tmp/hgt_msc_axioms.lean` passed with exit 0; every list contains only
`propext`, `Classical.choice`, and `Quot.sound`. Log: `/tmp/hgt-msc-axioms.log`.
Index passed with 2 changed and 0 removed modules; log
`/tmp/hgt-msc-final-index.log`. `scripts/formal_tools.py lint --check-generated`
exited 1 solely on these unrelated modules missing their umbrella imports:

- `BiScaleUncertainty.CentralBinomialRatioGrowth`
- `BiScaleUncertainty.EndpointCycleDeterminant`
- `BiScaleUncertainty.FactorialPolarGramScaleSeparation`
- `BiScaleUncertainty.FactorialPolarLossAsymptotic`
- `BiScaleUncertainty.FactorialPolarLossLowerBound`
- `BiScaleUncertainty.SharpCycleGramRealization`
- `BiScaleUncertainty.SharpGramDetectionOrder`
- `BiScaleUncertainty.StationaryResolventMarkovPositivityAndNodalDefectProducer`
- `BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes`

No error names a module in this MSC package; no generated-file or forbidden
declaration error occurred. Preserve the concurrent work instead of importing
its unverified leaves. Global lint has **not** passed. Log:
`/tmp/hgt-msc-final-lint.log`. Manifest: `/tmp/hgt-msc-audit-manifest.json`.

API probe `/tmp/hgt_msc_api.lean` passed. No owned Lean process may overlap
another. Continue from the live handle rather than restarting an import-heavy
audit. RW still has 5 missing shared dependency objects in the final inventory;
the external build remains live and untouched.

RW remains audit-only while the external shared-dependency rebuild is live.
Do not duplicate that build. Both framework READMEs and the route ledger remain
read-only. Preserve concurrent BVI, cycle, diagonal, and stationary-resolvent work.
