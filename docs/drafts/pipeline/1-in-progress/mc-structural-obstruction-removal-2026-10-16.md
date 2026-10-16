# MC: structural obstruction removal

Status: IN PROGRESS. No contribution established yet.

## Objective

Find and prove one unconditional structural theorem that removes a hard obstacle
in the actual signed Möbius cancellation route. Improved bounds, RH equivalences,
conditional receivers, computational evidence, and generic rearrangements do not
meet the task. Use the Lean corpus as the research source; no web or external
novelty audit. Preserve unrelated existing edits.

## Plan

1. Recover the current frontier and obstruction from indexed Lean declarations
   and their full statements/proofs.
2. Iterate exact conjecture, attempted refutation, and learned replacement.
3. Complete a dependency-closed paper proof before formalization.
4. Formalize without unproved inputs; directly audit each new module using
   `lake --old env lean`, audit axioms, wire imports, run formal lint, clean scratch.

## Corpus findings

- `MobiusSquareResidueShortBilinear`: exact short reconstruction retains all
  product cutoffs; its kernel has a cubic positive diagonal and negative terminal
  principal minor. Sign-blind positivity is unavailable.
- Route MC's current entry identifies joint principal-counterterm/high-product
  cancellation as open. Small-modulus, low-product and terminal estimates do not
  control the whole source.
- Existing prime-insertion, physical-wavelet and growing-smoothing results must
  be inspected before proposing another local cancellation or smoothing scheme.

## Conjecture ledger

1. **Repair the square kernel using the source counterterms. Rejected: FALSE.**
   `MobiusSquareRenormalizedKernel.squareKernel_firstRowCorrection_minor_neg`
   leaves a negative principal minor at indices `2,N` for every `N >= 4`,
   for every correction supported in the first row or column. Its explicit
   negative direction and cubic positive diagonal exclude the proposed
   coefficient-independent sign mechanism. No new no-go is claimed.

2. **Obtain a positive source kernel by increasing prime-packet smoothing.
   Rejected in the fixed physical window.** The existing normalized packet
   escape theorem prevents a unit-mass pointwise limit in that window.
   Recentering would change the physical observation; it is not a proof of
   cancellation of the original source.

3. **Cancel opposite signs within complete product fibres. Rejected: FALSE.**
   `MobiusProductFibreVariation.pair_sign` proves
   `mu(m) mu(n) = lambda(m*n) mu(m)^2 mu(n)^2`.
   `abs_signedFibre_eq_unsigned` proves that product grouping loses no
   unsigned variation. Cancellation must cross products, even when factors
   share primes. `MobiusProductFibrePrimeBalance` already supplies the exact
   local two-placement law; its diagonal cancellation at prime three leaves
   child diagonals and other pair channels.

4. **Use complete LCM-fibre cancellation at the physical cutoff. Rejected:
   FALSE.** `EulerDeletionAllShiftLcmPolarity` already gives the full divisor
   incidence identity. `EulerDeletionCenteredLcmInitialCutoffSign` proves
   that the literal physical window `(t,H)=(0,15)` has complete-grade prefix
   through `10` equal to `-45/196`. Divisor-closed positive conservation
   therefore cannot be transferred to the physical initial segment.

5. **Upgrade finite-dimensional prime steering into exhaustive cancellation.
   Rejected as a completed argument: MISSING STEP.**
   `MobiusDivisorFiniteDepthPrimeCancellation` already produces an inward
   actual-prime collar for every nonzero coefficient vector in any fixed
   finite child field, uniformly on its coefficient sphere. A positive-span
   corollary would not advance this frontier. `MobiusDivisorUniformReserveHistory`
   controls sparse histories at all cutoffs, whereas
   `MobiusDivisorExhaustiveClockCheckpoints` exhausts primes only with budgets
   at moving checkpoints and short collars. Neither result pays the old
   cutoff after its remaining primes are processed. These different
   quantifiers cannot be interchanged.

## Current unresolved point

### Continuation: whole clock intervals

Fresh source inspection found that `MobiusDivisorPaidPrimeExhaustion` now
constructs an exhaustive history whose blocks are paid at their assigned
cutoffs. Its theorem does not transport payment between cutoffs. Arbitrary
retained finite fields and simultaneous finite Boolean phase gates are also
already solved (`RetainedPrimeBoundedBatches`, `MobiusDivisorPreparedPrimeCube`).
These are existing results, not contributions of this investigation.

6. **Repay prescribed debt using arbitrarily delayed bounded-mass preparation.
   Rejected: FALSE.** The new clock-delayed insertion theorem in
   `MobiusDivisorInheritedPrimeInsertionProducer` separates a favorable
   insertion marginal from payment of the original debt. Bounded halfweight
   preparation can leave a fixed positive net debt at arbitrarily late clocks.

7. **Iterate local quantitative debt payments to complete repayment.
   Rejected as a proof: MISSING STEP.** Payment constants and admissible helper
   thresholds depend on the changing core. The available per-step reciprocal
   prime payments do not imply a divergent total payment along the constructed
   history.

8. **Positive dilation cone on an entire compact clock interval. ACTIVE;
   paper argument completed, formalization in progress.** For the actual complete continuous Abel source `A`, conjecture
   that the positive cone of `u ↦ A(exp(t+u))`, with arbitrarily late `t`, is
   dense in `C([0,L], R)` for each finite `L`. This would remove the restriction
   to finitely many fixed receiving coefficients. Proposed mechanism: a
   separating continuous functional has an entire Fourier--Borel transform of
   finite exponential type; eventual one-sidedness of its source convolution
   permits Landau continuation; surviving simple critical poles force that
   transform to vanish. The corpus proves a superlinear simple-critical-zero
   census and the required general exponential-type nonannihilation theorem.
   Remaining proof obligations: the literal Banach-valued source transform,
   compact-head subtraction, real-axis Landau continuation, injectivity of the
   compact functional transform, and cone separation. No density theorem or
   actual prime-history consequence is claimed yet.

   Important audit: density alone does not provide uniformly bounded synthesis
   coefficients, simultaneous actual-prime block rounding, or a history that
   retains payment after the cutoff changes. Those implications need separate
   proofs and must not be smuggled into the conjecture's significance claim.

### Exact paper argument for conjecture 8

Write `f(t) = exp(-3t/2) A(exp t)`, the corpus's literal
`criticalAbelLogProfile`. It is continuous, bounded, and zero for `t <= 0`.
For `a >= 0` put `v_t(u) = f(t-u)` in `C([0,a], R)`.

1. A continuous real functional `L` has a canonical complexification. Its
   transform `F(s) = L_C(u -> exp(-s*u))` is entire with finite exponential
   type. If `F` vanishes identically, exponential difference quotients force
   all polynomial moments of `L` to vanish. Polynomial density forces `L=0`.
2. Banach integration and the literal causal cutoff give the exact identity
   `Laplace(L(v_t))(s) = F(s) Laplace(f)(s)` for `Re(s)>0`. The proof uses
   the actual complete source, not a replacement spectral function.
3. For `g(t)=exp(t)L(v_t)`, the continued transform is
   `F(s-1) M(s+1/2)`, where `M` is the completed critical Abel Mellin source.
   It is meromorphic everywhere and analytic at every real `s>1/4`.
4. If `L != 0`, the corpus's superlinear census of simple critical zeros
   forces `F(-1/2+it) != 0` at some such zero. The source's genuine simple
   pole survives, giving the product a pole at real part `1/2`.
5. If `L(v_t)` were nonnegative after a finite depth, its positive tail,
   with compact head retained, would have a real convergence abscissa.
   Landau and real-axis analyticity force that abscissa to `1/4`. The
   reconstructed transform is analytic on `Re(s)>1/4`; meromorphic identity
   propagation contradicts the pole from step 4.
6. Thus every nonzero continuous functional takes a strictly negative value
   on `v_t` beyond every depth threshold. Hahn--Banach separation implies
   that the positive cone of these late profiles is uniformly dense in the
   entire continuous-function space. In particular, a finite positive
   mixture is strictly negative throughout the whole clock interval.

The substantive upgrade is from finite receiving vectors to all continuous
clock trajectories with one common finite positive synthesis. It gives no
uniform bound on synthesis coefficients or source depths. Transfer from
these positive mixtures to exhaustive actual-prime histories is not proved.

Formal progress: the generic meromorphic tail-separation proof and the
literal Banach source transform / compact-dual injectivity have passed
scratch Lean checks. Source-specific pole separation and the final cone
producer are still being checked. No completed contribution is claimed yet.

No unconditional construction has been found that retains the actual full
signed source and removes the changing-cutoff obstruction. For the square
bilinear formulation, principal counterterms and high-product remainder
remain jointly uncontrolled. A theorem merely restating their required
control, a finite-rank steering corollary, or another local cancellation
identity would not meet the requested contribution.

No route is newly retired. All negative results above were already proved
in the corpus. No new positive survivor or paper proof is claimed.

## Search and source audit

Used the documented `scripts/formal_tools.py research` command in lexical,
hybrid, and deep modes, including searches across all indexed Lean areas and
dependencies. Inspected candidate lemmas and source arguments, then read
relevant Lean statements/proofs. Search reported no unfinished stages in
the completed semantic requests, but warned of older coverage snapshots and
unmeasured semantic coverage; search results are leads, not a completeness
certificate. No web search, external novelty audit, or numerical experiment
was performed. Only the explicitly requested MC frontier entry and operational
instructions were read as repository Markdown; historical research cards
were not used.

## Self-audit

- No new mathematical knowledge established; requested frontier advance not achieved.
- Existing corpus results killed the proposed mechanisms before code was added.
- Formalizing their immediate consequences would be theorem packaging, not
  the requested structural breakthrough.
- Paper-proof and Lean phases remain uncompleted because no qualifying exact
  theorem has survived the mathematical audit.

## Verification

No Lean source changed, so no build or new axiom audit was run. Existing user
edits were preserved. This card records incomplete research, not completion.
