# SZ: structural cancellation at original cutoffs

Status: in progress. Corpus-only research; no external novelty audit.

## Objective

Remove a structural obstruction in the actual SZ source, unconditionally.
An improved bound, RH equivalence, or interface carrying the missing input
does not meet the objective.

## Plan

1. Identify the actual frontier from Lean source and corpus search.
2. Form exact conjectures, attack them, retain what each failure teaches.
3. Complete a dependency-closed mathematical proof before formalization.
4. Audit each finished module directly with `lake env lean`, wire imports,
   run formal lint, and remove scratch artifacts owned by this task.

## Verified corpus frontier

- `MobiusDivisorCriticalCorrelationTailSign`: actual boundary
  autocorrelation is negative beyond every lag cutoff.
- `MobiusDivisorCriticalFiniteCorrelationSign`: actual finite critically
  weighted pairings can also be negative.
- `MobiusDivisorFiniteClockCountingCancellation`: exact weighted counting
  identity retains signed mixed terms and pays copied diagonal squares.
  Offset one retains the completely processed head; offset zero loses it.
- `MobiusDivisorFiniteDepthPrimeCancellation`: every nonzero finite linear
  combination of delayed processed heads takes both signs; a uniform actual
  prime inward collar exists for each fixed finite child field.
- `MobiusDivisorGrowingDepthCurrentPayment`: an omitted prime of logarithmic
  size can be paid at the current clock, starting from one fixed small core.
- `MobiusDivisorExhaustiveClockCheckpoints`: nested exhaustive cores have
  bounded energy at moving checkpoints, not at frozen earlier cutoffs.
- `MobiusDivisorTerminalClockOrder`: terminal insertion prefixes stay below
  the larger endpoint energy; the completed source square remains unpaid.

## Conjecture log

1. Replace cumulative signed control by eventual positivity of actual
   correlations. **FALSE**, explicitly disproved by existing Lean theorems.
   Lesson: preserve signed products; neither tail removal nor finite-cutoff
   restriction repairs positivity.
2. Obtain completion by combining exhaustive checkpoints with the terminal
   insertion order. **CIRCULAR**: the order retains the completed source
   square as its second endpoint. Lesson: original cutoffs must remain in
   the source construction; changing checkpoint cannot discharge their debt.
3. Extend fixed-field inward selection to simultaneous original-cutoff
   protection. **UNDER ATTACK**: a finite vector statement alone may be a
   restatement of the existing arbitrary-delay result. Fresh primes above
   an old cutoff cannot alter it. A surviving construction must address
   actual finite supply and cumulative insertion, not convex weights alone.

## Search limitations

Hybrid `critical correlation` search completed, but semantic coverage was
unmeasured and results were predominantly source-only. Broad deep search
returned partial results (malformed local-model JSON and interrupted text
retrieval). Exact source searches supplement these results; no claim of
complete semantic coverage is made.

## Completion gate

Not met. No new theorem or obstruction removal is claimed yet.

## Current SZ source target and rejected rediscoveries

The current frontier-map SZ entry (read only its current entry, not historical
notes) identifies moving-source Wronskian control with retained cusp
cancellation. The Mobius-divisor finite-clock branch is related but does not
resolve this source realization problem.

The complete retained-prime linear cone already exists in
`RetainedPrimeLandauSeparation`, `RetainedPrimeFiniteSourceMargin`, and
`RetainedPrimeBoundedBatches`. Positive inherited covariance circuits and
actual batches already exist in `MobiusDivisorTwoDebtSourceCycle` and
`MobiusDivisorPositiveDebtBatches`. Neither is a new contribution here.

Increasing the prescribed coercive shift is not a repair:
`SuzukiTaV2PrescribedCarrierCollapse` proves locally uniform collapse to zero.
`CCMSuzukiCrossApertureCurvatureLeakage` identifies the retained curvature as
metric-shift times physical shell leakage. Merely changing normalization does
not control it.

## Candidate: asymptotic self-adjoint orbit realization

`SuzukiLocalizedOrbitLiftTrilemma` excludes one nonzero square-summable
translation-covariant weight. `SuzukiOrbitCarrier` instead supplies exact
covariance with nonselfadjoint weighted shifts. Test a third realization:
normalized square-summable lifts with ordinary unitary shifts, retaining the
covariance error and sending it to zero.

For a finite prime alphabet P, put w_rho(nu)=rho^|nu|_1 and
Z_rho=sum_nu w_rho(nu)^2. For 0<rho<1 define
J_rho(u)(nu)=w_rho(nu)/sqrt(Z_rho) times U_(ell nu)u.
The corpus proves Z_rho is finite and positive. Translation is unitary, hence
J_rho is an exact linear isometry. Ordinary coordinate translations remain
unitary; their real symmetric combinations remain self-adjoint.

For each valuation step s, the two terms in
S_s J_rho(u)-J_rho(U_(ell s)u) have the same physical translate.
Weight subadditivity gives a relative difference at most
rho^(-|s|_1)-1. After normalization, its norm therefore tends to zero as
rho approaches one from below, independently of lattice rank and u on the
unit ball. Finite operator words and all signed matrix coefficients follow
without replacing a correlation by its absolute value. Physical multipliers
must be transported coordinatewise with the translated physical coordinate,
not with a fixed diagonal valuation cutoff.

Paper obligations still under attack:
1. Exact Hilbert lift, ordinary unitary covariance limit, and adjoint recovery.
2. Literal aperture cutoff intertwining and full completed source-form recovery,
   including archimedean/polar terms, not only finite prime adjacency.
3. Moving-alphabet compatibility and whether this removes a source-domain
   obstruction used by SZ rather than merely producing another interface.

This construction is not a positivity claim or a Wronskian bound. It must not
be reported as satisfying the requested frontier contribution unless the
actual source application and obstruction removal are established.

## Candidate revision: closed two-leg Gamma synthesis

The normalized orbit-lift proposal has not removed moving-source cancellation; no Lean implementation or frontier claim is warranted for it.

A more concrete survivor of the two-leg source-normal graph obstruction is now under audit. The existing obstruction excludes square-summability of the deattenuated amplitude family, not closability of the feature-synthesis operator on finite source packets.

### Dependency-closed paper argument

Write `d(0)=1`, `d(k+1)=k+3`, `c_k=JacobiNormalization(d(k))`, `r_pe=tanh((e+1) log(p)/2)`, and `phi_pe=cosh((e+1) log(p)/2)^(-1/2)`. The actual deattenuated column is

`v_pe(k)=p * weight(h,a,pe) * phi_pe * c_k * r_pe^d(k)`.

Keep these columns unchanged. Their adjacent weighted difference is

`c_(k+1) v_pe(k) - c_k v_pe(k+1)
 = p * weight * phi * c_k*c_(k+1) * r^d(k) * (1-r^(d(k+1)-d(k)))`.

The degree gap is two at the first coordinate and one thereafter. Since `p(1-r) <= 2`, each such row is bounded by a constant times the original square-summable amplitude family. Hence every difference row defines a continuous linear functional on the full source Hilbert space.

Define a graph by these continuous row equations, together with zero output in the unused arithmetic-coordinate sector. This graph is closed. Its vertical kernel is zero: every homogeneous solution has feature coordinates `z*c_k`; the squared Jacobi coefficients are normalized central binomial coefficients and dominate `1/(d(k)+1)`, hence are not summable. Thus the graph defines a closed operator. Every coordinate source lies in its domain with exactly the displayed deattenuated column, so the domain is dense. Restricting to finite source packets and taking graph closure gives the canonical minimal closed synthesis operator, without replacing any finite source coefficient or Gram matrix.

This construction uses cancellation between neighboring Gamma coordinates, not a fixed diagonal graph norm. It therefore does not contradict the existing amplitude-admission no-go. A further audit must establish that the realized operator genuinely leaves the bounded/trace-class class, and connect its exact finite-packet energy to the existing Gamma Schur kernel. Neither a Robin/Ward comparison nor the full signed Weil source law is proved by this construction alone.

### Current gates

- Paper closability mechanism: explicit, pending detailed Lean audit.
- Exact finite-column and Gram recovery: required.
- Dense domain and canonical graph closure: required.
- Escape from bounded/trace-class realization: required.
- Significance for the full SZ objective: still under assessment; do not present a carrier construction alone as completion of the requested contribution.

### Verified structural core and next conjecture

Direct Lean audits now verify boundary cancellation, canonical graph closure, zero vertical kernel, dense domain, exact finite-packet recovery, exact Gram kernel `p*q*GammaSchur(pe,qe)`, nonexistence of a bounded extension, and the fixed premise-free canonical theorem. The finite-row boundary classification audit remains in progress.

The stronger conjecture is an exact boundary-domain classification. For a finite complex family `a_k`, the source row `sum_k a_k*v_pe(k)` is representable by an arithmetic-sector Hilbert vector if and only if `sum_k a_k*c_k=0`.

Paper proof: set `b_k(pe)=v_pe(k)` and `R_k=c_(k+1)*b_k-c_k*b_(k+1)`. Each `R_k` is a Hilbert row. Induction gives a Hilbert row `W_k=c_0*b_k-c_k*b_0`, using `W_0=0` and `W_(k+1)=(c_(k+1)/c_k)*W_k-(c_0/c_k)*R_k`. Therefore `c_0*sum a_k*b_k-(sum a_k*c_k)*b_0=sum a_k*W_k` is a Hilbert row. A zero boundary coefficient suffices. A nonzero boundary coefficient would make `b_0` a Hilbert row, contradicting its prime-harmonic divergence. This classifies the obstruction as one explicit boundary functional on finite Gamma tests. It is not a new assumption on the source.

### Unboundedness and exact scope

At depth zero the first row satisfies the exact identity

`|b_0(p,0)|^2 = C_h^2 log(p) [p/(p+1)]^2 [(p-1)/(p+1)]^2 [1-disk((h/2)a,p)]^4 /(p+1)`,

where `C_h=(h sqrt(h))^-1`. The disk term tends to zero. The displayed square therefore dominates a positive multiple of `1/p` eventually. Prime-harmonic divergence rules out a Hilbert representative of this row. If a bounded operator reproduced the columns, its adjoint applied to the first Gamma coordinate would be such a representative. Thus no bounded extension exists.

The old amplitude-admission predicate remains false. The positive theorem constructs a different, non-diagonal closed graph for the **same columns and finite energy kernel**. It does not assert that the forbidden amplitude vector becomes square-summable, nor that the minimal closed graph equals every maximal extension. The exact finite-row boundary condition and canonical graph closure are the structural advance. The completed signed Robin/Ward comparison remains unresolved.
