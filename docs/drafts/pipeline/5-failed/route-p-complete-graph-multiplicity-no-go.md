# Route-P complete-graph multiplicity no-go

- **ID:** `P-G83`
- **Stage:** `5-failed`
- **Type:** exact cofinal-assembly no-go with formal positive survivor
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-critical-finite-packet-feshbach-assembly.md`
- **Survivor:** `../1-in-progress/hedenmalm-theta-route-p-adjacent-prime-cofinal-feshbach.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalCompleteGraphMultiplicityNoGo.lean`

## Failed conjecture P-G83.A

Sum P-G82's literal four-cell packet denominator over every ordered prime pair and every depth.
Conjecture: local prime/depth decay makes this complete interaction graph summable.

**Verdict: false.** Fix depth zero and lower prime `2`. Every edge `(2,q)` repeats the same
strictly positive within-prime consecutive minor at `2`. Its packet total Fisher clock contains
the same positive prime-`2` clock. Hence every `q != 2` slice has one common positive lower bound:

```text
anchorFloor <= DenominatorTerm(2,q,0).
```

The slice does not tend to zero along the cofinite prime filter, so it is not summable. Composition
with the injective anchor embedding proves the full complete-graph denominator is not summable.
Failure occurs before any quotient, Schur ratio, or exhaustion choice.

## New knowledge and higher principle

Obstruction is incidence multiplicity, not local chirality, valuation decay, or weak-kernel
continuity. P-G82 packets are overlapping local determinant charts: summing every chart repeats
same-prime Pluecker minors infinitely often. This is not a global Cauchy--Binet exterior sum, where
each selected column pair occurs once.

Necessary condition for any unrenormalized infinite packet assembly: every same-prime minor has
finite total incidence. Bounded-degree prime graphs satisfy this necessary condition without
altering physical packet weights. Canonical ordered adjacent-prime path is strongest source-first
choice available without fitted coefficients; P-G84 formalizes it.

## No-go closure audit

Positive survivor is nontrivial and dependency-closed:

```text
finite-incidence packet graph
  -> no repeated-minor floor
  -> adjacent-prime analytic majorant
  -> absolutely summable cofinal physical Feshbach fraction in (1/2,1).
```

Thus failed complete graph is retired. Re-attempt only with explicit de-duplication, weak-kernel
renormalization, or a proof identifying another source-forced finite-incidence graph.

## Lean audit

Headline declarations:

- `gammaSewnCriticalCompleteGraph_anchorFloor_pos`;
- `gammaSewnCriticalCompleteGraph_anchorFloor_eventually`;
- `not_summable_gammaSewnCriticalCompleteGraph_anchorSlice`;
- `not_summable_gammaSewnCriticalCompleteGraph_DenominatorTerm`.

```text
lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalCompleteGraphMultiplicityNoGo
Build completed successfully (12736 jobs).
```

Capstone `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Honest boundary

This theorem rejects only naïve complete packet overlap. It does not reject the P-G78 weak Köthe
kernel, a de-duplicated global exterior construction, bounded-incidence source graphs, completed
Gamma/polar Feshbach identification, or RH.
