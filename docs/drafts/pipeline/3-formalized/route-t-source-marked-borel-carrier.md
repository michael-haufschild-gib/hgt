# Route T source-marked residual Borel carrier

- **ID:** T-C5a
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/route-t-required-residual-continuation.md · C5a
- **Statement:** The complete Wold residual jet has a source-faithful second-factorial Borel carrier holomorphic on one nontrivial disc independent of boundary point.

## Goal

Retain every Wold prime edge while turning the corpus Gevrey-2 boundary jet into a genuine local
holomorphic object. Full Route-T chain is:

```text
source-marked Borel carrier
  -> positive-normal-ray continuation and exponential type [C5b OPEN]
  -> lateral Borel-Laplace reconstruction with zero jump [C5b OPEN]
  -> forced required residual regularity
  -> riemannHypothesis_iff_requiredResidualContinuation_continuousAt
  -> RH.
```

## Gates

- [x] 0 → 1 in-progress: source-pure carrier, exact Route-T passport
- [x] 1 → 2 fully-proven: dependency-closed normal-convergence proof
- [x] 2 → 3 formalized: Lean module and targeted build green; closed-axiom audit green
- [ ] 3 → 4 publication-ready: external expert novelty audit and standalone exposition

## Approach

Split the square-root-exponential Wold estimate into a summable edge factor and an even-factorial
height moment. The central-binomial bound converts the remaining second-factorial series into a
geometric majorant. Absolute summability over `(source, order)` then permits exact Fubini
regrouping, and a Cauchy-dominated `tsum` theorem gives holomorphy.

## Formal certificate

Module:
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelCarrier.lean`.

Principal declarations:

- `exists_global_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_sqrt_rate`
- `exists_radius_summable_norm_xiHeatCassiniWoldResidualBorelAtom`
- `exists_radius_xiHeatCassiniWoldResidualBorelCarrier_eq_jetSeries`
- `exists_radius_differentiableOn_xiHeatCassiniWoldResidualBorelCarrier`

`lake env lean` and targeted
`lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelCarrier` pass. `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into RHTower umbrella;
umbrella build was intentionally not run. Global lint currently fails on unrelated pre-existing
unreachable modules in shared theorem-area umbrellas.

## Novelty status

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` Internal corpus and primary-literature audit found no prior
source-labelled Wold prime-edge second-factorial carrier, common-disc normal-convergence theorem,
or exact residual-jet regrouping. External expert review remains required before publication.

## Log

- 2026-08-29 — paper proof completed, formalized, targeted build and closed-axiom audit passed
