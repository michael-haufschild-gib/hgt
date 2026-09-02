# Suzuki common-domain Gamma--Robin trace no-go

- **ID:** CCM-FU-C26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/irregular-stokes-robin-gamma-holonomy-coercivity.md`
- **Statement:** No fixed common Hilbert graph domain with fixed Hilbert--Schmidt ingress/egress and weakly bounded domain-preserving observers can lower-semibound the corrected Suzuki transition-core Ward defect.

## Goal

Kill the fixed-common-domain singular observer survivor left by C24--C25 in the CCM-FU chain. This does not prove RH; it forces any remaining Gamma--Robin producer outside fixed weakly bounded graph domains or fixed Hilbert--Schmidt sandwiches.

## Gates

- [x] 0 → 1: source-pure conjecture from C24--C25 and corpus trace-ideal machinery
- [x] 1 → 2: weak boundedness → uniform graph norm → Hilbert--Schmidt trace bound → Ward contradiction
- [x] 2 → 3: `RHTower.no_suzukiCausalDepthGammaCommonDomainWardProducer`; targeted build and axiom audit pass
- [ ] 3 → 4: publication-ready standalone statement and external novelty audit

## Approach

Two Banach--Steinhaus steps uniformly bound observer norms on the common graph domain. Hilbert--Schmidt ideal composition and trace Cauchy--Schwarz uniformly bound the scalar correction. The transition-core Ward defect still tends to `-∞`, contradicting its eventual lower floor.

## No-go closure

- **Exact killing theorem/mechanism:** `no_suzukiCausalDepthGammaCommonDomainWardProducer` in `SuzukiCausalDepthGammaCommonDomainRobinTraceNoGo.lean`.
- **Strongest positive survivor:** a viable singular producer must use moving domains, graph-weak blow-up, non-domain-preserving action, or non-Hilbert--Schmidt/non-nuclear ingress or egress.
- **New insight:** unboundedness only in the ambient `L²` norm is insufficient; regularization through any fixed weakly controlled Hilbert graph domain remains trace-bounded and cannot cancel transition-core escape.
- **Status:** paper proof dependency-closed; Lean closed as `¬ Nonempty`; only standard `propext`, `Classical.choice`, `Quot.sound`; targeted module build passes.

## Log

- 2026-09-01 — proved and formalized as CCM-FU C26.
