# FZZ-P higher cleared-screening exchange-stable orientation

- **ID:** fzz-p-higher-cleared-screening-exchange-stable-orientation
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** literal restored two-puncture screening source; `FZZCigarHigherScreeningGammaContinuation`
- **Statement:** No finite exchange-stable or joint all-depth depth integration of the complete restored cleared higher-screening source has nonzero FZZ-P orientation.

## Goal

Test whether the already source-defined higher screening continuation can supply the missing oriented replica--momentum Ward term.

## No-go closure

- **Exact killing theorem/mechanism:** `fzzScreeningHigherClearedSource α β` is real and reflection-symmetric. Its complex depth kernel is Hermitian, so both the finite ordered-source identity and the all-depth joint exchange identity give zero imaginary part on every exchange-stable source domain.
- **Strongest positive survivor:** On arbitrary finite ordered support, its full non-real current is exactly `fzzRadialCouplingDepthOrderDefect`; for an all-depth source, a physically derived non-joint order prescription or independent non-Hermitian phase-frame/full-Ward coupling is necessary.
- **New insight:** Continuation, local counterterms, exterior screening, and joint all-depth summation cannot conceal the required FZZ current in a complex coefficient. A viable source must derive a literal order datum rather than obtain it from scalar continuation.
- **Status:** dependency-closed Lean formalizations in `formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningOrderedSourceNoGo.lean` and `formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningAllDepthJointNoGo.lean`; direct `lake env lean` audits passed; leaf OLeans materialized; audited claims use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella build intentionally not run under leaf-only audit policy.

## Log

- 2026-09-21 — closed as a source-specific FZZ-P subroute; survivor retained.
