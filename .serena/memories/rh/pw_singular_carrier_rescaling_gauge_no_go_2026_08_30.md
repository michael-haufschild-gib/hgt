# PW singular-carrier rescaling-gauge no-go (2026-08-30)

Significant PW-B route-class kill formalized.

Exact chain attacked: `PW endpoint winding -> singular FE partner -> source-forced partner balance -> Deninger Ward -> RH`.

New theorem: exact singular gain `a(x)=A(x^2)=x^-1 exp(x-x^-1)` is a positive reciprocal cocycle and the explicit coboundary `g(x)/g(x^-1)` with `g=sqrt a`. Hence full weighted reciprocal reflection is multiplication-conjugate to bare reflection, and every two-channel block is diagonally similar to channel exchange. Closed universal no-go proves no predicate invariant under positive channel rescaling can select `x=1`. Source-adapted positive energy exists/conserves at every scale; fixed neutral energy conserves iff `x=1`. Gauge tends to zero and inverse to infinity at Borel boundary, so surviving PW-B work must use source-independent channel calibration or singular domain/connection data.

Lean:
- Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekSingularCarrierRescalingGaugeNoGo.lean`
- Capstone: `RHTower.pwSingularCarrier_rescalingGauge_noGo`
- Card: `docs/drafts/pipeline/3-formalized/pw-singular-carrier-rescaling-gauge-no-go.md`
- Umbrella: imported by `formal/GaloisForLFunctions/RHTower.lean`

Verification: direct `lake env lean` PASS; targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekSingularCarrierRescalingGaugeNoGo` PASS; `#print axioms` only `[propext, Classical.choice, Quot.sound]`. Global lint currently fails only on unrelated pre-existing unreachable modules in shared dirty tree; new module is reachable and has no forbidden proof-token failure.

External audit: generic pseudo-Hermitian/2x2 metric and weighted-composition theory is prior art; novelty is exact PW singular-carrier global coboundary + universal wall-selector obstruction + singular-boundary survivor. 2026 Akpinar et al. derive local detailed balance only with extra spin-universality input, consistent with need for calibration.