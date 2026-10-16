# CHMD: operator core and physical spectral synthesis

Status: investigation. RH goal active; no new theorem claimed.

## Current evidence

Previous contribution formally classified the full graph radical and the full Xi-zero sample kernel. The current corpus also constructs the positive arithmetic resolvent `R=(1+L)^-1`, its dense Riesz lift, and the bounded Weil operator. These do not prove its positivity. Prior source hashes for full nullspace/detection match their audited versions. `docs/architecture.md` and `docs/testing.md` are absent. Plan tooling is unavailable; this card tracks work.

First deep corpus search completed with `partial=false`, inventory 72712/72712, no inventory errors; compiler coverage mostly pending/stale and semantic coverage must not be treated as theorem validation. Useful source arguments include the actual resolvent, full graph density, translated cardinal sources, and full nullspace classification. Broad candidate lemmas were mostly unrelated. Follow-up search targets operator cores and theta mean-periodic spectral synthesis.

## Conjecture under investigation

The compact C² core is an operator core for the full arithmetic jump generator, not only a form core. If established, mass-space weak critical solutions detected by all Fourier and pole samples can be admitted into the actual graph; no hidden weak boundary modes remain. A generic form-core argument alone is insufficient and will not be used as a proof.

## Plan

1. Inspect actual whole-corpus operator-core and spectral-synthesis leads; isolate an unconditional mechanism.
2. Prove or disprove the proposed core upgrade on paper. If it fails, audit its strongest positive survivor before retiring it.
3. Formalize only a dependency-closed structural theorem, with actual arithmetic admission and no added positivity/core/synthesis premise.
4. Targeted --old leaf builds; final plain `lake env lean`; all-declaration axiom audit; umbrella wiring without full build; lint; exact scratch cleanup; memory.

## Boundary

A new equivalence for RH, a bounded-operator receiver, or a better estimate alone does not fulfill this turn's target. No external novelty search, numerical experiment, or assumed selfadjoint domain.

## Structural mechanism being audited

The literal prime edge weights are `Lambda(n)/sqrt(n) * Theta(x) * Theta(x+log n)`; mass is `Theta(x) cosh(x/2) dx`. Chebyshev's actual toolchain theorem `Chebyshev.psi_le_const_mul_self` gives a linear prefix bound, without PNT or RH. Abel summation should give `sum_{n<=Y} Lambda(n)/sqrt(n) <= K sqrt(Y)`. With `Theta(u) <= C exp(-4|u|)`, logarithmic shells centered at x then give

`sum_n Lambda(n)/sqrt(n) * Theta(x-log n) <= K' exp(x/2)`.

Reflection supplies the plus-shift estimate. Both endpoint marginals of the full prime edge measure are therefore dominated by a fixed multiple of the mass measure. This would admit the literal prime difference of EVERY mass-L2 source, construct its bounded difference map and positive adjoint-square generator, and identify the full graph domain with the archimedean graph domain. Finite-prime operators should converge strongly; no operator-norm tail convergence is asserted.

For the remaining archimedean core, the half-density unitary transforms the singular part into `a A a + V`, with `a=sqrt(Theta/cosh)` and A the stationary Levy operator. Theta Lipschitz regularity and the already proved first Levy displacement moment make the multiplication commutator bounded. A resolvent-regularizer argument may then prove essential selfadjointness of the sandwich and transfer the compact core. This is still a paper conjecture, not a completed proof or a Lean assertion.

Corpus cautions: the Meyer Xi synthesis theorem concerns its strong logarithmic source topology, not this weighted arithmetic graph, so it cannot be imported as graph synthesis. Existing Suzuki logarithmic operators concern bounded apertures and only provide form-core information here. The second broad deep search was partial (text/source retrieval interrupted); use available source hits without claiming complete coverage.

## Dependency-closed paper proof: arithmetic domain removal

This component is proved on paper; the operator-core upgrade remains under investigation.

Write a(n)=Lambda(n)/sqrt(n) for n>=2 and zero otherwise. The existing corpus theorem `RHTower.sum_vonMangoldt_div_sqrt_le` gives sum_{n<=Y} a(n)<=34 sqrt(Y) for every Y>=0 (extend the integer theorem using floor). Choose C>=0 with Theta(t)<=C exp(-4|t|), already proved by theta decay. For fixed x and any finite set of n, group it by k=floor(|x-log n|). Within the kth group, n<=exp(x+k+1), so its a-mass is at most 34 exp((x+k+1)/2), while every theta factor is at most C exp(-4k). Sum the geometric sequence exp(-7k/2). Thus the full nonnegative row sum exists and is <=K exp(x/2), where K=34 C exp(1/2)/(1-exp(-7/2)). Theta evenness gives the plus-shift bound K exp(-x/2).

Pushforward of the full prime edge measure by left has density Theta(x) times the plus-shift row; its right pushforward has density Theta(x) times the minus-shift row. Translation invariance justifies the latter identity term by term; monotone integration justifies the infinite sum. Since exp(+-x/2)<=2cosh(x/2), both marginals are <=2K times the mass measure.

Therefore each endpoint pullback is a bounded map from mass L2 to prime-edge L2, and the literal difference Dp has norm at most sqrt(8K). This is valid for every mass L2 equivalence class, with representative independence supplied by marginal absolute continuity. P=Dp*Dp is an everywhere-defined positive bounded selfadjoint operator. For each mass-L2 source v, full edge admission is equivalent to archimedean edge admission because L2 for the sum of two measures is the intersection and prime admission is automatic. The same-source map identifies the full closed graph with the archimedean closed graph as Banach spaces, with equivalent graph norms. Arithmetic introduces no extra form-domain boundary.

For finite prime sets increasing to all n, indicator projections QN on the prime-edge space converge strongly to identity. Thus PN=Dp* QN Dp converges strongly to P, with positive residual P-PN. This uses the actual edge coordinate log n; inactive n=0,1 have zero measure, and distinct n>=2 have distinct log n. An alternative uses the increasing restricted measures and their quadratic forms. No operator-norm convergence is claimed.

Third deep search completed without partial flag, inventory 72719/72719 and no inventory errors; most compiler states remain pending/stale. Its proposed Schur-block ingredient set does not establish the needed prime measure theorem. Direct exhaustive rg found the existing Chebyshev square-root sum in `ZetaSymbolArchimedeanHorizon` and a sharper constant in `FreeLagTraceCertificateObstruction`; the former avoids a larger import surface.
