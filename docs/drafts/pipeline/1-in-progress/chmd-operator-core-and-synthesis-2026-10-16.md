# CHMD: operator core and physical spectral synthesis

Status: archimedean operator-core investigation remains active. Arithmetic form/operator-domain removal is now formally proved; RH remains unproved.

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

## Operator-domain strengthening forced by the form identity

The bounded-prime statement yields more than equality of form domains. Let R be the corpus full arithmetic resolvent and Ra the Riesz resolvent of the actual archimedean graph. Polarization of the exact graph norm identity gives

`<p,q>full = <Tp,Tq>arch + <P source(p),source(q)>mass`,

where T preserves sources. Riesz uniqueness therefore proves both identities

`Ra(w - P Rw) = Rw`, and `R(w + P Ra w) = Ra w`.

Consequently `range(R)=range(Ra)`: the full and archimedean generators have exactly the same operator domain. Their actual operator graph relations obey

`R(u+v)=u iff Ra(u+v-Pu)=u`.

The graph change `(u,v) -> (u,v-Pu)` is a bounded invertible triangular map, with inverse adding Pu. Thus arithmetic introduces neither a form-domain boundary nor an operator-domain boundary. This is a dependency-closed consequence of the proved arithmetic admission mechanism; the separate archimedean compact operator-core conjecture remains open. Formalisation now targets this stronger exact operator-domain result as well.

## Archimedean core mechanism: next audit, not yet Lean

The candidate half-density identity has now been checked algebraically. With c(x)=cosh(x/2), a(x)=sqrt(Theta(x)/c(x)), and Uu=sqrt(Theta*c)u, the archimedean generator is `U La U^-1 = a A a + V`, where A is the stationary symmetric jump generator and

`V(x)=c(x)^-1 integral_{t>0} kappa(t)(Theta(x+t)+Theta(x-t)-2Theta(x)) dt`.

Theta's global Lipschitz bound and the first Levy moment bound V. Bounded second derivative and positivity of Theta imply the Glaeser inequality `|Theta'|^2 <= 2 M Theta` by Taylor expansion at displacement `-Theta'/M`; this gives a bounded Lipschitz square root, hence bounded Lipschitz a. This generic square-root step has not yet been found in the corpus or formalised.

For a positive selfadjoint stationary A and bounded selfadjoint a with bounded commutator C=[A,a], a preserves Dom(A). Set J_e=(1+e A)^-1. The exact commutator

`[a A a,J_e] = a (e A J_e) C J_e + J_e C (e J_e A) a`

is uniformly bounded and tends strongly to zero, since e A J_e tends strongly to zero. Applying the adjoint identity to any u in Dom((aAa)*) shows J_e u -> u and aAa J_e u -> (aAa)*u. Thus closure(aAa)=(aAa)* and the sandwich is essentially selfadjoint on Dom(A). A core for A is a core for this sandwich because its graph norm is bounded by the A graph norm. Adding bounded V and the now-bounded prime operator preserves that core.

A Fourier multiplier construction of stationary A is possible, but a purely variational route may fit the corpus better: use the same closed difference graph on unweighted Lebesgue L2; smooth convolutions commute with its generator and map all L2 into its operator domain because the kernel has finite first displacement moment. Then cutoffs have bounded commutators with norm tending to zero as their Lipschitz constants shrink. Smoothing followed by cutoffs should prove compact smooth operator-core density. These admission, commutation and limiting steps still require a closed paper audit and Lean proofs; no core or synthesis result is claimed from this paragraph.

Latest core-mechanism corpus search finished with partial=false, inventory 72734/72734, no inventory errors. Candidates included a square-root Lipschitz theorem for a positive quadratic form (not arbitrary positive smooth functions), algebraic bounded resolvent commutators, and maximal multiplication selfadjointness. No candidate supplies the required CHMD operator core. Existing `HedenmalmClosedWeightedDerivative.thetaWeightedDerivative_hasCore` is an actual PMap core theorem, but for a different weighted derivative. Its graph-closure method and `HTGeometry.MaximalMultiplicationSelfAdjoint` may provide formal infrastructure; neither proves the new jump-core claim.


## Verified arithmetic domain contribution

See `../3-formalized/chmd-prime-operator-domain-2026-10-16.md`. Five new leaves prove every mass-L2 source admits the full prime difference, construct its bounded positive selfadjoint generator, identify full/archimedean form graphs, and prove exact equality of their actual operator domains with a bounded invertible change of generator graph coordinates. All five targeted builds and final plain Lean audits passed; all 76 declarations have only standard axioms. The original compact archimedean operator-core and physical synthesis conjectures remain open. Do not infer them from equality of form domains or from this bounded perturbation theorem.
