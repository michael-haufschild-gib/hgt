# TG — matrix-complete source transgression

- **ID:** TG-matrix-complete-source-transgression-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Read-only current RH frontier, TG; current local Lean corpus.

## Current result

The exact native first-jet classification is paper-proved and Lean-verified in eight modules. On the full prime-depth source, every bounded ordinate family has a bounded, noncompact strong right derivative. Its native quotients have no operator-norm limit. Changing bounded ordinate clocks changes the first jet by a Hilbert–Schmidt operator; relative to the base clock, the native quotient converges in Hilbert–Schmidt norm. The complete synthesis is identified with the convergent series of the original Burnol columns, and all mixed Gram entries are retained.

This is a source regularity classification, not the actual Gaussian/Xi transgression. Gaussian damping changes coefficient amplitudes. The residual filling chain, its identification with the cubic phase defect, and its sign remain unproved. TG receives no qualifying-goal credit; progress remains **2/44 (PM, SZ)**. TG remains open, not retired.

## Goal

Overcome a hard mathematical obstruction in the original Euler/Gaussian source's matrix-complete cubic transgression. No improved estimate, new RH receiver, or source re-encoding counts as a qualifying contribution.

## Plan

1. Inspect source-level cubic transgression, projection-index, and central-gap results; locate the exact missing matrix identity and sign.
2. Form falsifiable conjectures; attack false, circular, already established, and insignificant versions against current Lean sources.
3. Complete the exact paper proof before Lean; formalize any substantive survivor, audit axioms, wire/index, and run final direct Lean checks.

## Constraints

Local Lean corpus only; no web, numerical experiments, novelty audit, old research Markdown, frontier edits, added axioms, or unproved analytic premises. One owned foreground Lean process at a time; no full/umbrella builds or heartbeat hacks. Preserve concurrent work.

## Conjecture ledger

1. **Cubic index admission/anchor invariance — already established.** `FormationAnchoredCubicSpecialization` already supplies trace class, exact two-channel decomposition, contour multiplicity, positive-anchor trace-norm continuity, and all-prime phase factorization. Repackaging these does not advance TG.
2. **Sub-unit cap automatically pays the cubic defect — unsupported.** `BurnolBaseCapPrincipalLift.burnolBaseCap_no_bubbling` assumes the actual residual filling, chain relation, and nonnegative residual area. Boundary phase fixes area only modulo integers. These premises are the missing source handoff.
3. **Undamped Gaussian endpoint from positive-anchor continuity — circular.** `FormationAnchoredCubicEndpoint` requires a zero-abscissa ceiling left of the rectangle; its all-rectangle endpoint is already RH-equivalent.
4. **Native Burnol clock can be differentiated in the source Hilbert field — false candidate.** The depth-zero base norm is `1/(4p(log p)^2)`. Multiplying each column by its native clock `log p` gives norm squared `1/(4p)`, which is nonsummable. A Hilbert–Schmidt first-jet realization cannot exist. This observation does not by itself exclude a bounded first-jet operator.

### Proved: complete native first-jet admission

Let `A` be the literal all-prime-depth Burnol base synthesis and `λ_(p,e)=log(p^(e+1))`. The finite-source operator with columns `λ_(p,e) A e_(p,e)` extends to a bounded operator on the **whole** source Hilbert space, despite failure of Hilbert–Schmidt admission. Its prime-depth-zero Gram is the exact cubic Cauchy kernel, namely a quarter of the corpus prime Poisson kernel times the positive normalized Cauchy correlation `2√(log p log q)/(log p+log q)`. Positive-depth columns have summable squared norms. This should put the complete image of `A` in the native damping generator domain, with strong derivative given by that bounded first jet. The critical operator should be noncompact, so operator-norm differentiability at the undamped endpoint should fail.

**Attack/status:** Paper proof and eight Lean modules close the native source admission and topology classification, including the original counting-source derivative and the full bounded-ordinate synthesis. Existing closed critical Laplace graph uses a different, stronger logarithmic column weight and has no bounded extension. Do not confuse those sources. Significance review awards no TG credit: the actual Gaussian/Xi filling identity and sign remain open.

### Paper proof: bounded, noncompact native first derivative

Write `k=e+1`, `n=p^k`, `λ=k log p`, `f_(p,e)` for the literal base column and `g_(p,e)=λ f_(p,e)`. The already established half-line Gram formula gives

`<g_(p,e),g_(q,d)> = 2 λ μ sqrt(log p / p^k) sqrt(log q / q^l) / (λ+μ)^3`.

All these entries are real and positive. Its diagonal is `1/(4 k p^k)`. On depth zero put `a=log p`, `b=log q`, `r(p,q)=2 sqrt(a b)/(a+b)`. Then

`<g_(p,0),g_(q,0)> = K_Poisson(p,q) r(p,q)/4 = r(p,q)^3/(4 sqrt(p q))`.

AM–GM gives `0<r≤1`. For a finite coefficient family `c`, expand the squared norm, take absolute values termwise, and use the bounded literal matrix operator `poissonPrimeOp` on the vector with coefficients `|c_p|`. This proves

`||Σ c_p g_(p,0)||² ≤ ||poissonPrimeOp|| Σ |c_p|² / 4`.

Finite sequences are dense in `ℓ²`, so finite synthesis has a unique bounded extension `B₀`. This is a conclusion proved from the source Gram, not an assumed Bessel premise. For positive depths,

`1/(4(e+2)p^(e+2)) ≤ (1/(4p²))(1/2)^e`.

Prime reciprocal squares and the geometric series are summable; hence these columns define a Hilbert–Schmidt synthesis `B₊`. Orthogonal source splitting into zero and positive depth gives bounded full synthesis `B(c₀,c₊)=B₀c₀+B₊c₊`. Its columns are exactly `g_(p,e)`, and density gives uniqueness.

For noncompactness use the established Mertens shells `S_j={j≤log log p<j+1}`, masses `m_j=Σ_(p∈S_j)1/p→1`, and normalized orthogonal vectors `u_j=Σ_(p∈S_j)(m_j p)^(-1/2)e_p`. In one shell, `exp(j)≤a,b≤exp(j+1)`, so `r(p,q)≥exp(-1)`. Therefore

`||B₀u_j||² ≥ exp(-3) m_j/4`.

Late shell vectors are orthonormal and the right side stays positive. Every compact operator sends an orthonormal sequence to zero in norm. Thus `B₀`, and consequently `B`, are noncompact. In particular they are not Hilbert–Schmidt; direct diagonal divergence agrees with this stronger obstruction.

Let `A` denote base synthesis, using the canonical identification between `ℓ²` and counting-measure `L²`, and `S_c` the actual weighted Burnol shift. Its established eigenfeature identity gives `S_c A=A D_c`, where `(D_c x)_i=exp(-c λ_i)x_i`. For `c>0` let `M_c` have diagonal `(1-exp(-c λ_i))/(c λ_i)`. These diagonals lie in `[0,1]` and converge pointwise to one. The finite-column identity and bounded extension give exactly

`(S_c A-A)/c = -B M_c`.

Dominated convergence on squared coefficients gives `M_c x→x` for every source vector. Hence the strong right derivative is `-Bx` for every `x`; the complete range of `A` lies in the native generator domain. This argument requires no integral exchange or assumed domain membership. Each difference quotient is compact because the established `A` is Hilbert–Schmidt. Norm differentiability would make `-B` a norm limit of compact operators, contradicting noncompactness. Thus strong right differentiability holds on the whole source while operator-norm right differentiability fails.

**Dependencies and scope.** Only the literal base Gram, bounded prime Poisson operator, Mertens shell mass theorem, prime reciprocal-square summability, native eigenfeature identity, base Hilbert–Schmidt admission, and elementary Hilbert-space completion/compactness are used. All analytic source ingredients already have unconditional Lean proofs. No Xi zero location, residual filling, chain relation, or RH-equivalent premise enters. This does not yet identify the cubic residual filling or prove its sign; significance must be judged against that still-missing TG step.

## No-go closure

TG remains live. Any new mechanism retirement requires its strongest nontrivial positive survivor, with exact paper and Lean status.

## Verification

- Final owned result: eight direct Lean module checks passed; the top-level `BurnolOrdinateNativeGenerator.lean` also passed the final invocation without `-o`.
- All **86** public declarations passed `#print axioms`; the only dependencies are `propext`, `Classical.choice`, and `Quot.sound`. Exhaustive current-corpus declaration-name scan found no collisions. Each new module has exactly one theorem-area umbrella import. Scoped `git diff --check` passed.
- Owned temporary search results, API probes, and audit files were removed. Verified state and next-turn route accounting are persisted in Serena memory `rh/tg-native-firstjet-classification-2026-10-17`.
- Final full repository lint exited **1**, after the earlier five-module lint pass. Its only errors are unrelated modules not yet reachable from their theorem-area umbrellas: `RHTower.ThetaRenewalCausalDecay`, `RHTower.ThetaRenewalCausalKernel`, `RHTower.ThetaRenewalCausalModes`, `RHTower.ThetaRenewalCausalResponse`, `HTGeometry.CausalExponentialIntegrals`, `HTGeometry.HilbertSchmidtProductLimits`, `HTGeometry.PositiveSchurKernel`, `HTGeometry.RegularizedDeterminantMultiplication`, and `HTGeometry.StrictlyCausalFredholm`. These concurrent files were left outside this task's write scope. The eight owned modules had no lint errors.

- `HTGeometry/GramDominatedSynthesis.lean`: direct Lean check passed. Finite complex-phase Gram domination gives coefficient-faithful bounded synthesis.
- `RHTower/BurnolBaseFirstJetAdmission.lean`: direct Lean check passed. Exact prime Gram, all-depth energy, positive-depth summability, full Bessel admission, and original-column identities verified.
- `RHTower/BurnolBaseFirstJetNoncompact.lean`: direct Lean check passed, including the final style-only refresh. Persistent shell energy proves noncompactness of prime synthesis and, via the bounded prime-slice inclusion, full source synthesis.
- `RHTower/BurnolBaseCoefficientCoordinates.lean`: direct Lean check passed. Canonical counting-measure `L²`/`lp` identification and exact original Bochner synthesis transport verified. Explicit Hölder exponents avoid an elaborator timeout; no heartbeat limit raised.
- `RHTower/BurnolBaseNativeGenerator.lean`: full proof drafted; first direct check running. Bounded averages, strong derivative for the actual original source, and operator-norm failure are not yet claimed as verified.
- All 55 public declaration names searched throughout current `HTGeometry` and `RHTower` sources; no duplicate declarations found.
- Native generator verification passed without diagnostics, including the final direct invocation without `-o`. The noncompactness module passed its final style-only refresh. All five modules are wired into their respective umbrellas. Fourteen principal declarations passed `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint exited 0 (`formal lint passed`); repository-wide large-file warnings remain unrelated to these modules.

### Implementation continuation

The derivative proof can use a bounded diagonal average instead of a Bochner integral: `m_c(i)=(1-exp(-cλ_i))/(cλ_i)`, `0≤m_c≤1`, and `m_c→1` coordinatewise. The corpus `LpDiagonal.lpDiag`, `HilbertBasis.dense_span`, and `tendsto_of_dense_of_uniform_bound` provide strong convergence of the averages. Finite-column identities extend by density. Counting-measure `L²` and `lp` must be explicitly identified before claiming the theorem for `routePPrimitiveBurnolBaseSynthesis` itself; mathlib's `LpEquiv` lists this equivalence as a TODO.

The existing `RoutePPrimitiveBurnolApertureDefectFirstFlux` proves summability of `2λ||f||²` and scalar energy differentiation. It does not admit the vector first jet: that requires the distinct `λ²||f||²` energy and its off-diagonal boundedness. No new claim is based on conflating these weights.

### Proved survivor: cancellation of the noncompact jet under an ordinate anchor

**Status:** Corpus search running; no Lean implementation or qualification claimed. This is the next positive survivor suggested by the absolute norm-differentiability obstruction, not a completed TG residual filling.

For the actual clocked column `f_i(κ)=exp(-iκt)f_i(0)`, the native jet is `g_i(κ)=(λ_i+iκ)f_i(κ)`. The literal cubic Cauchy Gram gives `||λ_i(f_i(κ)-f_i(0))||²≤3κ²w_i`, where `w_i=||f_i(0)||²`. One derivation uses `|exp(-iκt)-1|≤|κ|t` and the exact moment `λ_i²||t f_i(0)||²=3w_i`; an alternative uses the real part of the already proved Cauchy cube. Hence `||g_i(κ)-g_i(0)||²≤8κ²w_i`.

For any uniformly bounded real clock family `κ_i`, the original summable base mass therefore makes the difference of native jet columns square summable. It defines a concrete Hilbert–Schmidt synthesis `H_κ`, and the complete clocked native jet is `B_κ=B₀+H_κ`. Thus every bounded clock family has bounded, noncompact native synthesis with the **same class modulo Hilbert–Schmidt operators**. This retains all mixed prime-depth and ordinate entries.

The stronger survivor to audit is relative-source differentiability: `R_κ=A_κ-A₀` should satisfy `(S_hR_κ-R_κ)/h→-H_κ` in Hilbert–Schmidt norm. For an HS operator `H`, strong continuity and contractivity of `S_t` give `||(S_t-1)H||_HS²=Σ_i||(S_t-1)He_i||²→0` by domination with `4||He_i||²`. Integrate `S_tH_κ` over `[0,h]` in the complete HS column space. The finite eigenfeature identity gives `S_hR_κ-R_κ=-∫₀ʰS_tH_κdt`; boundedness and finite-source density extend it to the complete source. Continuity in HS norm makes the normalized integral converge to `H_κ`.

This could provide the relative differentiability needed by a source transgression despite failure of absolute operator-norm differentiability. It still does not identify the Gaussian/Xi cubic residual, its filling chain, or its sign. Check that TG's actual anchor uses this source relation before crediting route progress.

**Source audit and implementation:** The literal Gaussian amplitude is `eulerLogDirichletCoeff n * exp(-pi*x*n^2)` in `GaussianEulerContinuumRelativeFormation.lean`. It changes amplitudes and is not an ordinate modulation. Therefore ordinate cancellation alone cannot be credited as the actual Gaussian/Xi transgression. The independently meaningful positive survivor is the common essential first jet for every bounded ordinate family. `BurnolRelativeOrdinateFirstJet.lean` contains its verified construction. Its proof uses the exact same-prime Cauchy-cube ratio, whose real part is `(1-3*t^2)/(1+t^2)^3`; the resulting square-summable correction retains every mixed source Gram entry. Relative Hilbert–Schmidt differentiability is also verified in the following module.

**Continuation:** `BurnolRelativeOrdinateFirstJet.lean` and `BurnolRelativeOrdinateDifferentiability.lean` passed direct Lean verification and are wired into the umbrella. The bounded synthesis has exactly the native differentiated columns, is noncompact for every bounded ordinate family, and any two such syntheses differ by a Hilbert–Schmidt operator. For relative differentiability, an equivalent mean-value argument avoids integration in an operator space: the literal relative column orbit has derivative `-S_t delta_g_i`; contractivity gives `||q_c(i)|| <= ||delta_g_i||`. The squared slope error is dominated by `4||delta_g_i||^2`, summable by the preceding theorem. Coordinatewise differentiation and Tannery therefore give the exact relative HS derivative. This is the endpoint regularity theorem, not a Gaussian/Xi chain identity.

**Full ordinate-family classification, paper corollary:** Define `A_kappa=A_0+R_kappa`. Applying both synthesis operators to the convergent coordinate expansion gives exactly `A_kappa x = sum_i x_i f_i(kappa_i)`, not a replacement source. Its native quotient is exactly `Q_0(c)+Q_relative(c)`. The first term converges strongly to `-B_0`; the second converges in HS norm, hence operator norm, to `-H_kappa`. Thus the full source has strong derivative `-B_kappa` on every coefficient vector. An operator-norm limit of its quotient would, after subtracting the already convergent relative quotient, give an operator-norm limit of `Q_0`, contradicting the verified base obstruction. This proves the same absolute/relative regularity classification for every bounded ordinate family and completes the original first-jet admission conjecture at finite height.

## Log

- 2026-10-17 — Objective reread. Prior MC turn yielded source evidence rejecting specific shortcuts but no qualifying theorem. TG selected as twenty-first attempted route. Architecture/testing docs absent; Serena memory inventory checked. `update_plan` and `multi_tool_use.parallel` unavailable; this card tracks work and batched reads use `Promise.allSettled`.
