# RBH source-faithful Markov normalization no-go (2026-08-30)

Formal route-class kill completed.

- Module: `GaloisForLFunctions.RHTower.ReflectedBiHeatSourceFaithfulMarkovNormalizationNoGo`
- Capstone: `RHTower.reflectedBiHeat_sourceFaithfulMarkovNormalization_noGo`
- Card: `docs/drafts/pipeline/3-formalized/rbh-source-faithful-markov-normalization-no-go.md`
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Direct Lean and targeted module build pass.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint remains red only from unrelated pre-existing umbrella reachability debt; new module is reachable.

Mathematics:
1. Every injective reflection-equivariant normalization reflects fixed points, with no linearity, continuity, metric, or finite-dimensional assumptions. Off-wall fixed output forces a source-orbit collision and noninjectivity.
2. Every real two-channel generator commuting with swap, conserving total mass, and having nonnegative off-diagonal rates is uniquely `L_r(u,v)=(r(v-u),r(u-v))`, `r>=0`.
3. Its exact Markov flow is positive for nonnegative rate/time, satisfies semigroup and ODE laws, and multiplies difference by `exp(-2rt)`.
4. Finite-time flow is injective and balanced iff input is balanced. Applied to actual multiplicity-leading RBH norms: balance iff `Re rho=1/2`, globally iff RH.
5. At positive rate, difference tends to zero for every input at infinite time, so equilibrium balance is universal information loss and cannot select Xi support.

Exact route consequence: kills normalization-only and reflection-symmetric Markov heat equilibration as RBH balance producers. Any survivor needs an additional source-first law directly forcing raw shared Ward charge zero. Parent two-state CTMC algebra is classical; novelty claim is restricted to exact actual-RBH synthesis and route closure.

Frontier map was treated read-only and not edited by this work.