# PW singular flat reflection carrier (2026-08-30)

Significant PW-B premise discharged and formalized.

- Card: `docs/drafts/pipeline/3-formalized/pw-singular-flat-reflection-carrier.md`
- Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekSingularFlatReflectionCarrier.lean`
- Unconditional theorem: `RHTower.schwarzschildParikhWilczek_singularFlatReflectionCarrier`
- Exact source identity: at `epsilon=x/4`, literal first PW endpoint winding is `exp(-1/x)` and constructs forced multiplier `A(x^2)=x^-1 exp(x-1/x)`.
- The multiplier is globally continuous, positive on `(0,infinity)`, and `A(y)/y^N -> 0` from the right for every `N`.
- Its log profile equals reflected Gamma profile pointwise and Fourier transform is exact `Gamma(1/2+2*pi*xi*i)`.
- Fourier uniqueness classifies every continuous-profile L1 reflection carrier: same multiplier on full positive ray.
- No globally continuous complex extension analytic at zero can realize carrier, by prior analytic infinite-row no-go.
- Direct Lean and targeted build passed; axiom audit only `propext`, `Classical.choice`, `Quot.sound`; wired into RHTower umbrella.
- Global lint nonzero only from unrelated shared-worktree unwired modules.
- Remaining PW-B core: derive forward/reflected partner balance from genuine source dynamics before Xi specialization. Carrier existence is no longer open.