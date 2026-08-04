# Route R fixed-ideal Gamma cofinal frontier (2026-08-04)

Created paper and Lean theorem module `RHTower/PrimeFirstTraceGammaCofinalNormalizerFrontier.lean`.

Unconditional results for `|t|<1`:
- raw all-prime Gamma character preserves fixed prime `ell1` ideal iff `t>=0`; reflected character iff `t<=0`; both iff `t=0`;
- every finite-prime Gamma multiplier induces identity on `(P -> C)/ell1`;
- every finite Fisher truncation vanishes in quotient;
- explicit cofinal Bockstein `beta_t=[F_-t]-[F_t]` is nonzero iff `t!=0`, while every finite-prime Bockstein is zero;
- actual retained rational-adelic period-one source class survives at least one physical Gamma orientation at every Xi divisor; off line exactly one orientation erases;
- difference of two actual physical source landings is nonzero leading Xi jet times `beta_(2 Re rho-1)`;
- global Bockstein annihilation, global two-orientation nonerasure, and two-sided fixed-ideal normalization are each equivalent to RH.

Killed mechanism: finite adelic/Fourier/Gamma naturality cannot create physical nonerasure because it is quotient-trivial. Exact remaining producer: an independent singular cofinal all-prime source Stokes/Cartier secondary boundary annihilating explicit `beta`, without assuming `beta=0`, equal trace-class status, or critical-line placement.

Verification: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.PrimeFirstTraceGammaCofinalNormalizerFrontier` passed; axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`; forbidden-declaration rg clean. Umbrella import in `RHTower.lean`.