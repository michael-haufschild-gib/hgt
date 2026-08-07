# Route E moving terminal-kernel resonance (2026-08-07)

New unconditional quantitative class theorem after static regular-kernel closure.

For `Y>1`, `eta>=0`, define terminal log-band by `0 <= log Y - log p <= eta log Y`. For arbitrary complex aperture-dependent kernel `K : Primes×Primes -> C`, entrywise absolutely summable and supported on band squared, Lean proves at explicit physical frequency `tY = pi/log Y`:

`|| Σ'_(p,q) K(p,q) (1+p^(itY)) conj(1+q^(itY)) || <= (pi eta)^2 Σ'_(p,q)||K(p,q)||`.

No positivity, Hermitian, diagonal, or aperture-independence premise. Proof is the exact chord bound `||1+p^(itY)|| <= pi eta` plus complete ordered-pair `tsum` domination. Hence moving support alone cannot evade antiscale coherence. Coercivity requires entrywise mass at least inverse-square in relative log-band width, cross-scale entries, singular/source renormalization, or signed cancellation before norm. Fixed-ratio band `(Y/C,Y]` has `eta=log C/log Y`, giving necessary mass `Omega((log Y)^2)`.

Module: `formal/GaloisForLFunctions/RHTower/RouteEMovingTerminalKernelResonance.lean`, wired into `RHTower.lean`. Targeted build 9721/9721; axioms only `propext`, `Classical.choice`, `Quot.sound`. Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-e-moving-terminal-kernel-resonance.md`. Active Route E and frontier updated. `OPEN-SOURCE-001` remains open.

This follows `mem:route_e/static_regular_kernel_closure_2026_08_07`.