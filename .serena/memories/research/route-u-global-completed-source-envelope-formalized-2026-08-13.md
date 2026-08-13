# Route U unrestricted completed-source envelope formalized (2026-08-13)

New Lean module: `formal/GaloisForLFunctions/RHTower/PolynomialGaussianGlobalCompletedSourceEnvelope.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

For every real polynomial Q and every t>0, Lean proves literal half-density prime-tail summability and
`tail <= routeUVonMangoldtSquareMass * routeUPolynomialGaussianMass Q t * exp(8*(natDegree Q+t))`.
Key exact coercivity is the completed-square inequality
`-xi^2/(4t)+2*sqrt(d)*xi/sqrt(t) <= 8d+8t-2xi`,
so at xi=log n the aperture cost becomes `exp(8(d+t))*n^-2` without shell counting.

Combining source domination with the exact polynomial-Gaussian explicit formula and radius-zero Gamma envelope yields
`(gammaHardyPhaseRate 0 - C_Lambda*exp(8*(natDegree Q+t))) * M_Q(t) <= pi*trace_Q(t)`.

Public capstones:
- `summable_routeUPolynomialGaussianPrimeGlobalAbsoluteTail`
- `routeUPolynomialGaussianPrimeGlobalAbsoluteTail_le`
- `re_routeUPolynomialGaussianPrimeSource_le_globalAbsoluteTail`
- `pi_mul_xiPolynomialGaussianHeatTraceReal_ge_globalEnvelope`

Verification: direct `lake env lean` passes; named `lake build GaloisForLFunctions.RHTower.PolynomialGaussianGlobalCompletedSourceEnvelope` passes; axiom audit only `propext`, `Classical.choice`, `Quot.sound`; no forbidden declarations. Full lint currently fails only because unrelated concurrent RHTower modules are not umbrella-reachable; this new module is wired and not in failure list.

Research card: `docs/drafts/pipeline/3-formalized/polynomial-gaussian-global-completed-source-envelope.md`. Frontier updated. This closes PDH.7 and all non-scalar parabolic inputs. Exact next open core: scalar filtered-Gamma/incomplete-Gamma domination combining strict ultraviolet wedge positivity with exponentially costly global tail; this is needed for full parabolic degree horizon and is not yet RH.