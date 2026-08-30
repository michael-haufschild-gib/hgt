# T2 prime-clock interior Abel singularity no-go (2026-08-30)

Formal module:
- `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldPrimeClockInteriorAbelSingularityNoGo.lean`
- umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`
- pipeline card: `docs/drafts/pipeline/3-formalized/t2-prime-clock-interior-abel-singularity-no-go.md`

Exact route kill:
- `not_T2PrimeClockBohrAllSourceGraphInteriorAbelRegularityPrinciple`
- The literal witness `r_N = exp(-h_N/20)` satisfies primitive vanishing, every polynomial graph law in harmonic/activation-Fisher/essential-edge sources, and height-1/10 Bohr square summability, but its prime-clock Stieltjes--Abel germ has no continuous extension at strict-interior `s=-1/20`.
- Therefore these topology-only source laws cannot produce the strict-interior regularity premise in `riemannHypothesis_iff_woldNatSingularAbelContinuation_strictRight_regular`.

Generic new theorem:
- For every `α>0`, `primeClockExpResidual α` has an absolutely summable Stieltjes germ on `-α<s<0` (`summable_primeClockExpResidualStieltjesAtom`).
- Along `q_M=α/(2+α h_M)`, its positive radial mass tends to infinity, so no continuous extension exists at `s=-α` (`not_exists_continuousAt_primeClockExpResidualStieltjesCurrent`).
- Core lower bound telescopes prime-log gaps exactly: finite radial mass is at least `(α/2) exp(-(1+α)) (h_M-h_0)`.

Positive survivor:
- All finite polynomial graph domains are insufficient.
- Viable T2 producer needs positive exponential radius, source-marked noncompact boundary mass, or a source-specific arithmetic identity.
- Existing `tendsto_primeClockTerminal_of_exponentialGraphEnergy` gives the sufficient exponential graph threshold.

Audit:
- `lake env lean` passed.
- Targeted `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldPrimeClockInteriorAbelSingularityNoGo` passed.
- Axioms only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint failure is only pre-existing unrelated unreachable modules; new module is reachable and has no forbidden declarations.
