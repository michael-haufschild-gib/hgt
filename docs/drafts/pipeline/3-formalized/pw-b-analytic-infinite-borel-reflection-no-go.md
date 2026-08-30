# PW-B analytic infinite Borel reflection no-go

- **ID:** pw-b-analytic-infinite-borel-reflection-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · PW-B surviving infinite-range producer
- **Statement:** No source-independent countable PW grade resummation with a Borel generating kernel analytic at zero can map the first-winding forward Mellin response `Gamma(s)` to its functional-equation partner `Gamma(1-s)` on the critical line.

## Goal

Kill the regular infinite-range survivor of the chain

`PW Borel tower -> source-independent countable grade resummation -> Gamma(1-s) partner -> partner balance on Xi support -> Deninger Ward cancellation -> RH`.

The sharp survivor must be beyond all perturbative PW grades, use a reflected nonlocal channel, or depend on the spectral parameter/source. No Xi divisor or RH premise enters the obstruction.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement, exact chain, attack, hostile alternatives
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean theorem, targeted `lake build`, axiom audit
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, Lean certificate, novelty audit

## Frozen conjecture

Let `A` be the analytic generating kernel of a source-independent countable PW grade row. Its critical-line logarithmic source profile is

`u |-> exp(u/2-exp(u)) A(exp(2u))`.

If this profile has the same Fourier transform as the reflected Gamma profile

`u |-> exp(-u/2-exp(-u))`,

then Fourier uniqueness forces

`A(x^2) = x^(-1) exp(x-1/x)` for every `x>0`.

The right side is nonzero but flat beyond every power at `x=0`; analytic quasianalyticity makes an analytic germ matching it locally zero, contradiction.

## Approach

1. Use corpus `HTGeometry.ae_eq_of_fourierIntegral_eq` plus continuity to classify the kernel pointwise.
2. Package the forced identity as `x exp(-x) A(x^2)=exp(-1/x)`.
3. Prove the right side is all-orders flat along an exponential scale.
4. Apply corpus `reesAllOrdersFlat_analyticNormAlongScale_iff`; analytic flatness forces local zero, contradicting positivity of `exp(-1/x)`.
5. Formalize both exact classification and route-level nonexistence.

## Proof `[PROVED HERE]`

Put

`g_A(u)=exp(u/2-exp(u)) A(exp(2u))`,

`g_R(u)=exp(-u/2-exp(-u))`.

Both profiles are continuous and integrable by producer admissibility. Equality of their Fourier transforms at every real frequency and `L1` Fourier uniqueness give `g_A=g_R` almost everywhere. Continuity and full support of Lebesgue measure upgrade this to pointwise equality. For `x>0`, substitute `u=log x` and cancel the nonzero exponential factor:

`A(x^2)=x^(-1) exp(x-1/x)`,

equivalently

`x exp(-x) A(x^2)=exp(-1/x)`.                                           (1)

Define the complex germ `F(z)=z exp(-z) A(z^2)`. It is analytic at zero. Sampling (1) at `x=1/h`, `h>0`, yields

`F(1/h)=exp(-h)`.                                                        (2)

The right side is little-oh of `h^(-N)` for every natural `N`; hence `norm(F(1/h))` is all-orders flat along the positive contracting scale `h |-> 1/h`. Analytic Rees quasianalyticity forces `analyticOrderAt F 0 = top`, so `F` vanishes in a neighborhood of zero. Therefore `F(1/h)=0` for all sufficiently large `h`, contradicting (2) and positivity of `exp(-h)`. No analytic producer exists.

The pointwise classification before the contradiction is the strongest positive survivor: exact reflection uniquely forces a nonzero all-orders-flat sector, invisible to every perturbative PW grade.

## Hostile audit

- The stronger conjecture “every infinite row fails” is false as a route statement: divergent/transseries resummations and reflected nonlocal transforms remain possible.
- Burnol's Hankel transform realizes the Gamma reflection ratio through a reflected input channel; it is outside the killed source-independent pointwise grade row and identifies a genuine survivor.
- Classical Mellin inversion gives the reciprocal exponential kernel, but corpus and searched literature contained no PW first-winding analytic-grade classification or route kill.

## No-go closure

- **Exact killing theorem/mechanism:** Mellin/Fourier uniqueness forces a nonzero all-orders-flat multiplier; analytic quasianalyticity forbids it.
- **Strongest positive survivor:** exact forced kernel `x^(-1) exp(-1/x)` and all-orders-flat multiplier `x^(-1) exp(x-1/x)`.
- **New insight:** functional-equation reversal is invisible to the complete perturbative PW grade tower; a surviving producer must introduce a nonperturbative reciprocal-energy sector or a reflected/channel-coupled operation.
- **Status:** Lean-closed in `ThetaCuspHawkingParikhWilczekAnalyticInfiniteBorelReflectionNoGo.lean`; final theorem `not_schwarzschildParikhWilczekAnalyticInfiniteBorelReflectionProducer`.

## Literature audit (2026-08-30)

- NIST DLMF 1.14: Mellin definition, strip analyticity, inversion.
- Burnol, *Scattering, determinants, hyperfunctions in relation to Gamma(1-s)/Gamma(s)*, arXiv:math/0602425: nonlocal Hankel/reflected-channel realization.
- Karp--Prilepkina, *An inverse factorial series for a general gamma ratio*, arXiv:1707.01734: inverse-factorial Gamma-ratio expansions, not the PW positive-shift row classification.

## Log

- 2026-08-30 — created in 1-in-progress after corpus and literature hostile audit; conjecture frozen.
- 2026-08-30 — `[PROVED HERE]`; promoted to 2-fully-proven.
- 2026-08-30 — formalized exact Gamma target, pointwise forced-kernel classification, all-orders-flat survivor, and closed route no-go; direct Lean check and targeted module build passed; axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Global lint remains red only on unrelated pre-existing umbrella reachability findings.
