# Actual Müntz infinite zero-side limit

- **Stage:** 3-formalized
- **Routes:** WL/RW; actual factorial source.
- **Parent:** [actual diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [smooth Weil transfer](../3-formalized/factorial-muntz-smooth-weil-transfer-2026-10-18.md).
- **Objective achieved:** Remove the infinite-zero-sum continuity hypothesis for the actual corrected source and its normalized smoothings. Prove absolute convergence, strict positivity of the corrected form, and eventual positive complete smooth Weil energy uniformly over every factorial index.

## Plan

1. Audit the installed critical-strip kernel bounds, reflected-zero identities and summable zero majorant.
2. Prove a uniform normalized-kernel transform bound; combine it with the exact corrected zero readout.
3. Prove absolute convergence and dominated convergence of the entire actual Weil zero sum. Derive the exact reciprocal-zero representation and its sign.
4. Direct leaf and axiom audit, umbrella wiring, index/lint, and parent/memory update.

## Dependency-closed paper proof

Write `G_n` for the canonical corrected source, `c_n=1/(2 sqrt(n+1))`, and `H_(n,k)=kappa_k*G_n` for the already verified normalized smoothings. Each nonnegative `kappa_k` has integral one and support in `[-1,1]`. On `0<=Re s<=1`, `|exp((s-1/2)x)|<=exp(1)` on that support, so `|readout_s(kappa_k)|<=exp(1)` uniformly in `k` and the imaginary part of `s`.

At every nontrivial zero `rho`, the exact transform product yields `readout_rho(H_(n,k))=readout_rho(kappa_k)*c_n/rho`. Thus both factors in the Weil summand have a bound proportional to `c_n/(1+|Im rho|)`, uniformly in the smoothing index. The reflected zero stays in the same open critical strip. The existing unconditional summability of `multiplicity/(1+normSq(gammaOf rho))` gives a summable bound for the entire product. The already proved fixed-readout limits therefore pass through the infinite zero sum by dominated convergence.

For the unsmoothed real source, conjugation turns the second Weil factor into the readout at `1-rho`. Hence the exact summand is `multiplicity*c_n^2/(rho*(1-rho))`. Its real part is nonnegative: `Re(rho*(1-rho))=Re rho*(1-Re rho)+(Im rho)^2>0`, and complex inversion preserves that real-part sign. Absolute convergence permits taking real parts termwise. This is positivity of the corrected source's zero-side form; it does not establish all-source Weil positivity or the original compact ramp's coupled margin.

More explicitly, the installed unconditional separation `|Im rho|>=4` and the strip bound give `1+normSq(gammaOf rho)<=2*norm(rho)*norm(1-rho)`. Thus `2*c_n^2*multiplicity/(1+normSq(gammaOf rho))` bounds the corrected summand's norm. Multiplication by `exp(1)^2` bounds every smoothed summand uniformly. This supplies the previously missing summable domination. Factoring the absolutely convergent sum gives the exact whole-family law `W(G_n,G_n)=c_n^2*sum_rho multiplicity/(rho*(1-rho))`.

For each finite smoothing the full Weil identity is already proved. Consequently the combined physical quantity `archPoleEnergy(H_(n,k))-abelPrimePairing(Lambda,H_(n,k))` converges to `Re W(G_n,G_n)>=0`. This conclusion uses the actual zero-side limit; it does not require or assert separate convergence of the two physical terms.

The sign strengthens to strict positivity. Every summand has positive real part because its multiplicity is positive, `c_n>0`, and `Re(rho*(1-rho))>0`. The installed unconditional theorem `RHTower.exists_riemannZeta_zero_mem_openStrip` supplies an actual summand. The absolutely convergent sum therefore has positive real part. Convergence implies that the complete physical difference is positive for every sufficiently narrow smoothing at each fixed `n`. The required smoothing threshold is produced by convergence; no threshold or positivity premise is supplied by the caller.

The exact factorization further removes dependence of that threshold on `n`. For each fixed `k`, the smoothed zero form is `c_n^2*S_k`, where `S_k` is the same kernel-weighted reciprocal-zero sum for every factorial index. Therefore `c_m^2*W(H_(n,k))=c_n^2*W(H_(m,k))`. Set `m=0`. The eventual strict positivity already obtained for `H_(0,k)` transfers, through the positive squared coefficients, simultaneously to every `n`. Thus one eventual range of smoothing indices yields positive complete Weil energy for the entire actual corrected factorial family. This does not prove positivity of the original compact ramp/tent span or density of this corrected family in the full Weil cone.

## Scope and verification

These results do not prove separate archimedean and Abel-prime limits, quantitative transfer back to the original compact factorial ramp, the coupled diagonal margin or RH. Every factorial index has the same zero-readout profile up to the scalar `c_n`; positivity of this family does not establish positivity of the original ramp/tent span or all-source RW. No numerical experiment, web search, novelty audit, heartbeat increase or full build. Corpus search `/tmp/bsu-muntz-zero-limit-search.json` finished with partial=false and no execution errors; semantic coverage is unmeasured, background refresh incomplete, and compiler freshness mixed. All 20 candidate and 20 source-argument summaries were inspected. The existing compact-source `Wsummand_mollify` does not apply to the noncompact corrected source. The installed `ArchimedeanGenusZeroSum` identifies a corresponding multiplicity-copy reciprocal sum with `2+gamma-log(4*pi)`, but that indexing bridge is not assumed here.

Implementation is in `FactorialMuntzZeroReadout.lean` and `FactorialMuntzZeroSideLimit.lean`, with 22 public theorems and two definitions. Both direct leaf checks, both API probes and the final 24-declaration axiom audit passed with empty logs. All audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Both new leaves are wired exactly once into the area umbrella. Current source hashes and object freshness match `/tmp/bsu-muntz-zero-verification.json`; predecessor hashes match the prior verified smoothing package.

The strongest endpoint is `factorialMuntzSmoothed_weil_difference_eventually_pos_uniform`: for all sufficiently large `k`, simultaneously for every `n`, the actual `archPoleEnergy(H_(n,k))-abelPrimePairing(Lambda,H_(n,k))` is positive. The infinite-sum step is `factorialMuntzSmoothed_W_tendsto`; `factorialMuntzBoundaryCorrected_W_eq_scaled` and `factorialMuntzSmoothed_W_cross_scale` record the exact scaling laws. No domain, convergence, positivity or RH premise remains at these actual-source endpoints.

All Lean checks used `lake --old env lean -j 1`, one owned process at a time. The final audit script is `/tmp/bsu-muntz-zero-axioms.lean`, with output `/tmp/bsu-muntz-zero-axioms.log`. No temporary import-cache snapshot was created; no owned Lean process remains live. All ten links across this card and the parent resolve.

Final `scripts/formal_tools.py index` passed. Final `scripts/formal_tools.py lint --check-generated` exited 1 with six unrelated missing umbrella imports: `RHTower.PrimeArchQuadraticSaddleBands`, `BiScaleUncertainty.CompensatedHausdorffPhase`, `BiScaleUncertainty.CubicSievePhaseRecovery`, `BiScaleUncertainty.HausdorffSaddleScale`, `BiScaleUncertainty.ParityLiftedSieveMoments`, and `BiScaleUncertainty.SieveTripleFourier`. Generated catalogs are current in that check; 381 size warnings remain. Logs are `/tmp/bsu-muntz-zero-index-final.log` and `/tmp/bsu-muntz-zero-lint-final.log`. No failure names either new leaf.
