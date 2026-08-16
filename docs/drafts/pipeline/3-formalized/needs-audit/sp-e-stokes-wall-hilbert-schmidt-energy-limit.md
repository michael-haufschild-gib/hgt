# SP-E Stokes-wall Hilbert--Schmidt energy limit

- **ID:** SP-E-WALL-HS-LIMIT
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM
- **Source:** corpus-first move beyond P-G105Q/P-G105R
- **Statement:** Literal P-G105K cofinal child Hilbert--Schmidt energy converges to `256/35` as physical aperture `d → 0+`.

## Goal

Replace previous nonzero energy floor by exact source-faithful wall invariant. This isolates complete quadratic mass retained by SP-E child and gives exact limiting balanced determinant square jet. It does not identify wall determinant divisor with Xi.

## Gates

- [x] 0 → 1 in-progress: corpus frontier audited before conjecturing
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: closed Lean theorems, target module build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem/proof/certificate

## Corpus audit

Queries run before conjecturing:

- `Euler prime current cubic coherence pair expectation`
- `bounded continuous except singleton weak probability integral convergence`
- `quantile product expectation probability measure`
- `normalized higher valuation von Mangoldt mass tends zero sigma one`
- `SP-E cubic coherence expectation exponential Beta 4 4 16 35`
- `a cubed b cubed divided by a plus b sixth exponential`
- `Hilbert Schmidt energy limit 256 35 Stokes wall`
- `valuation one prime current probability weak convergence`
- `bounded kernel weak convergence discontinuity null set product law`
- `ratio of two independent exponential variables uniform A divided by A plus B`
- `Gamma beta independence exponential sum ratio`
- `wallHilbertSchmidtEnergy weightedPointLaw product integral routePBaseCauchy kernel exact identity`
- `prime child Hilbert Schmidt energy normalized weighted point law double sum cubic coherence`
- `integral weightedPointLaw product measure tsum pair kernel`

Corpus already contains full von-Mangoldt exponential clock, Laplace continuity, quantile coupling, exact P-G105K Schur law, `W(d) → 4`, and P-G105Q positive floor. It contains no valuation-one SP-E product-coherence limit, no `16/35` value theorem, no energy/expectation factorization, and no `256/35` energy limit.

## Literature audit

Exact-phrase and structural arXiv searches for signed-permutation Eulerian RH, prime-log Cauchy Hilbert--Schmidt kernels, exponential prime clocks, and constants `16/35`/`256/35` found generic Fredholm/Cauchy-kernel and signed-Eulerian literature but no matching arithmetic aperture-wall theorem. Elementary Beta evaluation is not claimed novel in isolation. Novel object is exact identification of literal SP-E cofinal child energy with this exponential coherence law.

## Conjecturing loop

### C5 — reuse full von-Mangoldt exponential clock directly

**Failed.** SP-E weight is valuation-one ordinary-prime current

```text
w_d(p) = 8 d log(p) p^(-1-2d),
a_d(p) = 2d log(p),
```

not full prime-power von-Mangoldt law. Existing clock theorem cannot identify literal P-G105K energy.

### C6 — moment convergence implies cubic-coherence convergence directly

**Failed as stated.** Kernel

```text
g(a,b) = 64 a^3 b^3/(a+b)^6
```

is undefined by continuity argument at `(0,0)`. Compactified weak convergence alone does not justify integrating `g`.

### C7 — quantile coupling removes singular corner

**Succeeded.** Exact prime-weight dilation gives every Laplace moment of normalized valuation-one wall law. Corpus Laplace continuity yields CDF convergence to `Exp(1)`; quantiles converge pointwise on `(0,1)`. Pulling product laws to unit square moves only singularity to null boundary corner. Since `0 ≤ g ≤ 1`, dominated convergence gives

```text
∫ g d(μ_d ⊗ μ_d) → ∫ g d(Exp(1) ⊗ Exp(1)).
```

### C8 — exact exponential value and literal energy factorization

**Succeeded.** Substitute `b = at` on positive quadrant. Radial integral is

```text
∫₀∞ a exp(-(1+t)a) da = (1+t)^(-2),
```

and remaining beta-prime integral is

```text
64 ∫₀∞ t^3/(1+t)^8 dt
  = 64 B(4,4)
  = 16/35.
```

For every `d>0`, exact P-G105K Schur law and weighted-point-law expansion give

```text
E(d) = W(d)^2 ∫ g d(μ_d ⊗ μ_d).
```

Therefore `W(d) → 4` gives

```text
E(d) → 4^2 · 16/35 = 256/35.
```

## Formal theorem

Modules:

- `GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallCubicCoherenceWeakLimit`
- `GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallExponentialCubicCoherenceValue`
- `GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyLimit`

Main declarations:

- `tendsto_wallCompactLaw_nhdsGT_zero`
- `tendsto_wallHalfLineCDF_nhdsGT_zero`
- `tendsto_integral_wallCubicCoherence_prod_nhdsGT_zero`
- `integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq`
- `integral_wallCubicCoherence_prod_raw_eq_tsum`
- `wallHilbertSchmidtEnergy_eq_current_sq_mul_expectation`
- `tendsto_wallCubicCoherenceExpectation_nhdsGT_zero`
- `tendsto_wallHilbertSchmidtEnergy_nhdsGT_zero`

Target-only `lake build GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyLimit` passed. Axiom audit reports only Lean standard dependencies `propext`, `Classical.choice`, and `Quot.sound`. Modules are wired into `GaloisForLFunctions.RHTower`; umbrella was not built. Global lint is blocked only by two unrelated untracked modules already present and unreachable from their own umbrellas.

## Strongest new insight

Previous wall obstruction was interpreted as coordinatewise mass escape. Exact law shows escape is not arbitrary: after source normalization it has universal independent exponential projective shape. P-G105K cubic incidence converts that diffuse law into rigid energy `256/35`. Thus correct wall object is not fixed-coordinate operator limit but projective probability law plus its coherence moments. Determinant aperture convergence should be attacked through convergence of the complete trace-power law, not entrywise kernel convergence.

## Next falsifiable conjecture

For each fixed `m ≥ 2`, normalized cyclic trace `Tr(K_d^m)` has finite aperture-wall limit determined by an `m`-fold independent exponential projective integral. If limits satisfy a locally summable Fredholm-log majorant uniformly on compact spectral-parameter sets, balanced determinants converge locally uniformly at wall with nonzero quadratic jet `-16384/35`.

This conjecture must receive a fresh corpus search before attack.

## Log

- 2026-08-16 — corpus frontier audited before conjecturing; full von-Mangoldt shortcut rejected.
- 2026-08-16 — quantile/DCT transfer, exact `16/35` Beta value, literal energy factorization, and `256/35` limit proved in Lean.
- 2026-08-16 — target module build and axiom audit passed; umbrella wired; route map left unchanged.
