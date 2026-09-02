# The Petersson formula for `SL(2,ℤ)` in Lean

- **ID:** `PETERSSON-L1-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (unconditional, classical), extracted from `5-failed/ulf-share-ledger-ceiling-kuznetsov-producer.md`
- **Source:** brick 6 of `ULF-SLC-001`; the producer card was retired as an RH route, this theorem survives it.
- **RH used:** no. **Computation used:** no. **Axioms:** `propext`, `Classical.choice`, `Quot.sound`.

## Statement

For `k = k'+1 ≥ 3`, `m, n ≥ 1`, and any orthonormal basis `(b_i)` of the level-one cusp forms of weight
`k` for the Petersson inner product `⟨f, g⟩ = ∫_𝒟 conj(f) g y^k dμ`,

```text
2 (4πm)^{1−k} Γ(k−1) Σ_i conj(a_{b_i}(m)) a_{b_i}(n)
  = (1 + (−1)^k) [ δ_{nm} + 2π (−i)^k (n/m)^{(k−1)/2} Σ_{c ≥ 1} S(m,n;c)/c · J_{k−1}(4π√(mn)/c) ].
```

Lean: `GaloisForLFunctions.HTGeometry.petersson_formula_levelOne`
(`formal/GaloisForLFunctions/HTGeometry/PoincareSeriesBesselCoefficient.lean`). The `(1+(−1)^k)`
and the factor `2` come from the Poincaré series being summed over all coprime rows `±(c,d)`;
`J_ν` is defined by its power series, `S(m,n;c)` is the corpus's `RHTower.Sieve.kloostermanSum`.

## Modules (all in `formal/GaloisForLFunctions/HTGeometry/`, wired into the umbrella)

| Module | Content |
|---|---|
| `HolomorphicPoincareSeries` | `poincareSeries k m` over `gammaSet 1 1 0`, transformation law, locally uniform convergence |
| `HolomorphicPoincareSeriesModularForm` | holomorphy, boundedness at the cusp, `poincareSeriesMF : ModularForm 𝒮ℒ k` |
| `HolomorphicPoincareSeriesCuspForm` | `‖P_m(z)‖ ≤ 2e^{−2πmy} + C y^{−1/2}`, `poincareSeriesCF : CuspForm 𝒮ℒ k` (`m ≥ 1`) |
| `ModularFundamentalDomainMeasure` | `PSL2Z`, `isFundamentalDomain_fd` for `dx dy/y²` (boundary null) |
| `ModularStripUnfolding` | coset-representative fundamental domains, the strip, `Σ_{(c,d)} ∫_𝒟 φ∘M_{c,d} = 2∫_{strip} φ` |
| `UpperHalfPlaneStripIntegral` | `volume = comap coe withDensity y⁻²`, chart, Fubini on the strip |
| `ModularFundamentalDomainVolume` | `volume 𝒟 < ∞`, `IsOpenPosMeasure (volume : Measure ℍ)` |
| `PoincareSeriesPeterssonIntegrand` / `…Unfolding` / `…Coefficient` | `⟨f, P_m⟩ = 2(4πm)^{1−k}Γ(k−1) conj(a_f(m))` |
| `PeterssonInnerProductLevelOne` | `PeterssonSpace k` as a finite-dimensional `InnerProductSpace ℂ` |
| `PeterssonFormulaLevelOne` | coefficient functional, `a_{P_m}(n) = c_{k,m} Σ_i conj(a_{b_i}(m)) a_{b_i}(n)` |
| `GammaSetPositiveRowEquiv`, `PoincareSeriesCosetDecomposition`, `PoincareSeriesExponentialExpansion`, `PoincareSeriesKloostermanPhase`, `PoincareSeriesCoefficientMajorant`, `PoincareSeriesFourierExpansion` | `a_{P_m}(n)` through Kloosterman sums (Lipschitz-sum route) |
| `PoincareSeriesBesselCoefficient` | Bessel form and `petersson_formula_levelOne` |

## Gates
- [x] 0 → 1 — [x] 1 → 2 — [x] 2 → 3 (`lake build` green per module, axioms clean)
- [ ] 3 → 4 publication-ready

## Log
- 2026-09-02 — built as brick 6 of `ULF-SLC-001`; extracted here when that card was retired.
