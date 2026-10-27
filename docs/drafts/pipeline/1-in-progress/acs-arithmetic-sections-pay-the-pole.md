# Arithmetic sections pay the pole

- **ID:** acs-arithmetic-sections-pay-the-pole
- **Stage:** 1-in-progress
- **Type:** CANDIDATE — Lean formalization in progress
- **Source:** ACS; `acs-arithmetic-section-space`
- **Statement:** At a fixed positive fraction of integer-log spacing, the full Weil form dominates square mass on every independent arithmetic section, without a pole-moment constraint.

## Goal

Remove the sinh-neutral restriction from the existing arithmetic section-space theorem. This proves Riemann–Roch, ampleness, and Hodge index on the entire source-defined arithmetic section space. It does not claim a cofinal exhaustion of all compactly supported tests: gaps between short arithmetic cells remain.

## Gates

- [x] 0 → 1: source-defined section space; no spectral premise.
- [x] Paper argument audited; not counted as proved until Lean verifies it.
- [ ] 2 → 3: exact Lean theorem, leaf check, transitive axiom audit.

## Paper argument

Let `N ≥ 1`, `δ_N = log(1+1/N)`, and let each real `C²` profile `g_n` be supported in `[0,w]`. Put

`f(u) = Σ_{1≤n≤N} g_n(u-log n)`, `E_n = ∫g_n²`,
`L = 1+log N`, `d_n = 1+(n/N)L`, and `D = Σ d_n E_n`.

Choose

`c = min(arithmeticSectionRatio, spacingRatio/2, 1/(8(exp 1+1)))`

and assume `0 < w ≤ c δ_N`. All constants are explicit and positive. Since `δ_N ≤ 1/N`, we have `wN ≤ c`, and since `spacingRatio < 1/2`, also `w < 1`.

### Retaining the tilted row reserve

The existing independent-profile prime and Lévy estimates give

`M(f) ≥ Σ E_n [2γ + log(1/w) - log N - 2(log 4+4) + (n/(4N))log n - 8exp(5/2)wn(1+log(N+1))]`.

Apply `crossRow_le_saving` to `2w`: the last loss is at most `(n/(8N))log n + 3/8`. With `a = 2γ + log(1/w)-log N-spacingConstant`, the remaining coefficient is at least `a+5/8+(n/(8N))log n`. The existing `arithmeticSectionGain_ge_one` gives `a ≥ 1`.

For `q=n/N`, the elementary inequality `log(N/n) ≤ N/n-1` gives `qL ≤ q log n+1`, so `d_n ≤ 2+q log n`. Therefore the coefficient is at least `1+d_n/8`. Disjoint cells give `∫f²=ΣE_n`. Consequently

`M(f) ≥ ∫f² + D/8`.

### Complementary pole estimates

Write `A=∫f(u)exp(u/2)du`, `B=∫f(u)exp(-u/2)du`. Translating each cell gives

`A=Σ sqrt(n) ∫g_n(v)exp(v/2)dv`,
`B=Σ (1/sqrt(n)) ∫g_n(v)exp(-v/2)dv`.

Cauchy–Schwarz on `[0,w]` gives squared local moments at most `w exp(w)E_n` and `wE_n`, respectively. Weighted finite Cauchy–Schwarz then gives

`A² ≤ w exp(w) (Σ n/d_n)D`,
`B² ≤ w (Σ 1/(n d_n))D`.

Since `d_n ≥ (n/N)L` and `d_n ≥ 1`,

`Σ n/d_n ≤ N²/L`, `Σ 1/(n d_n) ≤ Σ 1/n ≤ 1+log N=L`.

The square `(sqrt(L/N)A+sqrt(N/L)B)² ≥ 0`, equivalently weighted Young's inequality, yields

`2AB ≥ -(L/N)A²-(N/L)B² ≥ -wN(exp(w)+1)D ≥ -D/8`.

The last step uses `exp(w) ≤ exp 1` and `wN ≤ 1/(8(exp 1+1))`.

### Full Weil form and the ACS surface

The exact pole decomposition is `W(f,f)=M(f)+2AB`. Hence `W(f,f) ≥ ∫f²` for every arithmetic section, with no condition on either pole moment or the signs of profiles. Apply the established `l2SourceCone_riemannRoch_iff_weilPair_ge` and `l2SourceCone_ample` to `arithmeticSectionTests N w`; the resulting original scaling subsurface satisfies Hodge index.

## Dependency and scope audit

- Arithmetic inputs: the existing tilted prime-row estimate and independent-profile archimedean cross-kernel estimate.
- Remaining elementary inputs: integral and finite weighted Cauchy–Schwarz, harmonic-sum bound, `log x ≤ x-1`, and exact pole decomposition.
- No zero-location, Weil-sign, or unproved section-growth premise.
- New content: the non-neutral pole directions are included in the same source-defined linear space.
- Full ACS remains open: sparse support does not give arbitrary compactly supported tests or unrestricted section growth.

## Lean verification

Implementation: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticSectionsPayThePole.lean`.

Main declarations:

- `markovEnergy_arithmeticSection_ge_reserve`
- `neg_sectionReserve_le_poleProduct`
- `integral_sq_le_weilPair_arithmeticSection`
- `arithmeticSections_effectivity`

Kernel verification is pending. The initial leaf check found elaboration and rewrite errors;
these have been corrected and the revised leaf is being checked. This card stays in stage 1
until the exact file passes and all four declarations have clean transitive axiom audits.

## Log

- 2026-10-27 — Candidate isolated; complete algebraic argument written for audit and formalization.
