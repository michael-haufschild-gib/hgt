# WL — source-estimate conjecture loop

- **ID:** wl-source-estimate-loop-2026-10-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md`, WL open obstacle.
- **Statement:** Prove, from the actual prime source, `sup_T E(T) < ∞`
  (`E = ccmPrimeDeficitCriticalEnergy`), or a lower bound for
  `ccmPrimeDeficitCoprimeCrossWork`, or the lag/spline sign, or one of the
  weaker sufficient signed-work/rate targets.

## Goal

Discharge the WL receiver unconditionally. Every listed target is at least
zero-free-strip strength: `riemannHypothesis_iff_bddAbove_ccmPrimeDeficitCriticalEnergy`,
`riemannHypothesis_iff_bddBelow_ccmPrimeDeficitCoprimeCrossWork`, and for
`0 ≤ σ < 1/2`, `zetaZeroWidth_le_iff_endpoint_equivalences`. A new receiver,
an improved constant, or a no-go is not completion.

## Gates

- [x] 0 → 1: targets, receivers and unconditional inputs located.
- [ ] 1 → 2: dependency-closed paper proof of a source estimate.
- [ ] 2 → 3: Lean theorem, direct compile, transitive axiom audit.

## Inputs in use

- `exists_abs_ccmPrimeDeficitIncoming_sub_spectralDeficitSum_le`: unconditional
  `incoming(T) = Re Σ_q e^{T(ρ_q−1/2)}/ρ_q² + O((1+T)e^{−T/2})`.
- `abs_ccmPrimeDeficitCriticalEnergy_add_coprimeCrossWork_le`: `|E + cross| ≤ 49/4`.
- VK envelope `exp(T − κT^a)`, `0 < a < 3/5`; Guth–Maynard density `30/13`.

## Selectivity constraints (from the programme READMEs)

A producer must fail for: continuous Beurling systems with regular integers
and an off-line zero (`regular_integers_do_not_constrain_zeros`), the shifted
pair, parity twins, the golden datum, one-node deletion at `log 4`. Hence it
must use discreteness of `ℕ` beyond its counting function, together with the
Euler product. Growth-plus-positivity arguments (de la Vallée Poussin, VK)
give only regions shrinking to `Re s = 1`; large-value and density estimates
carry `T^ε` losses and cannot exclude a single zero.

## What the attempts say about the problem

WL's deficit is the trivial-character (major arc at `0`) count. Nothing
oscillates there, so additive tools (circle method, sum–product, Kloosterman,
decoupling) have no phase to exploit: they give subconvexity and density
estimates, never non-vanishing. Multiplicative identities, Selberg's symmetry
formula and integer counting are Beurling-universal (ledger item 1). The
growth-plus-positivity family (de la Vallée Poussin, VK) yields regions that
shrink to `Re s = 1`. What remains is positivity proved independently of the
zeros, i.e. a Weil-form certificate. The only certificates known come from
archimedean dominance at small aperture, Frobenius/Hodge index over `𝔽_q`, and
self-adjointness for Selberg zeta functions (which read `ζ` only on `Re s=1`,
item 7). A WL producer must be a fourth positivity source.

## Conjecture ledger

1. **Bounded integer counting forces a strip.** Positive prime measure and
   `N(x) = cx + O(1)` imply width `< 1/2`. Refuted (continuous systems):
   `ζ_B(s) = (s/(s−1)) R(s) e^{G(s)}`, `R = (s−ρ₀)(s−ρ̄₀)/(s+1)²`, with
   `G` the transform of a compactly supported positive correction, has
   positive prime density, `N_B(x) = R(1)x + O(1)`, and the zero `ρ₀`.
   Corpus already holds the `O(x^δ)` version. Survivor: any producer must use
   that `ℕ` is discrete; regularity of `N` alone is Beurling-universal.
2. **Mean-energy floor.** `liminf T⁻¹∫₀ᵀE ≥ C₄` unconditionally. Plausible,
   but it is a lower bound; it does not bound adverse correlation. Not pursued.
3. **Hyperbola-block square-root cancellation.** With `B_m(x)` the Möbius sum
   over `(x/(m+1), x/m]`, `Σ_{m≤√x}|B_m|² ≪ x log x`. Fails as a route: the
   block `m=1` alone is `M(x)−M(x/2) = O(√(x log x))`, RH strength. Restricting
   to `m ≥ x^θ` gives short-interval Möbius variance at square-root size, which
   is not known unconditionally (Matomäki–Radziwiłł–Tao give `o(h)` only).
4. **Positivity of Λ orients the lag.** `(d²−1/4)Φ = P − e^{L/2} + a(L)` with
   `P ≥ 0`, so `Φ + Le^{L/2} − v_a` is a subsolution; the maximum principle
   bounds `Φ` by sinh-interpolation plus `(L−α)(β−L)e^{L/2}/2`. Only a mesh with
   gaps `≪ e^{−L/4}` keeps this bounded. Rediscovery of
   `quadraticLagMesh_actual_primes`; the trivial size bound is all positivity gives.
5. **Two-sided squeeze `0 ≤ Λ ≤ log`.** The upper comparison measure has an
   explicit lag (no zeros), but both comparisons lose a full `e^{L/2}` mass.
   Fails: one-sided measure comparisons cannot see square-root cancellation.
6. **Recursive coprime energy.** From `logarithmicCoprimeEnergy_eq_endpoint_add_cross`,
   separating the pairs through `1` gives
   `(g(T)−R(T))² = cross'(T) − Σ_{2≤d≤x} μ(d)R(T−log d)²`, where `cross'` is the
   coprime cross sum over `m,n ≥ 2` of `g(T−log m)g(T−log n)`. So `E` bounded
   iff `cross' ≤ O(x)`: the energy at scale `T` is the coprime cross energy of
   all smaller scales. Inductive square-root bounds give `cross' ≪ x²`; random
   signs give `x log x`. The recursion is critical, and no contraction appears.
7. **Spectral positivity through Eisenstein series.** The coprime Dirichlet
   series `Σ_{(m,n)=1} m^{−u}n^{−v} = ζ(u)ζ(v)/ζ(u+v)` is the coprime structure of
   `cross`, and of `E(z,s)`. Maass–Selberg positivity and the Selberg trace
   formula on `SL₂(ℤ)\H` read `φ(1/2+it) = ξ(1−2it)/ξ(1+2it)`, i.e. `ζ` on
   `Re s = 1` only. Fails: self-adjoint spectral positivity on the modular
   surface does not reach the critical denominator.
8. **Vasyunin reciprocity pays the Möbius–sawtooth Gram.** `D = μ * R` with `R`
   a bounded sawtooth combination; the Báez-Duarte Gram `⟨ρ_j,ρ_k⟩` is explicit
   through Vasyunin cotangent sums, which obey a Euclid-type reciprocity. Hope:
   reciprocity bounds `Σ μ(j)μ(k)w_jw_k V(j/k)/(jk)`. Fails at the first step:
   reciprocity relates `V(h/k)` and `V(k/h)` (a two-term period law), while the
   bilinear form needs square-root cancellation of `μ` against the moving
   modulus `k`; the period law carries no Möbius information.
9. **Zero-density truncation localizes the adverse part.** Unconditionally, with
   the 30/13 density bound, zeros with `|γ| ≥ e^{13T/30}` contribute `O(1)` to
   `incoming(T)`. True but only a localization: the remaining finite zero sum
   still needs a strip. Not formalized (receiver-type reduction).
10. **Sum-of-squares representation of the prime side.** A zero-slack proof
   must exhibit `W(f*f̃) = Σ_j |L_j f|²` with arithmetically defined `L_j`
   (Λ(Ξ) = 0 under RH forbids slack). This is the Hilbert–Pólya problem
   (APT 7.8); no candidate `L_j` from the WL ledger.
11. **A fourth positivity source.** Candidates checked on paper:
   (a) total positivity of the Ξ moment sequence (Edrei: RH iff PF_∞; only PF₂
   is known); (b) heat-flow monotonicity (Λ_dBN = 0 is the boundary itself);
   (c) Jensen plus mollifier on Littlewood's lemma: RH iff
   `∫₀ᵀ log|ζ(σ₀+it)| = O(log T)`, but `∫|ζM|² ≥ T` makes the Jensen loss
   order `T·(mean-square excess)`, so the method stops at density bounds;
   (d) unitary matrix coefficients (Connes cokernel). None is produced from
   the WL ledger. No survivor beyond known theorems.
12. **WL is the Mertens problem.** Euler–Maclaurin on the dilation source gives
   `S(t) = (1+γ)e^t − (½ log 2π) t + c + O(t e^{−t})`, so
   `D = (1+γ) x m(x) − ½ log(2π) ∫₁ˣ M(u) du/u + c M(x) + Σ_{d≤x} μ(d) r(x/d)` with
   `r = O(log y / y)`. The last sum needs `μ` to cancel on `(x/K, x]` at
   square-root precision. Every WL target is therefore an MC target with the
   same principal counterterm; no WL-specific cancellation exists to exploit.
   Rediscovery: `abs_ccmLogChebyshevDeficitPrimitive_sub_moebius_tail_le` already
   isolates `explicitWork + L·M(⌊x⌋)` with error `(T+14)/4`.
13. **Chebyshev weights at square-root precision.** For `F_c(y) = Σ c_k⌊y/k⌋ ≥ 0`
   with `F_c ≥ 1` on `[1,a)` and `Σ c_k/k = 0`, Stirling gives
   `ψ(x) − ψ(x/a) ≤ λ_c x + O(Σ|c_k| log x)`, `λ_c = −Σ c_k log k/k`. The loss
   `(λ_c − 1 + 1/a)x` is the prime mass of `F_c − 1_{[1,a)} ≥ 0`. Exact
   vanishing would need `(a^s−1)/(sζ(s))` to be a Dirichlet polynomial, which it
   is not; the best loss for weights up to `K` is the error of approximating
   `1/ζ` by Dirichlet polynomials of length `K`, i.e. the Nyman–Beurling/mollifier
   problem. Fails: Chebyshev positivity reproduces Möbius cancellation.
14. **Subharmonicity of the Gabor transform.** With a Gaussian window,
   `e^{t²/2} G(T,t)` is entire in `T+it`, and the mean-value theorem gives
   square-root size of `G` on average over `|t| ≤ H` once `H ≥ e^T`. Jensen at
   `T+i0` needs the circle average of `log|G|`; a radius `≍ e^T` reaches scales
   where `|G|` is huge, and a radius `O(1)` needs bounds on `G(T',t)` for
   `|t| ≤ r`, which are governed by zeros near those heights. Fails: the
   problem is only moved to nearby heights.

## Log

- 2026-10-25 — created; frontier, WL cards and 18 programme READMEs read.
- 2026-10-25 — items 1–12 attempted on paper; no source estimate, no new Lean.
