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

Item 19 sharpens the selectivity requirement: integer counts more regular than
`⌊x⌋` coexist with off-line zeros. What `ℕ` has and those systems lack is the
exact periodic sawtooth `{x}`, i.e. Poisson summation and the functional
equation. The input must therefore be the Gamma/polar side of WL's explicit
formula coupled to the primes, not regularity of the integers.

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
15. **Successor rigidity of multiplicative functions.** Kátai/Wirsing-type
   rigidity (successor-regular multiplicative ⇒ `n^{it}`) and Halász bounds see
   `μ` only through `D(μ, n^{it}; x)`, i.e. `ζ` on `Re s = 1`; the best output is
   `M(x) ≪ x/(log x)^{1−ε}`. Fails: pretentious rigidity is one-line information.
16. **Integrality of dual lattices.** `lcm(1..2N−1)·H_N` is integral for the
   Hilbert matrix, so `lcm^N ≥ 1/det H_N`; weighted Gram matrices improve this
   only to the integer Chebyshev constant (`ψ(x) ≥ 0.86x` at best). Fails:
   integrality reaches the density scale, never the square-root scale.

17. **Maass–Selberg positivity off the line.** `‖Λ^T E(·,s)‖² ≥ 0` continues to
   `1/4 < Re s < 1/2`; with `2σ−1 < 0` it yields `|φ(s)|² ≥ T^{4σ−2} − O(T^{2σ−1}/|t|)`,
   i.e. `|ξ(2s)| ≲ |ξ(2−2s)|`: an upper bound for `ξ` in the strip. Upper bounds
   cannot exclude zeros, and near `s₀ = ρ/2` the norm blows up consistently.
18. **Harmonic sign of `Re ξ'/ξ`.** RH iff `u = Re ξ'/ξ > 0` on `Re s > 1/2`;
   `u = 0` on the line and `u → +∞` to the right, so with no zeros the minimum
   principle gives `u ≥ 0`. A quadruple makes `u < 0` on `(1/2, β₀) + iγ₀`, which
   no boundary datum forbids. Fails: the boundary values do not see interior
   dipoles.
19. **Over-regular continuous systems.** Sharpening item 1: the density
   `(e^t − 2e^{βt}cos γt − K e^{−t} + (K+1) e^{−εt})/t` is nonnegative for fixed
   large `K` and small `ε` (majorant derivative test), with zeta
   `((s−β)²+γ²)(s+1)^K / ((s−1)(s+ε)^{K+1})`, which tends to `1` at infinity.
   Perron's residues at `1` and `0` give `N(x) = cx + ζ_B(0) + O(x^{−ε} log^K x)`
   (paper; smoothing not written out): more regular than `⌊x⌋`, yet with the
   off-line zero. Not formalized (a
   no-go strengthening of `regular_integers_do_not_constrain_zeros`).

20. **Krein accelerant comparison.** `Φ = W * e^{−|x|/2}` and
   `−Φ'' = e^{t/2} − Φ/4 − a(t) − Σ Λ(n) n^{−1/2} δ_{log n}`: the prime atoms enter
   the accelerant with a fixed sign, so Sturm-type comparison with the
   prime-free accelerant was tested. Fails: the prime-free form `W₀ = arch +
   poles` is itself indefinite (its symbol `Re ψ(1/4+it/2) − log π` is negative
   at low frequency), so comparison moves in the wrong direction and positivity
   of `Φ|[−A,A]` remains a finite-prime check at every `A`.
21. **Herglotz representation.** The lag sign is the statement that the boundary
   measure of `Re ξ'/ξ` on the line, `πΣδ_γ`, is positive, i.e. that `ξ'/ξ` is
   Herglotz on `Re s > 1/2`. Herglotz/Nevanlinna representation theorems
   presuppose that sign. Rediscovery of the corpus Herglotz bridges; no producer.

22. **Twist average plus continuity in the twist.** Twisted energies `E_t(T)`
   (source `Λ(n)n^{−it}`) are bounded on average over `t ∈ [H,2H]` for
   `x ≤ H^{c}` by density estimates, and `∂_t E_t = O(T E_t)`. A large `E_0(T)`
   persists only for `|t| ≲ 1/T`, which carries weight `1/(TH)` in the average,
   so the average forces nothing at `t = 0`. Fails quantitatively: averaged
   bounds leave the trivial twist free, as for the major arc in item 13.

23. **High-zero localization, sharpened.** With the hybrid exponent
   `igmDensityExponent σ ≤ 1 − (4/3)(σ − 1/2)` and the folded shell sums of
   `ZeroDensityFilteredCriticalDeficitLaw`, a dyadic shell `|γ| ≍ U` gives
   `Σ_shell e^{T(Re ρ−1/2)}/|ρ|² ≪ U^{−1+η}` once `U ≥ e^{(3/4+ε)T}`. So zeros above
   `x^{3/4+ε}` contribute `O(1)` to `incoming(T)`, improving item 9's `x^{13/30}`
   reading of the 30/13 bound alone. True, but a reduction of the same kind:
   the low block needs a strip. Lean:
   `BiScaleUncertainty/HighZerosCarryABoundedCriticalDeficit.lean` proves, for
   `0 < α < 2/3`, the uniform bound on the high-zero weight
   (`exists_highZero_deficitZeroWeight_tsum_le`), the finite low-zero
   representation of `incoming` up to `O(1)`
   (`exists_abs_incoming_sub_lowZeroDeficitSum_le`, `lowZeroDeficitSum_eq_sum`)
   and `E ≤ 2(Re low)² + C`; the same for the Weil lag function
   (`exists_abs_weilLagFunctionReal_sub_lowZeroLagSum_le`, lag weight ≤ 2× deficit
   weight). It bounds the high-zero parts of `E` and of the lag only.
24. **Exponentiated lag as an Euler product.** `e^{tΦ(L)} = e^{tΦ_arch(L)}·
   Π_{n≤e^{|L|}} exp(2tΛ(n)n^{−1/2} sinh((|L|−log n)/2))`, and RH iff `e^{tΦ}` is
   positive definite for all `t > 0` (Schoenberg). Each local factor is unbounded
   and not positive definite, and finite Euler products with the Gamma factor
   have no zeros to approximate `Φ`. No positive approximants arise.

25. **Effective horocycle equidistribution.** For incomplete Eisenstein series
   the closed-horocycle average at height `y` is the constant term
   `(1/2πi)∫ψ̂(s)φ(s)y^{1−s}ds`; shifting to `Re s = 1/2` meets only `s = 1`, giving
   the unconditional `O(y^{1/2})` that mixing and spectral-gap dynamics reproduce.
   The zeros enter as poles `s = ρ/2` left of the unitary line, residues
   `y^{1−ρ/2}`, which RH places at `y^{3/4}`. Fails: dynamical rates are unitary-line
   information and cannot pass the line where the zero poles sit.
26. **Low-zero block after localization.** By item 23 the adverse part is a finite
   sum over `|γ| < x^{3/4+ε}`, but its weights `e^{δT}/|ρ|²` are largest at the
   lowest heights, where density estimates count `O(1)` zeros with no saving.
   Any proof must exclude off-line zeros at bounded height without
   computation; density, VK and the localization give nothing there.

27. **Existence plus rigidity instead of an estimate.** Let `K_N` be the convex
   set of weights `λ ≥ 0` on `[2,N]` for which the Weil form (arch + poles −
   prime atoms with weights `λ`) is nonnegative on tests of aperture
   `(log N)/2`. The sets are nested under restriction and compact, so if every
   `K_N ≠ ∅` an inverse limit gives `λ_∞` with `WeilPositiveFull λ_∞`; a general
   rigidity theorem `WeilPositiveFull λ ⇒ λ = Λ` would then give RH with no
   estimate. By Farkas, `K_N ≠ ∅` iff no test `g = Σ f_j*f̃_j` on the window has
   negative arch+pole pairing and nonpositive pairing with every atom at
   `log n`, `n ≤ N`, a statement free of the primes. Status: the corpus proves
   rigidity only under smallness of `λ − Λ`
   (`eq_vonMangoldt_of_weilPositiveFull_of_sq_summable_separated`,
   `…_of_log_square_summable`, harmonic pinning). Without discreteness of the
   spectral measure, Hamburger's theorem is unavailable and rigidity for
   arbitrary `λ ≥ 0` is unproved, so `K_N ≠ ∅` alone yields nothing. Open
   on both halves; no Lean.

28. **Arithmetic Hodge index (Faltings–Hriljac).** The arithmetic Hodge index is
   proved for arithmetic surfaces `X → Spec O_K` of relative dimension one; Weil's
   argument needs the self-product of the base, `Spec ℤ × Spec ℤ`, which has no
   arithmetic-surface model. Fails at the missing surface, the open core of ACS.
29. **Rankin–Selberg / Shahidi nonvanishing.** Positivity of `L(s,π×π̃)` gives
   nonvanishing of automorphic `L`-functions on `Re s = 1` only. One-line class.
30. **Low-zero sum as a smoothed prime count.** By the truncated explicit formula
   the low-zero sum of item 23 is the WL deficit smoothed at multiplicative
   resolution `x^{−3/4}`, i.e. primes averaged over windows of length `x^{1/4}`.
   The WL deficit is already twice integrated, so the smoothing changes nothing
   at square-root precision. Fails: the reduction is self-dual.

31. **Testing rigidity by an integer-supported Herglotz series.** Item 27's
   rigidity fails if some `λ ≥ 0` on `ℕ`, `λ ≠ Λ`, has `G − F_λ` Herglotz on
   `Re s > 1/2`, where `G = 1/(s−1) + 1/s + A(s)` is ζ's archimedean term and
   `F_λ = Σ λ(n)n^{−s}`. Necessary: residue `1` at `s = 1` and
   `Re F_λ ≤ ½ log|t| + O(1)` throughout the half-plane. Poisson summation shows
   that any integer-supported series differs from its integral by a dual sum of
   the size of `ζ(1−s)`. Constant weights therefore inherit ζ's large values
   (`≫ exp(c√log t)`), and positivity of `λ` forbids sign cancellation. No
   construction found; rigidity is neither refuted nor proved.

The ledger now separates three information classes: one-line data (PNT,
pretentious, Eisenstein, Selberg trace), averaged data (density, large sieve,
mean values), and pointwise critical data. Items 1–16 all land in the first
two; every WL target lies in the third.

## Log

- 2026-10-25 — created; frontier, WL cards and 18 programme READMEs read.
- 2026-10-25 — items 1–12 attempted on paper; no source estimate, no new Lean.
- 2026-10-25 — item 23 formalized: direct compile of `HighZerosCarryABoundedCriticalDeficit.lean`
  exit 0, no output; transitive axioms of its four public results `{propext, Classical.choice,
  Quot.sound}`; wired into `BiScaleUncertainty.lean`. WL obstacles remain open.
- 2026-10-25 — lag-function localization added to the same module; direct compile exit 0;
  axioms of both new results `{propext, Classical.choice, Quot.sound}`.
- 2026-10-25 — cross-work corollary `exists_neg_coprimeCrossWork_le_lowZeroDeficitSum` added;
  direct compile exit 0; axioms `{propext, Classical.choice, Quot.sound}`.
