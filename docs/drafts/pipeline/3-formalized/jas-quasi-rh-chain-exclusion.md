# JAS chain exclusion under quasi-RH

- **ID:** jas-quasi-rh-chain-exclusion
- **Stage:** 3-formalized (moved: see Lean section)
- **Type:** THEOREM (Lean)
- **Source:** jas-goal-loop-2026-10-09.md rows 48–54
- **Statement:** If every Xi zero has `Re ρ ≤ ½ + α` with `α < ½`, and the dressed JAS aggregate is
  positive semidefinite at some `σ ≥ 1`, then the off-line zeros do not form a chain whose supremal
  distance `δ*` satisfies `σ < 1 + δ*`. Consequently `RH ⟺ JasDressedPSD 1 ∧ (∃ α < ½, XiZeroHalfPlaneBound α)`.

## Goal
Replace the exotic `¬JasOffLineChain` in the JAS capstone by the classical quasi-RH condition
`Θ < 1`. Together with the farthest-zero theorem this gives, under `Θ < 1`, the bimodal abscissa law
`σ* ∈ {0} ∪ [½ + Θ, 2]`. The chain residual of rows 48–49 (gapless real-part ladders) disappears;
what is left of chains is exactly the case `Θ = 1`.

## Gates
- [x] 0 → 1  well-posed, attack idea
- [x] 1 → 2  complete paper proof (below)
- [x] 2 → 3  Lean: `RHTower.one_add_sSup_le_of_jasDressedPSD_of_chain`,
  `RHTower.riemannHypothesis_iff_jasDressedPSD_one_and_quasi` (standard axioms only)

## Paper proof

**Setting.** `c = σ − ½ ≥ ½`. For a zero copy `q = β + iγ`, `A_p(q) = p^{−(q+c)}`, `B_p(q) = p^{−(1−q+c)}`,
weight `w_q = 1/(q(1−q))`. PSD(σ) gives, for every finite prime set `P` and `z : P → ℂ`
(`jasBernoulliAggregate_nonneg`):

`Re Σ_q w_q ∏_{p∈P} (1 + |z_p|² + z_p A_p(q) + z̄_p B_p(q)) ≥ 0.`

With `z_p = t_p e^{iθ_p}`, `t_p ∈ [0,1]`, `s_p = t_p/(1+t_p²) ≤ ½`, the factor is
`(1+t_p²)(1 + u_p(q))`, `u_p(q) = s_p(e^{iθ_p}A_p(q) + e^{−iθ_p}B_p(q))`.

**Step 0 (parameters).** Let `δ* = sup_q |Re q − ½| ≤ α < ½`; a chain has `δ* > 0`, not attained.
Assume `σ < 1 + δ*`. Fix `σ₁ = (1 + ½ + α)/2`, so `½ + α < σ₁ < 1`; put `η₂ = (1 − σ₁)/2`.
Put `μ = (1 + δ* − σ)/2 > 0`. Choose `θ′ = min(μ/2, η₂/8, δ*/4)` and then `ε > 0` with
`ε ≤ min(μ, η₂/8, δ*/2)` and `ε < θ′ c₀ /(C₀ log 8 + 2)`, where `c₀ ∈ (0,1)` is the peak-isolation
exponent (row 51) and `C₀` the window-count constant (zeros with `|γ − t| < 1` number at most
`C₀ log t`).

**Step 1 (target).** Pick a chain zero with distance `> δ* − ε`; by rows 51–52 there is a zero
`q_t` (take the left copy, `β_t = ½ − δ_t`) of height `γ_t ≥ H` with `δ* − ε < δ_t ≤ δ*` such that
every zero with `|γ − γ_t| ≤ γ_t^{c₀}` has distance `≤ δ_t`. Then `α_t := σ − δ_t ≤ 1 − μ`.

**Step 2 (design).** `P = {p prime : √N < p ≤ N}` (endpoints at half-integers),
`θ_p = φ + γ_t log p`, `s_p = τ p^{α_t − 1} log p` with `0 < τ ≤ τ_max = N^{θ′}/log N`
(then `s_p ≤ ½`). For every zero:

`Σ_P u_p(q) = τ(e^{iφ} S(z_q) + e^{−iφ} S(w_q))`,  `S(z) = Σ_P (log p/p) p^z`,

`z_q = (β_t − β) + i(γ_t − γ)`, `w_q = (β + β_t − 1) − i(γ_t − γ)`. One of `Re z_q, Re w_q` is
`δ − δ_t ≤ ε` and the other `−δ − δ_t`. Since `|u_p| ≤ 2τ (log p/p) p^{ε} ≤ N^{−1/8}`,
`∏(1 + u_p) = exp(Σ u_p)(1 + ρ_q)` with `|ρ_q| ≤ 2Σ|u_p|² ≤ N^{2θ′+2ε−1/2} log² N → 0`
uniformly in `q`.

**Step 3 (pairing).** `q ↦ 1 − q̄` maps `z ↦ w̄`, `w ↦ z̄`, `w_q ↦ w̄_q`, so the aggregate is
`Σ_{on-line} w_q e^{τE_q}(1+ρ_q) + Σ_{off-line, β<½} 2 Re(w_q e^{τE_q}(1+ρ_q))`,
`E_q = e^{iφ}S(z_q) + e^{−iφ}S(w_q)`. For `β < ½`: `|τ S(w_q)| ≤ τ N^{−(δ+δ_t)/2} M ≤ ½`, and
`≤ N^{θ′−δ_t}` for `δ ≥ δ_t − ε`.

**Step 4 (prime sums).** `M = S(0) ≍ ½ log N` (Mertens). For `Re z ≤ 0`, `|S(z)| ≤ M`,
`Re S(z) ≤ M`. Put `λ_q = 1 − Re S(z_q)/M ≥ 0` for zeros in the window. For `|Im z| ≥ 1`,
`Re z ∈ (−1/8, ε]`, the uniform shifted Perron formula (row 53) at `s₀ = 1 − z`, applied at the two
half-integer endpoints (the `ζ′/ζ(s₀)` terms cancel), gives
`|S(z)| ≤ 4N^{max(Re z,0)}/|Im z| + K N^{−η₂}(1 + log(N + |Im z| + 10))² + K N^{−1/8}`.
For `Re z ≤ −1/8`, `|S(z)| ≤ N^{−1/16} M` trivially.

**Step 5 (cluster).** Let `τ_min = τ_max/8^{K}`, `K = ⌈C₀ log γ_t⌉`, `L₀ = 3(c₀ + 3) log γ_t`.
Cluster `𝒞` = zeros with `|γ − γ_t| < 1` and `τ_min M λ_q ≤ L₀`; `|𝒞| ≤ K`. Window zeros with
`|γ − γ_t| ≥ 1` have `|S(z_q)| ≤ 8 + o(1)`, so `λ_q ≥ ½`: not in the cluster.

**Step 6 (alignment).** For `q ∈ 𝒞` put `ϑ_q = M Im S(z_q)/M = Im S(z_q)`. By simultaneous
Dirichlet approximation (`exists_fin_simultaneous_two_pi_phase_approximation_anisotropic`) there is
`1 ≤ ν ≤ 8^K` with `|ν τ_min ϑ_q − 2π r_q| ≤ π/4` for all `q ∈ 𝒞`. Set `τ = ν τ_min ∈ [τ_min, τ_max]`
and choose `φ ∈ (0, π/2)` with `arg w_t + τ M sin φ = π`; then `φ ≤ 4/(τM)`.

**Step 7 (signs).** Target pair: `2Re(w_t e^{τE_t}(1+ρ)) = −2|w_t| e^{τM cos φ}(1 + o(1))`.
Each cluster pair: `2Re(w_t e^{τE_t} · (w_q/w_t) e^{τ(E_q − E_t)})`, where
`τ Im(E_q − E_t) = τϑ_q cos φ − (π − arg w_t)λ_q + O(N^{θ′−δ_t})` and `arg(w_q/w_t) = O(1/γ_t)`;
since `λ_q ≤ L₀/(τ_min M)` and `|ϑ_q| ≤ √(2λ_q) M`, all corrections are `o(1)`, so the phase is
within `π/4 + o(1)` of `0 mod 2π` and every cluster pair contributes `≤ 0`.

**Step 8 (background).** Window non-cluster zeros: `τ Re E_q ≤ τM cos φ − τMλ_q(1 − o(1)) + ½`, so
their total is `≤ C γ_t^{c₀} log γ_t · (2/γ_t²) e^{τM cos φ} e^{−L₀/2 + 1}`. Far zeros
(`|γ − γ_t| > γ_t^{c₀}`) with `|γ − γ_t| ≤ exp(N^{η₂/4})`: Step 4 with
`N^{ε} ≤ γ_t^{c₀} log N/32` gives `|τS(z_q)| ≤ τM/4 + o(1)`; their total is
`≤ e^{τM/4 + 2} Σ|w_q|`. Far zeros above `exp(N^{η₂/4})`: trivial `|τS| ≤ τ N^{ε} M ≤ N^{θ′+ε}` and
`Σ_{|γ|>T}|w_q| ≪ log T/T`, total `≤ exp(N^{θ′+ε} − N^{η₂/4}/2)`. On-line zeros have
`|τE_q| ≤ 1`.

**Step 9 (choice of N).** `N = (γ_t^{c₀} log γ_t/64)^{1/ε}`. Then
`τ_min M ≥ N^{θ′}/(3·8^K) ≥ γ_t^{c₀θ′/ε − C₀ log 8 − 1} ≥ γ_t ≥ L₀ e^{…}`, all background terms are
`o(|w_t| e^{τM cos φ})`, and the aggregate has negative real part, contradicting PSD(σ).

**Corollary.** With the farthest-zero theorem (`not_jasDressedPSD_of_maximal_offLine`), under
`Θ < 1`: `JasDressedPSD σ` with `σ < ½ + Θ` forces RH. With `σ = 1` and `¬Chain ⇒ Θ < 1` (Lean):
`RH ⟺ JasDressedPSD 1 ∧ ∃ α < ½, XiZeroHalfPlaneBound α`.

## Why rows 48–49 left a residual
They resolved near ties by Turán/Nazarov power-sum lower bounds, whose exactness and `e^{X max|d_j|}`
losses forced multiplicative gaps. Here all cluster weights are positive and the amplification scale
`τ` enters every cluster phase linearly, so simultaneous Dirichlet approximation aligns all phases
at cost `8^K = γ_t^{O(1)}`. Peak windows of polynomial size (row 51) make that cost affordable.

## Lean plan
1. `Sieve/JasLogWeightPrimeSum`: `S(z)` and Step 4 bounds from `ShiftedPerronUniform`.
2. `JointAncestryLogWeightBernoulli`: Steps 2–3 (factor identity, product/exp comparison, pairing).
3. `JointAncestryClusterAlignment`: Steps 5–7.
4. `JointAncestryQuasiRHChainExclusion`: Steps 8–9 and the corollary.

## Lean
Modules (all in `GaloisForLFunctions/RHTower/`):
- `JointAncestryLogWeightBernoulli` — PSD(σ) ⟹ positivity of log-weight tests centred at any point.
- `JointAncestryLogWeightPrimeSum` — window sums `S(z)`, Mertens bounds, Perron form uniform in height.
- `JointAncestryLogWeightExpansion` — `∏(1+u_p) = exp(Σu_p + R)`, reflection symmetry, remainder.
- `JointAncestryClusterPhase` — target normalisation, aligned points are non-positive.
- `JointAncestryZeroTailBound` — `Σ_{|Im q|>T}|w_q| ≤ 80(C+log(3T+4))/T`.
- `JointAncestryQuasiRHAmplification`, `JointAncestryQuasiRHCore` — per-point estimates and the
  amplification contradiction with explicit numerical hypotheses.
- `JointAncestryQuasiRHParameters` — the window parameters and their eventual inequalities.
- `JointAncestryQuasiRHChainExclusion` — Dirichlet alignment, peak selection, final theorems.

## Corollaries (Lean)
- `JointAncestryAbscissaGap`: σ* ∉ (0, ½), so RH ⟺ σ* < ½. Under a half-plane bound α < ½, σ* = 0
  or σ* ≥ 1 + δ*. And 0 < σ* ≤ 1 forces sup Re ρ = 1.
- `JointAncestryHalfPlaneExistence`: XiZeroHalfPlaneBound α (α ≤ 1/20) ⟹ JasDressedPSD(1 + 3α). Off RH,
  under quasi-RH with δ* ≤ 1/20: 1 + δ* ≤ σ* ≤ 1 + 3δ*.
- `JointAncestrySharpAbscissaLaw`: for K > coth(π/4) ≈ 1.525 and small α, a half-plane bound α gives
  JasDressedPSD(1 + Kα), which is the best per-zero constant. Concretely 1 + δ* ≤ σ* ≤ 1 + (5/3)δ* for δ* ≤ 1/100.
- `JointAncestryHaarSingularCertificate`: for 0 < σ < ½, every certificate (a finite measure whose Fourier
  coefficients are the dressed aggregate) is singular to Haar measure, and above ½, under RH, the
  certificate is Haar-absolutely continuous.
- `JointAncestryLargePrimeAbscissa`, `JointAncestryLargePrimeMaximalExclusion`: JAS positivity on primes > X
  holds unconditionally at every σ > 3/2. Under quasi-RH and off RH, its abscissa tends to exactly ½ + Θ.
  The chain theorem is refactored to `one_add_sSup_le_of_jasWindowPositivity_of_chain`.
- `JointAncestryWeilEulerBridge`: the zero-sum density equals Π(1 − p^{−2σ}) times Weil's lag form on the
  Euler vector e_w(m)m^{−σ} over P-smooth integers. For σ > ½, JAS positivity ⟺ Weil positivity on Euler
  vectors, and RH ⟺ Weil positivity on harmonic Euler vectors ∧ quasi-RH.
- `JointAncestryArithmeticCapstone`: RH ⟺ (arithmetic Fejér forms ≥ 0) ∧ (Σ(Λ(n)−1)n^{−σ} has an
  abscissa θ < 1); RH ⟺ ∃σ < ½, JasDressedPSD σ.

## Reading
JAS positivity at level σ is Weil's lag form tested on Euler vectors c(m) = χ(m) m^{−σ} supported on
P-smooth m. The twisted partial Euler density at w equals Π(1 − p^{−2σ}) Σ_{m,n} w^m w̄^n (mn)^{−σ} Φ(log m − log n).
- Below ½, these vectors detect every off-line zero.
- Between 1 and 1.15, positivity is a zero-free half-plane up to the factor 3.
- At 1, positivity is the bridge from a power-saving PNT to RH.

The case Θ = 1 is open (ledger row 56). It needs large-value or Bohr-set control of the near-1 ordinates.

## Log
- 2026-10-10 — created; paper proof drafted (row 54).
- 2026-10-11 — formalized; RH ⟺ JasDressedPSD 1 ∧ Θ < 1 in Lean.

## Route verdict (2026-10-11)

- Exact reduction [L]: RH ⟺ no off-line chain ∧ for every σ > 1, JAS positivity on characters of primes > X(σ)
  (`JointAncestryPositivityAtInfinity`). Small primes and σ ≤ 1 carry no further content.
- Existence at infinity: unconditional above σ = 3/2 [L]. In (1, 3/2] it is equivalent to zero-free half-planes
  (large-prime abscissa = ½ + Θ under quasi-RH [L]).
- No chain: excluded under quasi-RH [L]. Θ = 1 chains have loglog plateau records [L]
  (`JointAncestryPlateauRecords`). On paper, window, log-window and amplitude averaging at plateau records leave only
  clusters of ≳ log(1/κ) near-1 zeros that are mutually Bohr-aligned on primes ≤ (log γ)^A at height differences in
  [exp((loglog γ)^{3/2}), γ^{1+ε}] (ledger rows 69, 71–73).
- Method no-go: plateau control needs log N = O(loglog γ), while a zero-free region of exponent θ_Z excludes
  alignment only when log N ≥ (log γ)^{θ_Z}. So window tests close Θ = 1 only with a zero-free strip (circular) or a
  new non-alignment theorem for near-1 zeros.
- Producer side [L]: certificates below ½ are Haar-singular; height-mixture certificates exist iff RH and equal the
  zero measure; JAS positivity = Weil positivity on Euler vectors.

## Route verdict update (2026-10-11, after ledger rows 74–83)

- [L] Cluster theory for the b-side kernel: exact cluster identity (polydisc patterns), twin inequality, exponential
  coherence threshold, ordinate and Dirichlet-polynomial forms (MUST-1211–1215).
- Correction (row 83): the a-side factor of the JAS local density perturbs the b-side Hermitian structure at relative
  order ≈ S/N. For actual zeros the rescue condition is polynomial incoherence, not exponential. Twins are still
  excluded, but structured clusters of about a members (N = S^a) evade, with a ≲ c/(η loglog γ).
- Intrinsic detectability limit (row 82): single-shell JAS tests at σ = 1 see only zeros with η ≲ 1/(240 loglog γ).
- Open core of Θ = 1: structured near-1 clusters (r-th order phase cancellation on small primes) at plateau records,
  and the invisible slowly approaching chains.

## Route verdict update (2026-10-11, after ledger rows 86–87)

- [L] Two-sided cluster theory for clusters with a common real part (`JointAncestryClusterTwoSided`, MUST-1243).
  The full JAS local factor is (1 − ab)(1 − aw)⁻¹(1 − bw̄)⁻¹ on the circle. The member-averaged two-sided kernel is a
  twisted positive double Dirichlet series, and it obeys the exponential coherence threshold with the a-side mass at
  most S/100. The a-side caveat of rows 83–84 is removed for homogeneous clusters.
- [P] Exponent gap is invariant (row 86).
  - Plateau records kill every single spoiler at polynomial height differences: the spoiler zero would be deeper than
    the record below it, or would break the plateau.
  - Collective spoilers survive. About log Δ zeros of depth ≤ 2/A in one unit window align a dyadic window, and
    Jensen with the VK bound permits that many.
  - Larger shells (super-plateau records) and other dressing levels σ ∈ (1, 3/2) reproduce the same gap,
    θ < θ′ ≤ 2/3 ≤ θ.
- Reading: JAS chain exclusion is neutral relative to zero-free-region technology. It excludes only chains that hug the
  boundary of the best available zero-free region. The Θ = 1 core needs one of two inputs:
  - a local zero-count bound n_loc(d) ≪ (log Δ)^{Ad/2} for the zeros of depth ≤ d in a unit window at height Δ near
    the 1-line, for d ∈ [κ/loglog Δ, 2/A] (at the low end this is a log-log zero-free region, since VK–Jensen gives
    only d^{3/2} log Δ);
  - or a non-alignment theorem.
- [L] Cluster dichotomy (row 88, `JointAncestryClusterDichotomy`, MUST-1250). A rescuing cluster has effective size at
  least 1/(ε + 6e^{−S/60}), where ε is its worst pairwise alignment. For zeros, ε is the partial Euler product ratio
  at a height difference. With VK density, homogeneous clusters reduce to Bohr-aligned pairs. Dispersed clusters need
  only polylog effective size, so the binding residual is real-part dispersion plus Bohr-aligned pairs at height
  differences beyond exp(c(log N)^{3/2}).
- [L] Producer side (row 89, `JointAncestryLargePrimeAttainment`, MUST-1256): summability criterion `d_ρ < σ₀ − 1`, `Σ|w_ρ|/(σ₀−1−d_ρ) < ∞` ⟹ `∃X ∀σ ≥ σ₀`, large-prime positivity. Unconditional at `σ₀ = 3/2` via the zero-free region. Attained abscissa `1 + δ*` for summable chains under quasi-RH. The large-prime producer is equivalent to a zero-free half-plane, up to chains and boundary summability.
- [L] Row 90 (MUST-1258): endpoint exclusion at exponent one; a farthest zero makes the large-prime producer set the open ray `(1 + d₀, ∞)`; off RH, attainment forces a chain. The chain residual is the endpoint behaviour of the producer.

## Producer-side verdict (2026-10-11, after ledger rows 89–90c)
- **Large-prime producer law [L].** Positivity above some X at level σ ≥ 1 forces the closed strip `|Re ρ − ½| ≤ σ − 1`, unless `sup |Re ρ − ½| = ½`. Conversely, the open strip plus convergent boundary series `Σ|w_ρ|/(σ−1−d_ρ)` produces positivity (one X for all levels ≥ σ). Unconditionally the producer exists at `σ = 3/2`, the pole threshold where `Σ (ab)^{−σ}(a/b)^{1/2}` stops converging.
- **Endpoint structure [L].** With a farthest zero, the producer set is the open ray `(1 + d₀, ∞)`; summable chains attain `1 + δ*`. Off RH, attainment forces a chain. The all-prime abscissa exceeds `1 + d₀` strictly when a farthest zero exists.
- **Capstone [L].** RH ⟺ (∃X, large-prime positivity at σ = 1) ∧ quasi-RH.
- **Reading.** JAS has no positivity source independent of zero location. Below 3/2 a producer is a zero-free strip, and at σ = 1 it is RH (modulo Θ = 1). This is the prime-side analogue of Hadamard positivity `Re ξ'/ξ > 0` right of all zeros, shifted by the pole of ζ. The archimedean (Poisson-in-L) dressing has abscissa `Θ − ½`, the prime (Poisson-in-primes) dressing `Θ + ½`. Proportion results (critical zeros ≥ 67%, Selberg density) cannot feed JAS positivity, because one off-line zero with `d > σ − 1` has unbounded amplification. The only JAS-specific open content left is the Θ = 1 escape (receiver residual [B]), which needs zero-distribution input beyond Vinogradov–Korobov (rows 86–88). A route-JAS proof of RH therefore needs an RH-strength producer from outside the Euler-product side: modularity/theta or an independent zero-free half-plane.
- NO INDEPENDENT PRODUCER EXISTS INSIDE JAS (positive survivors: rows 89, 90, 90b, 90c).

## What would close route JAS (2026-10-11, after rows 89–92b)
- **[A] Producer (RH-strength).** Large-prime positivity at σ = 1 (equivalently, Weil positivity on large-prime harmonic Euler vectors). With quasi-RH this is RH [L] (`riemannHypothesis_iff_exists_jasDressedPSDAbove_one_and_quasi`, `riemannHypothesis_iff_weilEulerPositiveAbove_one_and_quasi`). No producer for it exists inside JAS. The unconditional producers are local: in dressing (σ ≥ 3/2, MUST-1256) and in log-scale (windows ≤ (σ−1) log X, MUST-1260).
- **[B] Receiver completion.** Exclude Θ = 1 configurations with large-prime positivity at some σ < 3/2. Then positivity at σ ∈ [1, 3/2) ⟺ the zero-free strip Re ρ ≤ σ − ½, and RH ⟺ large-prime positivity at σ = 1 with no side condition. Needed inputs, in paper form:
  - (B1) a Ford-type density `N(1−κ, T) ≪ T^{Cκ^{3/2}}(log T)^{C}`, which kills chains on the VK boundary (row 88). The corpus has VK and Ingham's density, but not this.
  - (B2) a growth law making farther-from-the-line zeros polynomially higher in log-height (row 86 exponent gap), or a non-alignment statement for zero ordinates at super-VK height differences. Both are beyond current knowledge.
- **Verdict.** Route JAS is a complete receiver modulo [B], and its producer is RH-strength. Every remaining step is a statement about zeros of ζ near Re s = 1 (B1, B2) or RH itself (A).

## Minimal producer target (2026-10-12, rows 100–101)
- Every receiver uses only rank-one Bernoulli product tests. RH ⟺ (∃X, product-test positivity on primes > X at σ=1) ∧ quasi [L] (R:JointAncestryLargePrimeAttainment). Under quasi, block-positivity of the zero operators Σ_ρ w_ρ ⊗_p M_{ρ,p} forces full PSD (MUST-1267).
- Product tests reduce to the Kronecker line: RH ⟺ (∃X: Re Σ_ρ K_P(ρ−it)/(ρ(1−ρ)) ≥ 0 for every finite P ⊂ primes > X and t ∈ ℝ, K_P(s) = ∏_{p∈P}(1 + p^{−1}cosh((s−½)log p))) ∧ quasi [L] (R:JointAncestryPrimeCosineKernel, MUST-1270). This is the smallest form of [A]: Weil positivity against translates of positive large-prime cosine products.
- (row 103) The half-plane hypothesis is JAS-internal: quasi-RH ⟺ single-prime JAS positivity at some σ < ½ on large primes, and RH ⟺ single-prime positivity at σ = 0 (the WL prime-lag bound). Capstone: RH ⟺ ∃X: single-prime positivity below ½ ∧ cosine positivity at σ = 1 [L] (R:JointAncestrySinglePrimeLevel, MUST-1272).

## Producer map (2026-10-12, rows 99–108, all [L] unless noted)
On large primes, JAS positivity is graded by prime-number-theorem strength:
- **Single-prime tests** (one prime, level σ) ⟺ \|Φ(log p)\| ≤ Φ(0)p^σ. Level ½: unconditional (PNT). Level σ ∈ [¼,½): ⟺ half-plane Re ρ ≤ ½ + σ, up to the boundary. Some level < ½: ⟺ quasi-RH. Level 0: ⟺ RH (the WL prime-lag bound). (R:JointAncestrySinglePrimeLevel, MUST-1272/1273)
- **Product tests** (rank-one, squarefree) ⟺ **cosine-kernel tests** at every level (R:JointAncestryPrimeCosineKernel, MUST-1270). They are monotone up in the level. Some level < ½: ⟺ RH, with no side condition. Level 1: ⟺ RH given quasi-RH. Level ≥ 3/2: unconditional.
- **Minimal producer:** quasi-RH (single primes below ½) plus RH given quasi-RH (cosine positivity at level 1). Both are classical.
- **[B]** (does level-1 positivity force single primes below ½?) is blocked at every level in [½,1]. Single coefficients carry no information there [L]. Averaging in t at width h caps amplification at e^{1/(2h)} [P], so averaging (density, large-sieve) methods cannot certify the competitors. Pointwise tools (records, VK, Ω-balanced ratios) leave collective dispersed rescue (rows 86, 88, 99, 102, 107, 108). [B] needs information about individual near-edge ordinates beyond averaging, the same kind quasi-RH needs.

## Producer map, sharpened (2026-10-12, rows 112–114, all [L])
- **Single-prime level is exactly Θ − ½** on [0,½), with no ¼ artifact: a one-sided power-saving lag bound at the primes (upper: R:PrimeLagLandauPowerSaving; lower: R:PrimeLagPowerSavingLowerBound) is a zero-free half-plane. One test vector (z = 1 alone, or z = −1 alone) suffices.
- **Bounded complexity sees only Θ − ½** (R:JointAncestryProductComplexity). For every fixed k, k-prime product positivity has the single-prime abscissa. Positivity holds on all sets of ≤ c·X^{σ−α} primes under a half-plane α ≤ σ, unconditionally for σ ≥ ½.
- **Consequence for the producer:** off RH, the product abscissa Θ + ½ is carried only by tests on ≫ X^{σ−α} primes. Both [B] and RH-given-quasi live in this high-complexity regime, where every unconditional bound is a zero-free-region bound.
- **Unconditional producer = bounded prime budget** (row 117, [L]): for every σ and K, positivity holds on all sets of primes > X with Σ_P p^{−(σ−½)} ≤ K once X is large. Few-primes (K·X^{σ−½}) and global (σ > 3/2) producers are special cases. Growing budgets need a zero-free region; unrestricted budget at σ = 1 is [B].

## [B] closed (2026-10-12, row 119, [L])
`riemannHypothesis_iff_exists_jasProductPositiveAbove_one`: RH ⟺ ∃X, JasProductPositiveAbove X 1, with no quasi-RH hypothesis (R:JointAncestryDiagonalBochnerLevel). Product positivity at any level σ ≥ 0 forces |Re ρ − ½| ≤ max(0, σ − 1). The method is the diagonal Bochner bound (card `jas-diagonal-bochner-level-one`). The producer side now has a single target: prove product positivity on large primes at level 1.

## Route JAS: final producer verdict (2026-10-12, rows 119–124, all [L])
- **Receiver: closed.** RH ⟺ ∃X: constant-vector product positivity over prime intervals at level 1 (MUST-1290, 1293). Positivity at level σ forces |Re ρ − ½| ≤ max(0, σ − 1) for every configuration of zeros.
- **Producer: graded exactly by zero-free regions.** Budget y^λ ⟺ half-plane ½ − λ (MUST-1294). Power-of-log regions (log|γ|)^{−θ} transfer to budget (log y)^{1/θ−} (MUST-1296). The unconditional producer reaches (log y)^{3/2−ε} via Vinogradov–Korobov.
- **No independent producer inside JAS.** Every JAS producer statement is a zero-free-region statement, at every scale. Second pass tried: z-averaging of the on-line square structure, the functional-equation pairing, the Kolmogorov/Bochner torus measure, torus L^q receivers, and Euler-polynomial expansion (the product test is the Weil form on |Euler polynomials|²). None supplies positivity beyond the zero-free region in use. Status: route complete as an equivalence; NO INDEPENDENT PRODUCER FOUND. The next producer step (any λ > 0) is quasi-RH.

## Weighted JAS and the final producer classification (2026-10-12)

**Positive survivor.**
- Weighting each zero by g(ρ)/(ρ(1−ρ)), for any dressing g positive on the line, keeps the receiver: RH ⟺ level-1 weighted positivity.
- The weighted family is unconditionally positive at every budget exp(log y·(log log y)^{−θ'}), θ' > 2/3, for g_κ = exp(|κ|(1 − cos 3(s−½))).
- For every dressing, a budget y^λ is exactly the half-plane ½−λ.
- Modules: R:JointAncestryWeighted{Lag,LagGrowth,Bochner,Level,Producer,CosProducer,BudgetLaw}; MUST-1305 and MUST-1308.

**New insight.** The undressed (log y)^{3/2} stop is an artifact of the zero-weight tail. All sub-power JAS budgets are reachable from VK alone. So the JAS producer problem is exactly the fixed-power gap, which is quasi-RH.

**Why no JAS-internal producer can close that gap.**
1. Single off-line zeros are visible at every power budget for every dressing. Density inputs (Selberg, Levinson, zero-density) cannot help. This is consistent with the admissible-shape classification in R:DegradationRateRanking.
2. A prime-side proof would need a one-sided bound on S(L) = Σ_{n≤e^L} Λ(n) n^{−½}·2 sinh((L−log n)/2) to within e^{aL}, a < ½, of its main term.
   - The upper direction needs better than the factor-2 sieve bound; this is the parity barrier.
   - The lower direction needs a lower bound on primes at power precision.
   - In both cases the positivity of Λ lies on the wrong side of the explicit-formula duality.
3. Zero-side inputs are the zero-free region lane. There the Vinogradov family sits at κ = 3/2 and quasi-RH needs κ = ∞ (R:ExponentChainKappa).

**Verdict.** NO INDEPENDENT PRODUCER INSIDE JAS. A JAS proof of RH needs a global, non-linear Euler×FE coupling that gives a fixed-width zero-free region. No route in the corpus currently supplies one.

## Measure paradigm closure (2026-10-12)
- Random phases z_p = rω^{k_p} on a set P of primes in (y, 2y], y ≥ Y:
  - the exceptional set is at most N^{|P|}·Σ_ρ|w_ρ| exp(−c y^{2ω_ρ} log y), where
    ω_ρ = ½ − |Re ρ − ½|;
  - this gives exp(−(log y)^{3/2−ε}) unconditionally and exp(−c y^{1−2α} log y) under a
    half-plane α (R:JointAncestryRandomPhaseWidthGraded, MUST-1320).
- Parseval: the phase variance equals Σ_e κ_e²Φ(L_e)² over sign patterns.
  - On Huxley windows: subpower variance ⟺ RH, and power-saving variance ⟺ quasi-RH
    (R:JointAncestryRandomPhaseParseval, MUST-1324).
- Classification: every phase-averaged statistic is a faithful receiver of the zero-free region.
  None supplies positivity. Direct counting (row 142) fails because it bypasses the zero side.
- Rows 150–158 add three facts.
  - Sparse-scale relaxations of the cofinal receiver are blocked by the lack of γ-decay of the
    twisted prime sums B_ρ(y).
  - The full-prime PSD abscissa has ceiling ½ + Θ.
  - The one-prime lattice receiver is already in the corpus (R:WeilLagFunctionSingleBase).
