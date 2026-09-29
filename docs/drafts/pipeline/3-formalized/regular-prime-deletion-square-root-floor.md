# Regular prime deletions have integer error Ω(x^{κ/2−ε}) (DMU on all regular deletions)

- **ID:** `MC-DMU-REGULAR-DELETION-FLOOR`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, axiom-clean)
- **Source:** MC loop cycle 89 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`). It closes the even-λ question left open in `3-formalized/prime-deletion-residue-quantization.md` (cycles 30/77/83).
- **Statement:** Let `Q ⊆ ℙ` satisfy `θ_Q(x) = Σ_{q∈Q, q≤x} log q = A x^κ + O(x^η)` with `A > 0`, `0 < η < κ/2`, `κ < 1`. Let `S` be the set of `Q`-free integers and `a = Π_{q∈Q}(1−1/q)`. Then `N_S(x) − a x ≠ O(x^θ)` for every `θ < κ/2`.

## Goal
Discrete multiplicative uncertainty (DMU, loop cycle 22) predicts `Θ ≤ max(½, 2β)`. On the deletion family `ℙ∖Q` the prime exponent is `≥ κ`, so DMU asks for `β ≥ κ/2`. The corpus proved this only for odd `λ = Aκ` (branch point at `κ/2`, `not_isBigO_qFreeCount_of_odd`). The even case was open, and cycle 77 attributed the heuristic floor to prime-position randomness. The theorem settles every `λ`, including non-integers. The floor is an ℓ²-divergence: `Σ_{q∈Q} q^{−2σ} = ∞` exactly for `σ ≤ κ/2`. Randomness plays no role, and neither does the greedy construction.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete paper proof below, no open dependency
- [x] 2 → 3  formalized: `RHTower.PrimeDeletion.not_isBigO_qFreeCount_of_leading_chebyshev`
- [ ] 3 → 4  publication-ready

## Proof
Suppose `N_S(x) − ax = O(x^θ)` with `η < θ < κ/2`. Fix `σ ∈ (θ, κ/2)` and `σ₀ = (θ+σ)/2`.

1. **Integer side.**
   - `Z_S(s) = Σ_{n∈S} n^{−s} = as/(s−1) + s∫_1^∞(N_S(x)−ax)x^{−s−1}dx` is analytic on `Re s > θ` except at `s=1`.
   - For `Re s ≥ σ₀ − δ` and `|Im s| ≥ 1` it satisfies `|Z_S(s)| ≤ C₁|s|`.
2. **Deleted prime side.**
   - For `Re s > κ`: `Z_S = ζ·G` with `G = Π_{q∈Q}(1−q^{−s}) = exp(−P)` and `P = Σ_{q,k} q^{−ks}/k`.
   - `−P' = ∫x^{−s}dψ_Q` with `ψ_Q(x) = Σ_{k<K} A x^{κ/k} + O(x^η)`. Hence `P'` is meromorphic on `Re s > η`, with simple poles only at the real points `κ/k`, and `|P'(s)| ≪ |s|`.
   - On the simply connected region `H = {Re s > η, Im s > 1}`, `P` continues analytically with `|P(s)| ≪ |s|²`. `G = exp(−P)` there, so `G` is analytic and zero-free on `H`, and `Z_S = ζ·G` on `H` by the identity theorem.
3. **Poisson–Jensen ceiling.** Take `c_t = 3+it` and radii `r₁ = 3−σ < R₁ = 3−σ₀ < R₂ = R₁+δ`, with `D' = B(c_t, R₂) ⊂ H ∩ {Re s > θ}`.
   - `log|G|` is harmonic on a neighbourhood of `D̄'`. For `|z−c_t| ≤ R₁`, the Poisson representation on `∂D'` with kernel `≤ κ₂ = (R₂+R₁)/(R₂−R₁)` gives
     `log|G(z)| ≤ κ₂(∫log⁺|Z_S| + ∫log⁺|ζ| − log|ζ(c_t)|) ≤ M_t = O(log t)`.
   - This uses `log|G| = log|Z_S| − log|ζ|` a.e. on the circle, `∫P(−log|ζ|) ≤ κ₂∫log⁺(1/|ζ|)`, and Jensen `∫_{∂D'}log|ζ|dm ≥ log|ζ(c_t)| ≥ log(ζ(6)/ζ(3))`.
   - No zero-free region is needed, because `G` itself has no zeros.
4. **Borel–Carathéodory** (Mathlib `Complex.borelCaratheodory_zero`) is applied to `f(z) = P(c_t) − P(c_t+z)` on `B(0,R₁)`.
   - `Re f ≤ M_t + |P(c_t)| = O(log t)`, which gives `|P(σ+it)| ≤ C₅ log t` for all large `t`. (★)
5. **Linearized mean square.** Take `W = T^{1/2}`, `X = T^{1/4}`, and `F(τ) = sinc(τ/W)^{2m}` with `m ≥ 3`. Then `F ≥ 0`, `F̂ ≥ 0` is supported in `[−2m/W, 2m/W]`, and `|F̃(τ+iy)| ≤ (W/|τ|)^{2m}e^{2m|y|/W}`. Put `K(t) = F(t−T)` and `B(t) = Σ_{q∈Q, q≤X} q^{−σ−it}`.
   - Cauchy on the rectangle `[σ,3]×[T/2,3T/2]` moves `∫K(t)q^{it}P(σ+it)` to `Re s = 3`. There `P = Σ b_n n^{−s}`, and every integer `n ≠ q` has `|log(n/q)| ≥ 1/(2X) > 2m/W`, so only `n = q` survives.
   - Hence `∫KPB̄ = (∫F)Σ_{q≤X}q^{−2σ} + o(1)` and `∫K|B|² = (∫F)Σ_{q≤X}q^{−2σ} + o(1)`. The horizontal edges and the tails are `O((W/T)^{2m}T²X³) = o(1)`.
   - The pointwise inequality `|P|² ≥ 2Re(PB̄) − |B|²` then gives
     `∫K|P(σ+it)|² ≥ (∫F)Σ_{q∈Q, q≤X} q^{−2σ} − o(1) ≫ (∫F)X^{κ−2σ}/log X`.
6. **Contradiction.** By (★) the left side is `≤ (∫F)C₅²log²(2T)`, while `X^{κ−2σ} = T^{(κ−2σ)/4} → ∞`. ∎

## Audit
- **Rediscovered mechanism.**
  - Hilberdink (J. Number Theory 112 (2005)) proves: `ψ = x+O(x^α)`, `α<½` implies `N−ρx = Ω(x^{½−ε})`.
  - Broucke–Hilberdink, "Omega-results for Beurling generalized integers" (preprint, cage.ugent.be/~fabrouck), sharpen this to `Ω(√x e^{−(log x)^β})` for `β > 2/3`.
  - Both use Borel–Carathéodory on `log ζ_B` and a mean-square lower bound for the truncated prime sum.
- **Novelty.**
  - The deletion setting differs: the Beurling zeta is `ζ·G` with `ζ`'s zeros unknown. The new step is the Poisson–Jensen ceiling (step 3), which never needs a lower bound for `|ζ|`.
  - The exponent is `κ/2`, the square root of the deleted dimension, rather than `½`.
  - Scientific content: DMU holds on every regular deletion, and the corpus reading ("the floor comes from prime-position randomness", cycle 77) is corrected to ℓ²-divergence.
- **Significance.** The theorem is a rigorous instance of DMU for all `λ`. It gives no RH input. For `ℤ` itself the argument needs `log ζ` analytic, which is RH.

## Log
- 2026-09-29 — created in 2-fully-proven (MC loop cycle 89). Lean: not started. Needed pieces are the continuation of `P` from `θ_Q` (the corpus has `residue_quantization` infrastructure), the Poisson/Schwarz representation on discs, Jensen for `log|ζ|`, Mathlib Borel–Carathéodory, and the contour shift with `complexSinc` kernels (`MobiusHilbertLogarithmicFloor`).
- 2026-09-29 — formalized. Axioms: propext, Classical.choice, Quot.sound only.
  - `HTGeometry/LogQuotientDerivativeCeiling.lean`: Jensen inequality `log‖f c‖ ≤ circleAverage log‖f‖`; Poisson kernel bounds; `re_le_of_exp_mul_eq` (Poisson–Jensen ceiling for `g` with `exp g · Z = N`); `norm_deriv_le_of_exp_mul_eq` (Borel–Carathéodory + Cauchy derivative bound).
  - `RHTower/PrimeDeletionLogDerivativeCeiling.lean`: `exists_norm_deletedLogDeriv_le_log` — the continued `−ζ_Q'/ζ_Q` (form `z(Σ c_ρ/(z−ρ) + ∫…)`) is `O(log t)` on `Re s = σ ∈ (max(θ,η), 1]`.
  - `RHTower/PrimeDeletionWindowedMeanSquare.lean`: Gaussian window `exp((s−σ−iT)²/W²)`, rectangle shift to `Re s = 3`, exact Fourier formula; `windowed_meanSquare_ge` (linearized head mass).
  - `RHTower/PrimeDeletionSquareRootFloor.lean`: `not_isBigO_qFreeCount_of_leading_chebyshev` (general `ψ_Q = Σ_{ρ∈J} c_ρ x^ρ + O(x^η)`, leading `c_κ > 0`, `θ, η < κ/2`, `κ ≤ 1`) and `not_isBigO_qFreeCount_of_multiplicity` (every `l > 0`, i.e. every λ, odd or even).
  - Formal windows differ from the paper: Gaussian `W = u²`, `T = u⁴`, head `N = ⌊u⌋` in place of `sinc^{2m}`; the log-derivative `ζ_Q'/ζ_Q` is bounded in place of `log ζ_Q`.
- 2026-09-29 — complex exponents (MC loop cycle 91): `not_isBigO_qFreeCount_of_leading_chebyshev_complex`. Take finitely many complex exponents with `Re ρ < κ` for `ρ ≠ κ`, leading `Re c_κ > 0`, `η < κ/2`, `κ ≤ 1`. The poles of the continued `L(Λ_Q)` then sit at bounded height `B = Σ|Im ρ|`. The ceiling discs (centre `3+it`, `t ≥ d+3δ+3+|B|`) and the Gaussian rectangle `[σ,3]×[T/2,3T/2]` (`T/2 ≥ B+1`) avoid them. The real theorem is now a corollary. An imitated off-line zero of any multiplicity is a secondary term, so it never beats `κ/2`.
- Open beyond finite `J`: an infinite family of poles with `Re w ≥ κ/2` near every height breaks the linearization. This happens when `ψ_Q` inherits ζ's critical oscillation with multiplicity other than 0 or full. See loop cycle 91.
- 2026-09-29 — refactor (cycle 95). The analytic lemmas are now general in an integer-supported pair `(a, e)`, namespace `RHTower.IntegerBeurling`: `exists_norm_pertLogDeriv_le_log`, `exists_log_ratio_on_ball`, `norm_windowed_line_integral_sub_le`, `windowed_meanSquare_ge` (signed heads), `head_mass_le_of_log_bound`, and `not_isBigO_count_of_leading_chebyshev`. The deletion theorems keep their names in `RHTower.PrimeDeletion` and are instances (`a = 1_S`, `e = Λ_Q`). Generalization card: `3-formalized/integer-supported-beurling-half-dimension-floor.md`.
