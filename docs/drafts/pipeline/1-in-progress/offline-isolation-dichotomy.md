# Off-line isolation dichotomy from the unconditional Montgomery form

- **ID:** `offline-isolation-dichotomy`
- **Stage:** 1-in-progress (verdict recorded; no Lean planned)
- **Type:** CONJECTURE → REDISCOVERED (mechanism-different); route-independent constraint on how RH can fail
- **Source:** Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, *An unconditional Montgomery theorem for pair
  correlation of zeros of the Riemann zeta-function*, Acta Arith. 214 (2024), arXiv:2306.04799; Maynard–Pratt,
  *Half-isolated zeros and zero-density estimates*, arXiv:2206.11729; corpus `claude-zeta23-rank-trace-audit.md`.
- **Statement (proved on paper, clean version).** Let `ρ = 1/2 + δ + iγ` run over the zeros with `0 < γ ≤ T`,
  `x = T^α`, `0 ≤ α ≤ 1`, `L = log T`, and let `M` bound the number of zeros in any unit ordinate interval
  (`M ≍ log T`). Fix `Θ ≥ 1` and put `A(Θ) = {ρ : x^{δ} ≥ Θ}`. **If every two distinct elements of `A(Θ)` are at
  ordinate distance `≥ 10`, then** `Σ_{ρ : x^{δ} ≥ 96 M Θ} x^{2δ} ≤ 2 F(x,T) + 10⁴ M² Θ² ·#A(Θ)`, where
  `F(x,T) = Σ_{ρ,ρ'} x^{ρ+ρ̄'−1} w(ρ+ρ̄'−1)`, `w(u) = 4/(4−u²)`, is the BGSTB form, and unconditionally
  `F(T^α,T) = (T/2π) log T · (α + T^{−2α} log T + O(1/√log T))`. With `Θ = 1` the loss term is `≤ 10⁴ M² · T/10`
  (10-spaced sets have at most `T/10` elements), so the useful conclusion is: **the zeros with `T^{δ} ≥ K L³` that
  are pairwise 10-spaced *and* whose companions below threshold are only on-line-type zeros satisfy the
  density-hypothesis count `N ≪ T^{1−2δ} log T`.**

## Why the form detects spaced zeros (paper proof)

`F(x,T) = (2/π) ∫_ℝ |Σ_ρ x^{δ+iγ} / (1 + ((t−γ)+iδ)²)|² dt` exactly (BGSTB (2.8)), i.e. `F = ‖Σ_ρ g_ρ‖²` in
`L²(dt)` with `g_ρ(t) = x^{δ} x^{i(γ−t)} k_δ(t−γ)`, `k_δ(s) = 2/(1+(s+iδ)²)`, `|δ| < 1/2`.
Elementary bounds: `‖g_ρ‖² ≥ π x^{2δ}` (`|1+(s+iδ)²|² ≤ 2(1+s²)²`), and
`|⟨g_ρ, g_ρ'⟩| ≤ x^{δ+δ'} · 29/(3 + (γ−γ')²)` (`|1+(s+iδ)²| ≥ 3/4 + s²` and the Lorentzian convolution
`∫ ds/((3/4+s²)(3/4+(s−Δ)²)) = (2π/√(3/4))/(3+Δ²)`).
Split `Z = A ∪ R`, `R = {x^{δ} < Θ}`. Then `F ≥ ‖g_A‖² − 2|⟨g_A, g_R⟩|`;
10-spacing gives `‖g_A‖² ≥ (π − 0.84) Σ_A x^{2δ}` (`Σ_{m≥1} 58/(3+100m²) ≈ 0.84`);
the local count gives `|⟨g_A, g_R⟩| ≤ Σ_A x^{δ} · Θ · 55 M`. Hence
`F ≥ Σ_A x^{δ}(2.3 x^{δ} − 110 M Θ)`, and the elements with `x^{δ} ≥ 96 M Θ` contribute `≥ 1.15 x^{2δ}` each while
the others contribute `≥ −10⁴ M² Θ²` each. ∎

The positivity is the whole mechanism: a spaced sub-configuration cannot cancel against the rest because the
cross terms are bounded by the *absolute* far field, which the local zero count controls.

## Where the refined version breaks (the wall, made exact)

One would like isolation only from *other significantly off-line* zeros, allowing arbitrary on-line zeros
nearby. The cross term `⟨g_A, g_B⟩` with a clustered set `B` of large `x^{δ}` at distance `≥ 10` is not
controlled by `Σ_A x^{2δ}`: `B` may be charge-balanced (`Σ_{k∈B} x^{δ_k} x^{iγ_k}(smooth) ≈ 0`, invisible to
`F`) yet dipole-unbalanced, with far field at distance `D` of size `≍ x^{δ} · #B · width/D³`. With `#B ≤ M ≍
log T` and width `≍ δ` this can mask an isolated zero of the same displacement at `D = 10` once
`δ log T ≳ 10³`. So isolation must be measured against multipole-balanced clusters, and the clean theorem
needs global spacing above a threshold. This is the same obstruction Maynard–Pratt name: vertical arithmetic
progressions with difference `2πc/log T` make every short zero-detecting polynomial small; in the Montgomery
form the invisible configuration is a cluster of width `≲ δ` whose phases `e^{iγ log x}` are balanced over the
effective range `α ∈ [1 − 1/(2δ log T), 1]` (two zeros at ordinate distance `π/log x` already cancel at `α=1`).

## Literature verdict

**REDISCOVERED (mechanism-different).** Maynard–Pratt Corollary 5: the number of half-isolated zeros with
`β ≥ σ`, `γ ∈ [T,2T]` is `≤ T^{2(1−σ)+o(1)}`, via short zero-detecting polynomials and an improved power-sum
inequality (`|Σ_r e^{itθ_r}| ≥ (B₀R)^{−99}` for some `t ∈ [A,2A]`). Their half-isolation asks nearby zeros to
have real part close to `β₀` and to lie above `ρ₀`; the pair-correlation route above asks for spacing among all
zeros above a low threshold. Neither route is unconditional about *all* zeros; both leave exactly the clustered
configurations. No density improvement, no RH content. The pair-correlation route has one advantage worth
keeping: it is a two-line consequence of a mean-square identity, so it transfers verbatim to any family with an
unconditional Montgomery form (primitive Dirichlet `L`, per BGSTB's method).

## Lean disposition

Not built. The finite-multiset core ("a 10-spaced sub-configuration above threshold is detected by the
Montgomery mean square") is elementary, but it consumes BGSTB's Theorem 1, which the corpus does not own
(Montgomery's lemma is available through the explicit-formula modules; the unconditional Fejér second moment
and the Korobov–Vinogradov truncation are not). A port is justified only with a consumer that needs spaced
off-line zeros specifically; the `75%` programme (`zeta23-beyond-bandwidth-one-proportion.md`) does not.

## Log

- 2026-09-07 — conjectured while auditing the Zeta-23 Frobenius-norm evaluation (an isolated off-line pair
  contributes an excess `≍ L² T^{2δ}/δ²` to `‖P+Q‖²_HS`; a `π/log T`-paired cluster contributes `≈ 0`);
  proved the clean spaced-configuration bound on paper from BGSTB (2.8); found the masking obstruction for the
  refined version; located Maynard–Pratt Cor. 5. Verdict recorded; STATUS CANNOT-332 written.

## Sharpening (2026-09-07, second cycle): the exact invisible configuration

Average BGSTB over the scale: `G(T) := ∫_{1/2}^{1} F(T^α,T) dα = (T/2π) log T (3/8 + o(1))` unconditionally, and
`G = (2/π)∫_{1/2}^{1}∫_ℝ |Λ(α,t)|² dt dα` with `Λ(α,t) = Σ_ρ T^{αδ} e^{iαγL} k_δ(t−γ)`, `L = log T`.
Two exact computations decide what can hide in this mean square.

1. **Local clusters cannot hide.** For zeros confined to a window of width `w ≤ 1/2`, expanding
   `e^{i(α−1)(γ_j−γ̄)L}` and `k(t−γ_j)` around `γ̄` shows `Λ ≈ 0` on `α ∈ [1−ε,1]` forces the phase-weighted
   moments `Σ_j e^{iγ_jL}(γ_j−γ̄)^m` to vanish for `m ≤ M` with `M ≍ ε L w`. The local zero count
   `N(t+1)−N(t) ≤ 0.43 log t` caps the number of zeros, hence of killable moments, at `≍ 0.2 L w`, so
   `ε ≲ 0.06` and the cluster is detected at `α ≈ 0.94` with weight `≥ T^{1.88δ}` per zero (up to polylog).
   A finite non-periodic cluster therefore obeys `N ≪ T^{1−1.88δ+o(1)}`, better than Ingham's `1−(4/3)δ`
   — for *that* configuration class only.
2. **Vertical arithmetic progressions hide completely.** For `γ_j = γ₀ + 2πcj/L`, Poisson summation with
   `k̂(ω) ∝ e^{−|ω|}` gives `Λ(α,t) ∝ (L/2πc) Σ_m e^{−|m−cα| L/(2πc)}`, i.e. amplitude
   `T^{−dist(cα,ℤ)/(πc)}`. For `c ≤ 1/(1+2πδ)` this beats the weight `T^{αδ}` for every `α ∈ (0,1]`, so the
   progression is invisible at every scale `x ≤ T`; for `c ≥ 0.37` its density `L/(2πc) ≤ 0.43 L` respects the
   local count. Hence **the configurations invisible to all bandwidth-`≤1` statistics are near-vertical
   arithmetic progressions of off-line zeros with common difference `2πc/log T`, `0.37 ≲ c ≤ 1/(1+2πδ)`**,
   i.e. spacing between `0.37` and `1` mean spacings, on a line at displacement `δ < 0.27`. This is
   Maynard–Pratt's barrier ("`S_Y(ρ₀)` small for all `Y < T^{1/c−ε}`") with the Montgomery-form
   exponent and the admissible `c`-range made explicit.

`[OPEN CORE]` Inverse theorem: prove that `‖Λ‖_{L²(α∈[1−ε,1], t)}` small forces near-AP structure
(perturbations of finitely many progressions). With it, every off-line zero not in such a progression
would satisfy `N ≪ T^{1−(2−O(ε))δ}` unconditionally — a structural zero-density theorem, not RH.
`[LEAN, brick 1]` `RHTower/MontgomeryFormLogScaleMeanSquare.lean`: for every finite family in `0<Re ρ<1`,
`Σ_{j,k} x^{ρ_j+ρ̄_k−1} w(ρ_j+ρ̄_k−1) = ∫ e^{−2|ξ|} |Σ_j (xe^{−ξ})^{ρ_j−1/2}|² dξ` (`montgomeryForm_eq_integral`), hence real and
`≥ 0` (`montgomeryForm_re_nonneg`). This is the exact object behind every statement above; BGSTB's Theorem 1 itself is
the target of `unconditional-montgomery-pair-correlation-programme.md`.

## Correction and third cycle (2026-09-07): infinite progressions are impossible; periodic block arrays are the true evaders

1. **An infinite vertical progression violates the argument principle.** `N(t+ℓ) − N(t) ≤ (ℓ/2π) log t + 0.224 log t + o(log t)`
   (Trudgian's `|S(t)| ≤ 0.112 log t + …`). A progression with spacing `2πc/L`, `c < 1`, has `ℓL/(2πc)` zeros on
   length `ℓ`, so `ℓ ≤ 1.41 c/(1−c)`; at the invisibility edge `c = 1/(1+2πδ)` this is `ℓ ≤ 0.22/δ`.
   Progressions are therefore **finite blocks**, and blocks must alternate with gaps to keep the mean density.
2. **A single finite block is detected.** Near `cα ≈ 1` the block's phases alias to the slow frequency
   `(cα−1)L/c`; integrating by parts, a block of `K ≍ 0.035 L/(δc)` zeros contributes to `Λ(α,t)` like two
   endpoint Lorentzians of amplitude `1/(4π²cδ)`. Its energy is a fraction `≍ 0.036/(δL)` of the nominal
   `K T^{2δ}`, so isolated blocks (random block positions) still satisfy `N ≪ δ log T · T^{1−2δ}`.
3. **A periodic array of blocks is invisible.** For blocks repeated with period `D ≍ 0.44/δ`, the zero
   counting measure has Fourier support on `ξ ∈ 2π(m/D + m'/s)`, `s = 2πc/L`; the Montgomery form reads
   `Λ̂(η) = k̂(η) T^{αδ} ρ̂(η − αL)`, and in the passband `|η| ≤ 1` the lattice/block factor is bounded by
   `1/|sin(παc)| ≤ 1/(2πδ)`. The whole array, with `N` zeros, therefore has energy `≍ T^{2αδ}/δ³` — `O(1/δ³)`
   effective zeros in total. Inter-block cancellation is exact for a lattice and survives the `S(t)` constraint.
   Random or quasi-random block positions destroy it (point 2).

**Corrected law.** What every bandwidth-`≤1` statistic cannot see is a *periodic, or near-periodic, array
of finite vertical-progression blocks* (block spacing `2πc/L`, `0.37 ≲ c ≤ 1/(1+2πδ)`, block length
`≤ 1.41c/(1−c)`, period `≍ 0.44/δ`) — equivalently a zero counting measure whose exponential sums
`Σ_γ e^{iγξ}` carry no energy in the band `L/2 ≤ |ξ| ≤ L` (all their energy sits at `|ξ| ≥ L/c`). Maynard–Pratt's
one-sided short-scale detector (`Y = T^{o(1)}`) sees the bottom zero of each block when real parts are rigid
(their Hypothesis F, Theorem 1); unconditionally the evaders also need real parts varying at scale `≳ 1/log T`
so that no block bottom is half-isolated (their §8).

**Corpus source objects against this configuration.** The lag function `a_n = Σ_ρ n^{ρ−1/2}/(ρ(1−ρ))` is
coherent on a `c`-progression exactly at `log n = L/c ≥ (1+2πδ)L`, i.e. `n ≥ T^{1+2πδ}`: it sees the
configuration only through primes beyond `T^{1+2πδ}`, where its prime side is the RH-equivalent lag
ceiling (MUST-236–256). The constrained Weil forms at aperture `S` read frequencies `|ξ| ≤ S/2·(…)` and are
blind for the same reason (CANNOT-330). No corpus object detects the periodic array unconditionally; the
wall is exactly: **primes beyond `T^{1+2πδ}` at height `T`, or a source law that sees a periodic block
structure of the zero measure at frequencies `≥ L/c`.**
