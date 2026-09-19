# Off-line isolation dichotomy from the unconditional Montgomery form

- **ID:** `offline-isolation-dichotomy`
- **Stage:** 1-in-progress (verdict recorded; the spaced-configuration survivor is in Lean, see "Lean disposition")
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

**Built (2026-09-07).** `formal/GaloisForLFunctions/RHTower/MontgomerySpacedDetectionCore.lean` and
`RHTower/MontgomerySpacedZeroDetection.lean` (axiom-clean, wired), consuming the unconditional pair-correlation
budget `RHTower.tendsto_montgomeryForm_div_leadingOrder` of `unconditional-montgomery-pair-correlation-programme.md`.
With `a_ρ = x^{Re ρ − 1/2}` (`zeroAmp`), `F(x,T)` the Montgomery form over `zeroWindow T` (all zeros with
`0 < γ ≤ T`, with multiplicity), `L_T = C + log(T+4)` (`windowLog`), and `A(Θ) = {ρ : a_ρ ≥ Θ}`:

- `spaced_configuration_energy` (finite, zeta-free): a Hermitian pair array with `Re P_jj ≥ a_j²`,
  `|P_jk| ≤ 4 a_j a_k w_jk`, nonnegative sub-blocks, internal weights `Σ_{k∈A, k≠j} w_jk ≤ 1/25` and total
  weights `Σ_k w_jk ≤ 8L` satisfies `Σ_{a_j ≥ 200ΘL} a_j² ≤ 2 Re Σ_{Z×Z} P + 25600 Θ² L² #A`.
- `sum_inv_three_add_sq_le_of_spaced`: for a `10`-spaced family, `Σ_{k≠j} 1/(3+(γ_j−γ_k)²) ≤ 1/25`
  (injection of each side into `ℕ_{≥1}` through `⌊|γ_j−γ_k|/10⌋`).
- `spaced_zero_detection (hx : 1 ≤ x) (hT : 0 ≤ T) (hΘ : 0 < Θ) (hsp : A(Θ) pairwise 10-spaced)`:
  `Σ_{ρ ∈ Z, a_ρ ≥ 200 Θ L_T} a_ρ² ≤ 2 Re F(x,T) + 25600 Θ² L_T² · #A(Θ)`. Entries: `Re F_ρρ ≥ a_ρ²`
  (`zeroAmp_sq_le_pairEntry_self_re`), `|F_ρρ'| ≤ 4 a_ρ a_ρ'/(3+(γ−γ')²)` (`norm_pairEntry_le`, from
  `|4 − u²| ≥ 3 + (Im u)²` for `|Re u| < 1`); cross terms with the rest through the corpus Lorentzian
  zero mass `lorentzMass_le_log`; the rest through `montgomeryForm_re_nonneg`.
- `card_spaced_le`: a `10`-spaced family in the window has `≤ T/10 + 1` members.
- **`eventually_card_spaced_offline_le (hα0 : 0 < α) (hα1 : α < 1) (hΘ : 0 < Θ) (hδ₀ : 0 < δ₀)`**: for all
  large `T`, if `A(Θ)` at `x = T^α` is pairwise `10`-spaced then
  `#{ρ : 0 < γ ≤ T, Re ρ ≥ 1/2 + δ₀} ≤ (α T log T + 25600 Θ² L_T² (T/10 + 1)) / T^{2αδ₀}` — the
  density-hypothesis count `≪ T^{1−2αδ₀} log² T` for spaced configurations, unconditionally, every fixed `α < 1`.

Not built: the `α → 1` endpoint (needs the uniform pair-correlation asymptotic), the cluster and block
statements of the second and third cycles (paper only).

**Mechanism of the evader in Lean (2026-09-08).** `formal/GaloisForLFunctions/HTGeometry/NyquistLatticeSum.lean`
(wired, axiom-clean): `tsum_lattice_eq_integral_of_fourier_vanishes (f : SchwartzMap ℝ ℂ) (hs : 0 < s)
(hband : ∀ ξ, 1/s ≤ |ξ| → 𝓕 f ξ = 0) (x) : Σ_{n∈ℤ} f (x + n s) = s⁻¹ ∫ f` — Poisson summation on the lattice
`x + sℤ` keeps only the zero mode when `f` is band-limited below the lattice's Nyquist frequency `1/s`. Applied
to `f = (weight profile) · (test function)`, this is the exact form of the tapered-block invisibility: a block on an
AP of spacing `2π/L'` with weights of Fourier width `μ` is indistinguishable from its continuum average by every
test of exponential type `< L' − μ`, for every position of the block. Tools: `fourier_comp_mul_pos`
(dilation law of `𝓕`), `schwartzScale` (dilated Schwartz map), `fourier_zero_eq_integral`.

## Fourth cycle (2026-09-07): periodic arrays of sharp blocks obey the density count; tapered AP blocks do not

**Sharp blocks (all `δ_j = δ` in the block).** Re-deriving the third cycle's point 3 with Parseval on the comb: for a
periodic array of `B` blocks (`K` zeros each, spacing `s = 2πc/L`, period `D`) the passband energy at fixed `α` is
`x^{2δ} ∫ e^{−2|η|} |block(αL−η)|² |comb(αL−η)|² dη`. The comb factor has mean square exactly `B` over any `η`-interval
of length `≥ 2π/D` (Parseval), and its peaks (spacing `2π/D`, `D > Ks`) cannot all sit on the zeros of the block
factor (spacing `2π/(Ks)`, a coarser lattice); the block factor averages to `1/(2 sin²(παc)) = O(1/ε²)` for
`αc ≤ 1 − ε`. So the array has `≍ B/ε²` effective zeros — each sharp block counts as `O(1)` zeros instead of `K` —
and the third cycle's "`O(1/δ³)` in total" is the case `B ≍ 1/δ`. Since `K ≤ 0.22 L/(1−c) ≤ 0.036 L/δ` (argument
principle), periodic arrays of sharp blocks obey the pair-form count `N ≪ T^{1−2αδ} L²/(δε²)`, like spaced sets.

**Tapered blocks evade everything at bandwidth `≤ 1` (new, paper).** Let a block consist of `K` zeros on an exact
arithmetic progression of spacing `s = 2π/L'`, `L' = L(1+Δ)`, over a window of length `w`, with displacements
`δ_j = δ(γ_j)` following an analytic bump profile of height `δ₀` that vanishes at both ends. Relative to on-line
zeros at the same positions, the block's contribution to the zero sum at frequency `ξ` is
`Σ_j (x^{δ_j} − 1) e^{iξγ_j} = e^{iξγ₀} (1/s) Σ_m ĥ(ξ + mL')`, `h = x^{δ(·)} − 1` (Poisson summation). The `m = 0`
term is a saddle-point integral: for the parabolic profile, `|ĥ(ξ)| ≈ x^{δ₀} T^{−(ξ/L)² w²/(4δ₀)}` plus the endpoint
corner `O(δ₀/(wL))`; for `w ≥ 2` and `α ≥ 1/4` this is `O(1)` for every `δ₀ ≤ 1/2`. The alias `m = −1` is `O(1)`
once `Δ ≥ 2δ₀√α/w` (e.g. `w = 2`, `δ₀ = 1/4`: `L' = 1.25 L`, a density excess `0.08 L` over the block, within
Trudgian's `0.224 L`). Hence **a tapered AP block contributes `O(1)` energy to the pair form at every `α ≤ 1`,
independently of its `K ≈ 0.16 wL` off-line zeros**; averaging over `α` does not help (the bound is uniform in
`ξ ∈ [L/4, L]`), and no periodicity is needed. The third cycle's "single blocks are detected through their two
endpoints" holds only for sharp profiles (endpoint weight `x^{δ}`); a taper puts weight `x^0 = 1` at the ends.
What the block still costs: positions exact to `T^{−αδ_j}` (the AP must hold to that precision), and BGSTB's
`F(α) → α` forces the proportion of all zeros lying in such blocks to vanish (an AP block has energy `O(1)`
instead of `≍ αK`).

**Corrected law.** The configurations invisible to every bandwidth-`≤ 1` statistic are the **tapered
arithmetic-progression blocks** (near-mean spacing, analytic displacement profile), sparse among all zeros; a block
of length `w` hides displacements up to `δ₀ ≤ w√α/2`, so `w ≥ 2` hides everything and a cluster of width `1/2`
still hides `δ₀ ≤ √α/4`. The second cycle's "local clusters cannot hide" rested on Taylor-moment counting, which is
not a lower bound (Nazarov's Turán lemma allows an exponential polynomial with `K ≍ log T` terms to be
`(c·|E|/|I|)^{K}`-small on a band `E`); it is superseded. The pair form gives the density-hypothesis count for
spaced sets (Lean above) and for sharp blocks and their periodic arrays (this cycle, up to polylog); it gives nothing
for tapered blocks or tapered clusters. Consequently the `[OPEN CORE]` inverse theorem, even if true
("small passband energy ⟹ union of AP blocks"), does not yield a density theorem: the route from the pair form to
the density hypothesis is closed, and the lane's ceiling is the spaced/cluster/sharp-block count. Excluding tapered
blocks needs, as before, primes beyond `T^{1+Δ}` at height `T` or a source law that reads the zero measure at
frequencies `≥ L'`.

**Analytic rigidity does not exclude them (conjecture killed, 2026-09-07).** Conjecture: an entire function with
`ξ`'s order, type, functional equation and reality on the critical line cannot carry a tapered AP block of zeros to
precision `T^{−δ_j}`. False: the Hadamard product over any zero set with the block, its mirror under `s ↦ 1−s` and
conjugation, and the Riemann–von Mangoldt counting density satisfies all four properties. Only the Euler product
can forbid the block, and it does so only through primes beyond `T^{1+Δ}` (Landau's formula at `x > T` has error
`x log x`). Verdict for this lane: `NO POSITIVE SALVAGE` beyond the spaced-set theorem; the lane is closed.

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
- 2026-09-07 (fourth cycle) — spaced-configuration survivor formalized (`spaced_zero_detection`, `eventually_card_spaced_offline_le`); Parseval re-derivation shows periodic block arrays obey the same density count (saving ≤ block length ≤ 0.036 L/δ); the inverse-theorem open core is identified as DH-hard.
- 2026-09-07 (fourth cycle, corrected) — tapered AP blocks (analytic displacement profile) have `O(1)` pair-form energy at every `α ≤ 1`: the route from the pair form to DH is closed; the evader class is enlarged, the spaced-set Lean theorem stands.

## Spacing threshold of the survivor (2026-09-08, paper)

The Lean count assumes ordinate spacing `≥ 10` only to make the crude cross-term bound
`Σ_{k≠j} 1/(3+(γ_j−γ_k)²) ≤ 1/25` work. The true threshold is any fixed positive spacing: for `s`-separated ordinates the
Lorentzian Gram form `Σ_{j,k} c_j c̄_k · 2π/(4+(γ_j−γ_k)²) = ∫ |Σ_j c_j e^{−iγ_jη}|² |L̂(η)|² dη` with `L̂(η) = π e^{−|η|}`, and the
Montgomery–Vaughan lower bound on the band `|η| ≤ 3π/s` (corpus `MVHilbert`) gives
`≥ π² e^{−6π/s} · (3π/s) · Σ|c_j|²`. So the spaced detection theorem holds for every `s > 0` with the diagonal constant
`π/2` replaced by `c(s) = (3π³/s) e^{−6π/s}`, and the density count for `s`-spaced off-line zeros is
`≪_s T^{1−2αδ₀} log² T`. The dividing line of the dichotomy is therefore exact: spacing bounded below (any bound) is
detected at density-hypothesis strength; only spacing `≍ 1/log T` (the tapered AP blocks) evades. Not formalized: it needs
Plancherel for Lorentzian sums and the Fourier transform of `1/(1+t²)`, neither of which the pair-form modules use.

## Fifth cycle (2026-09-08): isolation at the mean-gap scale — conjecture, obstruction, survivor

**Conjecture (isolation–density law).** Fix `Δ > 0`, `δ > 0`. If a set `𝒵` of zeros with ordinates in `(0, T]` has pairwise
ordinate gaps `≥ (1+Δ)·2π/log T` (the mean gap times `1+Δ`), then `#{ρ ∈ 𝒵 : Re ρ ≥ 1/2+δ} ≪_{Δ,δ} T^{1−2δ·Δ/(1+Δ)+o(1)}`.
Its content: a violation of RH at density `T^{1−o(1)}` must consist of zeros packed at least as densely as the mean gap;
together with the tapered-block evader (fourth cycle) this would make the mean gap the exact threshold of the dichotomy.
Literature (arXiv 2306.04799, 2501.14545, Bui–Milinovich / Bredberg gap papers): gap results are for on-line zeros; no
statement links isolation of off-line zeros to their density. Verdict on the statement: `SURVIVES PRELIMINARY ATTACK`.

**Mechanism tried and its obstruction.** The pair form is a Bochner form in either the scale variable `α` (`x = T^α`) or the
Laplace variable `ξ` (`montgomeryForm_eq_integral`: `∫ e^{−2|ξ|} ‖Σ_j (x e^{−ξ})^{ρ_j−1/2}‖²`). A set with ordinate gaps
`(1+Δ)·2π/log T` has frequencies `u_j = γ_j log T/2π` with gaps `1+Δ`, and the Montgomery–Vaughan mean value gives
`∫_a^{a+ℓ} |Σ c_j e(u_j α)|² ≥ (ℓ − 1/(1+Δ)) Σ|c_j|²` (sharp constant) — so an `α`-window of length `> 1/(1+Δ)` detects the
set **if the coefficients are constant**. They are not: the off-line amplitude is `T^{α(β_j−1/2)}`, which varies over the
window by `T^{ℓδ}`, while the window cannot be shortened below `1/(1+Δ)`. Bottom-amplitude bounds (`|S(α)| ≥ T^{aδ}|S₀+E|`)
rescue a single narrow real-part band `β ∈ [σ, σ+τ/log T]` (power-series splitting of `T^{α(β_j−σ)}`, MV upper bounds for
the corrections), but the cross terms between different bands need the *top* amplitude of the lower band against the
*bottom* amplitude of the upper band, and these differ by `T^{ℓ·Δβ}`: the argument does not close for two or more bands.
The `ξ`-route at fixed `x` has pointwise cross-term control (as in `spaced_configuration_energy`) but the amplitude
`e^{−(β_j−1/2)ξ}` over the MV window `|ξ| ≤ W` forces `W = O(1)`, i.e. fixed ordinate gaps (`≳ 8` with the sharp constant,
`≳ 52` with the corpus constant `26`) — the regime the Lorentzian argument already covers with gap `10`. The fourth
cycle's constant `(3π³/s)e^{−6π/s}` for "any fixed `s`" omitted this amplitude factor; the qualitative claim stands
(fixed `s`), the constant acquires an extra `e^{−cδ/s}`.

**Exact state.** The law is `[OPEN CORE]` at the mean-gap scale for zeros of two or more distinct real-part bands.
Provable survivor (paper): the single-band case — if every zero with `Re ρ ≥ 1/2+δ₀`, `T < γ ≤ 2T`, has
`Re ρ ∈ [σ, σ+τ/log T]` with `σ − 1/2 ≥ 3δ₀` and the set is `(1+Δ)`-mean-spaced, then its cardinality is
`≪ T^{1−2(Δ/(1+Δ)−η)(σ−1/2)} log T`. This is the same shape of hypothesis as BGSTB II (all zeros in a box of width
`b/log T`) transported to a box away from the line.

**Lean (2026-09-08).** `HTGeometry/MontgomeryVaughanIntervalMeanSquare.lean`:
`interval_integral_normSq_expSum_ge`: for frequencies with pairwise gaps `≥ D` and any coefficients,
`(ℓ − 26/(πD)) Σ‖c_r‖² ≤ ∫_a^{a+ℓ} ‖Σ_r c_r e^{2πi u_r α}‖² dα` (from the corpus `MVHilbert 26`; axioms clean, wired).
This is the constant-coefficient detection step; the single-band theorem needs in addition a uniform-in-`α` upper bound for
the corpus pair form on `[a, a+ℓ]` (the capstone is pointwise in `α`) and the band perturbation lemma.

**Refinement (same cycle): what the scale-window method can and cannot resolve.** Flattening the pair form by
`T^{−2α(σ−1/2)}` makes one band's coefficients constant and all lower bands' coefficients decaying, so MV upper bounds
control the lower bands by their values at the window's bottom. For **two bands** (`δ₁ < δ₂`, counts `N₁, N₂`) this closes:
let `α_c` be the crossover of the energy lines `N_i T^{2αδ_i}`; a window of length `ℓ` ending just below `α_c` detects the
lower band (`N₁ ≪ T^{1−2(α_c−ℓ)δ₁} log T`), a window starting just above `α_c` detects the upper band, and whichever side has
room in `[η, 1−η]` gives an explicit bound for both (`Δ > 1` with the sharp MV constant, `Δ > 15.6` with the corpus
constant `26`). For **many bands** the energy envelope `E(α) = max_i N_i T^{2αδ_i}` is convex and piecewise linear; a band is
detected only if it dominates `E` on an interval of length `≥ ℓ`, and bands dominating in the gaps are bounded by the
chords of `E` between detected windows. This fails when *no* band dominates for length `ℓ`: a **ladder configuration** —
`≥ 2(1+Δ)` bands with counts `N_i ≈ N_{i+1} T^{2α_i(δ_{i+1}−δ_i)}` whose crossovers `α_i` are spaced below `1/(1+Δ)` — is
spaced, multi-band, and invisible to every scale window; and the top band always escapes when its dominance interval
`[α_c, 1−η]` is shorter than `ℓ`. Ladders are the third evader class after tapered blocks and periodic arrays, and they are
the exact reason the real-part resolution of the averaged pair form is `ℓ·δ` (window length times distance from the line)
rather than `1/log T`.

**Two-band isolation theorem — paper proof (2026-09-08, later).** Notation: `L = log T`, `u_j = γ_j L/2π`, pair form
`F(α) = ∫ e^{−2|ξ|} |Σ_ρ (T^α e^{−ξ})^{ρ−1/2}|² dξ`, uniform bound `F(α) ≤ 2 (T/2π) α L` on `[η, 1−η]` (Lean:
`eventually_montgomeryForm_div_leadingOrder_uniform`). Hypotheses: every zero with `Re ρ ≥ 1/2+δ₀` and `0 < γ ≤ T` lies in
`A = A₁ ∪ A₂`, `Re ρ ∈ [σ_i, σ_i+τ/L]` on `A_i`, `δ_i := σ_i − 1/2`, `δ₁ ≥ 3δ₀`, `τ ≤ 1/10`, and `A` is `D`-separated in
`u` (`D = 1+Δ`). Window length `ℓ` with `ℓ − 26/(πD) ≥ c₀ > 0` (corpus MV constant; sharp: `ℓ − 1/D`); windows
`[a, a+ℓ]` are used only with `a ≥ 2ℓ`, `a+ℓ ≤ 1−η`, so `3ℓ ≤ 1−η` (`D ≥ 30` with the corpus constant, `D ≥ 3.1` sharp).
1. *R-part.* With `R` = the other zeros (`a_k(α) = T^{α(Re ρ_k −1/2)} ≤ T^{αδ₀}`), the corpus's pointwise bounds
   (`norm_pairEntry_le`: `|P_jk| ≤ 4a_ja_k w_jk`, `w_jk = 1/(3+(γ_j−γ_k)²)`, `Σ_k w_jk ≤ 8L`, `F_RR ≥ 0`) give
   `F(α) ≥ F_AA(α) − 64 L T^{αδ₀} Σ_{j∈A} a_j(α)` at every scale; integrated over the window this cross term is
   `≤ 64ℓL T^{b(δ₀+δ_i+τ/L)} N_i` per band, and `b(δ₀+δ_i) ≤ 2aδ_i − aδ₀` when `a ≥ 2b/3` and `δ₀ ≤ δ_i/3`, so it is
   `≤ N_i T^{2aδ_i − aδ₀} · 64ℓLe^{τ}` — negligible against the detection term `c N_i T^{2aδ_i}`.
2. *Bochner form and flattening.* `F_AA(α) = ∫ e^{−2|ξ|} |S_A(α,ξ)|² dξ`, `S_A = Σ_{j∈A} T^{α(β_j−1/2)} d_j(ξ) e(u_jα)`,
   `d_j = e^{−(ρ_j−1/2)ξ}`; restrict to `|ξ| ≤ 1` (`|d_j| ∈ [e^{−1/2}, e^{1/2}]`, weight `≥ e^{−2}`). Flattening at band `i`:
   `S_A = T^{αδ_i}(P_i + Q_{i'})` with `P_i = Σ_{A_i} e^{θ_jα} d_j e(u_jα)`, `θ_j = (β_j−σ_i)L ∈ [0,τ]`, and `Q_{i'}` the
   other band with coefficients `T^{α(β_j−σ_i)} d_j`.
3. *Band perturbation.* `e^{θα} = Σ_{n<K} θ^nα^n/n! + R_K`, `|R_K| ≤ (τb)^K e^{τb}/K!` (`Real.exp_bound`). Hence
   `‖P_i − P_i^{(0)}‖_{L²[a,b]} ≤ (e^{bτ}−1)√((ℓ+26/(πD)) Σ|d_j|²) + √ℓ N_i e^{1/2}(τb)^K e^{τb}/K!`, where
   `P_i^{(0)} = Σ d_j e(u_jα)` has constant coefficients and `‖P_i^{(0)}‖² ≥ (ℓ − 26/(πD)) Σ|d_j|²` (Lean:
   `interval_integral_normSq_expSum_ge`); with `K = ⌈log₁₀ N_i⌉+1` the remainder is `≤ √ℓ e^{1/2} e^{τb}` and
   `‖P_i‖² ≥ c₁ N_i` for `τ ≤ 1/10`, `N_i ≥ N₀(c₀)`.
4. *Two windows at the crossover.* Let `α_c` solve `N₁ T^{2α_cδ₁} = N₂ T^{2α_cδ₂}` (if `N₂ ≥ N₁` take `α_c = 0`, if
   `N₁ ≥ N₂ T^{2δ₂−2δ₁}` take `α_c = 1`). Lower window `[a,b]` with `b = α_c − ε'`, `ε' = 2/((δ₂−δ₁)L)·log(8e(ℓ+26/(πD))/c₁)`:
   `‖Q₂‖² ≤ (ℓ+26/(πD)) e N₂ T^{2b(δ₂−δ₁)+2bτ/L} ≤ c₁N₁/8`, so `∫_a^b |S_A|² ≥ T^{2aδ₁}(‖P₁‖−‖Q₂‖)² ≥ c₁ N₁ T^{2aδ₁}/4`
   and, with 1., `N₁ ≤ (32/c₁) e² (2/2π) ℓ T^{1−2aδ₁} L + …`, i.e. `N₁ ≪ T^{1−2aδ₁} L`. Upper window with `a = α_c + ε'`:
   symmetric, `N₂ ≪ T^{1−2aδ₂} L`. Windows must satisfy `2ℓ ≤ a`, `a+ℓ ≤ 1−η`; when the crossover leaves no room on one
   side, that band is bounded through the crossover identity by the other band's bound
   (`N₁ = N₂ T^{2α_c(δ₂−δ₁)}`, resp. `N₂ = N₁ T^{−2α_c(δ₂−δ₁)}`). If `δ₂−δ₁ ≤ 2τ/L` the two bands are one band of width
   `3τ/L` and step 3 alone applies.
5. *Conclusion.* `N₁ + N₂ ≪_{Δ,δ₀,η} T^{1−c(Δ,η)δ₀} (log T)^2` with explicit `c > 0`; for a crossover in the interior
   both bands obey `T^{1−2(α_c∓ε'∓ℓ)δ_i} L`.
Lean plan: (i) MV upper bound (same module), (ii) Taylor band-perturbation lemma, (iii) Bochner form per scale from
`montgomeryForm_eq_integral` with the `A/R` split of `spaced_configuration_energy` transported to the integrated form,
(iv) the crossover case analysis.

**Lean (2026-09-08, later): band perturbation.** `HTGeometry/MontgomeryVaughanBandPerturbation.lean` (wired, axioms clean):
`interval_integral_normSq_expSum_le` (MV upper bound, same module as the lower bound) and
**`interval_integral_normSq_mvBandSum_ge`**: for `0 ≤ θ_r ≤ τ ≤ 1`, `[a,a+ℓ] ⊆ [0,1]`, `D`-separated frequencies, any
`K ≥ 1`, `(½(ℓ − 26/(πD)) − 2K(ℓ+26/(πD)) Σ_{1≤m<K}(τ^m/m!)² − 2ℓ N ρ_K²) Σ‖d_r‖² ≤ ∫_a^{a+ℓ} ‖Σ_r d_r e^{θ_rα} e(u_rα)‖²`,
`ρ_K = τ^K (K+1)/(K!K)`. Mechanism: `mvBandSum_eq` (finite Taylor split into constant-coefficient layers `mvPowerSum` and
the remainder `mvRemSum`), `Real.exp_bound` for the remainder, Cauchy–Schwarz on the layers, MV upper bound per layer.
This is step 3 of the two-band proof; remaining: the Bochner/`A–R` transport of `spaced_configuration_energy` to the
scale-integrated form and the crossover case analysis.

## Single-band isolation law — proved in Lean (2026-09-08, later)

`RHTower/MontgomerySingleBandIsolation.lean` + `MontgomerySingleBandExample.lean` (wired, axioms
`[propext, Classical.choice, Quot.sound]`):

**`eventually_card_singleBand_le`** (parametric): for `0 < a`, `0 < ℓ`, `a+ℓ < 1`, `2(a+ℓ) ≤ 3a`, `δ₀ > 0`,
`σ ≥ 1/2 + 4δ₀`, `D > 0`, `0 ≤ τ ≤ 1`, and `κ > 0` with `κ ≤ mvBandConstant ℓ D τ (N+1) N` for every `N`:
for all large `T` and every finite set `A` of zero copies in the window `0 < γ ≤ T` such that
(i) `σ ≤ Re ρ ≤ σ + τ/log T` on `A`, (ii) `Re ρ ≤ 1/2 + δ₀` off `A`, (iii) the ordinates of `A` are `D`-separated in
mean-spacing units `γ log T/2π`: `#A ≤ (ℓ e³/(πκ)) · T^{1 − 2a(σ−1/2)} · log T`.

**`eventually_card_singleBand_le_example`** (explicit): window `[3/5, 9/10]`, separation `50` mean gaps, band width
`(1/20)/log T`, `κ = 1/20`: `#A ≤ (6e³/π) · T^{1 − (6/5)(σ−1/2)} · log T`.

Chain: uniform capstone (`eventually_montgomeryForm_div_leadingOrder_uniform`) → pointwise block split
(`montgomeryForm_block_split`, Lorentzian cross budget `64 Θ L_T Σ_A a_j`) → Bochner window `|ξ| ≤ 1`
(`montgomeryForm_re_ge_window`) → Fubini → amplitude monotonicity `T^{α(σ−1/2)} ≥ T^{a(σ−1/2)}` → band-perturbation
Montgomery–Vaughan bound (`interval_integral_normSq_mvBandSum_ge`, Taylor order `K = #A + 1`) → `T^{gap}` absorbs the
cross term (gap `≥ (a+ℓ)(σ−1/2)/12`). Content: an RH failure of density `T^{1−o(1)}` cannot consist of one
`1/log T`-band of zeros isolated at `≥ 50` mean gaps while all other zeros hug the line; the multi-band and
mean-gap-scale cases remain the open ladder question. Exponent loss `(6/5)` versus the density-hypothesis `2` is the
window position; the sharp MV constant would allow `D ≥ 3.1` and windows near `α = 1`.

**Lean (2026-09-08, later): two-sided band lemma.** `interval_integral_normSq_mvBandSum_ge` now takes exponents of
either sign (`|θ_r| ≤ τ`), and `interval_integral_normSq_mvBandSum_le` gives the matching upper bound
`(2(ℓ+c) + 8(ℓ+c)Σ τ^{2m}/m! + 4ℓNρ_K²) Σ‖d‖²`. These are the inputs of the multi-band window theorem: flatten at
the band `i*` dominating the energy envelope at both ends of the window; every other band is a `|θ| ≤ τ` band times
a scalar `T^{α(σ_i−σ_{i*})}` bounded by its endpoint value, so `‖S_A‖ ≥ ‖P_{i*}‖ − Σ_{i≠i*} (endpoint scalar)·‖P_i‖`
with the upper bound per band; dominance by a factor `C·(number of bands)²` at both ends closes it.

**Lean (2026-09-08, later): several bands over a scale window.** `RHTower/MontgomeryMultiBandWindow.lean` (wired,
axioms clean): `band_inner_ge`/`band_inner_le` (one band's inner scale integral between
`c_low·e^{−1}·N` and `c_up·e·N`, `c_up = mvBandUpperConstant`), `bandScalarSq` (endpoint value of the relative amplitude
`T^{2α(σ_i−σ_{i₀})}`), `multiBand_inner_ge` and **`multiBand_block_window_ge`**: for a disjoint family of bands
`A_i` with `D`-separated union, flattened at `i₀`,
`2e^{−2} T^{2a(σ_{i₀}−1/2)} (½ c_low(i₀) e^{−1} N_{i₀} − m Σ_{i≠i₀} s̄_i² c_up(i) e N_i) ≤ ∫_a^{a+ℓ} Re F_{∪A_i}(T^α)`,
`m` = number of bands. With the dominance hypothesis `m·s̄_i²·c_up(i)·e·N_i ≤ ¼ c_low(i₀) e^{−1} N_{i₀}/m` for `i ≠ i₀`
(dominance at both window ends), the bracket is `≥ ¼ c_low(i₀) e^{−1} N_{i₀}` and the single-band assembly applies
verbatim to `N_{i₀}` (the cross term needs the lower bands not too far below: `a(σ_i−1/2) ≥ ℓ(σ_{i₀}−1/2) + (a+ℓ)δ₀`).
Remaining: the assembly theorem `eventually_card_dominantBand_le` and the two-band crossover corollary.

## Dominant-band isolation law — proved in Lean (2026-09-08, later)

`RHTower/MontgomeryDominantBandIsolation.lean`, **`eventually_card_dominantBand_le`** (wired, axioms clean): parameters
`0 < a`, `0 < ℓ`, `a+ℓ < 1`, `2(a+ℓ) ≤ 3a`, `δ₀ > 0`, `D > 0`, `0 ≤ τ ≤ 1`, `κ > 0` with `κ ≤ mvBandConstant ℓ D τ (N+1) N`
for all `N`. For all large `T`: for every finite family of pairwise disjoint bands `A_i` of zero copies in the window
(any index type), with base real parts `σ_i ≥ 1/2`, `σ_{i₀} ≥ 1/2 + 4δ₀`, real parts in `[σ_i, σ_i + τ/log T]`,
all other zeros within `δ₀` of the line, the union `D`-separated in mean-spacing units, and
(dominance) `m · Σ_{i≠i₀} s̄_i² · c_up(i) · e · N_i ≤ ¼ κ e^{−1} N_{i₀}` with `s̄_i² = max(T^{2a(σ_i−σ_{i₀})}, T^{2(a+ℓ)(σ_i−σ_{i₀})})`,
(mass) `Σ_i N_i T^{(a+ℓ)(σ_i−1/2)} ≤ 2 N_{i₀} T^{(a+ℓ)(σ_{i₀}−1/2)}`:
`N_{i₀} ≤ (4ℓe³/(πκ)) T^{1−2a(σ_{i₀}−1/2)} log T`.
This is the exact form of "a band dominating the energy envelope at both ends of a scale window is bounded". The
single-band law is the case `m = 1`. The two-band crossover corollary (windows placed just below/above the crossover
`α_c`, so that the dominance and mass hypotheses hold with `T^{−2ε'(δ₂−δ₁)}` margins) is the next assembly; ladders
(no band dominating over any full window) remain the open class.

**Computation (2026-09-08): ladder hiding search.** `2-fully-proven/computations/ladder-hiding-search-2026-09-08/`.
Minimising the maximal pair-form energy over `D = 2`-spaced configurations (`L = 30`), four- and eight-band ladders hide no
better than a single chirped band (`log10 H ≈ −2.4` for all structures, versus the window floor `−4.3` and perfect hiding
`−7.0`). Evidence, not proof, that ladders are not an evader class. Working conjecture (`[OPEN CORE]`): **full isolation
law** — every `D`-separated set of zeros with `Re ρ ≥ 1/2+δ`, `0<γ≤T`, has `≪_D T^{1−c(D)δ+o(1)}` elements, with no
dominance or band hypothesis; the proved cases are one band (CANNOT-336) and a dominant band (CANNOT-337).

## Sixth cycle (2026-09-08): the missing lemma behind the full isolation law

**Reduction.** Write the pair form in the scale variable `y = α log T − ξ`: `F(α) = ∫ e^{−2|α log T − y|} |S(y)|² dy` with
`S(y) = Σ_j d_j e^{(δ_j + iγ_j) y}`, so a scale window `[a, a+ℓ]` is a `y`-window of length `ℓ log T` on a sum with
frequencies `γ_j` (gaps `≥ 2πD/log T`) and growth rates `δ_j ∈ [δ_min, δ_max]`. Factor the top growth:
`|S(y)|² ≥ |S̃(y)|²` on the window, where `S̃` has *decaying* coefficients `e^{−(δ_max − δ_j)(y − a log T)}` and
constant part `d_j e^{δ_j a log T}`. Hence the whole law reduces to one inequality for exponential sums:

**Conjecture (damped Ingham inequality).** For `μ_k` pairwise `≥ g` apart, `0 ≤ ν_k ≤ K`, and `ℓ' ≥ 2/g`,
`∫_0^{ℓ'} |Σ_k c_k e^{−ν_k s} e^{iμ_k s}|² ds ≥ c₀ (ℓ' − 1/g) e^{−2Kℓ'} Σ_k |c_k|²` with an absolute `c₀ > 0`.
With `K = δ_max − δ_min`, `g = 2πD/log T`, `ℓ' = ℓ log T`, the loss is `T^{−2(δ_max−δ_min)ℓ}`, polynomial, and the window
argument then bounds *every* band at once: `N_top ≪ T^{1 − 2aδ_max + 2(a+ℓ)(δ_max − δ_min)} log T`, nontrivial when
`δ_min > δ_max ℓ/(a+ℓ)` (`≈ δ_max/3`). Grouping the real parts geometrically (factor `3`) leaves `O(log(1/δ))` groups,
so for `D ≥ D₀(δ)` some group dominates a full window and the dominant-band theorem (CANNOT-337, with the damped
inequality replacing the constant-coefficient Montgomery–Vaughan step inside a group) bounds it; the crossover identities
bound the rest. This is the exact route to the **full isolation law** for large separation.

**Why the constant must be exponential in `Kℓ'`.** On an interval much shorter than `1/g` the exponentials `e^{iμ_k s}` are
nearly linearly dependent (they are approximately polynomials of degree `< n`), so `n` fast-decaying terms
(`ν_k = K ≫ ng`) can be arranged to give `∫ |·|² ≍ (ng/K)^{2n} Σ|c|²/K`; the claimed floor `e^{−2Kℓ'}` lies below this,
so the near-dependence phenomenon does not refute the conjecture but shows no better than exponential loss is possible
in general. Naive Taylor expansion of the decay (the band-perturbation route) fails for `Kℓ' ≫ 1` because the layers grow
like `(Kℓ')^n/n!`. Corpus status: the bilinear Montgomery–Vaughan inequality (`MVHilbert 26`) is the only Hilbert-type
tool; no Ingham/Riesz-sequence inequality for complex frequencies and no Turán–Nazarov lemma exists. Verdict for the
cycle: the isolation programme is reduced to one clean analytic inequality (`[OPEN CORE]`), falsifiable on small `n`.

**Verdict on the damped Ingham conjecture (2026-09-08, computation `damped-ingham-spectral-test-2026-09-08`): FALSE as
stated.** The minimal Gram eigenvalue of damped exponentials with uniform decay `K > g` decays like `e^{−c(K/g)·n}` in
the number of terms (numerically `c ≈ 1.5` at `K/g = 3`), so no `n`-uniform floor `e^{−2Kℓ'}` exists; the effective
window `1/(2K)` is shorter than the Ingham length and the exponentials become nearly dependent. Correct principle:
**decay spread at most the frequency gap**. In the zero problem this is a real-part band of width `≍ D/log T` — the
natural generalisation of the single-band law (band width `τ/log T` → `cD/log T`), provable by the same method with
polynomial loss. Across wider spreads the Gram matrix can be exponentially degenerate in the number of interacting
zeros (`≍ log T/D` per unit height under the Lorentzian weight), so the full isolation law at fixed `D` cannot come
from Ingham-type bounds; it needs the averaged (Montgomery-weight) structure, i.e. that the actual coefficient
vectors `e^{−(ρ_j−1/2)ξ}` are not adversarial. Open core restated: **why the Laplace phases `e^{−iγ_jξ}` cannot align
with the degenerate eigenvectors of the damped Gram matrix.**

**Correction of the verdict (2026-09-08, later).** The damped Ingham conjecture is *not* refuted: for uniform decay the
floor `e^{−2Kℓ'}(ℓ'−2π/g)` is trivially true and `n`-uniform (pointwise weight comparison plus Ingham), the numerical
decrease in `n` must saturate above it, and the adversary never beat uniform decay. The data (`r` growing with `K`)
indicate a polynomial floor. **Mechanism found:** the half-line damped Gram matrix is the Gram of Cauchy kernels
`1/(ν_j + i(t+μ_j))`; with decay `K ≲` gap `g` the kernels are concentrated on disjoint windows carrying mass
`≈ π|x_j|²/ν_j`, and the cross terms are a Hilbert-type sum (Montgomery–Vaughan, `MVHilbert 26` in the corpus); the
finite window `[0,ℓ']` is the half-line Gram minus the `[ℓ',∞)` Gram, whose norm is `≤ e^{−2εℓ'}λ_max` after a shift
`ν ↦ ν+ε` (`ε ≍ log(Kℓ')/ℓ'`). This gives the **damped Montgomery–Vaughan inequality**: for `0 ≤ ν_k ≤ K ≤ c·g`,
`∫_0^{ℓ'}|Σ x_k e^{−ν_k s}e^{iμ_k s}|² ≥ c₁ (Kℓ')^{−C} Σ|x_k|²/K`, uniformly in `n`. Consequence: the single-band law
extends to real-part bands of width `≍ D/log T` (decay at most the gap), with polynomial loss in `D` only.
Lean plan (new modules): Cauchy-kernel Gram identity on the half-line; disjoint-window own-mass lower bound;
Hilbert cross-term bound from `MVHilbert`; tail subtraction; then replace `interval_integral_normSq_mvBandSum_ge` by the
damped inequality inside `singleBand_block_window_ge`.

## Damped Montgomery–Vaughan in Lean; wide single-band law (2026-09-08)

**Lean modules** (built, wired, axioms `[propext, Classical.choice, Quot.sound]`):
`HTGeometry/MontgomeryVaughanDampedMeanSquare.lean` — `mvPairExponent`, `mvEndCoeff`, `mvHilbertForm`,
`mvDampedRem`, exact decomposition `integral_normSq_mvBandSum_eq`, remainder bound `norm_mvDampedRem_le`
(`|rem| ≤ |d_r|e^{θ_r a}|d_s|e^{θ_s a} K/(π²(u_r−u_s)²)`, from `|w| ≥ |Im w|`), spacing input
`sum_inv_sq_sub_le` (`Σ_{s≠r} 1/(u_r−u_s)² ≤ 9/D²`, from the corpus `Adm.spacing_sq`), Schur/AM–GM
`sum_offDiagonal_weighted_le`, and the theorems `interval_integral_normSq_mvBandSum_ge_damped` /
`_le_damped` (exponents in `[−K,0]`) and `_ge_band` / `_le_band` (exponents in `[θ_top−K, θ_top]`, `θ_top ≥ 0`).
`RHTower/MontgomerySingleBandWide.lean` — `mvWideBandConstant ℓ₀ D τ = ℓ₀e^{−2τℓ₀} − 26/(πD) − 9τ/(π²D²)`,
`singleBand_block_window_ge_wide`, `eventually_card_singleBand_le_wide` (no `τ ≤ 1`, no `a+ℓ ≤ 1` hypothesis),
`mvWideBandConstant_hundred` (`1/(10τ) ≤ mvWideBandConstant (1/(2τ)) (100τ) τ`), and
`eventually_card_singleBand_le_wide_example` (width `τ/log T`, `τ ≥ 5/3`, isolation `100τ` ⟹
`|A| ≤ (3e³τ/π) T^{1−(6/5)(σ−1/2)} log T`).

**What changed mathematically.** No decay-versus-gap hypothesis is needed for the inequality; the constraint
appears only through positivity of the constant, `D ≳ 100 K`. The `K`-dependence is polynomial
(`ℓ₀ e^{−2Kℓ₀}` with `ℓ₀ = 1/(2K)` gives `1/(2eK)`), confirming the corrected reading of the spectral test. The
Taylor band lemma (`τ ≤ 1`) is now superseded. Recorded as CANNOT-338.

**External status.** Qualitatively the damped inequality is Ingham for complex frequencies with bounded real
parts (Komornik–Loreti's book; J. Edward, "Ingham-type inequalities for complex frequencies and applications to
control theory", JMAA 2006, which even allows unbounded imaginary parts). Verdict for the inequality:
REDISCOVERED in qualitative form, BRIDGE with explicit constants. The band consequence for zeta zeros is the
corpus's own.

**Next.** (i) The dominant-band law with wide bands (replace `mvBandUpperConstant` by the `_le_band` bound with
its `e^{2θ_top ℓ}` factor). (ii) The ladder class: with band width `≍ D/log T` a ladder needs many bands per unit
of isolation; combine the wide single-band law with the isolation dichotomy to bound the number of bands a dense
violation can occupy.

## Seventh cycle (2026-09-08): the full isolation law is exactly one strip Ingham bound

**Literature.** Edward (JMAA 2006, "Ingham-type inequalities for complex frequencies"), Theorem 2: gap
`|a_n − a_k| ≥ γ max(π/T, b_n)|n−k|`, `γ > √(10π)`, lower bound with weights `|x_n|²/(1+b_n²)` — the decay-at-most-gap
regime, by Schur diagonal dominance with Ingham's sine cutoff; Theorem 1 needs super-linear gaps `|n^r − k^r|`, `r > 1`.
His Example 3 (Ingham): for `ω_n = n + iδn` no inverse inequality holds. The bounded-strip case with arbitrary `K/g` is the
Riesz-sequence theory for exponentials with exponents in a horizontal strip (Young, *Nonharmonic Fourier series*;
Avdonin–Ivanov, *Families of exponentials*; Levin–Golovin sine-type functions), qualitative, no explicit constants.
Diagonal dominance (any cutoff) provably fails for `K ≫ g`: the damping `e^{−bt}`, `b ≍ 2K`, has bandwidth `K`, so `≍ K/g`
neighbours interact at full strength; the Schur row sum is `≍ (1/g) log(ng/K)` against a diagonal `≍ 1/K`.

**Why the strip bound is nevertheless plausible with loss `e^{−O(KT + K/g)}`, uniformly in `n`.** For a lattice
`μ_r = rg` and vertical displacements `ν_r ∈ [0,K]`, the generating function is `sin(πz/g)·R(z)`,
`R(z) = Π_r (1 − iν_r/(z − μ_r))`, and on the lines `Im z = ±(K+1)`, `log|R(z)| = Σ_r ν_r y/((x−μ_r)² + y²) + O(Σ ν_r²/|z−μ_r|²)
= O(K/g)` — a Poisson-kernel sum, bounded independently of `n` (the naive modulus bound `Σ K/|z−μ_r|` would give `(K/g) log n`;
the first-order term is positive and summable). So `G` is sine-type with constants `e^{O(K/g)}`, and Levin–Golovin gives a
Riesz sequence in `L²(0,T)` with constants `e^{−O(KT + K/g)}`. The near-dependence example (`n ≈ √(K/g)` fast terms vanishing
to order `n` at `0`) gives `λ_min ≲ e^{−c√(K/g)}` independently of `T`, consistent with this floor. Both losses are
polynomial in `T` in the zero problem, with exponent `→ 0` as `D → ∞` for the `K/g` part.

**Assembly subtlety (found in Lean).** The strip bound must be applied to *all* off-line zeros beyond `δ₀` at once, normalised
at the top `σ = 1`: applying it group by group leaves cross terms with higher groups, and the Lorentzian block budget
`64 Θ L Σ_{j∈G} amp_j` with `Θ` the complement's top amplitude is a triangle inequality that loses `T^{(a+ℓ)δ_max(compl.)}` — fatal
for every group but the top one, and for the top group against its own bottom. With the whole block as one band, the only
complement is the near-line set (`Θ = T^{αδ₀}`), and the cross term is dominated *termwise* by the detection term:
`ℓ·192 L T^{b(δ₀+δ_j)} ≤ e^{−3} T^{−λ} T^{2aδ_j}/(CD)` for every `j` with `δ_j ≥ 4δ₀`, provided `λ := C(ℓ + 1/D) < aδ₀/2`
(exponent gap `η = aδ₀/2 − λ`, using `ℓ ≤ a/2`).

**Lean (built, wired, axiom-clean): `RHTower/MontgomeryIsolatedDensityConditional.lean`.**
`StripInghamBound C : Prop` — for every finite `D`-separated frequency set, exponents in `[−K,0]`, window `ℓ ≥ C/D`:
`e^{−C(Kℓ + K/D)}/(CD) · Σ_r |d_r|² e^{2θ_r a} ≤ ∫_a^{a+ℓ} |Σ_r d_r e^{θ_r α} e^{2πiu_rα}|²`.
`stripInghamBound_small_decay`: the bound with `C = 100` is a theorem for `K ≤ D/100` (from the damped MV inequality,
constant `≥ 10/D`). `offline_block_window_ge_of_stripIngham`, `eventually_sum_offline_energy_le_of_stripIngham`
(`Σ_{j∈A} T^{2a(β_j−1/2)} ≤ (CDℓe³/π) T^{1+C(ℓ+1/D)} log T`), `eventually_card_offline_le_of_stripIngham`
(`N(1/2+δ, T) ≤ (CDℓe³/π) T^{1−2aδ+C(ℓ+1/D)} log T` for every `δ`, under: all zeros with `Re ≥ 1/2+4δ₀` pairwise `D` mean gaps
apart, all others within `δ₀` of the line, `C/D ≤ ℓ ≤ a/2`, `a+ℓ < 1`, `C(ℓ+1/D) < aδ₀/2`).

**Exact open core.** `StripInghamBound C` for some absolute `C` (equivalently: exponentials with exponents in a horizontal
strip and separated real parts form a Riesz sequence in `L²(0,T)` with lower constant `e^{−O(KT + K/g)}`, uniformly in the
number of terms). If it holds, **isolated off-line zeros obey the density hypothesis** (`a → 1`, `ℓ, 1/D → 0`):
a dense violation of RH cannot be isolated at the mean-gap scale at any real parts; it must cluster below the mean gap.
Formalisation route: Levin–Golovin for a lattice-completed finite set (explicit generating function, Poisson-kernel line
bounds, biorthogonal family by contour integration, Bessel bound by the Cauchy-kernel Gram + MV as in the damped module);
for non-lattice real parts the completion is a density-`1/g` separated set, whose generating function is Beurling–Seip
territory — the genuinely hard part.

## Block-length law — proved in Lean (2026-09-08)

`RHTower/XiZeroCountLocalCeiling.lean` (built, wired, axiom-clean): from the corpus's Riemann–von Mangoldt remainder
`exists_xiZeroCount_routeKSmoothRVMCount_log_remainder` and convexity of `u log u`
(`mul_log_sub_mul_log_le`, `routeKSmoothRVMCount_add_sub_le`): `exists_xiZeroCount_window_le`
(`N(t+H) − N(t) ≤ (H/2π)log(t+H) + 2C log(t+H)`), the copy-to-count bridge `card_le_xiZeroCount_sub`
(a finset of copies with ordinates in `(t,t+H]` injects into the sigma-finset over the new supports, `Finset.card_sigma`),
`exists_card_window_le`, and the **block-length law** `exists_card_block_le`: `L` copies spanning at most `(1−ε)(L−1)`
mean gaps satisfy `L ≤ 2C log(t+H)/ε`. This is the quantitative half of the evader class: tapered blocks (CANNOT-332) are
short, `O(log T/ε)` zeros each. CANNOT-340. Note: the corpus already owned the sharp count (`XiZeroCountRVMRemainder`,
`RiemannVonMangoldt`); search first.

## Wide dominant-band law — proved in Lean (2026-09-08)

`RHTower/MontgomeryMultiBandWide.lean` (built, wired, axiom-clean): `mvWideBandUpperConstant a ℓ D τ =
e^{2τ(a+ℓ)}(ℓ + 26/(πD) + 9τ/(π²D²))`, `band_inner_ge_wide`, `band_inner_le_wide`, `multiBand_inner_ge_wide`,
`multiBand_block_window_ge_wide`, `eventually_card_dominantBand_le_wide`. Generated from the narrow-band proofs by
replacing the Taylor band constants with the damped Montgomery–Vaughan bounds (`_ge_band`/`_le_band`); no `τ ≤ 1`,
`a + ℓ ≤ 1` hypotheses. All three band laws (single, dominant, isolated-density-conditional) are now at the natural
unit (isolation)/`log T`.

## Sixth cycle (2026-09-19): the fifth-cycle law is out of reach of every windowed mean square

**Question.** Can any windowed mean square of the zero exponential sum `S(η) = Σ_j e^{(δ_j+iγ_j)η}` (the
`α`-averaged Montgomery form is `∫|S|²K`, `K ≈ (1/L)·1_{[L/2,L]}`, `L = log T`) prove the isolation–density law
at `(1+Δ)`-times-mean-gap spacing for `δ ≫ 1/L`?

**Answer: no; the obstruction is one phenomenon, not two.** The weight `e^{2δη}` of a zero at distance `δ`
from the line puts its mean-square mass in the last `O(1/δ)` of any window. Montgomery–Vaughan on an
effective window of length `1/δ` needs ordinate gaps `≥ 2π(1+Δ)δ`. At mean-gap spacing `(1+Δ)2π/L` this is
`δ ≤ (1+Δ)/L`, where the count `N ≪ T^{1−2δ}` is trivial. The `ξ`-route's `W = O(1)` and the `α`-route's
"amplitude varies by `T^{ℓδ}` across bands" (fifth cycle) are both this localisation. Quantitatively, on
the half-line the Gram of `e^{−(δ+iγ_j)u}` has Carleson constant `≈ exp(−(δL)²/(6(1+Δ)²))`, so cross terms
can cancel the self terms of mean-gap-spaced zeros entirely once `δ ≫ 1/√L`.

**What the mechanism does give (uniform multi-band form; polynomial constants).** Cut `[L/2, L]` into windows
of length `θ/δ_max`; on each, the coefficients `e^{δ_jη}` vary by a factor `≤ e^{θ}`, so Montgomery–Vaughan
(lower bound, plus the upper bound for the perturbation) gives `∫_window |S|² ≥ (1−Cθ)(1 − 2π(1+Δ)δ_max/(θg))·
(θ/δ_max)·Σ_j e^{2δ_j a}` when the gaps satisfy `g ≥ 2π(1+Δ)δ_max/θ`; summing windows recovers
`c(θ,Δ)·Σ_j ∫_{L/2}^L e^{2δ_j a}da`, the full self-energy `≍ Σ_j T^{2δ_j}/δ_j`. Against the unconditional
BGSTB value `∫_{1/2}^1 F(T^α,T)dα = (3/16π)TL(1+o(1))` this yields the density-hypothesis count
`N(½+δ, T) ≪ δ L T^{1−2δ}` for zeros pairwise spaced by `≥ Cδ_max`. **Verdict: REDISCOVERED** — this is the
corpus's own threshold "clusters of width `≲ δ` are the evaders" (first/fourth cycles) with the constant
`(3π³/s)e^{−6π/s}` replaced by a polynomial one and the spacing scale tied to `δ_max`; no new evader is
excluded, since the evaders have width `< Cδ`.

**Status of the fifth-cycle law.** Unchanged as a statement (`SURVIVES PRELIMINARY ATTACK`); as a target
for mean-square mechanisms it is closed: no windowed mean square of `S` detects mean-gap-spaced zeros with
`δ ≫ 1/L`. A proof would need a different observable (a lower bound not localised by `e^{2δη}`), i.e. exactly
the phase-balanced-cluster information every producer must supply (CANNOT-332). No Lean: certifying the
uniform multi-band count would formalise a rediscovery.

**Candidate examined and killed the same day: robust finite Putnam / Landau at the block step.** The tapered
AP-block and periodic-array evaders have block spacing `s = 2πc/L`; a Putnam kernel at step `s` has period
`P = 2π/s = L/c`, and a Landau-formula reading `Σ_{γ≤T} x^{iγ}` of the same structure sits at `x = e^{L/c} = T^{1/c}
≥ T^{1+2πδ}`, where Landau's error term `O(x log² T)` exceeds the main term. Both are the wall this card already
states ("primes beyond `T^{1+2πδ}` at height `T`"): verdict BRIDGE/REDISCOVERED, not a new mechanism. Side facts
kept for reuse: the corpus certifies Putnam's exclusion of exact infinite one-sided vertical progressions of on-line
zeros (`xiRealDivisor_no_progression`, chain `PutnamKernel` … `PutnamPeriodizationLimits`); the kernel `C_{σ,a}`
with transform `−ζ(s)/s` exists at every `σ ∈ (0,1)`; and the abstract statement "bounded periodic function with a
jump and `N` vanishing nonnegative Fourier coefficients" gives only `log N ≲ sup|D|/|jump|` (sawtooth minus a
trigonometric polynomial is a model), so finite progression bounds must use the arithmetic of `{e^x}` (van
Frankenhuijsen 2005). No literature on approximate progressions found (searches 2026-09-19).
