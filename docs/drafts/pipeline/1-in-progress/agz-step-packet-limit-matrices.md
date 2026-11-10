# The limit matrices of the block-constant form: Weil's form on step packets

- **ID:** agz-step-packets (tasks A114, A80 of `docs/reports/review-1011/obstacles-summary.md`)
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), in work in `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/`
- **Source:** obstacles-summary §2.14, order of work, first item (question 2); §2.1 A114, A80
- **Statement:** on the divisors constant on the `3KR` blocks of `(RB, (3K+1)RB]` Weil's form on
  the comb, per block point, tends to Weil's form of the step packet; the Riemann hypothesis
  holds iff that form is nonnegative on step packets for all `K, R`; under the Riemann
  hypothesis the inequality at finite scale holds up to `η Σ c_n²` at all large scales.

## Goal
Question 2 of the `𝔽₁` programme. `HodgeTheoryOfAFixedPart` proves that a lower bound on
block-constant divisors at arbitrarily large block sizes gives the Riemann hypothesis
(`riemannHypothesis_of_frequently_blockFunction_combForm_ge`) and that the form of a divisor is
at least the form of its block averages up to `ε Σ c_n²`
(`exists_blockSize_combForm_ge_blockMean`). Missing: the limit of the form on block-constant
divisors and its sign under the Riemann hypothesis.

## Gates
- [ ] X1 the form of a packet in the coordinate of the autocorrelation; polar expansion on
      nested flat packets
- [ ] X2 one window: `combForm` of the flat divisor on `(aB, bB]`, over `B`, tends to the form of
      `flatPacket a b`
- [ ] X3 block-constant divisors: the limit is the form of the step packet (limit matrices)
- [ ] X4 under the Riemann hypothesis the form of a step packet is nonnegative (mollification)
- [ ] X5 RH ⇔ nonnegativity on step packets for all `K, R` (A114); RH ⇒ the inequality at finite
      scale up to `η Σ c_n²` at all large scales (A80)

## Approach

Notation: `h_g(x) = ∫ g(u) g(u + x) du`; `ω` the Lévy density of Weil's archimedean form;
`A(0) = ψ(1/4) − log π` (`EF.gammaBracket 0`); `d₁(g) = ∫ g e^{−u/2}`, `d₂(g) = ∫ g e^{u/2}`.

**The form of a packet.** For bounded `g` of bounded support and `Q` with `h_g(log n) = 0` for
`n > Q`:

`𝔚_Q(g) = 2 d₁ d₂ + A(0) h_g(0) + ∫_0^∞ 2ω(x)(h_g(0) − h_g(x)) dx − 2 Σ_{2 ≤ k ≤ Q} Λ(k) k^{−1/2} h_g(log k)`.

For `g ∈ C²_c` this is the sum over the zeros `Z(g)` (`zeroSum_eq_weilFullFunctional`,
`re_weilFullFunctional_packet`, `weilArchRe_sub_pole_packet`, `weilPoleTerm_packet`).

**X1. Polar expansion.** Every term of `𝔚_Q` is the diagonal of a bilinear expression in `g`
(`d₁(f) d₂(g)`; the cross-correlation `∫ f(u) g(u + x) du` at a fixed `x`). Hence for a finite
family `v_j` and reals `τ_j`

`q(Σ τ_j v_j) = ½ Σ_{j,l} τ_j τ_l (q(v_j) + q(v_l) − q(v_l − v_j))`   (∗)

for `q = 𝔚_Q` on nested flat packets `v_j = flatPacket x₀ x_j` (the jump integrand is a linear
combination of such `q`, integrable for each flat packet, so (∗) passes under the integral), and
for `q = combForm` on any divisors (a quadratic form on finite sums). For `j < l`,
`v_l − v_j = flatPacket x_j x_l`: (∗) writes both sides through single windows.

**X2. One window.** For naturals `1 ≤ a < b`, the divisor `1` on `(aB, bB]`:
`d₁ = H_{bB} − H_{aB} → log(b/a) = d₁(flatPacket a b)`, `d₂/B = b − a = d₂(flatPacket a b)`;
jets minus counterterm over `B` tend to `−(A(0) h(0) + ∫ 2ω(h(0) − h))`
(`tendsto_windowEnergy_jumpForm`); the contacts of ratio `k` are `2Λ(k)` times the points `m`
with `aB < m`, `km ≤ bB`, and their number over `B` tends to `h(log k)/√k`
(`HodgeTheoryOfAFixedPart.tendsto_flatContactPoints_self_autocorr`).

**X3. Limit matrices.** A divisor constant on blocks with values `σ_j` is
`Σ_{j=1}^{J} τ_j 1_{(x₀B, x_jB]}`, `x_j = R + j`, `τ_j = σ_{j−1} − σ_j` (`σ_J = 0`), and the step
packet is `Σ τ_j flatPacket x₀ x_j`. By (∗) on both sides and X2,
`combForm/B → 𝔚_Q(step packet)`; the limit is a quadratic form in `σ` with the entries
`½(q(x₀,x_j) + q(x₀,x_l) − q(x_j,x_l))`, `q(x, y) = 𝔚_Q(flatPacket x y)`.

**X4. Sign under RH.** Let `φ_ε ≥ 0` be a smooth bump of integral one supported in `[−ε, ε]` and
`g_ε = φ_ε ⋆ g`. Then `g_ε ∈ C_c^∞`, so `𝔚_Q(g_ε) = Z(g_ε) ≥ 0` under RH. Jensen:
`(g_ε(u + x) − g_ε(u))² ≤ ∫ φ_ε(s)(g(u + x − s) − g(u − s))² ds`, hence
`h_{g_ε}(0) − h_{g_ε}(x) ≤ h_g(0) − h_g(x)` for every `x`: the jump integral does not increase.
`g_ε → g` almost everywhere and boundedly on a fixed compact, so `d_i(g_ε) → d_i(g)` and
`h_{g_ε}(x) → h_g(x)` at `x = 0` and `x = log k`. So
`𝔚_Q(g) ≥ limsup 𝔚_Q(g_ε) ≥ 0`.

**X5.** (⇐) of A114: X3 with uniformity on the unit sphere of `ℝ^J` (entrywise convergence of
`J × J` matrices) and `riemannHypothesis_of_frequently_blockFunction_combForm_ge`. (⇒): X4.
A80: for a window of ratio `Q` at a scale `N`, pad to complete blocks above `N' = R⌊N/R⌋`, apply
`exists_blockSize_combForm_ge_blockMean` and X3–X4 along `B = ⌊N/R⌋ → ∞`.

## Log
- 2026-11-10 — created.
