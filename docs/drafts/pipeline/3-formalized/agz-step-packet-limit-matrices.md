# The limit matrices of the block-constant form: Weil's form on step packets

- **ID:** agz-step-packets (tasks A114, A80 of `docs/reports/review-1011/obstacles-summary.md`)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** obstacles-summary §2.14, order of work, first item (question 2); §2.1 A114, A80
- **Statement:** on the divisors constant on the `J` blocks of `B` points above the scale `RB`,
  Weil's form on the comb, per point of a block, tends to Weil's form `𝔚_Q` of the step packet;
  the Riemann hypothesis holds iff `𝔚_{3K+1}` is nonnegative on the step packets of `3KR`
  blocks for all `K, R`; and iff for every window ratio and `η > 0`, at all large scales
  `2 d₁ d₂ − D·D ≥ −η Σ c_n²` for every real divisor of the window.

## Gates
- [x] X1 the form of a packet through its autocorrelation; polar expansion on nested flat packets
- [x] X2 one window
- [x] X3 block-constant divisors: limit matrices, uniformly in the coefficients
- [x] X4 sign under the Riemann hypothesis
- [x] X5 A114 (equivalence) and A80 (the inequality at finite scale from RH)

## Paper proof

Notation: `h_g(x) = ∫ g(u) g(u + x) du`; `ω` the Lévy density of Weil's archimedean form;
`A(0) = ψ(1/4) − log π`; `d₁(g) = ∫ g e^{−u/2}`, `d₂(g) = ∫ g e^{u/2}`;

`𝔚_Q(g) = 2 d₁ d₂ + A(0) h_g(0) + ∫_0^∞ 2ω(x)(h_g(0) − h_g(x)) dx − 2 Σ_{2 ≤ k ≤ Q} Λ(k) k^{−1/2} h_g(log k)`.

**S0.** For `g ∈ C²_c` with `h_g(log n) = 0` for `n > Q`, `𝔚_Q(g)` is the sum over the zeros
`Z(g)`: explicit formula of `ζ` on a real packet, the archimedean term in Lévy–Khintchine form.

**S1. Polar identity.** If `q(g) = b(g, g)` with `b` additive and homogeneous in each argument
on the combinations of a finite family `v_j`, then
`q(Σ τ_j v_j) = ½ Σ_{j,l} τ_j τ_l (q(v_j) + q(v_l) − q(v_l − v_j))`   (∗).
Proof: `b(v_j, v_l) + b(v_l, v_j) = q(v_j) + q(v_l) − q(v_l − v_j)`. The identity is linear in
`q` and passes under an integral of a family `q_x` when `q_x(v_j)` and `q_x(v_l − v_j)` are
integrable in `x`. It holds for `d₁ d₂`, for `h_g(x)` at each `x`, hence for `𝔚_Q` on nested flat
packets `v_j = e^{u/2} 1_{(log x₀, log x_j]}`, where `v_l − v_j = ± flatPacket(min, max)` and the
jump integrand of a flat packet is integrable (explicit: rational rates on the width, then
`2(b − a)ω`). It holds for Weil's form on the comb at finite scale on every family of divisors
(bilinear form of the continuation).

**S2. One window.** Naturals `1 ≤ a < b ≤ Q a`, the divisor `1` on `(aB, bB]`:
`d₁ = H_{bB} − H_{aB} → log(b/a)`, `d₂/B = b − a`; these are the degrees of `flatPacket a b`.
The pairing is the energy of the jets in the window, minus the counterterm, plus the contacts.
Jets minus counterterm over `B` tend to `−(A(0) h(0) + ∫ 2ω(h(0) − h))`
(`tendsto_windowEnergy_jumpForm`). The contacts: `Σ_{m ≠ n} contact(m, n)` is twice
`Σ_{m ∣ n} Λ(n/m)` (the diagonal adds `Λ(1) = 0`), and with `n = km` this is
`2 Σ_{k ≥ 2} Λ(k) #{m ∈ W : km ∈ W}`; `k < Q` because `k·aB < km ≤ bB ≤ Q aB`. The count over
`B` tends to `(b/k − a)⁺ = h(log k)/√k` (continuation). Sum: `combForm/B → 𝔚_Q(flatPacket a b)`.

**S3. Nested windows.** For `τ` and the flat divisors `V_j` of `(x₀B, x_jB]`,
`x₀ ≤ x_j ≤ X ≤ Q x₀`: by (∗) on both sides and S2 on the windows `(x₀, x_j]`,
`(min(x_j, x_l), max(x_j, x_l)]`,
`combForm(Σ τ_j V_j)/B → 𝔚_Q(Σ τ_j flatPacket x₀ x_j)`. The difference is
`½ Σ τ_j τ_l e_{jl}(B)` with `e_{jl} → 0`, so it is at most `η Σ τ_j²` for all `τ` at once, at all
large `B` (`(Σ|τ_j|)² ≤ #s Σ τ_j²`).

**S4. Block-constant divisors.** Summation by parts: `Σ_{j<J} σ_j (Ψ_{j+1} − Ψ_j) =
Σ_{j ≤ J} τ_j Ψ_j`, `τ_j = σ_{j−1} − σ_j` (`σ_{−1} = σ_J = 0`). With `Ψ_j` the flat packet (the
flat divisor) of `(R, R + j]` this writes the step packet and the block-constant divisor through
nested windows; `Σ τ_j² ≤ 4 Σ σ_j²`, and `Σ_n σ(block(n))² = B Σ σ_j²`.

**S5. Sign under RH.** Let `g` be bounded, measurable, supported in an interval of length
`< log(Q + 1)`, with integrable jump integrand. Let `φ_i ≥ 0` be smooth of integral one,
supported in `[−1/(i+1), 1/(i+1)]`, and `g_i = φ_i ⋆ g`. Then `g_i ∈ C^∞_c`, `|g_i| ≤ sup|g|`,
supports in a fixed compact, `g_i → g` a.e. (Lebesgue differentiation). For large `i`,
`h_{g_i}(log n) = 0` for `n > Q`, so `𝔚_Q(g_i) = Z(g_i) ≥ 0` under RH (S0). Jensen with the
weight `φ_i`: `(g_i(u + x) − g_i(u))² ≤ ∫ φ_i(t)(g(u − t + x) − g(u − t))² dt = (φ_i ⋆ w)(u)`,
`w(v) = (g(v + x) − g(v))²`; integrating, `∫ (φ_i ⋆ w) = ∫ w`, so
`h_{g_i}(0) − h_{g_i}(x) ≤ h_g(0) − h_g(x)` for every `x`: the jump integral of `g_i` is at most
that of `g`. By dominated convergence `d_1, d_2` and `h(x)` at `x = 0, log k` converge. Hence
`𝔚_Q(g) ≥ lim (𝔚_Q(g_i) − jump(g_i) + jump(g)) ≥ 0`. A step packet satisfies the hypotheses (its
jump integrand is the polar combination of those of flat packets).

**S6. A114.** (⇒) S5 with `x₀ = R`, `X = (3K + 1)R`, `Q = 3K + 1`. (⇐) By S3–S4, if
`𝔚 ≥ 0` on step packets then at all large `B`, `combForm ≥ −η B Σ σ_j²` on all block-constant
divisors; the continuation's `riemannHypothesis_of_frequently_blockFunction_combForm_ge`
concludes.

**S7. A80.** RH, a ratio `3K + 1`, `η > 0`. Take `R` from the continuation's reduction to block
averages at the ratio `6K + 2` and `ε = η/2`. For `N ≥ R(B₀ + 1)` put `B = ⌊N/R⌋`, `N' = RB ≤ N <
N' + R`. The window `(N, (3K + 1)N]` lies in `(N', (6K + 2)N']`, which is `(6K + 1)R` complete
blocks of `B` points. Extend the divisor by zero; its form is at least the form of its block
averages minus `(η/2) Σ c²`, and that is at least `−(η/2) Σ c²` by S5 and S3–S4 at the block
size `B`.

**Entries.** For naturals `1 ≤ a < b`:
`𝔚_Q(flatPacket a b) = 2 log(b/a)(b − a) − (W(b, b) − 2W(a, b) + W(a, a)) − 2 Σ_{k ≤ Q} Λ(k)(b/k − a)⁺`,
`W(a, b) = ½((b + a) log(b + a) − (b − a) log(b − a)) + a(γ + log 2π − log a)`.

## Lean

Folder `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/`.

| Step | Module | Declarations |
|---|---|---|
| S0, S1 | `WeilsFormOnStepPacketsIsDeterminedByItsValuesOnWindows` | `packetForm`, `zeroSum_eq_packetForm`, `PolarOn`, `polarOn_of_bilin`, `PolarOn.setIntegral`, `polarOn_packetForm`, `flatPacket_sub_flatPacket`, `integrableOn_levyJump_flatPacket`, `polarOn_packetForm_flatPacket`, `packetForm_flatPacket_sub_flatPacket` |
| S2, S3 | `OnNestedWindowsTheCombFormTendsToWeilsFormOfTheStepPacket` | `polarOn_of_biadditive`, `polarOn_combForm`, `combForm_of_subset`, `windowDivisor`, `sum_sum_contact_window`, `combForm_window_eq`, `tendsto_combForm_window_div`, `tendsto_combForm_nested_div`, `eventually_abs_combForm_nested_sub_le` |
| S5 | `UnderTheRiemannHypothesisWeilsFormOfAStepPacketIsNonnegative` | `sq_integral_mul_le`, `mollify`, `packetAutocorr_mollify_sub_le`, `tendsto_packetAutocorr_mollify`, `packetForm_nonneg_of_riemannHypothesis`, `packetForm_step_nonneg_of_riemannHypothesis` |
| S4, S6, S7 | `TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets` | `stepPacket`, `sum_mul_sub_eq_nested`, `tendsto_combForm_blockFunction_div`, `packetForm_flatPacket_eq`, `riemannHypothesis_iff_forall_packetForm_stepPacket_nonneg`, `eventually_combForm_ge_of_riemannHypothesis`, `riemannHypothesis_iff_eventually_combForm_ge` |

Each module: `lake --old env lean`, exit 0, no output. Continuation inputs
(`HodgeTheoryOfAFixedPart`): `exists_blockSize_combForm_ge_blockMean`,
`riemannHypothesis_of_frequently_blockFunction_combForm_ge`,
`riemannHypothesis_of_frequently_combForm_ge`, `tendsto_flatContactPoints_self_autocorr`,
`formBilin`, `combBilin_comm`.

## Open
- The index at finite scale as the index of the limit (A94).
- A proof of nonnegativity of one of the matrices beyond the certified lengths: each is a
  statement of the strength of the inequality on a window.
- The Li ladder as comb forms of tails (A82) is proved for the Laguerre tails themselves:
  `agz-raw-laguerre-tails-li-ladder.md`.

## Log
- 2026-11-11 — formalized.
