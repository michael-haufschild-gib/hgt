# Route WD closing loop (review-0111 todo, blocks 1–7)

- **ID:** wd-review-0111-closing-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP + THEOREM (paper, block 2)
- **Source:** docs/reports/review-0111/route-WD.md (blocks 1–7); frontier map §WD; obstacles B17, B20–B25.
- **Statement:** Work the seven WD blocks in order; formalize every positive survivor.

## Block status

| Block | Status | Lean |
|---|---|---|
| 1 arithmetic input on the conjugate-diagonal side | open; the object is now explicit: the window energy `|𝒵(t)|²` (Thm 3, 8) | — |
| 2 certificate format | closed | `logStage_besselSzego_iff_invLog_corridor` (card wd-bessel-szego-certificate) |
| 3 averaged rung `o(log U)` | open | — |
| 4 height uniformity | open | — |
| 5 corridor rung | open; ⟺ certificate at log stage (Cor 10) | — |
| 6 shallow zeros | open | — |
| 7 closing step | format closed (RH ⟺ explicit certificate at every stage); the positivity itself is RH | `riemannHypothesis_iff_unitStage_besselSzego` |

## Block 2 — closed

Formalized: [wd-bessel-szego-certificate](../3-formalized/wd-bessel-szego-certificate.md).
The certificate class is `{besselSzegoCertificate n K E}` with `E(t) = |𝒵_N(t)|²`; it is complete
on corridor windows with explicit `K`, sound by `fredholmIndex_eq_zero_of_diskUnit_re_pos`, and
at the logarithmic stage equivalent to the `A/log|γ|` corridor
(`logStage_besselSzego_iff_invLog_corridor`). Every certificate equals `F·Ω` with `Re Ω > 0`
(rigidity, paper item 11), so the arithmetic content of sectoriality is the growth rate of the
energy `|𝒵(t)|²`: index 0 at stage `n` iff that rate is below `g_n = 1/(2n)`
(`integrableOn_energy_iff`, energy–index law).

## Gates
- [x] 0 → 1  blocks fixed; block 2 attack fixed
- [x] block 2 paper proof and Lean
- [ ] blocks 1, 3–7

## Ledger (conjecture loop)

| # | Block | Conjecture | Verdict | Insight |
|---|---|---|---|---|
| 1 | 2 | Re(FΛ)>0 is a quadratic form of the Hermite–Hankel matrix of centered moments | refined | the moment Hankel series diverges at the needed scale (`|z−mid|>½−c`); the convergent form is the Laplace/Bessel energy of `𝒵` (item 8) |
| 2 | 2 | canonical outer multiplier has a zero-free closed form in theta data | proved (7, 8) | cepstrum = alternating Bessel transform of `|𝒵|²` |
| 3 | 2 | a certificate cheaper than the cepstrum exists | refuted (11) | rigidity up to Carathéodory factors |
| 4 | 1 | Depth-weighted Montgomery identity bounds the conjugate diagonal: `Σ_ρ x^{2δ_ρ}w(0) ≤` prime mean square of `Σ_ρ x^{ρ−½}h_t(ρ)` | refuted | unconditional identity holds (zero side `Σ x^{δ+δ'}x^{i(γ−γ')}Ĥ(ρ,ρ')`), but even on RH the off-diagonal is `≈(α−1)·diag<0` for `α<1`; the diagonal exceeds the total. |
| 5 | 1 | Positive kernel `r̂` makes the depth-shifted off-diagonal `Re R(γ−γ'−i(δ+δ'))` nonnegative | refuted | `Re R(x−iy)=` FT of `r̂(α)cosh(αyL)`; compact `r̂` forces sign changes; positivity only for `(δ+δ')log T ≤ c₀` — shallow pairs, the wrong regime. |
| 6 | 3 | Mean index `o(log U)` at log stage from mean values of `𝒵_m(t)`, `t ≤ log U` | refuted (mechanism) | typical `|𝒵_m(t)|² ≍ t` (Montgomery–Vaughan / Selberg CLT), so depth `a/log U` is visible only when `e^{2a} ≫ log U`: this is exactly Selberg's `loglog U/log U` barrier. Clustering at fixed `a` needs prime sums longer than the height (`α>1` pair correlation with depth weights). |
| 7 | 3 | Certificate on density-one windows at stage `≍ log m/loglog m` | skipped (composition at Selberg strength) | `eventually_volume_badSharpLogLogCorridor_unitWindows_le` + `exists_xiZero_near_thetaZero` + `besselSzegoCertificate_mul_loop_pos`; Selberg strength, so not recorded as new. |
| 8 | 1 | Energy = conjugate-diagonal object | insight | `|𝒵(t)|² = 𝒵(t)𝒵(−t)` is bilinear-holomorphic by reflection; the true conjugate diagonal is its diagonal `Σ m² e^{2tδ}` (depth charge). Bilinear prime input (pair correlation) contains it, the off-diagonal is the obstruction: block 1 ⟺ off-diagonal pair control with depth weights. |
| 9 | 1, 3 | Bargmann subharmonicity of the window spectrogram `|V_g μ(t,m)|²` (Gaussian Gabor transform of `Σ Λ(n)n^{−½}δ_{log n}`) upgrades mean values over `m` to pointwise bounds | refuted | `log|V|+π|z|²/2` is subharmonic, so `log|V(z₀)| ≤ ½ log avg_{disk}|V|² + πR²/4`; Montgomery–Vaughan needs an `m`-range `≥ e^t` (log-frequency spacing `e^{−t}`), forcing `R ≥ σe^t` and penalty `≥ σ²e^{2t}`; uncertainty leaves only the trivial one-term window `σ ≤ e^{−t}`. |
| 10 | 7 | Explicit certificate format at every stage (polynomial resolution) | proved, Lean `riemannHypothesis_iff_unitStage_besselSzego` | `riemannHypothesis_iff_unitStage_besselSzego`: prefix `besselUnitPrefix m S = doorUnitPrefix + ⌈√budget⌉ + 1`, budget `≈ m + D_m log(128(S+6+2D_m²))`; locating theta zeros to depth `r` costs `N² ≳ m + d log(8/r)`, so polynomially small depths need only `Θ(√m+√(log m·log S))`. Converse: stabilization makes the index `N`-independent. |
| 11 | 1 | Lee–Yang/Pólya–Dickson reading of the window sum `𝒵̃_m(t)=Σ m e^{t(ρ−c_m)}` in complex `t` | insight (reformulation) | zeros of an exponential polynomial lie asymptotically in half-strips normal to the sides of the hull of its frequencies; window RH ⟺ hull is a vertical segment ⟺ all complex zeros of `𝒵̃_m` lie in a horizontal strip. Imaginary `t` damps height (`e^{−τγ}`), real `t` shifts log-prime scale. No new producer. |
| 12 | 1 | A prime-computable pair kernel `k(ρ+ρ̄'−1)` (sesqui-holomorphic, so bilinear explicit formula applies) that is pointwise `≥0`, letting the off-diagonal be dropped | refuted | `{z+w̄ : z,w in the strip}` is open, so a holomorphic `k` real and `≥0` there is constant (open mapping). Prime-computable pair kernels are at best positive-definite (Laplace transforms of positive measures), giving only `|𝒵|²≥0`. Dropping the off-diagonal then needs spacing (large sieve / Carleson embedding of the zero measure into `PW_L`), and the Carleson constant for weight `e^{2Lδ}` is the depth charge itself: circular. |
| 13 | 1 | Function-field calibration of the energy producer | insight | over `𝔽_q(C)` the window energy is `|Σ α_j^t|²` and the certificate's input is the Hasse–Weil bound `|#C(𝔽_{q^n})−q^n−1| ≤ 2g q^{n/2}` for all `n` — a square-root bound on the prime sum at every `t`, produced by Stepanov–Bombieri counting (auxiliary function + Riemann–Roch). Block 1 over `ℤ` asks for exactly this count; it is the LST/HWV open core (primitive `h¹` count), not a WD-internal estimate. |
| 14 | 4 | Smooth (Gaussian) height windows see low off-line zeros, giving height uniformity | refuted | a zero at height `γ₀` enters the window-`m` energy with weight `e^{−(m−γ₀)²}e^{tδ₀}`, visible only for `t ≳ (m−γ₀)²/δ₀`: prime sums of length `e^{m²}`; uniformity is the global PNT error, i.e. RH. |
| 15 | 3 | Bound the mean index by an energy integral `∫|𝒵_m(t)|²dμ(t) = Σ_{pairs}F(d)`, `F(z)=∫e^{tz}dμ`, with `Re F ≥ 1_{E_n}` and `Re F ≥ 0` on the strip | refuted (Harnack) | `Re F` is a nonnegative harmonic function on the strip; `≥1` on `E_n` (distance `g_n=1/(2n)` from the line `Re d=0`) forces `Re F ≥ 1−O(g_n)` on the imaginary-axis pair differences nearby (Harnack). On-line pairs then contribute `≍D²≍log²U` per window. Any energy majorant of the index must subtract the pair-correlation mass to precision `o(1/log U)` — second-order pair correlation. |
| 16 | 1, 3 | Extract the conjugate diagonal as the Bohr mean of the energy: `(1/H)∫_T^{T+H}|𝒵(t)|²e^{−2εt}dt → Σ_{same ordinate}` | reduction | same-ordinate pairs are `(z,z)` (weight `e^{2tδ}`, the depth charge) and `(z,z̃)` (weight 1); distinct ordinates average out only for `H ≫ 1/(min ordinate gap)` — the separation input Π13, with no lower bound on gaps. Via the explicit formula this is depth-weighted Montgomery `F(α)` as `α→∞`; mollifier form: mean values with length `T^θ`, `θ→∞`. Blocks 1/3 ⟺ unconditional long-range pair correlation with depth weights. |
| 17 | 3 | Clustering from the short-interval prime variance `∫_X^{2X}(ψ(x+h)−ψ(x)−h)² ∼ hX log(X/h)` | refuted as an input | a zero of fixed depth `δ` contributes `X^{1+2δ}min((h/X)²,γ^{−2})`, so the asymptotic for all large `X` already forbids every off-line zero (≥ RH); at a single scale the off-diagonal pair terms can offset the depth excess. Under RH, Goldston–Montgomery identify the variance with `F(α)`, `α>1` (Hardy–Littlewood pair heuristics); the unconditional depth-weighted form is the open input. |
| 18 | 1 | Weil's power-sum argument on the lattice `t = k log p`: pseudo-Frobenius numbers `α_ρ(p)=p^{ρ−½}`, window power sums `Σ_ρ α_ρ(p)^k = 𝒵(k log p)` | reduction | `Σ_k 𝒵(k log p)z^k = Σ_ρ α_ρ z/(1−α_ρ z)` has radius `p^{−δ*}`; bounds `|𝒵(k log p)| ≤ C(1+ε)^k` for all `k` give `δ* ≤ log(1+ε)/log p` — the abscissa law restricted to a lattice. Over `𝔽_q` the power sums are `q^k+1−#C(𝔽_{q^k})`, bounded by counting; over `ℚ` they are prime sums near `p^k` with no counting interpretation. Same missing producer as row 13. |
| 19 | 3 | Mean log-stage collision index (literal block-3 object) is `O(log U)` from the corpus depth-charge gate | refined | a pair inside `E_n` has `Re(z−w) > g_n`, so one zero is deeper than `1/(4n)`, but its partners are all zeros within `b_n = 1/n` in height. Depth charge plus the pointwise local count `≪ log m` gives only `O(log²U)`; `O(log U)` needs short-range pair counts (Selberg–Fujii second moment of `S(t+h)−S(t)`, not in the corpus), via Cauchy–Schwarz with the depth charge at `2L`. The exactly-horizontal charge is `≤ 2·#{δ>1/(4n)}` and is governed by the corpus TFAE `dyadicMean_corridor_and_polynomialTheta_littleO_log_tfae`; the Zhukovsky index adds near-horizontal pairs (the Π13 layer). |
| 20 | 3 (B21) | Montgomery's simple-zero argument with depths: the unconditional depth-weighted `F_dep(α)=|α|+T^{−2|α|}log T+o(1)` (`0<α≤1`, `x^{ρ−½}` form of his identity; prime side unconditional) with Fejér `r̂` gives near-line density at rate up to `2` | refuted after analysis | off-diagonal real parts are `Re r((LΔγ − i(a+a'))/λ)` (`supp r̂ ⊂ [−1/λ,1/λ]`), nonnegative only for `|a+a'| ≤ λη₀`, `η₀ = O(1)` set by `sup|ĝ'/ĝ|`; deep pairs are `O(λ e^{−(r−1/λ)A})`-negligible by Selberg only beyond `A ≍ r^{−1}log(1/ε)`, and the moderate band `λη₀ < |a+a'| < A` is uncontrolled. Closing the band needs `λ ≥ A/η₀`, giving rate `2/λ ≪ r`: no gain over Selberg. |

