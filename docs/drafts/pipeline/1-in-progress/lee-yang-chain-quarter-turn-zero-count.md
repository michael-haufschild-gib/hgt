# Lee–Yang chains: the quarter-turn zero count and the death of integer-anchored Γ-site chains

- **ID:** `lee-yang-chain-quarter-turn-zero-count`
- **Stage:** 1-in-progress (paper proof complete; Lean in progress)
- **Type:** `[THEOREM + ROUTE KILL]`
- **Parents:** MUST-820 (`RHTower.LeeYangChain.riemannSiegel_leeYang_chain`, route candidate ALY), MUST-819 (Lee–Yang resolution law), MUST-806 (prime fields cannot reach Ξ).
- **User direction (2026-10-08):** "Build a new route" from the Γ-site Lee–Yang chain. The route, built out, dies at its first site.

## Statement

**Setup.** This is the chain of MUST-820, with sites `0..N`, fields `u_k = e^{−itλ_k}` (`λ_k > 0`) and real wall fugacities `c_k`:
`A_0 = 1`, `B_0 = u_0`, `A_{k+1} = A_k + c_k B_k`, `B_{k+1} = u_{k+1}(c_k A_k + B_k)`, `Z_N = A_N + B_N`.

**Theorem A (quarter-turn zero count).** Let `|c_k| < 1` for all `k`, and let `T > 0`. Then `t ↦ Z_N(t)` has at least
`⌈ ½ Σ_{k=0}^{N} ⌊Tλ_k/π⌋ ⌉`
distinct real zeros in `(0, T]`. With `|c_k| ≤ 1`, the chain (unless it vanishes identically) has a zero in `[0, π/max_k λ_k]`.

**Theorem B (integer-anchored Γ-site chains die).** For the Γ sites `λ_k = log((k+2)/(k+1))`, which MUST-820 uses to make single walls carry the integer frequencies `log(k+2)`, `λ_0 = log 2`. So every such chain, with any `N` and any real fugacities in `[−1,1]`, has a real zero in `[0, π/log 2] ⊂ [0, 4.54]`. `Ξ` has no real zero there: `xi_ne_zero_of_im_sq_le` gives `|t| ≤ √32 ≈ 5.66` unconditionally. So for any normalizers `e_j` and any continuous zero-free `E`, the products `e_j·Z_{N_j}` never converge to `E·Ξ` uniformly on `[0, π/log 2]`.

**Theorem C (asymptotic excess, paper).** For the Γ sites,
`Σ_k ⌊Tλ_k/π⌋ = Σ_{n≥1} ⌊X log(1+1/n)⌋ = X(log X − 1 + γ) + O(√X)` with `X = T/π`.
So every Γ-site chain has at least `(T/2π)(log(T/π) − 1 + γ) + O(√T)` zeros in `(0,T]`, while Riemann–von Mangoldt gives `N_Ξ(T) = (T/2π)(log(T/π) − log 2 − 1) + O(log T)`. The obstruction is not a low-height accident. The chain carries `(log 2 + γ)·T/2π + O(√T)` excess zeros at every height.

## Proof

1. **Conjugate gauge on the real line.** For real `t` put `r_k = Σ_{j≤k} λ_j`. By induction, `B_k = e^{−itr_k}·conj(A_k)`: the base case is `B_0 = u_0 = e^{−itr_0}`, and the step uses that `c_k` is real. With `a_k = e^{itr_k/2}A_k` this gives
   `Z_N = e^{−itr_N/2}(a_N + conj a_N) = e^{−itr_N/2}·2 Re a_N`,
   `a_0 = e^{itλ_0/2}`, `a_{k+1} = e^{itλ_{k+1}/2}(a_k + c_k conj a_k)`.
2. **Explicit phase.** Write `a_k = ρ_k e^{iψ_k}` with `ρ_k > 0`, `ψ_0 = tλ_0/2` and
   `ψ_{k+1} = tλ_{k+1}/2 + E_{c_k}(ψ_k)`, `E_c(ψ) = ψ + arg(1 + c e^{−2iψ})`.
   This holds because `a + c conj a = ρ e^{iψ}(1 + c e^{−2iψ})`, and `Re(1 + c e^{−2iψ}) ≥ 1 − |c| > 0`. So the factor is nonzero and its principal argument lies in `(−π/2, π/2)`; it is continuous in `ψ`, and `ψ_k(0) = 0` because `arg(1 + c) = 0`.
3. **Quarter-turn invariance.** `⌊2E_c(ψ)/π⌋ ≥ ⌊2ψ/π⌋`. Put `j = ⌊2ψ/π⌋` and `θ = ψ − jπ/2 ∈ [0, π/2)`, so that `e^{−2iψ} = (−1)^j e^{−2iθ}`. With `c' = (−1)^j c`,
   `Im((1 + c' e^{−2iθ}) e^{iθ}) = (1 − c') sin θ ≥ 0`.
   If `arg(1 + c'e^{−2iθ}) < −θ`, the sum `arg + θ` would lie in `(−π/2, 0)`, which makes that imaginary part negative. Hence `E_c(ψ) ≥ jπ/2`.
4. **Count.** By step 3 and `⌊a + b⌋ ≥ ⌊a⌋ + ⌊b⌋`, induction gives `⌊2ψ_N(T)/π⌋ ≥ Σ_k ⌊Tλ_k/π⌋ =: S`. Each `ψ_k` is continuous in `t` and vanishes at `0`. So for every `j` with `2j + 1 ≤ S` the intermediate value theorem gives `t_j ∈ (0, T]` with `ψ_N(t_j) = π/2 + jπ`. There `Re a_N = ρ_N cos ψ_N = 0`, so `Z_N(t_j) = 0`. The `t_j` are distinct because their phases differ, which gives `⌈S/2⌉` zeros.
5. **Closed fugacities.** For `|c_k| ≤ 1`, apply step 4 to `s·c` with `s < 1` at `T = π/max λ`, where `S ≥ 1`. The zeros `t_s ∈ (0, T]` have a limit point `t*`, and `Z` is jointly continuous in `(s, t)`. So `Z(c, t*) = 0` with `t* ∈ [0, T]`.
6. **Kill.** `m = min_{[0,π/log 2]} |EΞ| > 0`. A uniform error below `m` contradicts the chain zero `t_j`, where `|e_j Z_j − EΞ| = |EΞ(t_j)| ≥ m`.
7. **Theorem C (paper).** `Σ_n ⌊X log(1+1/n)⌋ = X log(X+1) − Σ_{n≤X}{X log(1+1/n)} + O(1)`. For `n > √X`, `{X log(1+1/n)}` differs from `{X/n}` by at most `X/(2n²)`, apart from `O(√X)` wraps. Dirichlet's `Σ_{n≤X}{X/n} = (1−γ)X + O(√X)` then gives the claim.

## What this kills, and what survives

- **Killed: ALY with integer anchoring.** That is the MUST-820 chain together with every nearest-neighbour coupling profile, signed or ferromagnetic, at every length. The cause is the first site: its frequency `log 2` forces a half-turn by `π/log 2`. Couplings act by Möbius maps fixing `±1`, so they can delay a quarter-turn but never undo it.
- **Shifted Γ-chains**, whose first field is `log((K+2)/(K+1))`, have a forced zero at `≤ π/λ_K`: `4.53, 7.75, 10.92, 14.08` for `K = 0, 1, 2, 3`. All four lie below `γ₁ = 14.13`, so chains anchored at `2, 3/2, 4/3, 5/4` die. Only `K = 0` is formal (window `√32`); `K = 1, 2, 3` need the first-zero height. For `K ≥ 4` the counting bound `(T/2π)log(2e^γ/(K+1))` is below `Ξ`'s, so the quarter-turn law gives no obstruction.
- **Survivor (positive law).** Theorem A holds for every Lee–Yang chain with every positive frequencies. A chain approximating `E·Ξ` on `[0, T]` must satisfy `Σ_k ⌊Tλ_k/π⌋ ≤ 2N_Ξ(T) + 1`. In particular every frequency must be `≤ π/γ₁ ≈ 0.2223`. That excludes the integers `2, …, 5` as single-wall frequencies. The remaining room is fine-grid chains, i.e. Krein/Dirac systems, which is route SZ.
- **Reading.** Integer anchoring and the correct zero density are incompatible for nearest-neighbour Lee–Yang chains. The slow variables of MUST-819 are necessary, but anchoring the telescoping at the integer 2 already costs an early zero and a linear excess of `(log 2 + γ)T/2π`.

## Novelty audit

- The mechanism is a Prüfer/Sturm-type oscillation count for products of `SU(1,1)` Möbius maps fixing `±1`. That is standard in spirit: the OPUC rotation number of paraorthogonal polynomials.
- The application is new. The Γ-site Lee–Yang chain is corpus-original (MUST-820), and so are the early-zero kill and the constant `log 2 + γ`.
- Corpus search: `rg -i "quarter-turn|rotation number|prüfer" docs formal` finds Prüfer only in the Böttcher lane, which is unrelated.
- MUST-819 recorded "independent log-ratio spins attain the optimal order". Theorem C shows that the constant is wrong at every coupling.

## Lean (MUST-823; standard axioms; wired after `RiemannSiegelLeeYangChain`)
- `RHTower/LeeYangChainQuarterTurnZeroCount.lean`. Gauge: `chainPair_snd_eq`, `chainZ_eq_gauge`, `gaugeA_succ`. Polar form: `exists_gaugeA_polar`. Invariance: `floor_mul_le_phaseStep`. Count: `sum_floor_le_floor_chainPhase`, `exists_chainZ_zero_at_level`, `exists_chainZ_zeros` (injective `Fin M → (0,T]`). Closed fugacities: `exists_chainZ_eq_zero_Icc` (compactness in the scaling `s → 1`).
- `RHTower/GammaSiteLeeYangChainXiObstruction.lean`: `exists_gammaChainZ_eq_zero`, `XiC_ne_zero_of_mem_Icc_pi_div_log_two` (via `xi_ne_zero_of_im_sq_le`), `exists_gammaChain_error_eq`, `not_tendstoUniformlyOn_gammaChain_XiC`.
- Both direct `lake env lean` checks: zero messages. Targeted `lake build --old` of both passed. Lint reports nothing for these modules.
- Theorem C (asymptotic excess) remains paper.

## Log
- 2026-10-08: created and formalized (loop row 557, MUST-823). Next: the general-graph survivor.
