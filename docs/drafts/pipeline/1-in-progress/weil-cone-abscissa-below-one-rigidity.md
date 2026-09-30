# Weil-cone rigidity for deviations of absolute abscissa below 1 (Gaussian |ζ|² notch)

- **ID:** weil-cone-abscissa-below-one
- **Stage:** 1-in-progress
- **Type:** CONJECTURE → paper proof below; Lean programme planned
- **Source:** MC conjecture loop, cycle 169. It extends MUST-571 (`3-formalized/11-rh-zero-divisor-geometry/weil-cone-log-summable-deviation-rigidity.md`).
- **Statement.**
  - **Theorem 169.** Let `v : ℕ → ℝ` with `v(0) = v(1) = 0` and `|v(n)| ≤ 2 log n + A`. Assume `Σ_n |v(n)| n^{−1/2+η} < ∞` for some `η ∈ (0, 1/2)`. If `±ψ_v` is positive definite, then `v = 0`.
  - **Corollary.** If `lam` is full-cone Weil-positive with `Σ_n |lam(n) − Λ(n)| n^{−1+η} < ∞`, then `lam = Λ`. Equivalently, the deviation's Dirichlet series has absolute abscissa `< 1`.

## Reach

It contains MUST-571, and so every earlier sparse and log-square class. Moreover:
- supports with `#(S ∩ [1, X]) ≤ C X^{1/2−η}` (box deviations);
- full-support deviations `|lam(n) − Λ(n)| ≤ C n^{−ε}`.

The remaining wall is deviations of the size of `Λ` itself, where `Σ |v| n^{−1/2} = ∞`. There the lifted main-term functional is the critical gcd kernel `gcd(n, m)/√(nm)`, which annihilates `μ(n)/√n` formally.

## Why compact windows cannot reach it

The transform of a compact-window test decays only like `(log n)^{−K}`. The Bochner/Fubini pairing then needs `Σ |v(n)| (1 + log n)^{−K} < ∞`, which is exactly log-summability (MUST-571).

## Proof plan (paper)

Fix `η` and `n₀`; take `P = P_y` as in MUST-571.

1. **Analytic test.** Let `ω(t) = exp(−(t − 3L/2)²/H²)` with `H = L/log L`, `q` the MUST-571 weight, `G = ω q w^{−1}`, and `b = 1/2 − η/2`.
   - `G` is holomorphic in `|Im t| < 1/2`. The only poles of `w^{−1}` are at `±i/2`, since `1/Γℝ` is entire.
   - On horizontal lines `|G| ≪ e^{−(Re t − 3L/2)²/H² + O(1)} e^{π|Re t|/2} poly`, which is integrable.
   - Hence `|𝓕g(u)| ≪_L e^{−b|u|}`.
2. **Pairing for exponential decay.** From `K(y) ≤ C₁ e^{−2|y|}` and `|u| ≥ |c| − |u − c|`:
   `∫ K(u − c) |𝓕g(u)| du ≤ C (2/(2 − b)) e^{−b|c|}`.
   The Fubini interchange needs only `Σ |v(n)| n^{−b} < ∞`, which holds. Hence `Σ v(n) Re M(log n) ≤ 0`, with `M(y) = ∫ ω q |ζ|² e^{−iyt}`.
3. **Analytic tail.** Shift `t → t − ib` in `M(log n)`. The integrand `ω q ζ(½+it) ζ(½−it) e^{−it log n}` is holomorphic for `|Im t| ≤ b < 1/2`, because the poles of `ζ` are at `t = ∓i/2`. The horizontal edges vanish by Gaussian decay. This gives `|M(log n)| ≤ C_L n^{−b}` with `C_L = poly(L)` (convexity bounds for `ζ` at `Re = 1/2 ± b`, and `e^{b²/H²} ≤ e`).
4. **Twisted moments at `n ≤ N₀ = L^A`.** These are the MUST-570/571 estimates for the Gaussian window of width `H`:
   - diagonal `(hk)^{−1/2}(∫ ω log t − ω̂(0) log N + O(H(1 + log N)))`;
   - near-resonant mass `≤ H δ k min(√L, L/√h)` with `δ = L^{ε−1}`;
   - non-resonant `(Hδ)^{−K}`;
   - dual Mellin tails and residues `e^{−cL²}`, plus Gaussian tails `e^{−(log L)²/4}` of `ω` outside `[L/2, 5L/2]`.
5. **Sums.** Use `Σ_{n ≤ X} |v(n)| ≤ C X^{1/2−η}` and `Σ_{n > X} |v(n)| n^{−1/2} ≤ C X^{−η}`.
   - Near-resonant: `≤ H L^{ε}(√L · L^{1/2−η} + L · L^{−η}) = o(H log L)` for `ε < η`.
   - Uniform errors times `N₀^{1/2}`: negligible.
   - Tail `n > N₀`: `C_L Σ_{n>N₀} |v(n)| n^{−b} ≤ C_L N₀^{−η/2}`, negligible for `A` large.
   - Main term: `Π(1 − 1/p) ∫ ω log t ≍ H log L = L`. Diagonal remainders are `O(H) = o(L)`.
6. **Fibers, `y → ∞`.** As in MUST-571, since `Σ |v(n)| n^{−1/2} < ∞`.

## Lean programme
- (P1) Exponential-decay spectral pairing, `WeilNullPotentialSpectralPairing` extension.
- (P2) Gaussian notch test: holomorphy in the strip, contour shift of `𝓕g`.
- (P3) Twisted-moment stack for general smooth windows with Gaussian tails. This refactors the `ZetaNotch*` stack from `notchWindow` (block) to an abstract window with jets `‖W^{(j)}‖ ≤ c_j H^{−j} E(t)`.
- (P4) Analytic tail of `M`.
- (P5) Assembly.

## Log
- 2026-09-30 — created (cycle 169); conjecture survives the preliminary attack; paper proof plan above.

## Phase 4 verdict (2026-09-30): SURVIVES PRELIMINARY ATTACK

**Corpus audit.** The internal frontier is incomparable with or weaker than this class:
- MUST-571 (log-summable) and MUST-570 are contained, since `n^{−1/2+η} ≪ (1+log n)^{−J}`.
- `eq_vonMangoldt_of_weilPositiveFull_of_sqrt_scale` is contained: `|lam − Λ| ≤ C(log n)^B/√n`, so `Σ|v|n^{−1/2+η} ≪ Σ (log n)^B n^{η−3/2}`.
- `…_of_log_square_summable` is contained by Cauchy–Schwarz: `Σ|v|n^{−1/2+η} ≤ (Σ v² n (1+log n)^{−K})^{1/2}(Σ n^{−2+2η}(1+log n)^{K})^{1/2}`.
- The two-sided form of MUST-532 is contained; the one-sided excess and deficit theorems are incomparable.
- `…_of_sq_summable_separated` is incomparable.

**Mechanism check.**
- The strip of analyticity of the test `g = Ω q w^{−1}` is `|Im t| < 1/2`, because the double poles of `(¼+t²)^{−2}` sit at `±i/2`; `1/Γℝ` is entire. So `𝓕g(v) = O(e^{−c|v|})` for every `c < 1/2`. This is exactly the exponent the hypothesis needs, which makes the class the natural endpoint of the notch method.
- The critical case `Σ|v| n^{−1/2} < ∞` fails for two independent reasons: the near-resonance balance `δ u^{2−η}` needs `η > 0`, and the strip must stay strictly inside the poles.

## Phase 5 — complete paper proof

**Notation.**
- `a = 1/2 − η ∈ (0, 1/2)` (WLOG `η < 1/2`), `S = Σ_n |v(n)| n^{−a}`, `c = (a + 1/2)/2`, so `c − a = η/2` and `c < 1/2`.
- `B(s) = blockWindow 1 2 ½ (s)`. Then `notchWindow u (t) = B(t/u)` for `u > 0`, `B ∈ [0,1]`, and `supp B ⊂ [½, 5/2]`.
- `ρ_L(u) = e^{−(u−L)²}`.
- `Ω_L(z) = ∫_{1/2}^{5/2} B(s) s^{−1} e^{−(z/s − L)²} ds`. This is entire, and real and `≥ 0` on `ℝ`.
- `q = notchWeight P ε n₀ = Σ_{modes} m_{j,c} e^{i f_{j,c} t}`. Its entire extension `Q` satisfies `|Q(x+iy)| ≤ Σ|m| e^{F|y|}`.

**Step 1 (scale mixture).**
- For `t > 0`, the substitution `u = t/s` gives `Ω_L(t) = ∫_0^∞ ρ_L(u) u^{−1} notchWindow u (t) du`.
- For `t ≤ 0`, `(t/s − L)² ≥ L² + t²/6.25`, hence `0 ≤ Ω_L(t) ≤ 4 e^{−L²} e^{−t²/6.25}`.
- For continuous `F` with `|F(t)| ≤ C(1+|t|)²`, Tonelli (the integrand is supported in `u/2 ≤ t ≤ 5u/2`) gives
  `∫_{t>0} Ω_L F = ∫_0^∞ ρ_L(u) u^{−1} (∫ notchWindow u · F) du`.

**Step 2 (strip bounds).** For `|y| ≤ 1`:
- `|e^{−((x+iy)/s − L)²}| = e^{−(x/s−L)² + y²/s²} ≤ e^{4y²} ρ_L(x/s)`, so `|Ω_L(x+iy)| ≤ e^{4y²} Ω_L(x)`.
- `|Ω_L(x+iy)| ≤ C_{L,κ} e^{−κ|x|}` for every `κ`, because `(x/s − L)² ≥ x²/12.5 − L²`.

**Step 3 (pairing).**
- `W(z) = (2/(¼+z²))² Γℝ(½+iz)^{−1} Γℝ(½−iz)^{−1}` is holomorphic on `|Im z| ≤ c`, with `|W(x+iy)| ≤ C_W e^{π|x|}`. This follows from `exists_bound_norm_inv_Gammaℝ` for `|x| ≥ 2`, compactness for `|x| ≤ 2`, and `|¼+z²| ≥ ¼ − c²`.
- `G = Ω_L Q W` satisfies `|G(z) e^{−izv}| ≤ C e^{c|v|} e^{−|x|}` on the strip. The horizontal shift (`integral_horizontal_shift_(neg_)of_decay`) gives `|𝓕g(v)| ≤ C_g e^{−c|v|}`.
- Kernel smoothing: `K(y) ≤ C₁ e^{−2|y|}` and `e^{−c|w|} ≤ e^{−c|y|} e^{c|w−y|}` give `∫ K(w − y)|𝓕g(w)| dw ≤ C₁ C_g (2/(2−c)) e^{−c|y|}`.
- Fubini then needs only `Σ|v(n)| n^{−c} ≤ S`. Bochner (`−ψ_v = charFun σ`) and `Re G ≥ 0` give
  `Σ_n v(n) Re M_Ω(log n) ≤ 0`, where `M_Ω(y) = ∫ Ω_L q |ζ(½+it)|² e^{−iyt} dt`.

**Step 4 (analytic tail).**
- `Z(z) = ζ(½+iz) ζ(½−iz)` is holomorphic on `|Im z| ≤ c`, since `½ ± iz ≠ 1` there. It satisfies `|Z(x+iy)| ≤ C_Z(1+|x|)²` (`norm_riemannZeta_le_strip'` for `|x| ≥ 2`, compactness otherwise).
- Shifting to `Im z = −c` gives `|M_Ω(y)| ≤ e^{−cy} e^{4c²} C_Q C_Z ∫ Ω_L(x)(1+|x|)² dx` for `y ≥ 0`.
- By Step 1, `∫_{x>0} Ω_L(x)(1+x)² dx ≤ 2∫ρ_L(u)(1+5u/2)² du ≤ C(1+L)²`, and the part `x ≤ 0` is `O(e^{−L²})`.
- Hence `|M_Ω(log n)| ≤ C_T (1+L)² n^{−c}`, and `Σ_{n>N₁} |v(n)||M_Ω(log n)| ≤ C_T(1+L)² N₁^{−η/2} S`.

**Step 5 (per-scale main term with decaying envelope).** Take `u ≥ 16`, `δ(u) = u^{η/2−1} ≤ 1/4`, and `K` fixed. Every Bohr mode twist of `n` has reduced `h/k` with `k ≤ K₀ = twistBound` and `hk ≥ n/K₀`, hence `k/h ≤ K₀³/n`.
- `tsum_nearRes_le` and `tsum_nearRes_le'` give `u · nearMass ≤ min(24δK₀u^{3/2}, 16√2 δ K₀^{5/2} u²/√n) ≤ C δ u^{2−η} n^{−a}`. Check the two cases: for `n ≤ u` use `n^a ≤ u^a`; for `n > u` use `n^{−1/2} = n^{−a} n^{−η} ≤ n^{−a} u^{−η}`.
- The diagonal envelope is `≤ C u (1+log n) n^{−1/2} ≤ C' u n^{−a}`.
- Therefore
  `|Re M_u(log n) − mainWeight(n) e_P Re logWindow(u)| ≤ C[u n^{−a} + u^{1−η/2} n^{−a} + u^{2−Kη/2} + u² e^{−u²/32}]`.

**Step 6 (assembly at fixed P, n₀, ε = ±1).**
- Take `N₁ ≥ L^{4/η}` and `K ≥ (2 + 8/η)/η`, and write `Y_N = Σ_{n≤N} v(n) mainWeight(n)`.
- Sum Step 5 over `n ≤ N₁`, integrate against `ρ_L(u)/u` over `u ≥ 16`, and add the parts `u < 16` (`ρ ≤ e^{−(L−16)²}`), `t ≤ 0` (Step 1) and `n > N₁` (Step 4). The result is
  `Y_{N₁} e_P (2/e) log(L−1) ≤ C_E` for all large `L`.
- Every error term is either bounded (the diagonal gives `S√π C`; the near-resonance gives `∫ρ u^{−η/2} ≤ √π`) or polynomial in `L` times `e^{−L²/256}`, or `N₁^a (L/2)^{1−Kη/2} ≤ 2^{1+4/η}`, or `(1+L)² N₁^{−η/2} ≤ 4`.
- Letting `L → ∞` with `Y_{N₁} → Y` gives `Y(ε) ≤ 0` for `ε = ±1`.

**Step 7 (fibres).** This is verbatim MUST-571. With `P = P_y`:
- `2A_y ± B_y ≤ 0`;
- `A_y`, and `B_y − v(n₀)/1`, are bounded by `(2+√n₀) Σ_{n>y}|v(n)| n^{−1/2} → 0`, since `Σ|v| n^{−1/2} ≤ S`.

Hence `v(n₀) = 0` for every `n₀ ≥ 2`. ∎
