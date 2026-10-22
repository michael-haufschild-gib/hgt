# LP-maximality of Ξ: no Laguerre–Pólya operator other than a translation has Ξ in its image of LP

- **ID:** finite-order-newman-laplace-operator
- **Stage:** 1-in-progress (complete paper proof below, modulo two cited classical theorems)
- **Type:** THEOREM (paper)
- **Source:** loop card `rh-route-candidates-loop-2026-10-08.md`, rows 652–653, 656, 661
- **Statement:** let `0 < b < 4/π`. There is no `ψ` in the Laguerre–Pólya class with
  `ψ − b²ψ″ = Ξ`. More generally, the same holds for `φ(D)ψ = Ξ` whenever `φ` is a real
  polynomial of degree `d ≥ 2` with only real zeros, all of modulus `> π/4`.

## Goal
Newman's conjecture (Rodgers–Tao; corpus `DeBruijnNewmanNonnegative`) excludes the Gaussian
regulariser: `Ξ ∉ e^{−τD²}·LP`. This theorem excludes every finite-order real-rooted regulariser.
Ξ lies on the boundary of LP in every polynomial direction. For the producer programme it closes
the class "regularised real-rooted producers" `Ξ = φ(D)ψ`. The statement is RH-free: its proof
assumes RH without loss, and it cannot imply RH.

## Notation
`Ξ(x) = ξ(½+ix) = −A(x)Z(x)`, where `A(x) = ½(x²+¼)π^{−¼}|Γ(¼+ix/2)| > 0` and `Z` is Hardy's
function. Stirling gives `A(x) = c x^{7/4}e^{−πx/4}(1+O(1/x))`. `K_b(v) = e^{−|v|/b}/2b` is the
Green kernel of `1−b²D²`, and `ψ_b := K_b * Ξ`.

## Proof
1. **WLOG RH.** For `f ∈ LP` and real `c`, `f + cf′ ∈ LP` (step 3 below). So
   `1 − b²D² = (1−bD)(1+bD)` maps LP to LP, `ψ ∈ LP ⇒ Ξ ∈ LP`, and RH holds (corpus
   `riemannHypothesis_of_laguerrePolya_XiC`). From now on assume RH.
2. **Dense zeros of Ξ.** Under RH, `S(t) = O(log t/log log t)` (Littlewood). Since
   `N(t+h) − N(t) = (θ(t+h)−θ(t))/π + S(t+h) − S(t) + O(1/t)` with `θ′(t) = ½log(t/2π) + O(1/t)`,
   there are `C, t₀` such that every interval `[t, t+h(t)]` with `h(t) = C/log log t` and
   `t ≥ t₀` contains at least three zeros of Ξ, counted with multiplicity, all real.
3. **Interlacing.** Let `f ∈ LP` be non-zero with at least one real zero, and `c ≠ 0` real.
   Between consecutive zeros `p < p′` of `f`, `(f′/f)′ = −2α − Σ_k (x−x_k)^{−2} < 0`, so `f′/f`
   decreases strictly from `+∞` to `−∞`. Hence `f + cf′` has exactly one zero in `(p,p′)`, and it is
   simple. At a zero of `f` of multiplicity `m`, `f + cf′` has a zero of multiplicity exactly `m−1`.
   **Consequence:** an open interval free of zeros of `f` contains at most one zero of `f + cf′`.
   Apply this with `g = ψ + bψ′` and `Ξ = g − bg′`. An open interval `J` free of zeros of `ψ` contains
   at most one zero of `g`, splits into at most two `g`-zero-free pieces, and so contains at most two
   zeros of Ξ. (If `q ∈ J` is a zero of `g`, it is simple and `Ξ(q) = −bg′(q) ≠ 0`.) With step 2,
   **`ψ` has a zero in every interval `[t, t+h(t)]`, `t ≥ t₀`.**
4. **ψ = ψ_b.** Every real entire solution is `ψ_b + c₁e^{x/b} + c₂e^{−x/b}`. Here `ψ_b` decays on
   `ℝ` (step 5), so `c₁ ≠ 0` would make `ψ` zero-free on some `[X, ∞)`, contradicting step 3. Hence
   `c₁ = 0`, and likewise `c₂ = 0`. So `ψ = ψ_b`.
5. **Normal form.** Put `s := ψ_b/A` and `k(v) := e^{−|v|/b−πv/4}/2b`. Then `k, k′ ∈ L¹∩L²`,
   `k` is continuous, and `k′` is bounded with one jump. Split
   `ψ_b(x) = ∫K_b(x−y)Ξ(y)dy` at `|y−x| ≤ x/2`.
   - For `y < 0` the contribution relative to `A(x)` is `O(e^{x(π/4−1/b)}) → 0`.
   - For `0 ≤ y ≤ x/2` it is `O(e^{x(π/8−1/(2b))}) → 0`. Both use `b < 4/π`.
   - Locally, `A(x+v)/A(x) = e^{−πv/4}(1+O(|v|/x))`.
   Hence `s(x) = −(k*Z)(x) + E(x)` and `s′(x) = −(k′*Z)(x) + E₁(x)` (integration by parts), with
   `(1/T)∫_T^{2T}(E² + E₁²) → 0`, using `∫_T^{2T}Z² ≪ T log T`.
6. **Bounded mean-square frequency.** Ingham's shifted second moment, uniform for bounded shifts:
   `(1/T)∫_T^{2T}Z(x+v₁)Z(x+v₂)dx = (1/T)∫_T^{2T} 2Re[(x/2π)^{iΔ/2}ζ(1+iΔ)]dx + o(1)`, with
   `Δ = v₂−v₁`. The regular combination at `Δ = 0` equals `log(x/2π) + 2γ`. Tails `|v| > D` are
   handled by Cauchy–Schwarz and the exponential decay of `k`. With `K := k⋆k` (continuous,
   integrable) and the Dirichlet integral `∫K(Δ)·2sin(ΔL/2)/Δ dΔ → 2πK(0)` (`L → ∞`), plus
   Riemann–Lebesgue for the regular part of `ζ(1+iΔ)`:
   `(1/T)∫_T^{2T}(k*Z)² → 2π‖k‖₂²` and `(1/T)∫_T^{2T}(k′*Z)² → 2π‖k′‖₂²`.
7. **Poincaré.** Tile `[T,2T]` by intervals `I_j` of length `h = h(T)` (the largest `h(t)` on the range). Each contains a zero of `s`
   (step 3), so for `x ∈ I_j`, `|s(x)| ≤ ∫_{I_j}|s′| ≤ h^{½}(∫_{I_j}s′²)^{½}`, hence
   `∫_{I_j}s² ≤ h²∫_{I_j}s′²`. Summing and using step 6:
   `2π‖k‖₂²(1+o(1)) ≤ h(T)²·2π‖k′‖₂²(1+o(1))`. Since `h → 0`, this is false for large `T`. ∎

## General polynomial case
For `φ(z) = c∏_{j≤d}(1 − z/a_j)`, `d ≥ 2`, real `a_j` with `|a_j| > π/4`:
- step 3 iterates to "a `ψ`-zero-free interval contains `≤ d` zeros of Ξ";
- the Green kernel of `φ(D)` is continuous, with bounded derivative and decay rates `|a_j| > π/4`, so steps 4–7 go through.
- `d = 1` fails at step 6: the kernel has a jump, so `s′` contains `Z/b` and the mean-square frequency grows like `log T`. That case is open.

## Dependencies
- Classical, not in Lean:
  - Littlewood's RH-conditional bound `S(t) = O(log t/log log t)`. The corpus has the companion bound `|ζ| ≤ exp(C log t/log log t)` (`RiemannHypothesisLittlewoodBound`).
  - Ingham's shifted second moment, uniform for bounded shifts.
- Elementary: LP interlacing, Poincaré, Dirichlet integral, Riemann–Lebesgue.

## Gates
- [x] 0 → 1: well-posed; complete proof outline.
- [ ] 1 → 2: write steps 5–6 with explicit error terms; state Ingham's uniform shifted moment exactly
  and check uniformity in `|v| ≤ D = C log T`.
- [ ] 2 → 3: Lean. Order of work:
  - LP interlacing lemma (`f + cf′`);
  - RH ⇒ `N(t+h)−N(t) ≥ 3` with `h = C/log log t`;
  - the Poincaré tiling;
  - Ingham's shifted moment, the heaviest piece.

## No-go reading
- Producers of the form `Ξ = φ(D)ψ`, `ψ ∈ LP`, `φ` a real-rooted polynomial of degree `≥ 2`, do not exist.
- **Mechanism:** an LP pre-image has Ξ's zero density, so zeros at every scale `h(t) → 0`. But every finite-order Green kernel smooths `Z`, and `Z` has a flat mean-square spectral density, so the result has bounded mean-square frequency `‖k′‖₂/‖k‖₂`. Poincaré makes the two incompatible.
- **Positive survivor:** the mean-square frequency identity of step 6, `(1/T)∫(k*Z)² → 2π‖k‖₂²` for every `k ∈ L¹∩L²` with exponential decay. It says the spectral measure of Hardy's `Z` is asymptotically flat (`2π`-normalised Lebesgue measure) at every fixed scale. This is a usable tool for any smoothing argument on the critical line.

## Degree one, and every LP symbol with a real zero (row 662)
**Theorem.** Let `φ ∈ LP` have a real zero `a` with `|a| > π/4`, or with `|a| < π/4` and
`Φ(ia) ≠ 0` (Riemann's kernel `Ξ(x) = ∫Φ(u)cos(xu)du`). Then no `ψ ∈ LP` satisfies `φ(D)ψ = Ξ`.
Together with Newman's theorem (Gaussian symbols `e^{−αz²}`, `α > 0`), the only LP operators
`φ(D)` with `Ξ ∈ φ(D)·LP` are, up to the exceptional zeros above, the translations `Ce^{βz}`.

**Reduction to degree one.** Write `φ(z) = (1 − z/a)φ̃(z)` with `φ̃ ∈ LP`. If `φ(D)ψ = Ξ` with
`ψ ∈ LP`, then `ψ̃ := φ̃(D)ψ ∈ LP` (Laguerre) and `Ξ = (1 − D/a)ψ̃ = ψ̃ + bψ̃′` with `b = −1/a`.

**Degree one, `|b| < 4/π` (i.e. `|a| > π/4`).** Take `b > 0`; `b < 0` follows from `x ↦ −x`, since Ξ
is even.
1. WLOG RH.
2. **Interlacing.** In each gap of `ψ`, `ψ+bψ′` has exactly one simple zero, and at a zero of
   multiplicity `m` of `ψ` it has multiplicity `m−1`. Hence every closed interval `[γ, γ′]` between
   consecutive distinct zeros of Ξ contains a zero of `ψ`: either an interior sign change or a
   multiple zero of `ψ` at an endpoint. Interlacing at `−∞` forces the homogeneous term `Ce^{−x/b}` to
   vanish, so `ψ(x) = (1/b)∫_{−∞}^x e^{−(x−y)/b}Ξ(y)dy`.
3. **ODE.** `s := ψ/A` satisfies `bs′ = −Z − c(x)s` with `c(x) = 1 + bA′/A = c₀ + O(1/x)`,
   `c₀ = 1 − bπ/4 > 0`, and `s = −k₁*Z + o_{L²}(1)`, `k₁(v) = (1/b)e^{c₀v/b}1_{v<0}`.
4. **Local smallness.** Unconditionally all zero gaps of ξ at large height are `≤ 3/2`
   (`|S(t)| ≤ 0.12 log t + O(log log t)`). On a Ξ-gap `I` of length `ℓ ≤ 3/2`, `s` vanishes
   somewhere in `I`. Grönwall on `bs′ = −Z − cs` gives `max_I|s| ≤ C_b ∫_I|Z|`, hence
   `∫_I s² ≤ C_b²ℓ²∫_I Z²`. When `2Cℓ ≤ b` this is the Lean lemma
   `integral_sq_le_of_firstOrderFilter`, with `C_b = 2/b`.
5. **Summation.** `∫_T^{2T}s² ≤ C_b²∫_T^{2T}ℓ(x)²Z(x)²dx`. Apply Hölder with `q = 3/2`, `p = 3`.
   - Hardy–Littlewood (`∫Z² ≍ T log T`) and Ingham (`∫Z⁴ ≍ T log⁴T`) interpolate to
     `∫|Z|³ ≪ T(log T)^{5/2}`.
   - Gap moments `∫ℓ⁶ ≪ T(log T)^{−6}` come from `|{ℓ > u}| ≤ 2|{|S(x+u/2)−S(x)| ≥ u log T/4π}|`
     and the unconditional moments `∫|S(x+h)−S(x)|^{2m} ≪_m T(log(2+h log T))^m` (Selberg/Fujii),
     with `m ≥ 4`.
   - Together: `∫ℓ²Z² ≪ T(log T)^{−2}·(log T)^{5/3} = T(log T)^{−1/3} = o(T)`.
   All inputs are unconditional classical moment theorems. RH (WLOG) is used only so that the
   zeros counted by `N(t)` are the real zeros of Ξ.
6. **Flat spectrum.** `(1/T)∫_T^{2T}(k₁*Z)² → 2π‖k₁‖₂² = π/(bc₀) > 0` (Ingham shifted moment,
   `K = k₁⋆k₁ = (2bc₀)^{−1}e^{−c₀|Δ|/b}`). This contradicts step 5. ∎

**Degree one, `|b| > 4/π` (`|a| < π/4`).** `ψ(x) = e^{−x/b}((1/b)∫_ℝe^{y/b}Ξ(y)dy + o(1))` as
`x → +∞`. The integral is a non-zero multiple of `Φ(i/b)`. If it is non-zero, `ψ` is eventually
zero-free, contradicting the interlacing of step 2. ∎

**Mechanism.** Every non-translation LP operator has a first-order factor, and its inverse is an RC
low-pass filter. An LP pre-image must change sign in every gap of Ξ, but the filtered Hardy
function has macroscopic mean square `π/(bc₀)` and can only change sign at the cost
`∫ℓ²Z² = o(T)`. Newman's Gaussian case is the zero-free member of the same family.

## Lean status
- [L] `GaloisForLFunctions.HTGeometry.integral_sq_le_of_firstOrderFilter` and
  `abs_le_of_firstOrderFilter` (module `HTGeometry/FirstOrderFilterVanishingIntervalBound`, wired
  into `HTGeometry.lean`; standard axioms). These are step 4 of the degree-one proof.
- Corpus neighbour: `HTGeometry.LaguerreShiftRealRootCount` (`p − cp′` loses at most one real root).
- [L] `RHTower.laguerrePolya_sub_smul_deriv` and `riemannHypothesis_of_XiC_eq_sub_smul_deriv`
  (`XiLaguerrePolyaFirstOrderPreimage`): step 1 (WLOG RH).
- [L] `RHTower.exists_root_Icc_of_sub_C_mul_derivative` and `laguerreL1_eval_pos`
  (`LaguerreShiftInterlacing`): polynomial interlacing via the strict Laguerre inequality.
- [L] `RHTower.exists_zero_Icc_of_laguerrePolya_sub_smul_deriv`
  (`LaguerrePolyaFirstOrderInterlacing`): step 2 for entire LP functions, via Hurwitz.
- Not formalized:
  - (FS) the flat-spectrum lower bound for the RC-filtered `Z`, handed to the parallel session;
  - (G) the gap-weighted moment `∫ℓ²Z² = o(T)`;
  - the ODE and gap step are done, see the next line.
- [L] `RHTower.integral_sq_le_of_laguerrePolya_firstOrder_gap` (`LaguerrePolyaFirstOrderGapBound`):
  the deterministic half of the degree-one proof (steps 2–4) for arbitrary positive amplitudes `A`.
  Remaining for Stage 3: (FS), (G), and the summation over gaps.


## (FS) without shifted moments: paper proof via Riemann–Siegel (row 667)
**Claim.** For `a > 0` and `s_a(x) = ∫_0^∞ e^{−av}Z(x−v)dv`, `(1/T)∫_T^{2T}s_a² → π/a`.
1. **Riemann–Siegel:** `Z(t) = Re[2e^{iθ(t)}Σ_{n≤N(t)}n^{−½−it}] + O(t^{−¼})`, `N(t) = ⌊√(t/2π)⌋`.
2. **Moving cutoff.** For `v ≤ V = x^{1/3}`, `N(x−v)` differs from `N(x)` only for `O(V/√x)` top
   terms of size `x^{−¼}`, and `e^{−av}` makes `v > V` negligible. So
   `s_a(x) = Re[2e^{iθ(x)}Σ_{n≤N(x)} n^{−½−ix}/(a + iω_n(x))] + E(x)`, with
   `ω_n = θ′(x) − log n = log(N/n) + O(1/x)` (phase Taylor expansion
   `θ(x−v) = θ(x) − vθ′(x) + O(v²/x)`) and `∫_T^{2T}E² = o(T)`.
3. **Square.** `(Re[e^{iθ}B])² = ½|B|² + ½Re[e^{2iθ}B²]`. The second term has phases
   `2θ(x) − x log(nm)` with frequency `log(x/2πnm) ≥ 0`. Pairs `(N−j, N−k)` have frequency
   `≍ (j+k)/N`, so the mean is `≪ (1/a²T)Σ_{j,k≤N}N/(N(j+k)) ≪ N log N/(a²T) → 0`.
4. **Mean value with slowly varying coefficients.** On subintervals of length `L = T^{0.9}`
   (`≫ N log N`) the coefficients `c_n = n^{−½}/(a+iω_n)` and the cutoff `N(x)` are frozen up to
   `o(1)` relative errors; the moving-top terms contribute `≪ T^{−0.1}/a²`. The MVT gives
   `(1/T)∫½|B|² = 2Σ_{n≤N}|c_n|² + o(1)`.
5. **Sum.** `Σ_{n≤N}n^{−1}/(a² + log²(N/n)) → ∫_0^∞du/(a²+u²) = π/(2a)`. Hence the limit is
   `π/a = 2π‖k₁‖₂²` with `k₁(v) = e^{−av}1_{v>0}`. ∎
The same computation gives `(1/T)∫(k*Z)² → ∫_ℝ|k̂(ω)|²dω/(2π)·2π = 2π‖k‖²` for every
exponentially decaying `k ∈ L¹∩L²`, and in particular the upper bound for `k′` needed in the
degree-two route.

**Smooth-AFE caveat.** With a smooth AFE (such as the corpus's Gaussian
`hardyZ_eq_two_tsum_smoothAFE`) the transition zone around `n ≈ N` makes the anti-diagonal pairs
of step 3 non-oscillating. Those cross terms must be kept, and they reassemble the sharp value. The
corpus has no sharp Riemann–Siegel formula with an error bound (`HardyZ.lean` records the exact
carrier isometry only). Formal (FS) therefore needs either that formula or the cross-term
bookkeeping for the Gaussian AFE.
- [L] `RHTower.exists_zero_Icc_of_laguerrePolya_sub_sq_smul_deriv2`
  (`LaguerrePolyaSecondOrderInterlacing`): four distinct real zeros of `ψ − b²ψ″` force a zero of `ψ`
  between them (degree-two interlacing).
- [L] `HTGeometry.integral_sq_le_of_tiling` (`PoincareTilingVanishing`): `∫s² ≤ h²∫s′²` when every
  tile of length `h` contains a zero of `s` (step 7).
- Degree-two route, remaining for Stage 3: (FS) with the matching upper bound for `k′`, (L) (in
  progress in the parallel session), the normal form `ψ/A = k*Z + o_{L²}`, and the bridge from
  multiplicity counts to distinct zeros (a multiple zero of `ψ − b²ψ″` is a zero of `ψ`).


## Plan for formal (FS) on the corpus's Gaussian smooth AFE (Option B)
- Use `hardyZ_eq_two_tsum_smoothAFE_real` with cutoff at the balance point `x = √(t/2π)`.
- Filter each twisted term: `∫_0^∞e^{−av}cos(φ_n(x−v))dv = Re[e^{iφ_n(x)}/(a+iω_n)] + O(v²/x)`.
- **Diagonal terms:** the MVT on blocks of length `T^{0.9}` gives `2Σ_n|c_n|²V(n)²`.
- **Anti-diagonal terms** `nm ≈ t/2π`:
  - The phase `2θ − x log nm` is stationary at `x₀ = 2πnm`, with value `≡ −π/4 (mod 2π)` because `nm ∈ ℤ`. So these terms add coherently.
  - There `ω_m = −ω_n` and `c_nc_m = (nm)^{−½}/(a²+ω_n²) > 0`.
  - Their total is `2Σ_n|c_n|²V(n)V(N²/n)·(1+o(1))`, a divisor average over `k = nm ∈ [T,2T]/2π`.
- **Assembly:** with `V(u) + V(1/u) = 1`, diagonal plus anti-diagonal is `2Σ|c_n|²V(n)`. Symmetry of `|c_n|²` under `n ↦ N²/n` turns this into `∫_ℝ du/(a²+u²)·(…) = π/a`.
- **Lean ingredients:**
  - stationary phase for `∫e^{iΦ}w` with `Φ″ = 1/x`;
  - divisor averages `Σ_{k}Σ_{n|k}g(log(n/√k))` (the corpus has divisor-sum asymptotics);
  - the MVT (`dirichlet_meanValue_theorem`);
  - the phase asymptotics (`HardyZPhaseAsymptotic`).
- [L] `HTGeometry.norm_integral_expFilter_phase_sub_le` (`ExponentialFilterPhaseLinearization`):
  `‖∫_0^∞e^{−av}e^{i(−ωv+R(v))}dv − 1/(a+iω)‖ ≤ ε/a³` when `|R(v)| ≤ (ε/2)v²`, together with
  `∫_0^∞v²e^{−av} = 2/a³`. This is the term-wise filtering step of (FS), step 2.

## Corollaries (rows 683, 688)
- **Kernel criteria.** A sufficient real-rootedness criterion on even kernels that is stable under
  `K ↦ K/(1+b²u²)` (`b < 4/π`) or `K ↦ Ke^{−εu²}` fails for Riemann's `Φ`.
- **Appell no-go.** If `P_k = φ(D)x^k` with `φ ∈ LP` a non-translation (Hermite `H_k = e^{−D²/4}(2x)^k`),
  then `Ξ = Σb_kP_k` forces `g = Σb_kx^k = φ(D)^{−1}Ξ ∉ LP`. Turán's Hermite-strip theorem therefore
  cannot prove RH. The Hermite case is exactly `H_{−1/4}`, the backward heat flow.
- [L] (L), Littlewood short windows under RH (`RHTower.Littlewood`, module `LittlewoodShortWindowZeroCount`):
  `riemannHypothesis_eventually_xiZeroCount_window_ge`, which gives `∃ C > 0, ∀ m, ∃ t₀, ∀ t ≥ t₀,
  m ≤ xiZeroCount(t + C/log log t) − xiZeroCount t`. Tiling input for degree ≥ 2 under the WLOG-RH reduction.

## Degree two via theta Parseval (row 690): no Riemann–Siegel, no Stirling
**Theorem.** Let `a₁, a₂ ∈ ℝ∖{0}` with `a₁a₂ > 0`, or with `max(|a₁|,|a₂|) > π/4`. Then no
`ψ ∈ LP` satisfies `(1 − D/a₁)(1 − D/a₂)ψ = Ξ`. Hence, with Newman, `Ξ ∉ φ(D)·LP` for every
`φ ∈ LP` that has a Gaussian factor or two real zeros of this kind. Same-sign pairs have **no
exceptional set**, which improves the "general polynomial case" above.

**Conventions.** `Ξ(x) = ∫Φ(u)e^{ixu}du`. `Φ(z) = Σ_{n≥1}e^{z/2}R(n²e^{2z})e^{−πn²e^{2z}}` with
`R = 4π²X² − 6πX` (corpus `cuspSeries riemannCuspPoly`), holomorphic on `|Im z| < π/4`, even, and
real on `ℝ`, so `|Φ(−u+ic)| = |Φ(u+ic)|`. Put `m(u) = 1/((1−iu/a₁)(1−iu/a₂))` and
`ψ₀(x) = ∫Φ(u)m(u)e^{ixu}du`, so that `φ(D)ψ₀ = Ξ`.

**Theta form on the line `Im z = c = π/4 − ε`.** With `z = u + ic`, `τ := −e^{2u}e^{−2iε}` and
`S_k(τ) = Σ_{n≥1}n^k e^{iπn²τ}`:
`Φ(z) = e^{z/2}(4π²e^{4z}S₄(τ) − 6πe^{2z}S₂(τ))` and `Im τ = e^{2u}sin 2ε`. So `|Φ(z)|²` is
`e^{9u}|S₄|²` up to the lower-order term `e^{5u}|S₂|²`.

**Lemma P (Parseval over a period).** `∫_X^{X+2}|S_k(x+iy)|²dx = 2Σn^{2k}e^{−2πn²y}` for `y > 0`.

**Lemma V (vertical variation).** `∂_yS_k = −πS_{k+2}`, so for `y₀ ≤ y(x) ≤ y₁` on a period,
`‖S_k(·+iy(·)) − S_k(·+iy₀)‖²_{L²(period)} ≤ 2π²(y₁−y₀)²Σn^{2k+4}e^{−2πn²y₀}`.

**Lemma M.** `Σn^{2k}e^{−2πn²y} ≍_k y^{−k−½}` for `0 < y ≤ 1`, and `≤ C_ke^{−2πy}` for `y ≥ 1`.

**Ray bounds.** Parametrise the ray by `r = e^{2u}`, `τ = −re^{−2iε}`, `du = dr/2r`. One period of
`Re τ` is an `r`-interval `[R, R+P]` with `P = 2/cos 2ε`, on which `Im τ` runs over
`[y₀, y₀ + 2tan 2ε]`, `y₀ = R sin 2ε`. Lemmas P, V and M give:
- **(Up)** for every `j ∈ ℤ`, `∫_j^{j+1}|Φ(u+ic)|²du ≤ Cε^{−9/2}`, uniformly in `j` and in small `ε`.
  For `y₀ ≤ 1` the per-period bound is `C(R sin 2ε)^{−9/2}`, using `tan 2ε/y₀ = 1/(R cos 2ε) ≤ 1`.
  The weight `r^{7/2}` and the `≍ R(e²−1)/P` periods per unit of `u` cancel it to `Cε^{−9/2}`.
  The range `y₀ ≥ 1` is exponentially small, and `j < 0` follows by symmetry.
- **(Low)** there are `U₀` and `c₀ > 0` with `∫_{U₀}^{U₀+1}|Φ(u+ic)|²du ≥ c₀ε^{−9/2}` for all small `ε`.
  Take the main term `S₄(·+iy₀)` on each period, which gives `2Σn^8e^{−2πn²y₀} ≥ c y₀^{−9/2}`.
  Lemma V bounds the error by `Cy₀^{−9/2}/(R cos 2ε)²`, which is `≤ (c/4)y₀^{−9/2}` once `R ≥ e^{2U₀}`.
  The `S₂` term is `O(ε^{−5/2})`.

**Proof of the theorem.**
0. Since Ξ is even, `x ↦ −x` flips the signs of the `a_j`. Arrange that every negative `a_j` has
   `|a_j| > π/4`. Then the poles `−ia_j` of `m` avoid the closed strip `0 ≤ Im ≤ π/4`, and
   `(1+u²)|m(u+ic)|² ≤ C/(1+u²)` uniformly for `c ∈ [π/8, π/4]`.
1. WLOG RH, since `φ(D)` preserves LP.
2. (L) gives at least 3 zeros of Ξ, with multiplicity, in `[t, t+h(t)]`, `h(t) = C/log log t`, for
   `|t| ≥ t₀`. An open interval free of zeros of `ψ` contains at most two zeros of Ξ, all simple
   (first-order interlacing applied twice). So `ψ` vanishes in every such window, at both ends of `ℝ`.
3. `ψ − ψ₀ = C₁e^{a₁x} + C₂e^{a₂x}` (or `(C₁+C₂x)e^{ax}`). By the contour shift `ψ₀ → 0` at
   `±∞`, so a non-zero homogeneous part makes `ψ` eventually zero-free at one end, contradicting
   step 2. Hence `ψ = ψ₀`.
4. Put `g = e^{cx}ψ₀`. Plancherel after the contour shift gives `∫g² = 2π∫|Φm|²(u+ic)du`, which is
   `≥ c₁ε^{−9/2}` by (Low). It also gives `∫g′² = 2π∫u²|Φm|²(u+ic)du`, which is `≤ C₁ε^{−9/2}` by
   (Up) and the summable weight of step 0.
5. Poincaré tiling on `[X₁, ∞)` with tiles of length `h(X₁)` gives `∫_{X₁}^∞g² ≤ h(X₁)²∫g′²`.
   Also `∫_{−∞}^{X₁}g² ≤ M(X₁)`, independent of `ε`. Choose `X₁` with `C₁h(X₁)² ≤ c₁/2` and let
   `ε → 0`; this is a contradiction. ∎

**Why it works.** The Abelian mean square `∫e^{2cx}ψ₀²` is *exactly* an `L²` norm on the line
`Im u = π/4 − ε`, where Riemann's kernel is a theta series approaching the real axis. Parseval over
periods of `Re τ` makes `|Φ|²` flat in `u` at height `ε^{−9/2}`. That is the flat spectrum of Hardy's
`Z`, seen at the theta boundary. The lower bound needs only one window, because Plancherel is
termwise positive, so the anti-diagonal and balance-point bookkeeping of the Riemann–Siegel proof
disappears. Degree one fails at step 4 only, since `u²|m|² → 1/b²` is not integrable against a
flat spectrum of width `log(1/ε)`.

**Lean plan.** (T1) Lemma P; (T2) Lemma V and the ray bounds (Up)/(Low); (T3) Lemma M; (T4) contour
shift and Plancherel for `Φm` (parallel session); (T5) step 3; (T6) assembly with
`LittlewoodShortWindowZeroCount`, `LaguerrePolyaFirstOrderInterlacing` and `PoincareTilingVanishing`.

**Lean status of the degree-two programme (2026-10-09).**
- [L] (T4) `RHTower.KernelStrip` (modules `RiemannKernelComplexStrip`, `RiemannKernelStripPlancherel`).
  - `kernelC` is holomorphic on `|Im z| < π/4` (`differentiableAt_kernelC`), even (`kernelC_neg`), and decays like `C_r e^{−r|Re z|}` on closed substrips (`exists_norm_kernelC_le`).
  - (a) `exp_mul_kernelPsi_eq`.
  - (b) `integral_norm_sq_exp_mul_kernelPsi`.
  - (c) `hasDerivAt_exp_mul_kernelPsi` and `integral_norm_sq_deriv_exp_mul_kernelPsi`, for `m` holomorphic and bounded on `0 ≤ Im ≤ c < π/4`.
- [L] (T5) `RHTower.KernelStrip.ofReal_eq_kernelPsi_of_ode` (module `RiemannKernelStripHomogeneous`).
  - Statement: a real solution of `ψ − (1/a₁+1/a₂)ψ′ + ψ″/(a₁a₂) = Ξ` with zeros arbitrarily far at both ends equals `ψ₀ = kernelPsi (lorentzPair a₁ a₂)`.
  - Any nonzero `a_j` work, and `a₁ = a₂` is allowed.
  - Supporting results: `kernelPsi_ode` and `eq_zero_of_homogeneous`.
- [L] (T1/T3, partial) `HTGeometry.ThetaSumPeriodParseval`: Parseval over periods, moment bounds, vertical variation and the ray integral bound `integral_norm_sq_thetaMoment_ray_le`.
- Open: the ray bounds (Up)/(Low) for `kernelC(u + i(π/4 − ε))`, and the assembly (T6).
- [L] (T6a) `RHTower.eq_zero_and_deriv_eq_zero_of_sub_smul_deriv` (module `LaguerrePolyaDoubleZeroBridge`): a double zero of `f − cf′` is a double zero of `f`, for `f` in the Laguerre–Pólya class with a real zero and `c ≠ 0`.
- [L] (T6b) `RHTower.Littlewood.riemannHypothesis_XiC_window_zeros(_neg)` (module `XiRealZeroWindowsRH`): under RH, every window `(t, t + C/log log t]` and its mirror contain three distinct real zeros of `Ξ` or one critical real zero.
- The ray bounds and the final contradiction are being done by the session that owns this card (hgt-38, 2026-10-09).

## Lean status after the theta route (2026-10-09)
- [L] **Degree two, same-sign zeros, closed:** `RHTower.KernelStrip.not_exists_laguerrePolya_secondOrder_preimage_XiC`
  (`RiemannKernelStripLPMaximality`; axioms `propext, Classical.choice, Quot.sound`).
- Modules:
  - `HTGeometry/ThetaSumPeriodParseval`: Parseval over periods, moment bounds, vertical variation, ray bound.
  - `RHTower/RiemannKernelStripThetaBounds`: theta form of `Φ` on `Im = c`, flat window bounds, symmetry.
  - `RHTower/RiemannKernelStripLPMaximality`: whole-line bounds, tiling with a head, contradiction, capstone.
  - Parallel session: `RiemannKernelComplexStrip`, `RiemannKernelStripPlancherel`, `RiemannKernelStripHomogeneous`,
    `LaguerrePolyaDoubleZeroBridge`, `XiRealZeroWindowsRH`, `XiSecondOrderLaguerrePolyaPreimage`.
- Open for Stage 3:
  - degree two with mixed signs (one `|a_j| > π/4`): same proof, poles of `m` on one side;
  - degree one: needs gap moments (paper proof above).

## Degree one in Lean: plan (Abelian + large-gap tail)
Target: `Ξ ∉ (1 − D/a)·LP` for every `a ≠ 0`. For `a < 0` use the reflection `x ↦ −x`. For `a > 0`, take
`m(u) = 1/(1 − iu/a)` (pole below the real axis) and `g = e^{cx}ψ`.
- **(M1) total theta mass.** `∫|Φ(u+ic)|²du ≲ κ^{-9/2}(1 + log(1/κ))`, `κ = cos 2c`. Windows with
  `y₀ = e^{2U}κ ≥ 1` decay like `y₀^{13/2}e^{−πy₀}`, using `Σn^{2k}e^{−2πn²y} ≤ C_ke^{−πy}` for `y ≥ 1`.
  Plancherel with `m ≡ 1` gives the Abelian second moment of Ξ; `∫_X^{2X} f ≤ e⁴∫e^{−2x/X}f` makes it dyadic.
- **(M2) two-radius Grönwall.** `ψ′ = a(ψ − Ξ)`. A zero of `ψ` within `r_s` on `G` and within `r_l`
  everywhere give `∫e^{βx}ψ² ≤ K(r_s²∫e^{βy}Ξ² + r_l²∫_{B′}e^{βy}Ξ²)`, where
  `B′ = {y : [y, y+r_l] ⊄ G}`. Proof: pointwise Grönwall, then Fubini.
- **(M3) mesh to measure.** With `G = {x : N(x) − N(x − r_s) ≥ 2}`:
  `|B′| ≤ 4(r_l + r_s)/r_s · |{t : N(t + r_s/4) = N(t)}|`. Proof: Fubini on `1_E(t)1[y − r_s ≤ t ≤ y + r_l]`.
- **(LGT)** Under RH, `|{t ∈ [T,2T] : N(t + η/log T) = N(t)}| ≤ C_kT(log(2+η))^k/η^{2k}`. Parallel session.
- **(D1/D3)** First-order identification and windows (parallel session); fourth moment of Ξ (D7).
- **Assembly.** `r_s = 3η/log x` with `η = (log x)^{1/4}`, and `r_l = C/log log x`.
  - The short term is `o(κ^{-9/2})`, since the mass of `Ξ²e^{2cx}/log²x` is `≲ κ^{-9/2}/log(1/κ)`.
  - The long term is `o(κ^{-9/2})`, by Cauchy–Schwarz with the fourth moment and LGT with `k ≥ 10`.
  - Against the Plancherel lower bound `≥ Lκ^{-9/2}`.
- The parallel session handles `0 < |a| < a₀` separately by the Laplace argument (`XiStrongFirstOrderFilterNoGo`).
- [L] Degree-one programme, my half done:
  - `HTGeometry/FirstOrderTwoRadiusEnergy`: Grönwall, window averaging, two radii, flat stretches,
    bad-set measure, AM–GM.
  - `RHTower/RiemannKernelStripFirstOrderBounds`: `lorentzOne`, Plancherel lower bound.
  - `RHTower/RiemannKernelStripFirstOrderEnergy`: `false_of_firstOrder_data`, the full analytic core.
    Its inputs are first-order identification, zero windows, LGT with `k = 24`, and the 2nd/4th
    moments of Ξ.
  - Parallel session: `XiStrongFirstOrderFilterNoGo` (small `|a|`, no RH), `ZeroGapWindowPrimePolynomial`
    (LGT module A).
  - Remaining: LGT module B, D1, D3, D7, and the capstone glue.
- [L] Degree one, assembled modulo the fourth moment only. Built modules:
  - `XiExponentialMeanSquareThetaBound`: `exists_integral_exp_mul_norm_sq_XiC_le`, i.e. ∫_X^{2X} e^{πy/2}|Ξ|² ≤ C X^{9/2} log X. It comes from the flat theta mass on Im u = π/4 − 1/(2X): windows below height 1 carry κ^{-9/2} each, and there are log(1/κ) of them; windows above height 1 decay like e^{−2y}. No approximate functional equation is used.
  - `XiFirstOrderLaguerrePolyaMaximality`: `not_exists_laguerrePolya_firstOrder_preimage_XiC_of_fourthMoment`. For all a ≠ 0, given the dyadic fourth moment ∫ e^{πy}Ξ⁴ ≲ X⁸log⁴X, Ξ ∉ (1 − D/a)·LP. The case a < 0 follows by reflection.
  - Remaining: the fourth-moment input (hgt-61, from the corpus ζ fourth moment and Stirling).

## Transcendental symbols in Lean (2026-10-09, hgt-8a, MUST-873)
- `RHTower.KernelStrip.not_laguerrePolya_paperFT_div_symbol`: for every Laguerre–Pólya `φ` with `φ(0) ≠ 0` and a real zero `a ≠ 0`, the transform of `Φ(u)/φ(iu)` is not Laguerre–Pólya. Standard axioms.
- Route: `φ = (1 − z/a)φ₂` with `φ₂ = −a·dslope φ a ∈ LP` (`RHTower.laguerrePolya_dslope`). The general symbol theorem `laguerrePolya_paperFT_mul_symbol` applies `φ₂(D)` and lands on the degree-one damped transform, which `not_laguerrePolya_dampedKernelTransform` excludes.
- Modules:
  - `HTGeometry/LaguerrePolyaLocallyUniformLimit`;
  - `HTGeometry/LaguerrePolyaImaginaryAxisBounds`;
  - `RHTower/LaguerrePolyaDivideRealZero`;
  - `RHTower/RiemannKernelLaguerrePolyaSymbol`.
