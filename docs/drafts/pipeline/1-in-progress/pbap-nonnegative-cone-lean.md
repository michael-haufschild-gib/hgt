# Prime-blind positivity on the nonnegative cone (HF L349) — Lean programme

- **ID:** pbap-nonnegative-cone-lean
- **Stage:** 1-in-progress (paper proof complete in HF L349; this card is the formalization programme)
- **Type:** THEOREM (unconditional), existence half of the HF producer route
- **Source:** `hf-positive-hodge-attack/krein-producer-loops.md` L349, L355; route-candidates loop rows 712–715
- **Statement:** For real `g ≥ 0` with compact support whose autocorrelation vanishes at every `±log n`, `n ≥ 2`, the full Weil energy is nonnegative: `W(g) = pole(g) + arch(g) ≥ 0`. Hence every PBAP failure, i.e. every refutation of `W ≠ ∅`, needs sign-changing tests.

## Goal
This is the one unconditional theorem on the existence half (PBAP) that covers tests of arbitrarily long support. With MUST-718, RH = PBAP + (N1). This card closes the nonnegative sector formally.

## Proof plan (replaces L349's rearrangement by a 1D transport argument)
- **T1 (monotone transport) [new, mathlib-missing].** For measurable `S ⊂ ℝ` with `λ(S) = L < ∞`, let `F(u) = λ(S ∩ (−∞,u])`. Then:
  - `F` is monotone and 1-Lipschitz;
  - `F_*(λ|_S) = λ|_{[0,L]}`, and `F` is injective on `S` off a null set;
  - so every `g ≥ 0` supported in `S` equals `g'∘F` a.e. on `S`, with `g'` supported in `[0,L]` and `‖g'‖₂ = ‖g‖₂`.
- **T2 (kernel monotonicity).** For `k` decreasing on `[0,∞)`: `∫∫g g k(|u−v|) ≤ ∫∫g' g' k(|x−y|)`, since `|F u − F v| ≤ |u−v|` and `g ≥ 0`. For `K` increasing the inequality is reversed.
  - Apply T2 to the truncated Lévy kernels `min(ω, c)`: the Dirichlet form does not increase.
  - Apply it to `cosh(·/2)`: the pole does not increase.
- **T3 (Lévy–Khintchine form of arch).** `A(r) = A(0) + 2∫_0^∞(1 − cos rx)ω(x)dx` with `ω(x) = e^{−x/2}/(1−e^{−2x})`. So `arch(g) = A(0)‖g‖² + ½∫∫|g(u)−g(v)|²ω(|u−v|)` in the corpus normalization (`gammaHardyPhaseRate`).
- **T4 (dilation-free support).** Prime-blind `g ≥ 0` has `λ(supp g) ≤ log 2`. This is in Lean: `RHTower.DilationFree.volume_le_log_two_of_dilationFree`.
- **T5 (full window positivity).** `W(f) ≥ 0` for every real `f` supported in an interval of length `≤ log 2`.
  - Corpus has only the polar version, `one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo` (`μ₀(½log 2) ≥ 1/10`).
  - The full version needs a 2×2 Schur complement over the pole directions `e^{±x/2}`. For `f ≥ 0` the pole term is `2⟨f,e₊⟩⟨f,e₋⟩ ≥ 0`, which may shorten this step.
- **T6 (assembly).** Steps: `W(g) ≥ W(g')` by T1–T3, then `g'` lives on `[0, log 2]` by T4 and translation invariance, then `W(g') ≥ 0` by T5.

## Gates
- [x] 0 → 1 in-progress
- [ ] 1 → 2 (paper is HF L349; T5's Schur step still needs a written proof)
- [ ] 2 → 3 formalized

## Log
- 2026-10-09 — card created (route-candidates loop, after rows 712–715). The transport proof of T2 replaces Riesz rearrangement, so no symmetric-decreasing rearrangement is needed.
- 2026-10-09 — T3 (Lévy–Khintchine symbol plus Dirichlet-form identity) taken by hgt-8a, module `RHTower/GammaHardyPhaseRateLevyKhintchine`. T1/T2 by hgt-38. T5 open.
- 2026-10-09 — **T1/T2 closed [L]**: module `HTGeometry/MonotoneQuantileTransport` (standard axioms, wired after `LaguerrePolyaLocallyUniformLimit`).
  - `QuantileTransport.map_quantile_restrict_Ioo`: the quantile pushes `λ|_{(0,L)}` to `λ|_S`.
  - `abs_sub_le_abs_quantile_sub`: the quantile stretches distances.
  - `integral_restrict_eq_quantile`: single integrals transport exactly.
  - `integral_kernel_le_quantile`: cross terms against kernels decreasing in distance increase.
  - `integral_quantile_le_kernel`: for increasing kernels the inequality reverses.
  - No Riesz rearrangement is used: the Galois connection `G x ≤ u ↔ x ≤ F u` plus `Measure.ext_of_Iic` does it.
- **T5 analysis.**
  - After transport only nonnegative `f` on `[0, log 2]` are needed. For such `f`, `a = ⟨f,e₊⟩` and `b = ⟨f,e₋⟩` satisfy `a/b ∈ [2^{−½}, 2^{½}]`, so the pole Schur step need only be *copositive* on that cone, not PSD.
  - The crude bounds fail: the boundary term `2Ω(L/2) ≈ 3.847` and interior `ω(L) ≈ 0.943` leave `−0.87‖f‖² + 1.06(∫f)²`.
  - The pairwise-interval kernel `q(a, log 2) ≈ −0.13a` is negative for small centred `a`, so layer-cake entrywise positivity is false and a copositivity certificate is needed.
  - T5 therefore needs certified constants: arch Gram of the pole duals and `‖P₀Au±‖`, in the corpus `Encl` style.
- 2026-10-09 — **T5 analysis (parked).**
  - In autocorrelation form `Φ = f⋆f̃` (with `f ≥ 0` on `[−a,a]`, `a = ½log 2`, `L = 2a`, `φ = Φ/Φ(0)`):
    `W/Φ(0) = A(0) + 2Ω(L) + ∫_0^L [2ω(1−φ) + 4cosh(x/2)φ] dx`, where `A(0) + 2Ω(L) = −2.380`.
  - Each relaxation alone fails:
    - pointwise over `φ ∈ [0,1]`, the integral is `≥ ∫min(2ω, 4cosh) = 2.223`, short by `0.157`;
    - over positive-definite `φ` with `σ` concentrated near `t ≈ 6.8`, `α + β ≈ 2.08`.
  - The true minimum uses positive definiteness, `φ ≥ 0` and `supp ⊂ [−L,L]` together.
  - So T5 is a Delsarte-type linear-programming certificate. One needs a kernel split `4cosh − 2ω = P + N` with `N ≥ 0` and `P` positive on `PW_{L/2}` with constant `≥ 2.380`. Finding it is numerical and is not run under the no-computation rule.
  - Expected margin for nonnegative tests is about `0.4‖f‖²` (flat test `0.28/0.693`, cosine test `≈ 0.69`), so a coarse certificate should suffice once computation is allowed.
- 2026-10-09 — **T5 certificate specification** (to run once computation is authorized; nothing has been run).
  - *Primal.* Minimize `J(φ) = ∫_0^L [2ω(x)(1−φ(x)) + 4cosh(x/2)φ(x)] dx` over `φ = f⋆f̃/‖f‖²` with `f ≥ 0` on `[0,L]`, `L = log 2`. The target is `J ≥ 2.380 = −(A(0) + 2Ω(L))`.
  - *Dual certificate form.* Write `4cosh(x/2) − 2ω(x) = P(x) + N(x)` on `(0, L]` with:
    - `N ≥ 0` pointwise, so `∫Nφ ≥ 0` because `φ ≥ 0`;
    - `P` such that `∫_0^L P φ ≥ p₀` for every autocorrelation `φ` of an `L²(0,L)` function (`P̂ ≥ p₀` on `PW_{L/2}`, i.e. the operator `f ↦ (P⋆f)|_{[0,L]}` is `≥ p₀` with Toeplitz symbol of `P`).
    - Then `J(φ) ≥ ∫_0^L 2ω(x)dx(regularized) + p₀ ≥ 2.380` needs `p₀ − ∫_0^L 2ω·(regularized) ≥ …`. The regularization must be fixed by writing `2ω(1−φ) = 2ω − 2ωφ` with the singular part kept inside `P`.
  - *Search space.* `P` = truncated cosine series `Σ_{j≤J} c_j cos(2πjx/L')` with `L' ≥ 2L` (positive-definite on `PW` by Bochner when the Fourier coefficients are `≥ 0`), with `N = 4cosh − 2ω − P ≥ 0` checked on a grid with Lipschitz control. The ω-singularity at 0 goes into `P` as the `(1−φ)`-weighted Lévy term (an exact positive form).
  - *Lean.* Midpoint–radius `Encl` enclosures (corpus `HTGeometry.MidpointRadiusTrigEnclosures`), the same pattern as the corpus polar certificate.
- 2026-10-09 — **T6 closed [L], modulo T5 as an explicit hypothesis.** Module `HTGeometry/QuantileRearrangementEnergy` (generic):
  - `integral_sq_transport`: transport keeps `‖g‖₂`;
  - `lintegral_jump_transport_le`: jump energy `∫_{x>0}κ(x)∫(h(u)−h(u+x))²` does not increase, for any kernel `κ ≥ 0` decreasing on `(0,∞)` with `min(κ,n)` integrable there;
  - `lintegral_pair_transport_le`: the pair energy against an increasing kernel does not increase;
  - tools: `integral_jump_sq`, `integral_pair_eq_two_mul_Ioi`, `lintegral_jump_eq_iSup`.

  Module `RHTower/PrimeBlindNonnegativeConeReduction`, which uses hgt-8a's T3 (MUST-880) and glue `WeilLevyPole.weilArchRe_eq_levy_pole`:
  - `weilEnergyNonneg_of_primeBlind`: `WindowPositive` (the T5 inequality `|A(0)|‖h‖² ≤ J(h) + 2P(h)` for bounded measurable `h ≥ 0` vanishing off `(0, log 2)`) implies the same inequality for every bounded integrable `g ≥ 0` with `∫g(x+log n)g(x)dx = 0` for all `n ≥ 2`;
  - `weilArchRe_nonneg_of_primeBlind`: the smooth corollary, `0 ≤ weilArchRe(f⋆f̃)` for nonnegative `C²` compactly supported prime-blind `f`.

  Standard axioms. No sorries, no heartbeat options. The whole nonnegative cone of single tests now rests on one inequality on one window. T5 stays numeric: hgt-8a and I both estimate the true minimum only ≈ 0.15 above the target.
- 2026-10-11 — **T5 reduced to one resolvent number** (Opus loop rows 2062–2063).
  - On `[−a,a]`, `a = ½log 2`: the pole term is `2⟨f,c⟩² − 2⟨f,s⟩²`, with `‖s‖² = sinh a − a ≈ 0.007` (odd half negligible) and `‖c‖² = a + sinh a ≈ 0.700`.
  - The arch form decouples by parity. With `μ₀ > 0` on pole-vanishing vectors, T5 for every real `f` is equivalent to `inf{Q_even(f) : ⟨f,c⟩ = 1} ≥ −2`, together with an odd check of size `0.014`.
  - Certifying this from `μ₀ ≥ 1/10` fails:
    - the Schur loss `‖P₀Aĉ‖²/μ₀ ≈ 4` exceeds the margin `≈ 0.19`, because of the endpoint log singularities;
    - a trace certificate needs `‖P₀Kc‖ ≲ 6%·‖Kc‖`, which is numeric.
  - The √F-subadditivity relaxation for `f ≥ 0` gives only `≈ 0.10 < 0.157` (row 2062).
- 2026-10-12 — **T5 reduced to one explicit kernel (goal-loop row 991, [P]).**
  - Notation: `c_k = 2k + ½`, `Ŵ(t) = Σ_k (1 − e^{−c_k t})/c_k² = ∫_0^t W`, and
    `Φ(t) = −(|A0|/2)t + Ŵ(t) + 8(cosh(t/2) − 1)`.
  - Nested sets `F ⊆ E`: `J(1_E, 1_F) = ∫_F∫_{E^c} ω(|u − v|)`.
  - Concentric intervals of half-lengths `x, y`: the full form is `2[Φ(x + y) − Φ(|x − y|)]`.
  - Riesz rearrangement (`J` and `P` both decrease) therefore gives: T5 on the nonnegative cone ⟺ copositivity on `[0, ½log 2]²` of `G(x,y) = Φ(x+y) − Φ(|x−y|)`.
  - Green form (`X = max`, `Y = min`): `G = Σ_k (2/c_k²)e^{−c_kX}sinh(c_kY) − |A0| min(x,y) + 16 sinh(x/2)sinh(y/2)`.
  - Hand values of `Φ`: `0.0531` at `0.1`, `0.0558` at `0.15`, `0.0545` at `0.2`, `0.0474` at `0.3`, `0.0411` at `0.4`, `0.0397` at `0.45`, `0.0402` at `0.5`, `0.0475` at `0.6`, `0.0639` at `log 2`.
  - `Φ′ < 0` on about `(0.152, 0.462)`, which is why entrywise positivity fails for concentric layers (`G(0.15, 0.30) ≈ −0.032`).
  - Anchored intervals `(0,a) ⊆ (0,b)` are entrywise positive (`K = Φ(a) + Φ(b) − Φ(b−a) ≥ 0.028`), but anchored monotone rearrangement raises `J`, so it is not an admissible reduction.
  - Certificate shape needed: `Φ = Φ_inc + Φ_N` with `Φ_N″` positive definite absorbing the dip. Single cosines and `Si`-type tails cannot do it, because the dip interval has ratio `2.3 > 2` and positive-measure sine transforms are front-loaded. A Delsarte-type numeric design is still required.
  - Literature: Zhu (arXiv 2608.24827) proves full signed Weil positivity on support `[−0.8, 0.8]` by interval arithmetic, so T5 holds. The open task is only a Lean certificate.
- 2026-10-12 — **Where the T5 minimum sits ([P], hand estimates).**
  - For `h ≥ 0`, `P(h) ≥ (∫h)²`, so `Q ≥ Q̃ := W + 2·𝟙⊗𝟙` on `L²(0, log 2)`. If `Q̃ ⪰ 0` on all signed functions, T5 holds with no rearrangement at all.
  - Along `h = 𝟙 + εg` with `g = V̄ − V`, where `V(u) = W(u) + W(L−u)` is the killing potential (`V̄ = 4.155`, `‖V − V̄‖² ≈ 0.13`):
    - `Q̃ = 0.1175 − 2ε‖V−V̄‖² + ε²⟨g,Wg⟩`;
    - `Q̃ ⪰ 0` on this plane needs `⟨g,Wg⟩ ≥ ‖V−V̄‖⁴/0.1175 ≈ 0.149`;
    - the rough estimate is `⟨g,Wg⟩ ≈ 0.15–0.2`, so the plane is borderline.
  - So the near-minimizer is the flat profile with depleted edges, and the true margin is probably well below the flat value `0.18‖h‖²`. Any certificate must resolve the edge layer, where `W(u) ~ ½log(1/u)` is singular, at roughly 1% relative precision. The cosh weight in `P` adds only `≈ 0.01`.
