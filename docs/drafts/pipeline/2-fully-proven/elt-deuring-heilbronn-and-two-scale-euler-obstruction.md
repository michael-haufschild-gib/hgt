# Resolution of the Deuring–Heilbronn question: orthogonal factorization of `AAL`, co-moving remainder phase transition, and two-scale integer-norm Euler obstruction

- **ID:** elt-deuring-heilbronn-and-two-scale-euler-obstruction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0911/obstacles-summary.md` §3
- **Statement:** Unconditionally: (1) on `ZeroConfig` and `zetaZeroConfig`, `AAL` factors orthogonally as `LinearAbscissaLaw ∧ ExtremeDeuringHeilbronn` (`↔ LinearAbscissaLaw ∧ AsymptoticDeuringHeilbronn`), with `ExtremeDeuringHeilbronn ↔ (AAL ↔ (FiniteOffLine → RH))`; (2) for every `1/2 < θ ≤ θ₂ < β < 2/3` and `γ > 0`, there exists a convergent integer-norm Euler product `∏_k (1 − q_k^{-s})^{-1} = ∑_n a_n n^{-s}` (`q_k ≥ 2`, `a_n ∈ ℕ`, `(1/N)∑_{n<N} a_n → A > 0`) continuing holomorphically and zero-free across `Re s = 1/2` to `{Re s > 1/3, s ≠ 1}` whose zeros there are `{β ± iγ} ∪ {θ_n ± iω_n : n ∈ ℕ}` (`θ_0 = θ₂`, `θ_{n+1} = θ`, `ω_n > γ`, `ω_n → ∞`), realizing `(Θ, Θ₂, Θ∞) = (β, θ₂, θ)` and refuting extreme, asymptotic, and sub-`Θ₂` graded Deuring–Heilbronn on positive Euler products; (3) for `ζ(s)`, every pair of nontrivial zeros obeys an explicit multiplicity-exact 5-point repulsion inequality alongside `(1 − Re ρ₁) log(|Im ρ₁| · |Im ρ₂|) ≥ 1/58` (excluding the Siegel regime), while in the `exp(−at)` Gaussian prime current a co-moving remainder zero at `β_r + it` (`σ < β_r < β`) beats the supercritical top layer on the nonempty speed window `π/(2(β − σ)) < a < π/(2(β − β_r))` and is masked only for `a > π/(2(β − β_r))`.

## Goal
Give a complete unconditional resolution of the graded and extreme Deuring–Heilbronn questions for top-layer zero configurations, determine their exact equivalences and consequences for `ζ` (`AAL ↔ B13`, endpoint collapse of the linear-AAL dial, `LinAt C` amplification of asymptotic repulsion, symmetric-shift calibration), decide whether the `exp(−at)` Gaussian prime current reads an off-line remainder beneath a supercritical top layer, and determine whether an Euler product with natural norms, nonnegative integer Dirichlet coefficients, linear counting, and critical-line continuation forces top-layer repulsion.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `ExceptionalLayerTheory` and `ArithmeticPositiveDuality`, `lake --old env lean` green, `#print axioms` PASS

## Paper proof

### I. Exact orthogonal factorization of `AAL` and consequences for `ζ` (`[PROVED HERE]`)
Let `Z` be a `ZeroConfig` with global abscissa `Θ(Z) = zeroAbscissa Z` and asymptotic abscissa `Θ_∞(Z) = asymptoticAbscissa Z`. Define:
- `AsymptoticDeuringHeilbronn Z`: `¬AbscissaLaw Z → ApproachesLine Z`,
- `ExtremeDeuringHeilbronn Z`: `¬AbscissaLaw Z → (rightOf Z 0).Finite`.

1. **Equivalences of asymptotic and extreme repulsion.** By classical logic and `abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa`, `approachesLine_iff_asymptoticAbscissa_eq_half`:
   - `AsymptoticDeuringHeilbronn Z ↔ AbscissaLaw Z ∨ ApproachesLine Z ↔ (Θ(Z) − Θ_∞(Z))(Θ_∞(Z) − 1/2) = 0`.
   - The following are equivalent (`TFAE`):
     (i) `ExtremeDeuringHeilbronn Z`;
     (ii) `AbscissaLaw Z ↔ AbscissaLawAt Z 0`;
     (iii) `AbscissaLawAt Z 0 → AbscissaLaw Z`;
     (iv) `AbscissaLaw Z ∨ (rightOf Z 0).Finite`.
     Indeed, `AbscissaLaw Z → AbscissaLawAt Z 0` always holds (`h = 0`). If (i) holds and `AbscissaLawAt Z 0` holds, suppose `¬AbscissaLaw Z`: then `(rightOf Z 0).Finite` by (i), so `AbscissaLawAt Z 0` gives `∀ ρ ∈ Z, Re ρ ≤ 1/2`, hence `Pure Z`, hence `AbscissaLaw Z`, contradiction. Conversely, if (iii) holds and `¬AbscissaLaw Z`, then `¬AbscissaLawAt Z 0`, whose negation supplies `(rightOf Z 0).Finite` (and a witness `Re ρ > 1/2`).
   On `Z = zetaZeroConfig`, `(rightOf zetaZeroConfig 0).Finite ↔ FiniteOffLine` (`finite_copies_iff`, `finite_re_gt_half_iff_finiteOffLine`) and `AbscissaLawAt zetaZeroConfig 0 ↔ (FiniteOffLine → RiemannHypothesis)` (`B13`). Hence `ZetaExtremeDeuringHeilbronn` is unconditionally equivalent to `AsymptoticAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis)`.

2. **Orthogonal factorization of `AbscissaLaw`.** Unconditionally for every `ZeroConfig`:
   `AbscissaLaw Z ↔ LinearAbscissaLaw Z ∧ AsymptoticDeuringHeilbronn Z ↔ LinearAbscissaLaw Z ∧ ExtremeDeuringHeilbronn Z`.
   - `(→)`: `AbscissaLaw Z` implies `LinearAbscissaLaw Z` (at `C = 2` via `abscissaLaw_iff_forall_gt_one_linearAbscissaLawAt`) and makes `¬AbscissaLaw Z` false, discharging `ExtremeDeuringHeilbronn Z`, which implies `AsymptoticDeuringHeilbronn Z` since `(rightOf Z 0).Finite → ApproachesLine Z`.
   - `(←)`: Assume `LinearAbscissaLaw Z` (`ApproachesLine Z → Pure Z` by `linearAbscissaLaw_tfae`) and `AsymptoticDeuringHeilbronn Z`. If `¬AbscissaLaw Z`, then `ApproachesLine Z`, whence `Pure Z`, whence `AbscissaLaw Z` (`pure_iff_approachesLine_and_abscissaLaw`), contradiction.
   Specializing to `zetaZeroConfig`:
   - `AsymptoticAbscissaLaw ↔ ZetaLinearAbscissaLaw ∧ ZetaAsymptoticDeuringHeilbronn ↔ ZetaLinearAbscissaLaw ∧ ZetaExtremeDeuringHeilbronn`.
   - Under `ZetaExtremeDeuringHeilbronn`: `(FiniteOffLine → RiemannHypothesis) ↔ ZetaLinearAbscissaLaw` (collapsing the strict hierarchy `AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ LinearAAL ⊊ B13` onto a single truth value), `RiemannHypothesis ↔ ZerosApproachLine ∧ (FiniteOffLine → RiemannHypothesis)`, and under `FiniteOffLine → RiemannHypothesis` all eight clauses of `riemannHypothesis_tfae_of_asymptoticAbscissaLaw` become mutually equivalent.
   - Under `ZetaLinearAbscissaLawAt C` (`C ≥ 0`), any conditional asymptotic bound `¬AsymptoticAbscissaLaw → zetaAsymptoticAbscissa − 1/2 ≤ B` yields `¬AsymptoticAbscissaLaw → zetaZeroAbscissa − 1/2 ≤ C B`.
   - Under `¬AsymptoticAbscissaLaw`, for every `0 < a < (Θ − Θ_∞)/2`, the symmetric shift `ξ(s + a)ξ(s − a)` preserves `AAL`-failure with top abscissa `Θ + a` while Hardy's critical-line zeros of `ξ` produce infinitely many off-line zeros on `Re s = 1/2 + a > 1/2`.

### II. Nonreal 5-point repulsion, absence of the Siegel regime, and co-moving remainder phase transition for `ζ` (`[PROVED HERE]`)
1. **Multiplicity-exact 5-point repulsion and absence of the Siegel regime.** For `1 < σ` and `γ₁, γ₂ ∈ ℝ`, expanding `−Re(ζ'/ζ(σ + it)) = ∑_{n≥1} Λ(n) n^{-σ} cos(t log n)` against the nonnegative trigonometric polynomial
   `2(1 + cos u)(1 + cos v) = 2 + 2 cos u + 2 cos v + cos(v + u) + cos(v − u) ≥ 0`
   yields
   `0 ≤ 2 Re(−ζ'/ζ(σ)) + 2 Re(−ζ'/ζ(σ + iγ₁)) + 2 Re(−ζ'/ζ(σ + iγ₂)) + Re(−ζ'/ζ(σ + i(γ₂ + γ₁))) + Re(−ζ'/ζ(σ + i(γ₂ − γ₁)))`.
   By `re_logDeriv_xi_eq_realReciprocal_tsum`, for `1 < σ` and any zero copy `q₀ : XiZeroCopy` at `β₀ + iγ₀`, every term `xiRealReciprocal s 0 q = (σ − Re q)/|s − q|²` is nonnegative, while on the multiplicity fibre `xiZeroCopyFiber q₀.1` at `s = σ + iγ₀` each copy equals `1/(σ − β₀)`; hence `(xiZeroCopyFiber q₀.1).card / (σ − β₀) ≤ Re(ξ'/ξ(σ + iγ₀))`. Combining with the four-factor split on `1 < σ ≤ 2`, `neg_re_logDeriv_riemannZeta_real_le_neg`, and `neg_re_logDeriv_riemannZeta_le`, for all `q₁, q₂ : XiZeroCopy` with `4 ≤ Im q₁` and `Im q₁ + 4 ≤ Im q₂`:
   `2 m₁ / (σ − β₁) + 2 m₂ / (σ − β₂) ≤ 2 / (σ − 1) + 2 log γ₁ + 2 log γ₂ + log(γ₂ + γ₁) + log(γ₂ − γ₁) + (4/5 + 6 C_ψ)`.
   For `m₁ = 1`, `2/(σ − 1) − 2/(σ − β₁) = 2(1 − β₁)/[(σ − 1)(σ − β₁)] > 0` for all `σ > 1`. Moreover, by `re_le_one_sub_of_zeta_zero` and `four_le_abs_im_of_zeta_zero`, every pair of nontrivial zeros `ρ₁, ρ₂` of `ζ` satisfies `4 ≤ |Im ρ_j|`, `log |Im ρ₂| > 1`, and `(1 − Re ρ₁) log(|Im ρ₁| · |Im ρ₂|) ≥ (1 − Re ρ₁) log |Im ρ₁| ≥ 1/58`; and for any fixed `β < 1`, `(1 − β) log |Im ρ₂| → +∞` as `|Im ρ₂| → ∞`. Thus `ζ(s)` possesses no Siegel Deuring–Heilbronn regime.

2. **Exact speed phase transition of the `exp(−at)` Gaussian prime current.** At observation line `s = σ + it` and damping `y = e^{-at}` (`a > 0`), a fixed top-layer zero `ρ_top = β + iγ_top` has `gaussianObservationRate ρ_top σ a = a(β − σ)/2 − π/4`. By contrast, a co-moving remainder zero at ordinate `t` with real part `β_r` (`σ < β_r < β`), evaluated at `(β_r + it) − (σ + it) = β_r − σ > 0`, has zero vertical Gamma argument and exact positive mode
   `K(e^{-at}, β_r − σ) = (1/2) Γ((β_r − σ)/2) exp(a(β_r − σ)t / 2)`.
   Subtracting the exponential rates cancels `σ` identically:
   `Rate_top(β, σ, a) − Rate_co(β_r, σ, a) = a(β − β_r)/2 − π/4`.
   Hence for `σ < β_r < β`, the open interval `π/(2(β − σ)) < a < π/(2(β − β_r))` is nonempty; throughout it, `‖K(e^{-at}, ρ_top − (σ + it))‖ → +∞` (the top layer is supercritical) yet `‖K(e^{-at}, ρ_top − (σ + it)) / K(e^{-at}, (β_r + it) − (σ + it))‖ → 0` (a co-moving remainder zero exponentially dominates the top layer). Conversely, for `a > π/(2(β − β_r))`, `‖K(e^{-at}, (β_r + it) − (σ + it)) / K(e^{-at}, ρ_top − (σ + it))‖ → 0` (the top layer exponentially masks co-moving remainder zeros).

### III. Two-scale positive integer-norm Euler product with linear counting across `Re s = 1/2` (`[PROVED HERE]`)
Fix any `1/2 < θ ≤ θ₂ < β < 2/3` and `γ > 0`. Put `μ := 1 − β ∈ (1/3, 1/2)`, `ν := (3μ − 1)/2 ∈ (0, 3μ − 1)`, generating base `Params` `P` with `P.w(t) = primeDensity μ ν γ t`, top-layer pair `β ± iγ`, `c₀ := (1 − e^{-μ})^3 > 0`, `c₀ e^t / t ≤ P.w(t)` (`t ≥ 1`), and `P.w(t) ≤ 5 e^t / t` (`t > 0`).

1. **Continuous two-scale prime density.** Set `θ_0 := θ₂`, `θ_{n+1} := θ`, `U_0 := max 2 (16 / (c₀ (1 − θ₂)^2))`, `A_n := U_0 + n + 1`, `M_n := ⌈A_n (γ + 4 + n + 2^n e^{2 A_n}) / π⌉₊ + 1`, and `ω_n := (2 M_n + 1)π / (2 A_n)`. Then `ω_n > γ + 4 + n + 2^n e^{2 A_n}` and `cos(ω_n A_n) = cos(π/2 + M_n π) = 0`. Define
   `g_n(t) := if A_n ≤ t then −2 e^{θ_n t} cos(ω_n t) / t else 0`, `w_∞(t) := ∑'_{n=0}^∞ g_n(t)`, `w(t) := P.w(t) + w_∞(t)`.
   Because `g_n(A_n) = 0`, each `g_n` is continuous on `ℝ`; on `(-∞, B]`, `g_n ≡ 0` for `n ≥ ⌈B⌉₊`, so `w_∞` is continuous on `ℝ` (`w_∞(t) = 0` for `t ≤ U_0 + 1`). For `t ≥ U_0 + 1`, at most `⌊t⌋₊ ≤ t` summands are nonzero, so `|w_∞(t)| ≤ t · (2 e^{θ₂ t} / t) = 2 e^{θ₂ t}`. Since `e^{(1−θ₂)t} ≥ (1−θ₂)^2 t^2 / 2` and `t ≥ 16 / (c₀ (1−θ₂)^2)`, `2 e^{θ₂ t} ≤ c₀ e^t / (4 t) ≤ P.w(t) / 4`. Thus `(3/4) P.w(t) ≤ w(t) ≤ (5/4) P.w(t)` for all `t > 0`, and for `u ≥ u₁ := 2 log(9/c₀) + 2`, `w(u) − w(u/2)/4 ≥ (3c₀/4) e^u / u − (25/16) e^{u/2} / (u/2) > 0`.

2. **Entire cutoff-Frullani factors and holomorphic patching of `G_∞`.** For `A > 0` and `z ∈ ℂ`, define
   `J_A(z) := ∫_{t ∈ (0, A]} (e^{-t} − e^{-zt})/t dt`, `C_A := ∫_{t ∈ (A, ∞)} e^{-t}/t dt`,
   `F_A(z) := z exp(−J_A(z) − C_A)`, `Φ_A(z) := Log z − J_A(z) − C_A`.
   By `intervalIntegral_seg_cexp`, `(e^{-t} − e^{-zt})/t` is bounded on compact `z`-sets uniformly on `(0, A]` with `z`-derivative `e^{-zt}`, so `J_A` is entire with `J_A'(z) = ∫_{(0, A]} e^{-zt} dt = (1 − e^{-Az})/z` (`z ≠ 0`). Thus `F_A` is entire and vanishes iff `z = 0`. For `Re z > 0`, Frullani's identity `Log z = ∫_{(0, ∞)} (e^{-t} − e^{-zt})/t dt` splits at `A` to give `Φ_A(z) = −∫_{(A, ∞)} e^{-zt}/t dt` and `F_A(z) = exp(Φ_A(z))`. For `z ∈ ℂ \ (−∞, 0]`, `F_A(z) = exp(Φ_A(z))` and `Φ_A'(z) = z^{-1} − (1 − e^{-Az})/z = e^{-Az}/z`. For `Im z ≠ 0`, `z + x ∈ ℂ \ (−∞, 0]` for all `x ≥ 0` and `Φ_A(z + x) → 0` as `x → +∞`, so `Φ_A(z) = −∫_{x ∈ (0, ∞)} e^{-A(z+x)}/(z+x) dx` and `‖Φ_A(z)‖ ≤ e^{-A Re z}/(A |Im z|)`.
   Putting `ρ_n := θ_n + i ω_n` and, for `K ∈ ℕ`,
   `G_patch K s := (∏_{n < K} F_{A_n}(s − ρ_n) F_{A_n}(s − conj ρ_n)) · exp(∑'_{m=0}^∞ (Φ_{A_{m+K}}(s − ρ_{m+K}) + Φ_{A_{m+K}}(s − conj ρ_{m+K})))`,
   `G_∞(s) := G_patch (⌈|Im s|⌉₊ + 1) s`:
   on `S_N = {Re s > 0, |Im s| < N}`, every `n ≥ N` satisfies `|Im(s − ρ_n)|, |Im(s − conj ρ_n)| ≥ ω_n − N > 2^n e^{2 A_n}` and `−Re(s − ρ_n) < θ_n < 2`, whence `‖Φ_{A_n}(s − ρ_n)‖, ‖Φ_{A_n}(s − conj ρ_n)‖ ≤ 2^{-n}`. Moreover `G_patch j s = G_patch (j + 1) s` whenever `|Im s| < ω_j` (hence whenever `|Im s| < j + 4`). Thus `G_∞` equals `G_patch N` on `S_N`, so `G_∞` is holomorphic on `{Re s > 0}`, vanishes there iff `∃ n, s = ρ_n ∨ s = conj ρ_n`, and on `{Re s > 1}` equals `G_patch 0 s = exp(∫_{(0, ∞)} e^{-st} w_∞(t) dt)` by Fubini (`integral_tsum_of_summable_integral_norm`).

3. **Prime-square quantile discretization and integer-norm rounding.** Set `W(x) := distribution w x` and `V(x) := W(x) − W(x/2)/2 + W(min(x, u₁)/2)/2`. Because `w > 0` on `(0, ∞)` and `w(u) − w(u/2)/4 > 0` on `[u₁, ∞)`, `V` is continuous and strictly increasing on `[0, ∞)` with `V(0) = 0` and `V(x) ≥ (3/8) P.W(x) → +∞`. Let `t_k > 0` satisfy `V(t_k) = k + 1` and put `q_k := ⌈e^{t_k}⌉₊ ≥ 2`, `a_n := genCoeff q n`. By `tsum_neg_log_eq_cube`, `tsum_cexp_atoms`, `integral_cexp_density`, `differentiableOn_boundedLaplace_of_le`, `differentiableOn_primeCorrection`, `differentiableOn_primeCubeRemainder`, and `tendsto_genCoeff_count`, the Euler product `∏_k (1 − q_k^{-s})^{-1} = ∑_n a_n n^{-s}` has `(1/N)∑_{n<N} a_n → A > 0` and continues to `{Re s > 1/3, s ≠ 1}` as `ζ_c(s) G_∞(s) exp(Ψ(s))` with `Ψ` holomorphic on `{Re s > 1/3}`. Its zeros on `{Re s > 1/3, s ≠ 1}` are therefore `{β ± iγ} ∪ {ρ_n, conj ρ_n : n ∈ ℕ}`, none on `Re s = 1/2` or `(1/3, ∞) \ {1}`. Reflecting `{1/2 < Re s < 1, F(s) = 0}` via `s ↦ 1 − conj s` produces a `ZeroConfig` realizing `Θ = β`, `Θ₂ = θ₂` above height `γ`, and `Θ_∞ = θ`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Extreme Deuring–Heilbronn (`¬AAL ⇒ FiniteOffLine`), asymptotic Deuring–Heilbronn (`¬AAL ⇒ ZAL`), `AAL ⇔ B13`, and every sub-`Θ₂` graded repulsion bound `Θ_∞ − 1/2 ≤ f(β − Θ₂, γ)` (`f(β − Θ₂, γ) < θ₂ − 1/2`) are **falsified** across the entire class of convergent integer-norm Euler products with nonnegative integer Dirichlet coefficients, linear summatory counting `∑_{n<N} a_n ∼ A N` (`A > 0`), and zero-free holomorphic continuation across `Re s = 1/2`. The killing mechanism is high-ordinate exponential decoupling of cutoff-Frullani prime-density waves `−2 e^{θ_n t} cos(ω_n t)/t 1_{[A_n, ∞)}(t)` (`cos(ω_n A_n) = 0`): choosing `ω_n ≫ 2^n e^{2 A_n}` keeps the added density within `±(1/4) w₀(t)` globally while making the off-cut logarithmic integrals decay as `O(e^{-A_n Re z}/(A_n |Im z|)) = O(2^{-n})`, planting infinitely many off-line zeros at arbitrary `(θ_n, ω_n)` without disturbing positivity, integrality, linear counting, or critical-line continuation. Moreover, for `ζ(s)` itself, `(1 − Re ρ₁) log(|Im ρ₁| · |Im ρ₂|) ≥ 1/58` excludes the Siegel regime altogether, and in the `exp(−at)` Gaussian prime current a co-moving remainder zero at `β_r + it` dominates the supercritical top layer throughout `π/(2(β − σ)) < a < π/(2(β − β_r))`.
- **Strongest positive survivor:**
  1. **Exact orthogonal factorization of `AAL` and strict 2×2 independence:** Unconditionally on every `ZeroConfig` (and on `zetaZeroConfig`), `AbscissaLaw ↔ LinearAbscissaLaw ∧ AsymptoticDeuringHeilbronn ↔ LinearAbscissaLaw ∧ ExtremeDeuringHeilbronn`, with `ZetaExtremeDeuringHeilbronn ↔ (AsymptoticAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis))`; and on positive integer-norm Euler products with linear counting and critical-line continuation, `LinearAbscissaLaw` and `ExtremeDeuringHeilbronn` are **strictly independent** (`IntegerNormOneOff` satisfies `ExtremeDeuringHeilbronn ∧ ¬LinearAbscissaLaw`, whereas the two-scale Euler product satisfies `LinearAbscissaLaw ∧ ¬AsymptoticDeuringHeilbronn`).
  2. **Multiplicity-exact 5-point repulsion and exact `exp(−at)` masking threshold for `ζ`:** Every pair of nontrivial zeros of `ζ` with `4 ≤ γ₁` and `γ₁ + 4 ≤ γ₂` satisfies `2 m₁/(σ − β₁) + 2 m₂/(σ − β₂) ≤ 2/(σ − 1) + 2 log γ₁ + 2 log γ₂ + log(γ₂ + γ₁) + log(γ₂ − γ₁) + (4/5 + 6 C_ψ)` (`1 < σ ≤ 2`), and the `σ`-independent threshold `a_* = π/(2(β − β_r))` sharply separates co-moving remainder dominance (`a < a_*`) from exponential top-layer masking (`a > a_*`).
- **New insight:** Positivity of the Euler product, integer prime norms, nonnegative integer Dirichlet coefficients, Wiener–Ikehara linear counting, and analytic continuation across `Re s = 1/2` are completely compatible with both factors of `¬AAL` independently (`Θ > Θ_∞ = 1/2` and `Θ > Θ_∞ > 1/2` with `Θ_∞ = Θ₂`). Any genuine Deuring–Heilbronn reduction `AAL ⇔ B13` for `ζ` must therefore invoke the exact functional equation (`s ↔ 1 − s`) simultaneously with the Euler product (`EulerFETransportTheory`), because positivity/Turán/`3-4-1` mechanisms have no Siegel regime on `ζ` and fail on positive integer-norm Euler products without functional equation.
- **Status:** Dependency-closed on paper; proceeding immediately to unconditional Lean 4 formalization in `ExceptionalLayerTheory/NonrealZeroRepulsionAndCoMovingRemainders.lean`, `ArithmeticPositiveDuality/ATwoScaleIntegerNormOneOff.lean`, and `ExceptionalLayerTheory/TheDeuringHeilbronnQuestionForZeta.lean`.

## Log
- 2026-11-09 — created in 1-in-progress; paper proof completed.
