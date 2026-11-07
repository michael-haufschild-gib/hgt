# Mollified log-dilation bridges and prime-side Selberg–Hankel defect at fixed shift

- **ID:** mollified-log-dilation-bridge
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/README.md` Open Topic 1 & Open Topic 3; `TheDilationQuotientReadsTheInnerMass`; `TheInnerMassIsAMollifierInfimum`; `TheFixedBaseConeAndCriticalBernstein`.
- **Statement:**
  1. *Shifted Plancherel second moment, shifted Szegő infimum, and variational dilation ratio.*
     - For every `δ ∈ (−1/2, 1/2)` and `w ∈ ℂ` with `Re w > 1/2`, `τ ↦ ‖ζ(1/2 + δ + iτ)‖² P_w(τ)` is Lebesgue integrable on `ℝ`.
     - For `δ ∈ [0, 1/2)` and `Re w > 1/2` with `zetaEntire(w + δ) ≠ 0`, the shifted mollifier budgets `shiftedBudget δ w Q = ∫ ‖ζ(1/2 + δ + iτ) exp(Q(φ_w(1/2 + iτ)))‖² P_w(τ) dτ` over `{Q | Q.coeff 0 = 0}` have greatest lower bound `exp(2 I_δ(w)) (‖zetaEntire(w + δ)‖ / ‖w − δ‖)²`.
     - At `w = 1` and `δ ∈ (0, 1/2)`, `sInf {shiftedBudget δ 1 Q | Q(0) = 0} = (δ ‖ζ(1 + δ)‖ / (1 − δ))² exp(2 I_δ(1)) > 0`, so
       `exp(2(I(1) − I_δ(1))) = (δ ‖ζ(1 + δ)‖ / (1 − δ))² · sInf_Q budget 1 Q / sInf_Q shiftedBudget δ 1 Q`,
       and `RiemannHypothesis` holds if and only if `sInf_Q budget 1 Q / sInf_Q shiftedBudget δ 1 Q = ((1 − δ)/(δ ‖ζ(1 + δ)‖))²`.
  2. *Outer Euler-prefix mollification and prime cancellation.*
     For any finite set `S` of integers `p ≥ 2`, `eulerMollifier S s = ∏_{p ∈ S} (1 − p^{−s})` is nonvanishing on `Re s ≥ 1/2`, satisfies `∫ log ‖eulerMollifier S (1/2 + δ + iτ)‖ P_w(τ) dτ = log ‖eulerMollifier S (w + δ)‖` for all `δ ≥ 0` and `Re w > 1/2`, and transforms the log-dilation identity at `w = 1`, `δ ∈ (0, 1/2)` into
     `∫ (log ‖ζ(1/2 + iτ) eulerMollifier S (1/2 + iτ)‖ − log ‖ζ(1/2 + δ + iτ) eulerMollifier S (1/2 + δ + iτ)‖) P₁(τ) dτ = (I(1) − I_δ(1)) + log((1 − δ) ∏_{p ∈ S} (1 − p⁻¹) / (δ ‖ζ(1 + δ) eulerMollifier S (1 + δ)‖))`.
  3. *Exact shifted Poisson Gram matrix and Abel partial-sum coercivity of Dirichlet polynomials.*
     For `ξ ∈ ℝ`, `∫ cos(ξτ) P₁(τ) dτ = exp(−|ξ|/2)`. Consequently, for every `M : ℕ`, `b : ℕ → ℝ`, and `δ ∈ ℝ`, `dirichletPoly M b s = ∑_{m ∈ Icc 1 M} b_m m^{−s}` obeys
     `∫ ‖dirichletPoly M b (1/2 + δ + iτ)‖² P₁(τ) dτ = ∑_{m ∈ Icc 1 M} ∑_{n ∈ Icc 1 M} (b_m m^{−δ})(b_n n^{−δ}) / max(m, n)`,
     and for `M ≥ 1` this quadratic form equals the strictly positive-definite Abel sum of squares
     `(∑_{m ∈ Icc 1 M} b_m m^{−δ})² / M + ∑_{k ∈ Icc 1 (M − 1)} (k⁻¹ − (k + 1)⁻¹) (∑_{m ∈ Icc 1 k} b_m m^{−δ})²`.
  4. *Prime-side Selberg–Cholesky diagonalization and `δ → 0⁺` defect dichotomy.*
     For primes `p : Fin n → ℕ`, `σ ∈ ℝ`, and `eulerAmpl p σ k = ∏_i (p_i^{−σ})^{k_i}`:
     - `dirichletHankelForm (eulerAmpl p σ) N c = ∑_{d ∈ piBox n N} (∑_{u ∈ piBox n N} c(d + u) eulerAmpl p σ u)²`.
     - For every `N ≥ 2` and every `c` vanishing outside `piBox n N` with `c 0 = 1`,
       `∏_i (1 + p_i^{−2σ})⁻¹ ≤ dirichletHankelForm (eulerAmpl p σ) N c`,
       with exact equality on `selbergArray p σ` (`k ↦ ∏_i (if k_i = 0 then 1 else −p_i^{−σ}/(1 + p_i^{−2σ}))` on `piBox n 2`, `0` outside).
     - For every `δ > 0`, `exp(−∑'_{m : ℕ} m^{−(1 + 2δ)}) > 0` bounds `dirichletHankelForm (eulerAmpl p (1/2 + δ)) N c` below uniformly across all finite sets of distinct primes `p`, all `N ≥ 2`, and all `c` supported in `piBox n N` with `c 0 = 1`; at `δ = 0`, `inf_{n, p} dirichletHankelForm (eulerAmpl p (1/2)) 2 (selbergArray p (1/2)) = 0`; and as `δ → 0`, `δ ↦ log(dirichletHankelForm (eulerAmpl p (1/2 + δ)) 2 (selbergArray p (1/2 + δ)))` has derivative `2 ∑_i log p_i / (p_i + 1)` at `0`, whose prime series `∑_p log p / (p + 1)` diverges.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, foreground audit green, axiom check PASS

## Proof

1. *Shifted second moment and Szegő variational ratio (`[PROVED HERE]`).*
   For `δ ∈ (−1/2, 1/2)`, `φ_δ(u) = e^{−(1/2 + δ)u} {e^u}` satisfies `‖φ_δ(u)‖ ≤ e^{−η|u|}` with `η = min(1/2 + δ, 1/2 − δ) > 0` (using `{e^u} ≤ 1` for `u ≥ 0` and `{e^u} ≤ e^u` for `u < 0`), so `φ_δ ∈ L¹(ℝ) ∩ L²(ℝ)`, and `∫ ‖φ_δ‖² > 0` since `{e^u} ≥ 1/2` on `[log(3/2), log(7/4)]`. Because `s.re = 1/2 + δ ∈ (0, 1)`, `mellin_eq_fourier`, `mellin_comp_inv`, and `integral_Ioi_zero_fract_cpow` give `𝓕 φ_δ (t/(2π)) = −ζ(1/2 + δ + it)/(1/2 + δ + it)`. Plancherel (`integral_norm_sq_fourier`) yields `Integrable (fun τ => ‖ζ(1/2 + δ + iτ)‖² / ((1/2 + δ)² + τ²))`, and comparing `((1/2 + δ)² + τ²)⁻¹` with `(1/4 + τ²)⁻¹` against `exists_poissonKernel_le_one` gives `Integrable (fun τ => ‖ζ(1/2 + δ + iτ)‖² P_w(τ))` for every `Re w > 1/2`.
   For `0 ≤ δ < 1/2` and `Re w > 1/2` with `zetaEntire(w + δ) ≠ 0`, `G(z) = ‖ζ(discChart w z + δ)‖²` is measurable, positive a.e. on `𝕋` (since `{s | ζ(s + δ) = 0}` is countable), circle-integrable by `circleAverage_shift_eq_poisson` and shifted second-moment integrability, and log-circle-integrable by `(hasSum_shiftedInnerField ...).1`. Applying `isGLB_circleAverage` yields the shifted Szegő infimum; specializing to `w = 1`, `δ ∈ (0, 1/2)` and dividing `isGLB_budget_one` by `isGLB_shiftedBudget_one` expresses `exp(2(I(1) − I_δ(1)))` as the exact budget-infimum ratio and translates `riemannHypothesis_iff_log_dilation_quotient_eq` into the Szegő ratio criterion.

2. *Outer Euler-prefix mollification (`[PROVED HERE]`).*
   For `p ≥ 2` and `δ ≥ 0`, `1 − p^{−(s + δ)} = column (p : ℝ) ((p : ℝ)^{−δ}) s` has `‖(p : ℝ)^{−δ}‖ = p^{−δ} ≤ 1 < √p`, so `column_ne_zero_of_small` ensures nonvanishing on `Re s ≥ 1/2` (pointwise for every `τ ∈ ℝ`), and `integrable_and_integral_log_of_no_right_zeros` evaluates `∫ log ‖1 − p^{−(1/2 + δ + iτ)}‖ P_w(τ) dτ = log ‖1 − p^{−(w + δ)}‖`. Summing over `p ∈ S` and adding to `integral_log_dilation_quotient_eq` at `w = 1` (using a.e. nonvanishing of `ζ` on `Re s = 1/2` and `Re s = 1/2 + δ`) gives the prime-cancelled log-dilation identity, with `‖1 − (p : ℂ)⁻¹‖ = 1 − p⁻¹`.

3. *Shifted Poisson Gram matrix and Abel coercivity (`[PROVED HERE]`).*
   For `y ≥ 0`, `F(z) = exp(i y z)` is holomorphic and bounded by `1` on `{Im z ≥ 0}`, so `integral_halfPlanePoisson_one_mul_eq_apply_I` gives `∫ P₁^{\mathrm{UHP}}(x) e^{iyx} dx = e^{−y}`; taking real parts, using evenness of `cos`, and substituting `x = 2τ` (`P₁(τ) = 2 P₁^{\mathrm{UHP}}(2τ)`) proves `∫ cos(ξτ) P₁(τ) dτ = exp(−|ξ|/2)`. Expanding `‖∑_{m=1}^M b_m m^{−(1/2 + δ + iτ)}‖² = ∑_{m,n} b_m m^{−1/2−δ} b_n n^{−1/2−δ} cos((log n − log m)τ)` and integrating term-by-term gives `(b_m m^{−δ})(b_n n^{−δ}) m^{−1/2} n^{−1/2} exp(−|log n − log m|/2) = (b_m m^{−δ})(b_n n^{−δ}) / max(m, n)`. Induction on `M ≥ 1` splits `Icc 1 (M + 1) = insert (M + 1) (Icc 1 M)`: all border pairs have `max = M + 1`, and `S_M²/M + (2 w_{M+1} S_M + w_{M+1}²)/(M + 1) = S_{M+1}²/(M + 1) + (M⁻¹ − (M + 1)⁻¹) S_M²`.

4. *Prime-side Selberg–Cholesky minimum and `δ → 0⁺` defect (`[PROVED HERE]`).*
   Multiplicativity `eulerAmpl p σ (u + v) = eulerAmpl p σ u * eulerAmpl p σ v` factors `dirichletHankelForm (eulerAmpl p σ) N c` as `∑_{d ∈ piBox n N} L(d)²` with `L(d) = ∑_{u ∈ piBox n N} c(d + u) eulerAmpl p σ u`.
   For `N ≥ 2` and `c` supported in `piBox n N` with `c 0 = 1`, set `w_d = (−1)^{∑_i d_i} eulerAmpl p σ d` on `B₂ = piBox n 2 ⊆ piBox n N`. Reindexing `m = d + u` gives `∑_{d ∈ B₂} w_d L(d) = ∑_{m ∈ piBox n N} c(m) eulerAmpl p σ m ∑_{d ∈ B₂ : d ≤ m} (−1)^{∑_i d_i} = c(0) = 1` because `∑_{d ∈ B₂ : d ≤ m} (−1)^{∑_i d_i} = ∏_i (if m_i = 0 then 1 else 0)` vanishes for `m ≠ 0`. Cauchy–Schwarz on `B₂` gives `1 ≤ (∑_{d ∈ B₂} w_d²)(∑_{d ∈ B₂} L(d)²) ≤ (∏_i (1 + p_i^{−2σ})) dirichletHankelForm (eulerAmpl p σ) N c`.
   On `selbergArray p σ`, `L(d) = 0` for `d ∉ B₂`, while for `d ∈ B₂` the sum over `u` factors across coordinates (`u_i = 0` when `d_i = 1`, `u_i ∈ {0, 1}` when `d_i = 0`) as `L(d) = w_d ∏_i (1 + p_i^{−2σ})⁻¹`, giving exact equality.
   At `σ = 1/2 + δ`: for `δ > 0`, `1 + p_i^{−(1+2δ)} ≤ exp(p_i^{−(1+2δ)})` and injectivity of `p` into `ℕ` yield the uniform positive lower bound `exp(−∑'_m m^{−(1+2δ)})`; at `δ = 0`, `exists_finset_primes_ge_five_sum_gt` drives `∏_i (1 + p_i⁻¹)⁻¹` below any `ε > 0`; differentiating `−∑_i log(1 + exp(−(1 + 2δ) log p_i))` at `δ = 0` gives `2 ∑_i log p_i / (p_i + 1)`, and `log p / (p + 1) ≥ 1/(2p)` for `p ≥ 3` implies non-summability over `Nat.Primes` via `Nat.Primes.not_summable_one_div`.
