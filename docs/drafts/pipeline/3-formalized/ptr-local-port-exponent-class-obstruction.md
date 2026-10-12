# No local port from the cosine producer to Ξ (exponent-class obstruction)

- **ID:** ptr-local-port-exponent-class
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** PTR loop rows 267–280 (`1-in-progress/ptr-goal-loop-2026-10-09.md`); frontier-map PTR "Needs: nonlocal … port"
- **Statement:** For real `h` with `h ∉ 2ℤ`, no finite family of complex polynomials `Q₀, …, Q_N` satisfies
  `Σ_k Q_k(t) · A_h^{(k)}(t) = Ξ(t)` for all real `t`, where `A_h(z) = ∫ Φ(u) cosh(hu) e^{izu} du = cos(hD)Ξ`.

## Goal
PTR's safe producers are the cosine shifts `A_h = cos(hD)Ξ = Re ξ(½ + h + it)`, which are Laguerre–Pólya for `h ≥ ½`
unconditionally, and the frontier map asks for a "nonlocal" port from them to `Ξ`. The theorem shows that no *local*
port exists, in the strongest linear sense: there is no finite-order linear differential operator with polynomial
coefficients, whether or not it preserves real-rootedness. This covers the horizon producer `h = ½` and every
non-even-integer depth. It complements row 267, where no Fourier multiplier works inward (CANNOT-497 + Newman), and
rows 278–279, where no Mellin multiplier works inward.

## Proof
Notation: `paperFT g (z) = ∫ g(u) e^{izu} du`. Corpus: `Φ = S_R`,
`S_R(u) = Σ_{n≥1} e^{u/2} R(n²e^{2u}) e^{−πn²e^{2u}}`, `R = 4π²X² − 6πX` (`riemannPhiKernel_eq_cuspSeries`),
and `Ξ = paperFT Φ`.

1. **Kernel side.** With `f_h(u) = Φ(u)cosh(hu)` (super-exponentially decaying with all derivatives):
   `A_h^{(k)} = paperFT((iu)^k f_h)` (differentiation under the integral), and `z·paperFT G = paperFT(iG')`
   (integration by parts, `paperFT_deriv_of_superExpDecay`). So
   `Σ_k Q_k(t)A_h^{(k)}(t) = paperFT(L f_h)(t)` with `L = Σ_{k,m} q_{km}(i∂_u)^m ∘ (iu)^k`, a finite-order operator
   with polynomial coefficients in `u`.
2. **Fourier injectivity.** If the identity holds on `ℝ`, then `paperFT(L f_h − Φ) = 0` on `ℝ`. Since `L f_h − Φ` is
   continuous and integrable, `L f_h = Φ` pointwise.
3. **Cusp exponential polynomials.** Let `𝓔` be the space of finite sums `E(u) = Σ_γ p_γ(u)e^{γu}`
   (`γ ∈ ℝ`, `p_γ ∈ ℂ[u]`). On the set `{e^{−πe^{2u}}E(u)}`:
   - multiplication by `u` keeps the exponents;
   - `∂_u[e^{−πe^{2u}}p(u)e^{γu}] = e^{−πe^{2u}}[(p' + γp)e^{γu} − 2πp e^{(γ+2)u}]`.

   So `L` preserves "all exponents lie in a fixed union of classes mod 2". The `n = 1` term
   `φ₁(u) = e^{−πe^{2u}}(4π²e^{9u/2} − 6πe^{5u/2})` and
   `φ₁cosh(hu) = e^{−πe^{2u}}·(…)`, with exponents `9/2 ± h, 5/2 ± h`. Hence `L[φ₁cosh(h·)] = e^{−πe^{2u}}E_L(u)`
   with every exponent of `E_L` in `C_h = (½ + h + 2ℤ) ∪ (½ − h + 2ℤ)`.
4. **Tail.** For `u ≥ 1`, `L[(Φ − φ₁)cosh(h·)](u)` and `(Φ − φ₁)(u)` are `O(e^{Cu}e^{−4πe^{2u}})`, since every
   `n ≥ 2` term carries `e^{−πn²e^{2u}} ≤ e^{−4πe^{2u}}`, and derivatives and polynomial weights cost only
   `e^{Cu}`.
5. **Separation.** From `L f_h = Φ`:
   `e^{−πe^{2u}}(E_L(u) − 4π²e^{9u/2} + 6πe^{5u/2}) = O(e^{Cu}e^{−4πe^{2u}})`. So the exponential polynomial
   `E := E_L − 4π²e^{9u/2} + 6πe^{5u/2}` is `O(e^{Cu}e^{−3πe^{2u}})` as `u → +∞`.
   - **Leading-term lemma:** a nonzero `E ∈ 𝓔` with real exponents satisfies `|E(u)| ≥ c·u^d e^{γ_max u}` for
     large `u`.
   - So `E = 0` in `𝓔`, and its coefficient at exponent `9/2` vanishes.
6. **Exponent classes.** If `h ∉ 2ℤ`, then `½ ± h ∉ ½ + 2ℤ`, so `9/2 ∉ C_h` and `E_L` has no `e^{9u/2}`
   component. The coefficient of `e^{9u/2}` in `E` is therefore `−4π² ≠ 0`. Contradiction. ∎

## No-go closure
- **Exact killing mechanism:**
  - Polynomial-coefficient differential operators preserve the mod-2 class of the theta-kernel exponents.
  - `cos(hD)` shifts every class by `±h`.
  - `Ξ`'s kernel lives in class `½`.
- **Strongest positive survivor (exponent-class law):** any linear port from `A_h` to `Ξ` must move kernel exponents
  by `∓h + 2ℤ`. It must contain kernel factors `e^{∓hu}`, i.e. imaginary translations `t ↦ t ∓ ih`, so it evaluates
  off the real axis. With finitely many such shifts the extreme class `½ − 2Mh` survives unless `h` is rational, so
  generic `h` needs infinitely many shifts. That is the canonical `sec(hD)` (multiplier `sech(hu)`), which is not
  LP-preserving (CANNOT-497). Finite-shift ports for rational `h` remain open; the class argument does not decide them.
- **New insight:** "nonlocal" in the frontier map's PTR Needs line is forced, and in a specific way: the port must
  shift kernel exponents. Local (polynomial-coefficient, finite-order) ports cannot, whatever their positivity.
- **Status:** Lean-closed, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`):
  - module `formal/GaloisForLFunctions/RHTower/CosineProducerLocalPortObstruction.lean`, wired into `RHTower.lean`;
  - main theorem `RHTower.LocalPort.not_exists_polynomial_port_cosineProducer`;
  - identification `cosineProducer_eq_average` (`A_h = (Ξ(z−ih) + Ξ(z+ih))/2`);
  - reusable: the exponential-polynomial leading-term lemma `eq_zero_of_tendsto_mul_cexp`, the kernel calculus
    `KFun` (transform identities `iteratedDeriv_paperFT_kfun`, `mul_paperFT_kfun`,
    `polyEval_mul_paperFT_kfun`), Fourier injectivity `eq_zero_of_paperFT_real_eq_zero`, and the cusp head/tail
    split `KFun.exists_tail_le`.

  STATUS CANNOT-508. Novelty audited only against the corpus (no external search, per corpus policy).
- **Extension (CANNOT-509, Lean-closed):** module `RHTower/CosineProducerShiftPortObstruction.lean`,
  theorem `not_exists_shift_polynomial_port_cosineProducer`. For every `h ≠ 0` and every finite set of
  imaginary shifts `s ∈ S`, no `Σ_s Σ_k Q_{s,k}(t) A_h^{(k)}(t + is) = Ξ(t)`. This closes the open cases
  (`h ∈ 2ℤ`, rational `h`, finite shifts). New mechanisms:
  - exact `β`-grading of kernel functions via cusp-mode separation (`KFun.eval_part_eq_zero`);
  - annihilation by the top cusp coefficient (`KFun.annihilation`).

  Survivor: a port must use infinitely many imaginary translates, i.e. be infinite order, like
  `sec(hD)`.

## Log
- 2026-10-12 — created directly in 2-fully-proven (PTR loop row 280).
- 2026-10-12 — formalized; moved to 3-formalized (PTR loop row 281).
- 2026-10-12 — extended to all `h ≠ 0` with finitely many shifts (PTR loop row 282, CANNOT-509).
- 2026-10-12 — positive form: imaginary translates of `Ξ` are independent over polynomial-coefficient differential operators (`polynomial_differential_translates_independent`, row 283).
