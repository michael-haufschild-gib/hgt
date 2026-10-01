# Every Weil-positive system has a regularized Mertens constant

- **ID:** MC-195
- **Stage:** 3-formalized (STATUS MUST-635)
- **Type:** THEOREM (Lean)
- **Source:** MC loop cycle 195. It removes the hypotheses of MUST-621 (nonnegative with vanishing local mass) and of `WeilLittleODeviationHarmonicConvergence` (`d = o(Λ)`), which were needed for the existence of the harmonic constant `T`.
- **Statement.** For every full-cone Weil-positive `lam`, `Σ_{n < ⌈e^{K/8+1}⌉} (lam(n) − Λ(n)) χ_K(log n)/n` converges as `K → ∞` (`exists_tendsto_regularizedMertens`). Here `χ_K ∈ [0,1]` (`mertensCutoff_mem`) and `χ_K = 1` on `[1/8, (K−1)/8]` (`mertensCutoff_eq_one`).

## Proof
- **Telescoping bump.** `β(x) = s(8x+1) − s(8x)`, where `s` is the smooth transition. It is supported in `[−1/8, 1/8]` and `Σ_{k≤K} β(x − k/8) = s(8x+1) − s(8x − K)`.
- **Exact profile identity.**
  - For `g(u) = e^{−u/2}β(u)`, translation invariance gives `autoCorr(g)(x)e^{x/2} = ∫ e^{−v}β(v)β(v+x)dv`.
  - Summing the translates gives `∫ e^{−v}β(v)[s((v+y)·8 + 1) − s((v+y)·8 − K)]dv`. On the support of `β` the bracket is `1` when `1/8 ≤ y ≤ (K−1)/8`, and it lies in `[0,1]` always.
  - The window profiles of `WeilOneSidedConvergenceRigidity` therefore form an exact partition of unity, up to the constant `c₀ = ∫ e^{−v}β > 0`.
- **Summability.** `exists_abs_windowSum_sub_vonMangoldt_le` (window pinning plus the smoothed PNT) bounds window `k` by `C e^{−k/16} + C e^{−√(k/8)/1920000}`, which is summable.
- **Assembly.** The first `K+1` windows add up to `c₀ Σ_n d(n)χ_K(log n)/n`, since each window's range extends to the common range with vanishing terms. Summability gives the limit.

## Lean
- Module `RHTower/WeilConeRegularizedMertensConstant.lean`.
- Audit:
  - standard axioms;
  - collision scan clean;
  - wired after `WeilOneSidedConvergenceRigidity`.

## Novelty / significance
- **Mathematics.** The partition-of-unity identity for the pinning profile is a small new observation; the analytic input is the corpus window pinning.
- **Significance.**
  - The Mertens deviation `T(lam)` becomes a well-defined linear functional on the whole Weil cone. For `Λ` it is `0`.
  - HF's pole-point budget gives an upper bound of about `λ₁` for every producer.
  - The uniqueness question can be posed as "is `T` minimized at `Λ`?". This is the sign problem of cycle 188's ZIPM duality, now well-posed for every producer.

## Consistency with the harmonic constant (MUST-637, Lean)
- **Statement.** If `Σ_{n<N} d(n)/n → T` (`d = lam − Λ` on `n ≥ 2`), then `Σ_n d(n)χ_K(log n)/n → T`. No positivity is assumed.
- **Proof.**
  1. On `y ≥ δ`, `χ_K(y) = c₀⁻¹ ∫ e^{−v}β(v)(1 − s((v+y)/δ − K)) dv` with `s` the smooth transition. So `χ_K` is nonincreasing on `[δ, ∞)` and lies in `[0, 1]`.
  2. `χ_K(log n) = 1` for `2 ≤ n < A` once `log A ≤ (K−1)δ`. Here `log 2 ≥ δ = 1/8`.
  3. Abel summation: `Σ_{n≤B} a_n c_n − T = (S_{B+1} − T)c_B + Σ_{n<B}(S_{n+1} − T)(c_n − c_{n+1})`, where only the indices `n + 1 ≥ A` contribute. This is bounded by `ε c_B + ε(c_0 − c_B) ≤ ε`, for an `ε` that also covers the boundary term. Total `≤ 2ε`.
- **Corollary.** `regularizedMertens_nonpos_of_nonneg_of_localMass`: harmonic pinning (`T ≤ 0`; `T = 0 ⇒ lam = Λ`) transfers to `T_reg`.
- **Lean.** `formal/GaloisForLFunctions/RHTower/WeilConeRegularizedMertensConsistency.lean`. Axioms `[propext, Classical.choice, Quot.sound]`.
