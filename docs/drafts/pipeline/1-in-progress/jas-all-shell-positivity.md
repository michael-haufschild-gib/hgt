# All-shell constant-vector positivity as an RH criterion without a large-height input

## Conjecture C219

`RH ⟺ ∃ N₀, ∀ N ≥ N₀, JasConstProductPositiveOn (primes in (N, 2N]) 1.`

The forward direction is known. The content is the converse with NO ZAL, no-chain or quasi-RH side
condition. If true, RH would be a positivity statement with one complex parameter per dyadic scale.

Status quo:

- Infinitely many shells suffice under ZAL or no-chain (MUST-1411).
- Quasi-RH plus the doubly exponential windows gives no-chain (MUST-1413).
- Sparse families cannot drop the large-height input (CANNOT-518).
- C219 asks whether the full sequence of shells replaces the large-height input.

## Kill attempt (cycle 219): SURVIVES PRELIMINARY ATTACK

The analysis uses the explicit formula for shell big sums
`S_q(N) = Σ_{N<p≤2N} p^{−(3/2−q)}` of an off-line zero `q = ½ + δ + iγ`, with `x ∈ [N, 2N]` and
difference form:

- **main term** `x^{δ+iγ}/((q−½) log x)`, which dominates for `γ ≲ x^{½−δ}`;
- **self-interaction** from the conjugate zero `q̄`: `x^{2δ−½}/((2δ−½) log x)`, real and independent
  of `γ`;
- **cluster terms** `x^{q+ρ̄'−3/2}/((q+ρ̄'−3/2) log x)` from zeros `ρ'` near `q`;
- **on-line noise** from the zeros near `−γ`, heuristically `≈ x^{δ−½}·polylog`.

**Mechanism found (paper).**

1. **Legendre dominance.** Write `h_q(a) = a|S_q(N)| + log w_q`, with `w_q = |1/(q(1−q))|`. The test
   fails at scale `N` whenever the Legendre maximizer over `q` is isolated and `h ≥ log W₀ + C`. A
   multi-point tie group is handled by MUST-1411.
2. **Coherence law.**
   - In the self-interaction regime, isolated super-high zeros have REAL POSITIVE big sums.
   - So do clusters of diameter `≪ 1/log N`. The Cauchy–Gram matrix
     `K_{lm} = e^{i(γ_l−γ_m)log N}/((2δ−½) + i(γ_l−γ_m))` is positive definite (the Fourier transform
     of a positive function). Hence `Σ_l S_l = 1ᵀK1 ≈ M²·N^{2δ−½}/(2δ−½) > 0`.
   - Coherent families cannot cancel in their power sums. Positivity therefore forces the termwise
     weight penalty `w_q ≲ e^{−a S_q}` (Lean: MUST-1414).
3. **Graduation.** Every fixed off-line zero `q₀` eventually leaves the self-interaction regime. Its
   big sum then grows like `N^{δ₀}/γ₀` while its weight stays fixed, so it must be hidden by others.
4. **Θ dichotomy.** Let `Θ = sup|Re ρ − ½|`.
   - If `Θ < ½`, then for large `N` the top group lies in the main-term regime, at heights
     `≤ N^{½−δ}` and weights `≥ N^{−1}`. Hiding needs `≳ N^{Θ}/log N` phase-cancelling near-ties.
     Huxley density bounds the near-tie count by `N^{(12/5)(½−δ)²}`, which is smaller when
     `δ ≳ 0.21`.
   - If `Θ = ½`, super-high coherent zeros can be top. The weight penalty holds termwise, but zeros
     with large big sums relative to `q₀` pay `w_q ≤ 2W(S_q/S₀)^{−S₀/2}`. When `δ₀ > ¼` this makes them
     harmless to anti-aligning `q₀`.
5. **Scale averaging fails.** A Hilbert-inequality argument over `log N` cannot break cancellation
   inside a super-high cluster. Its frequency spacing is `~1/log γ`, while its reign has length
   `~log log γ` in `log N`, so the cluster is frozen over its whole reign.

**[OPEN CORE]: multi-scale pretentious super-high off-line zeros.** Positivity at all large shells
survives every argument above only if, for every large `N`, the top big-sum group consists of
off-line zeros at heights `log γ ≳ N^{c}`. For these the on-line noise is uncontrolled. Their shell
sums `|Σ_{N<p≤2N} p^{−(1−δ)−iγ}|` would have to be near-trivial in size (pretentious) at every scale
`N ≤ (log γ)^{C}`. No zero-density, zero-free-region (VK) or large-values estimate excludes a sparse
tower of such zeros. Excluding them needs control of prime sums at heights
`|t| ≥ exp((log N)^{3/2})`, where no cancellation is known.

## Lean (cycle 219)

- MUST-1413, `RHTower/JointAncestryDoubleExpWindowsDyadicShells`: RH ⟺ quasi-RH (or single-prime
  `σ < ½`) ∧ doubly exponential window positivity ∧ ∃ᶠ N shell positivity.
- MUST-1414, `HTGeometry/PositiveExponentialSumPowerSums`: Carathéodory power-sum law for (summable)
  exponential sums with `Re ≥ 0`, and the coherent weight penalty `w_j (R S_j)^n ≤ 2 n! Σ w`.

## Next

- Make the coherence law exact for the JAS kernel. Use Fourier coefficients in `arg u` of the
  non-holomorphic `K_u = exp(u S_big + ū S_small + e)`.
- Attack the open core with a multi-scale large-values bound for `Σ_p p^{−1+δ−iγ}` along a single
  ordinate `γ`. The measure of ordinates that are pretentious at `K` independent scales should decay
  like `e^{−cK}`. Combine it with zero spacing to show such ordinates cannot host zeros.
