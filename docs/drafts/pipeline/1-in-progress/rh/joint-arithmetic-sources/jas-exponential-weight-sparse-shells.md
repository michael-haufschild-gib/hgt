# Exponentially weighted JAS: sparse shell positivity is RH (no large-height input)

## Conjecture C221

Fix `0 < λ < π`. For a zero `q` of ξ (with multiplicity), write `q = ½ + δ_q + iγ_q` and use the
weight

`ω_q = exp(−λ √(q(1−q)))`,

where the principal square root is taken and `Re q(1−q) = ¼ − δ² + γ² > 0`. For a dyadic shell
`P_N = primes in (N, 2N]` put `W^±_q(N) = Σ_{p∈P_N} p^{−1} p^{∓(q−½)}`, and define the
**exponential-kernel test**

`E_N(u) = Re Σ_q ω_q [exp(u W⁺_q + ū W⁻_q) + exp(ū W⁺_q + u W⁻_q)]`.

**C221:** `RH ⟺ ∃ᶠ N, ∀ u ∈ ℂ, E_N(u) ≥ 0`.

**Forward direction.** Under RH every `q` is on the line, so `W⁻_q = conj W⁺_q` and both exponents
are real. Also `q(1−q) = ¼ + γ² > 0` makes `ω_q > 0`, so every term is positive.

This is a sparse JAS receiver without ZAL, no-chain, quasi-RH or single-prime input. Compare
MUST-1411: infinitely many shells under ZAL. Compare CANNOT-518: sparse families with the polynomial
weights `1/(q(1−q))` cannot drop the large-height input.

## Why the weights matter (insight from cycles 219–220)

With the weights `|1/(q(1−q))| ≈ γ^{−2}`, positivity at a scale with top big sum `Z` allows a top
group with weight `≤ e^{−cZ}`, that is, at heights `γ ≥ e^{cZ/2}`. There density estimates and
prime-sum control are useless, which is the CANNOT-518 obstruction.

With `|ω_q| ≤ e^{−λ|γ_q|}` the penalty `log(1/|ω|) ≳ Z` puts the relevant zeros at heights
`≲ Z/λ ≤ N^Θ`. In that range Ingham's density theorem bounds every candidate tie group by `N^{θΘ}`
with `θ < 1`, which is far too few to cancel the power sums.

The uniform angle survives: `|arg ω_q| = λ|Im √(q(1−q))| ≤ λ|δ_q| ≤ λ/2 < π/2`, so
`Re ω ≥ cos(λ/2)|ω|`. This is because `Im √(a − ib) = −b/(2 Re √)` with `Re √ ≥ |γ|` and
`b = 2δγ`. Weights such as `e^{−γ²}` rotate their phase and fail this test.

## Paper proof of `⇐` (to be completed in full detail before Lean)

Assume `¬RH`. Let `Θ = sup|δ_q| ∈ (0, ½)`. Let `θ(σ) = 3(1−σ)/(2−σ)` be Ingham's exponent, which is
`< 1` for `σ > ½`. Fix `ε > 0`. Pick a zero `q₀` right of the line with
`δ₀ > Θ·max((2 + θ*)/3, 4/5)`, where `θ* = θ(½ + δ₀/2) + ε`. Such a zero exists because `Θ` is a
supremum: the margin is `≈ (2/3)Θ²`.

1. **Fourier power sums.** `E_N ≥ 0` on the circle `|u| = r` gives `|Ê_k(r)| ≤ Ê_0(r)`. For the
   exponential kernel the `k`-th coefficient is `(r^k/k!)·½Σ_q [ω_q (W⁺)^k + ω̄_q conj(W⁻)^k + …]`
   up to the factors `Σ_j (r²W⁺W⁻)^j k!/((k+j)! j!)`. Since `|W⁺W⁻| ≲ 1/log² N` uniformly, these are
   `1 + O(1/log² N)`, and `Ê_0(r) ≤ 3W` for `r ≤ log N`. So
   `|Σ_{family} ω̃ W̃^k| ≤ 4 k! W/r^k`, with weights `ω̃ ∈ {ω, ω̄}` of uniform angle.
2. **Bounds.**
   - Trivial bound: `|W_q| ≤ C₁ N^{|δ_q|}/log N` (Chebyshev).
   - Target: `|W_big(q₀)| ≥ c₀ N^{δ₀}/log N` (shell main term, MUST-1411).
3. **Adaptive height cutoff.**
   - Let `G(T) = {q : |γ_q| ≤ T, |δ_q| ≥ δ₀/2}` and `Z(T) = max_{G(T)} |W_big|`; `Z(T)` is
     nondecreasing and finitely valued.
   - Put `κ(Z) = e²(C₁N^Θ/Z)²` and `L(Z) = log(C₁N^Θ/Z)`, with
     `T(Z) = (2/λ)((Z/κ)L + log D)`.
   - Iterating `T ↦ T(Z(T))` stabilizes at `T*`. Take `ν ≈ Z/κ`.
4. **Turán** (`HTGeometry.exists_norm_weightedPowerSum_ge`) on `G(T*)`. Each top group contains the
   maximizer and has weight sum `≥ c_λ e^{−λ(T*+1)}`, by the uniform angle and the height bound. So
   some `ν ∈ [M+1, M+n]` has `|Σ_G ω̃ W^ν| ≥ c_λ e^{−λ(T*+1)} Z^ν/D`, where
   `D = 2en(6(n+1)(M+2n+2))^n`.
5. **Rest.** The remaining terms are small:
   - zeros with `|δ| < δ₀/2` give `≤ W(C N^{−δ₀/2})^ν`-relative; this needs `δ₀ > 4Θ/5`;
   - zeros above `T*` give `≤ e^{−λT*/2}(C₁N^Θ)^ν`; this is the choice of `T(Z)`;
   - the small-W parts are negligible.
6. **Counting** (Ingham–Huxley, `exists_zeroHeightBox_ncard_le_ingham_huxley`):
   - `n = |G(T*)| ≤ C T*^{θ*}(log)^B`, with `T* ≲ N^Θ`;
   - `κ log D/Z ≪ 1` needs `δ₀ > Θ(2+θ*)/3`.
7. **Contradiction.** `c_λ e^{−λT*} Z^ν/D > 4ν! W + rest`. By the choice of `κ` this reduces to
   `log(eκ) ≥ 2L + 3κ log D/Z`. So `E_N(u) < 0` for some `u` at every large `N`.

The open points before Lean are full bookkeeping of all constants, and the claim that
`Ê_0(r) ≤ 3W` holds uniformly.

## Lean plan (multi-cycle)

1. Definitions:
   - `jasExpWeight λ q`, via cpow `½`;
   - `jasExpKernelTest P u`, the exponential kernel with these weights;
   - the predicate `JasExpShellPositive N λ`.
2. Weight facts: uniform angle, `|ω| ≤ e^{−λ|γ|}`, `|ω| ≥ e^{−λ(|γ|+1)}`, summability.
3. RH ⇒ positivity for all `u`.
4. Fourier extraction on circles for the exponential kernel family (non-holomorphic in `u`):
   `|Σ ω̃ W̃^k| ≤ 4k!W/r^k`.
5. Cumulative Ingham count `#{|γ| ≤ T, Re ≥ σ} ≤ C T^{θ(σ)+ε}`, by summing the corpus dyadic-box
   bound.
6. The fixed-point height and the Turán application.
7. Assembly: `¬RH ⇒ ∀ᶠ N, ¬positivity`.
8. Capstone: `RH ⟺ ∃ᶠ N, JasExpShellPositive N λ`.

## Kill attempt (cycle 220, continued): SURVIVES, with a sharper open core

The paper sketch above has a gap at steps 1 and 4, found while checking the bookkeeping.

- **Mixing.** The `k`-th Fourier coefficient of the exponential kernel is
  `Σ_j (rW_big)^{k+j}(rW_small)^j/((k+j)! j!)`. Its corrections are small only relative to each
  zero's own term (`|W_big W_small| ≲ 1/log² N`). Turán's lower bound loses a factor
  `e^{−λT}/D`, which is exponentially small, so polynomially small relative corrections cannot be
  absorbed. Exact power sums are unavailable at level 1, and raising the level `σ` only makes the
  mixing polynomially smaller.
- **Robustness is the real constraint.** Any anti-alignment of `n` near-tied points with errors `e_t`
  in the exponents must tolerate the root-of-unity configuration. That forces
  `|e_t| ≲ e^{−C n log n}` (Turán) or a cost `R ≈ R₀^{2^n}` (ladder, MUST-1411). The kernel errors
  here (small sums, `ū W_small ≈ R N^{−2δ}`) are only polynomially small. So the admissible near-tie
  count is `n ≲ c' log N/log log N` (Turán-robust) or `n ≲ log log N` (ladder).
- **What exponential weights do achieve.** Take the target to be the heaviest (lowest) zero `q_low`
  among those whose big sum is near maximal. Every other near-maximal zero of non-negligible weight
  lies in a height window of length `O(1/λ)` above `γ_low`. All super-high zeros are negligible.

**Sharpened [OPEN CORE].** The receiver works if, at heights `≤ N^{O(1)}`, a height window of length
`1/λ` contains `≤ c' log N/log log N` zeros with `|Re ρ − ½| ≥ δ₀/2`. Known bounds give only
`O(log N)` per unit window. So the large-height obstruction (CANNOT-518) has been converted into a
**local clustering bound for off-line zeros in short windows at moderate height**. This is a cleaner
and strictly more local target. Scale averaging over all shells (`∀ᶠ N`) might also break such
clusters, but that remains open.

Status: C221 remains OPEN. The exponential-weight mechanism is a valid reduction. Next Lean target: a
robust, polynomial-cost multi-point anti-alignment lemma (Turán + Carathéodory with explicit error
tolerance), which is reusable for all JAS receivers.
