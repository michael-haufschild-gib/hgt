# Hardy threshold in the theta-power family: ζ and L(s,χ₈) at the cusp-order walls

- **ID:** theta-power-family-hardy-threshold
- **Stage:** 1-in-progress
- **Type:** CONJECTURE → THEOREM programme
- **Source:** 3F/route2-charge-line-hardy-rigidity (integer points a = 4(n+1)); 1/theta-module-strip-rigidity.
- **Statement.** For real a ≥ 0 put F_a = θ₃^{1−2a}(θ₂θ₄)^a = θ₃·h^{a/4} (branch positive on iℝ₊; h = θ₂⁴θ₄⁴/θ₃⁸
  is zero-free on ℍ, so h^{a/4} = exp((a/4)·log h) is holomorphic). F_a(−1/τ) = (−iτ)^{1/2}F_a(τ), |F_a(τ+2)| = |F_a(τ)|,
  F_a(iy) ~ 2^a e^{−πay/4}, and at cusp 1: F_a(1−1/v) = e^{iπa/4}(−iv)^{1/2}2^{−m}e^{−mπiv/4}(1+o(1)), m = 2a−1.
  Let Λ_a = modXi F_a (entire, even, real on ℝ). Then
  (T1) a > 1/2 (m > 0): Λ_a has finitely many real zeros (saddle at the pole cusp 1 dominates);
  (T2) 0 ≤ a < 1/2 (m < 0): Λ_a has infinitely many real zeros;
  (T3) a = 1/2: F_{1/2} = √(θ₂θ₄) = √2 Σ_{n≥1} χ₈(n) e^{πiτn²/8}, so Λ_{1/2} is the completed L(s,χ₈);
  a = 0 is θ₃, i.e. ξ.
- **Structure.** The holomorphic segment a ∈ [0,1/2] of the unique S-symmetric weight-½ theta-power family has the two
  Euler products exactly at its ends: a = 0 is the wall of the cusp-∞ order (pole for a < 0), a = 1/2 the wall of the
  cusp-1 order (pole for a > 1/2). Hardy's property is exactly nonpositivity of the cusp-1 order.

## Mechanisms
- T1: exact saddle on Im x = −β at cusp 1 with real m; saddle phase e^{iπa/4}·e^{−imπ/8} = e^{iπ/8}, independent of a
  (h > 0 on the unit-circle arc); Farey far field depends on m only linearly in the exponent ⇒ cap R₀/3 persists;
  |F_a| = |θ₃|^{1−2a}|θ₂θ₄|^a is branch-free for all far-field bounds.
- T2 (new short Hardy argument): if Λ_a keeps one sign on a half-line, T(iα) bounded as α → π/4 (cusp −1 is a zero
  of F_a when m < 0) gives, by Fatou, ∫|D| cosh(πw/4) < ∞, hence T bounded on the closed strip, hence
  |F_a(p)| ≤ B|p|^{−1/4} on ℍ. But τ_k = −1/(τ₀+2k) has |τ_k|^{1/4}|F_a(τ_k)| = |τ₀+2k|^{1/4}|F_a(τ₀)| → ∞.
  Uses only the S-law, |F|-periodicity and the axis bound. It fails exactly at m = 0 (axis blow-up ≍ Im^{−1/2} equals the
  transferred bound), which is where L(χ₈) sits.

## How it could fail
Branch of log h at cusp 1 (k ≠ 0) — excluded: h real > 0 on |τ| = 1 forces Im log h = 0 there. Far-field constants for
non-integer m. Fatou step needs strip inversion for general F (corpus has it only for ζ).

## Lean plan (descriptive module names)
1. ThetaHauptmodulLogarithm — θ zero-free on ℍ (from Δ = (θ₂θ₃θ₄)⁸/256 and Δ ≠ 0), holomorphic log of h on ℍ
   (Cayley + `DifferentiableOn.isExactOn_ball`), S-invariance, real on iℝ₊ and on |τ| = 1, cusp-1 branch formula.
2. ThetaPowerFamily — F_a, S-law, modulus periodicity, cusp decay at rate πa/4, window law at cusp 1 for real a.
3. Transform machinery at cusp-decay rate κ (generalizes ModularAxisSourceTransform / tail / contour shift).
4. T1: real-m saddle, far field, dominance, finiteness.
5. T2: strip inversion for general F, Fatou transfer, modular growth contradiction.
6. T3: θ₂θ₄ = 2(Σχ₈(n)q^{n²/8})², Mellin identification.

## Log
- 2026-09-26 — frozen; supersedes theta-module-strip-rigidity as the next target (SR folds into T1 later).
- 2026-09-26 — T2 [L]: `thetaPowerXi_real_zeros_infinite` (0<a<1/2), module ThetaPowerHardyZeros; generic transfer
  `strip_bounded_of_stripDensity_tail_sign` / `exists_fourier_zero_ge_of_strip_unbounded` (StripSourceHardyTransfer):
  axis-bounded even real strip source + one-signed Fourier tail ⇒ bounded on the strip.
- 2026-09-26 — T1 [L]: `thetaPowerXi_real_zeros_finite` (a>1/2), modules ThetaPowerSaddleWindow/FarField/Integral:
  real-m saddle (Gaussian law R₀−Reψ ≥ ms²/(28t⁶), core radius (1008(a+1)/m+1)t³), Farey |F_a| ≤ 36^a|cτ+d|^{-1/2}e^{mπIm/4},
  holomorphic extension to |Im w|<1. Infrastructure: holomorphic log h on ℍ (ThetaHauptmodulLogarithm),
  exact cusp-1 branch log h(1−1/v) = iπ − 8log2 − 2πiv + Log Q(v), window law for all real a (ThetaPowerFamily).
  All axioms [propext, Classical.choice, Quot.sound]. Open: T3 (a = 1/2 is L(s,χ₈)); a = 1/2 Hardy (transfer fails exactly there).
