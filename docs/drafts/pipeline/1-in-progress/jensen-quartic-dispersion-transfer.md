# Quartic Jensen hyperbolicity from a dispersion margin: the corrected tolerance law and the two-sided theta dispersion

- **ID:** `jensen-quartic-dispersion-transfer`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE → THEOREM (Lean, bricks) — successor of `jensen-polya-unconditional-frontier.md` §14–§22
- **Source:** Pólya's Jensen criterion (RH ⟺ all `J^{d,n}` hyperbolic); the corpus's exact `ε`-reduction
  (`jensenPolyEval_eq_model_add_perturbation`), the two-sided moment-ratio sandwich (`MomentRatioTwoSided`),
  the theta-kernel log-concavity (`ThetaCuspKernelLogConcavity`), and the Xi bridge
  `PrimeArchThetaCumulantMinor.iteratedDeriv_Xi_zero_eq_rawEvenMoment`.
- **Statement (target):** `J^{4,n}` is hyperbolic for every `n ≥ n₀` with an explicit `n₀`, by pure analysis
  (no zero data), through a quantitative two-sided Turán inequality for the Taylor coefficients of `Ξ`.

## Objects

`Φ := thetaCuspFullSource` (even, positive, strictly log-concave on `ℝ`), `m(k) := thetaCuspRawEvenMoment k
= 2∫₀^∞ x^{2k} Φ(x) dx`, so `iteratedDeriv (2k) Xi 0 = (−1)^k m(k)` and `ξ(½+z) = Σ m(k) z^{2k}/(2k)!`.
Pólya's coefficients are `γ(k) = k!·m(k)/(2k)!`, `J^{d,n}(X) = Σ_j C(d,j) γ(n+j) X^j`. Tilted measures
`π_k ∝ x^{2k}Φ(x)dx` on `(0,∞)`, `s = x²`. Dispersions `D_k := m(k)m(k+2)/m(k+1)² − 1 = Var_{π_k}(s)/E_{π_k}[s]²`.
Turán at `k` is `D_k ≤ 2/(2k+1) = 1/b`, `b = k+½` (corpus `turan_iff_dispersion_le`).

## Finding 1 — the quartic tolerance is `1/(2b)`, not `2/(3b)`; the general law is `K*(d) = 1/⌊d/2⌋`

Write `z = −b(1+δ)`, `δ = t/√b`, `ρ_j = b^j/(b)_j = 1 − C(j,2)/b + (C(j,2)² + Σ_{i<j}i²)/(2b²) + …`.
The model `A(z) = Σ_j C(4,j) z^j/(b)_j` satisfies, exactly at `t = 0`, `(b)₄·A(−b) = 3b² − 18b`, and
`A(−b(1+t/√b)) = b^{−2}(t⁴ − 6t² + 3) + O(b^{−5/2}) = b^{−2}·He₄(t) + …` (probabilists' Hermite). The
old card's `A(−b(1+δ)) = δ⁴ − (6/b)(1+δ)²δ² + O(b⁻²)` drops the `+3/b²` term, which is of the same order
as the two it keeps; its critical points `w = 1 ± √(2/b)` and the value `κ* = 2/(3b)` are artefacts.

With `ε_j = C(j,2)κ` the perturbation is `Σ_j C(4,j)ε_j z^j/(b)_j = 6κ(1+δ)²[ρ₂ − 2(1+δ)ρ₃ + (1+δ)²ρ₄]
= (6κ/b)(t² − 1) + O(κ b^{−3/2})`, so with `K := κb` the perturbed quartic is, to leading order,

```text
He₄(t) + 6K·He₂(t) = t⁴ − 6(1−K)t² + 3(1−2K),
```

hyperbolic iff `K ≤ 1/2` (the two inner roots collide at `t = 0`, i.e. at `z = −b`, when `K = 1/2`).
So `κ*(b) = 1/(2b)·(1 + O(b^{−1/2}))`. Checks: `d = 2` gives `He₂ + K·2·He₀`... exactly `t² − 1 + K`,
threshold `K = 1` (the corpus's exact `1/b`); `d = 3` gives `He₃ + 3K He₁ = t(t² − 3 + 3K)`, threshold
`K = 1`.

**General degree (leading order).** For every `d`, `Σ_j C(d,j)C(j,2)(−1)^j(1+δ)^j ρ_j` expands to
`(−1)^d b^{−(d−2)/2}[C(d,2)t^{d−2} − ((d)₄/4)t^{d−4}] + … = (−1)^d b^{−(d−2)/2}·½He_d''(t) + …`, and
`A_d(−b(1+t/√b)) = (−1)^d b^{−d/2} He_d(t) + …`. Hence the leading-order perturbed polynomial is

```text
He_d(t) + (K/2)·He_d''(t) = He_d(t) + (K/2)·d(d−1)·He_{d−2}(t) .
```

The first root collision is the central one: at `t = 0` for even `d` the constant term is
`(−1)^{d/2}(d−1)(d−3)!!·(1 − Kd/2)`, vanishing at `K = 2/d`; for odd `d` the linear coefficient vanishes at
`K = 2/(d−1)`. Verified by hand for `d ≤ 6` that no other collision precedes it. **Law (leading order):**

```text
J^{d,n} hyperbolic  ⇐  D_k ≤ K*(d)/b for k ∈ [n, n+d−2],   K*(d) = 1/⌊d/2⌋ .
```

Against the theta dispersion `D_k ≈ 2/(k(1+2u_k))` (`u_k ≈ ½ log k` the tilted mode), this gives the
explicit exponential wedge `d ≲ 1 + 2u_k`, i.e. `n ≳ e^{2d−2}`. This is weaker than Holland's 2026 wedge
`n³log²n ≥ K d⁵` (arXiv:2608.08682) for large `d`, but explicit; the perturbative dispersion route is
confined to `d ≲ log n`, as `jensen-polya-unconditional-frontier.md` §10.3 predicted.

**Consequence for `d = 4`.** The requirement `D_k ≤ 1/(2b)` against `D_k ≈ 2/(k(1+2u_k))` closes when
`u_k ≥ 3/2`, i.e. `k ≳ 90`; with rigorous constants the expected threshold is a few hundred, not `n ≥ 5`.

## Finding 2 — the transfer is anisotropic; a two-sided dispersion bound is required

The exact perturbation is a function of three dispersions: `1 + ε_j = ∏_{l<j−1}(1 + D_{n+l})^{j−1−l}`, i.e.
`ε₂ = D_n`, `ε₃ = (1+D_n)²(1+D_{n+1}) − 1`, `ε₄ = (1+D_n)³(1+D_{n+1})²(1+D_{n+2}) − 1`. Along the diagonal
`D_n = D_{n+1} = D_{n+2} = κ` the tolerance is `≍ 1/b`; in the transverse direction (e.g. `D_{n+1}` alone)
the perturbation at `z = −b` is `≈ −2D_{n+1}b⁴` against `A ≈ 3b²`, tolerance `≍ 1/b²`. So the box
`0 ≤ ε_j ≤ (1+κ)^{C(j,2)} − 1` of `MomentRatioTwoSided` is useless for the quartic: the hypothesis must be
`D_{n+l} ∈ [κ(1−η), κ]` with `η = O(1/b)`. For the theta measure `D_{k+1}/D_k = 1 − O(1/k)`, so this is
satisfiable, but it demands a **lower** bound on `D_k` matching the upper bound to relative `O(1/k)`.

## Programme (all unconditional, all Lean)

1. **`LogConcaveDensityCalculus`** (general, on `ℝ`): for `μ = e^{−V}dx/Z` with `V ∈ C²`, `V'' > 0`,
   `e^{−V} → 0` at `±∞`: integration by parts `E[gV'] = E[g']`; **one-dimensional Brascamp–Lieb**
   `Var(f) ≤ E[f'²/V'']` (proof: `Var f = ∫∫_{x<y}(∫_x^y f')² dμdμ`, Cauchy–Schwarz against `V''`, and
   `∫∫_{x<t<y}(V'(y)−V'(x))dμdμ = ρ(t)`); **Cramér–Rao** `Var(f) ≥ (E f')²/E[V'']`. Absent from mathlib.
2. **`QuarticJensenDispersionTransfer`** (Theorem A, exact): if `b ≥ b₀` and `D_{n+l} ∈ [κ(1−η), κ]`
   (`l = 0,1,2`) with `κ ≤ θ/(2b)`, `η ≤ c/b`, then `J^{4,n}` is hyperbolic. Proof: sign alternation of the
   monic quartic `(b)₄·A_ε` at `z = −b ± √(3b)` and `z = −b` (`hyperbolic_of_alternating`), all polynomial
   inequalities in `b, √(3b), D's`.
3. **`ThetaTiltDispersionBounds`** (Theorem B, two-sided): in the log variable `w = log x`, `π_k` has density
   `∝ e^{(2k+1)w}Φ(e^w)` with `V_k''(w) = u|(log Φ)'(u)| + u²c(u)`, `c = −(log Φ)'' ≥ 4πe^{2u}(1−η(u))`
   (corpus: `thetaCuspBornWittenLogCurvature_bounds`, tail weights). Brascamp–Lieb and Cramér–Rao with
   `f = e^{2w}` both evaluate to `4/(ū² V_k''(ū))·(1 + O(1/k))` at the tilted mean `ū`, so
   `D_k = 4/(2k + ū²c(ū))·(1 ± C/k)` with explicit `C`, once `Var_k(u) ≤ 1/inf V''` (concentration) and a
   lower bound on `ū` are proved. This is a **quantitative two-sided Turán inequality for Ξ**; its upper
   half gives `D_k ≤ 1/(2k)` for `k ≥ k₀` (Turán with margin one half).
4. **`JensenQuarticXi`** (Theorem C): `J^{4,n}` hyperbolic for all `n ≥ n₀`.

## Novelty, stated hostilely

- Finding 1 corrects a corpus error; the leading-order law `K*(d) = 1/⌊d/2⌋` for `He_d + (K/2)He_d''` is
  a small exact statement about Hermite polynomials that I have not found in the literature, but it is a
  computation. Holland (Aug 2026) proves a far stronger wedge by matching five ratio quotients.
- Theorem A is a Laguerre-model stability lemma of the type of Holland's Prop. 2.2 (fifth-order multiplier
  stability), at second order and with explicit constants; not deep.
- Theorem B (two-sided `D_k` with explicit constants) is, to my knowledge, new: CNV give `D_k ≤ 1/b`,
  GORZ give asymptotics without explicit inequalities. It is the one statement here worth defending.
- Theorem C is known to be true (GORTTW Cor. 1.3 via `RH` verified to `3.06·10¹⁰`); its value is a
  computation-free proof with an explicit threshold, and the method.

## Gates
- [x] 0 → 1: corrected tolerance law, anisotropy finding, exact programme with named bricks
- [ ] Theorem A in Lean
- [ ] `LogConcaveDensityCalculus` (IBP, Brascamp–Lieb, Cramér–Rao) in Lean
- [ ] Theorem B in Lean (two-sided, explicit `C`, `k₀`)
- [ ] Theorem C in Lean, wired, axiom-clean
- [ ] STATUS entries; frontier map Jensen line updated

## Log
- 2026-09-06 — created; Findings 1–2 derived on paper (hand-checked `d ≤ 6`); programme fixed.
- 2026-09-06 — `HTGeometry/OneDimBrascampLieb.lean` (axiom-clean, `lake build` green, wired):
  `sq_intervalIntegral_mul_le` (Cauchy–Schwarz on an interval), `sq_sub_le_integral_mul`
  (`(f(y)−f(x))² ≤ (∫ₓ^y f'²/V'')·(V'(y)−V'(x))`), `integral_Ioi_deriv_mul_density`,
  `integral_Iic_deriv_mul_density`, `double_integral_kernel` (`∬_{x<t<y}(V'(y)−V'(x))ρρ = ρ(t)`),
  **`variance_le_integral_deriv_sq_div_curvature`** (one-dimensional Brascamp–Lieb for an abstract
  positive density with `ρ' = −V'ρ`, proved by Fubini/Tonelli — no Witten Laplacian, no boundary
  behaviour of `f`), `variance_le_of_exp` (Gibbs form), `sq_integral_mul_mul_le` (weighted
  Cauchy–Schwarz on `ℝ`), `integral_deriv_mul_density_eq` (integration by parts `∫g'ρ = ∫gV'ρ`),
  `integral_score_mul_density_eq_zero`, **`sq_integral_deriv_le_variance_mul_curvature`**
  (Cramér–Rao `(∫f'ρ)² ≤ Var(f)·∫V''ρ`). Mathlib has none of these; the corpus had only algebraic
  interfaces (`OneDimBrascampLiebCorrection`, `DoublyExponentialMargin.variance_le_of_convexity` is
  a tautology). Both directions of the dispersion sandwich now have their general engine.
- 2026-09-06 — **Theorem A in Lean.** `HTGeometry/QuarticJensenDispersionTransfer.lean` (axiom-clean,
  `lake build` green, wired): `quartic`/`quarticPoly` (the monic quartic of three dispersions),
  `quartic_eq_ref_add` (exact decomposition `F = F_ref + ε₁L₁ + ε₂L₂ + Q`), `refQuartic_expansion`
  (the five `δ`-coefficients, Lean-verified against the symbolic expansion), `quartic_split`,
  `refQuartic_center_ge` (`F_ref(−b) ≥ ¾b² − 18b − 3/2`), `refQuartic_outer_le`
  (`F_ref(−b(1+δ)) ≤ −6(1−K)²b² + 90b + 104 + |δ|(8(1−K)²b² + 88b + 78)` at `δ² = 3(1−K)/b`),
  `center_pos`, `outer_neg`, `quartic_far_left_pos`, and
  **`hyperbolic_quarticPoly`**: for `b ≥ 2000`, `0 ≤ D_l`, `D₀b ≤ 1/2`, `|D₀−D₁|·b^{3/2} ≤ 1/8`,
  `|D₀−2D₁+D₂|·b² ≤ 1/5`, the quartic has four distinct real roots (sign alternation at
  `−3b < −b−s < −b < −b+s < 0`, `s = √(3(1−D₀b)b)`). Constants are deliberately loose; the sharp
  diagonal threshold is `D₀b < 1`. Interface for Theorem B: two-sided dispersion control with
  relative precision `O(1/b)`, i.e. third and fourth cumulant bounds of the tilted log variable.
