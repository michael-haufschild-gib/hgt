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

## 2026-09-06 — external SOTA audit: Holland, arXiv:2608.08682 (9 Aug 2026)

**Verdict on this card's paper content: REDISCOVERED.** Jonathan Holland, "A new hyperbolicity wedge
and a joint semicircle limit for Jensen polynomials of Riemann's ξ-function" (arXiv:2608.08682,
math.NT, 9 Aug 2026) works in exactly the objects of this card and goes much further:

- Same coordinates: `γ(n) = n!/(2n)!·M_n` with `M_n = ∫Φ(u)u^{2n}du`; `γ(n+j)/γ(n) =
  E_n[U^{2j}]/(4^j (n+½)_j)` (his (11)); quotient invariants `q_k = R_{k+1}²/(R_k R_{k+2})`, i.e.
  `q_k = (b+k+1)/((b+k)(1+D_k))` in our dispersions; the Laguerre family `S^j/(B)_j` is the
  "diagonal" (Gamma-renormalised) reference, realised as a beta–Sonine dilation of the baseline.
- Same defect sizes: `δ₀ = Δ² log M = 2/(n 𝓛_n)(1+O(1/𝓛_n))` (so `D₀ b → 0` like `2/log n`),
  first defect `𝒟_n = 2/(n² 𝓛_n)` (our `ε₁`), second defect `𝒬_n = 2/(n³ 𝓛_n)` (our `ε₂`), from the
  sectorial saddle `h''(x) = 2/(x𝓛_x)`, `h''' = −2/(x²𝓛_x)`, `h⁗ = 4/(x³𝓛_x)` (his Lemma 4.2), with
  `𝓛_x = L_{2x−2}` the Lambert-type solution of `x = L(πe^L + ¾)`. This is the paper proof of
  Theorem B (MUST-224's inputs) at every order, with the sign pattern of the log-moment derivatives.
- Strictly stronger theorem: matching `R₀..R₄` exactly by a finite-free product of two Jacobi
  factors (Laguerre → Jacobi → `₃F₂` model), then a fifth-order multiplier stability principle
  (his Prop. 2.2: `c(0)=…=c(4)=1`, `sup_Ω|c−1| ≤ ε < 1/6`, critical-point ratio bounds
  `|y^k p^{(k)}/p| ≤ r^k`) gives `J^{d,n}` hyperbolic whenever `n³ log²(n+2) ≥ K d⁵`; for `d ≤ 4`
  the model matches all coefficients and hyperbolicity is automatic for large `n`. Joint semicircle
  law for the zeros along the wedge.

**What survives here (corpus assets, not literature novelty):**
- `hyperbolic_quarticPoly` / `quartic_signs`: an explicit-constant degree-four certificate
  (`b ≥ 2000`, `D₀b ≤ ½`, `|ε₁| b^{3/2} ≤ 1/8`, `|ε₂| b² ≤ 1/5`) by sign alternation at five points —
  the anisotropic tolerance (`ε₁` direction gains `√b` over an isotropic `o(δ⁴)` condition because the
  linear response `L₁` vanishes at `z = −b` to leading order) is not stated by Holland, but it changes
  nothing for `Ξ` (his defects sit far inside both boxes).
- `JensenQuarticXi.lean`: `J^{4,n}(X) = γ(n)/(b)₄ · quartic(b, D₀, D₁, D₂, tX/4)` and the
  conditional capstone for `Ξ`; dispersions are the corpus Pearson chi-squares (nonnegative).
- The 1-D Brascamp–Lieb / Cramér–Rao module and the tilted theta log-density calculus.

**Consequence for the programme.** Theorem B (two-sided cumulant bounds of the tilted theta
measures with relative precision `O(1/n)`) is now a formalisation of Holland's Lemmas 4.2–5.4, not
new mathematics; it is deprioritised. The regime `d = o(n)` is perturbative and RH-blind by theorem
(unconditional hyperbolicity). The fixed-`n`, all-`d` regime is `F₀^{(n)} ∈ LP` for
`F₀(x) = Σ γ(j)x^j/j!` (`Ξ(t) = F₀(−t²)`), which by Kim / Ki–Kim (Pólya–Wiman, Fourier–Pólya for
order `< 2`) holds for some `n` iff `Ξ` has only finitely many non-real zeros. The model-matching
method cannot pass `d ≍ n log n`: with `K` Jacobi factors the Hermite–Genocchi residual is
`≍ (d+2r)^{2K+1}/(n^{2K}(2K+1)! log n)`, `r ≍ √(nd)`, so `d ≲ 2nK/e` with `K ≲ log n/log log n`
factors at most, and below the saddle threshold the coefficients are arithmetic (the low-lying zeros).
The lane is a receiver in both regimes; next cycle pivots.

## 2026-09-06 — Lean close-out

- `HTGeometry.QuarticJensenDispersionTransfer`: refactored; `quartic_signs` exports the five sign
  facts (`0 < s < b`, signs at `−3b, −b−s, −b, −b+s, 0`) and `hyperbolic_quarticPoly` is its corollary.
  Rebuilt, axioms `[propext, Classical.choice, Quot.sound]`.
- `RHTower.JensenQuarticXi` (new, wired after `ThetaTiltLogDensity` in `RHTower.lean`; imports only the
  transfer module and `XiCTaylorThetaTailMomentLogConvex`): `xiJensenCoeff k = k!·m(k)/(2k)!`,
  `thetaDispersion k = m(k)m(k+2)/m(k+1)² − 1 ≥ 0` (from `thetaCuspRawEvenMoment_sq_le_adjacent`),
  `thetaMomentRatio`, the chain `xiJensenCoeff_succ`, the exact identity
  `eval_jensenPoly_xi_four : (jensenPoly xiJensenCoeff 4 n).eval X = γ(n)/((b)(b+1)(b+2)(b+3)) ·
  quartic b D₀ D₁ D₂ (tX/4)` (`b = n+½`, `t = m(n+1)/m(n)`; `field_simp; ring` after expanding the
  five binomial terms and the factorial chain), and the capstone
  `hyperbolic_jensenPoly_xi_four (hn : 2000 ≤ b) (hK : D₀ b ≤ ½) (hε₁ : |D₀−D₁| b√b ≤ 1/8)
  (hε₂ : |D₀−2D₁+D₂| b² ≤ 1/5) : Hyperbolic (jensenPoly xiJensenCoeff 4 n)` (sign alternation at
  `X_i = 4y_i/t`). Built (`lake build`), axioms clean.
- `RHTower.ThetaTiltLogDensity`: imports trimmed to `OneDimBrascampLieb`, `ThetaCuspKernelLogConcavity`,
  `ThetaCuspGlobalReflectedRiccati`, `XiCTaylorThetaTailSeamJets`; built, axioms clean.
- Not built (dropped after the Holland audit): the Brascamp–Lieb integrability discharge for the tilted
  theta density and the cumulant bounds of Theorem B — these are Holland's Lemmas 4.2–5.4 and would be
  formalisation of literature, not research. The capstone's three hypotheses are therefore *not*
  discharged in Lean; the theorem is an explicit-constant certificate, conditional on the dispersion
  box, and the box is known (paper, Holland) to hold for all large `n`.
- Traps met: `Polynomial.eval_finset_sum` is deprecated (`eval_finsetSum`), but the sum evaluates via
  `Finset.sum_range_succ` + `eval_add` anyway; `simp [altPoints]` rewrites `0 < √a` into `0 < a` and
  breaks `linarith` against hypotheses stated with `√a` — abstract the root as a variable first
  (`obtain ⟨s, hs⟩ : ∃ s, s = √…`); `lake env lean` reads stale `.olean`s of a refactored dependency,
  so `lake build` the dependency before compiling a consumer; oleans in the shared tree can vanish
  under concurrent agents' builds (`PrimeArchThermalKrylovRH.olean` did) — rebuild the target with
  `lake build <module>` rather than chasing.
