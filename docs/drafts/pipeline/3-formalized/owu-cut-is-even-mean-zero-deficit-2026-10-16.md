# OWU: the real cut is exactly the even mean-zero deficit

- **ID:** owu-cut-is-even-mean-zero-deficit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU, Need "remove the real cut";
  successor of `3-formalized/owu-odd-spectral-measure-2026-10-16.md`
- **Statement:** Let `lam` be odd Weil-positive with odd Nevanlinna data `(ν, c)` of
  `aΨ(½+a)`, `z = a²`. Then for EVERY `C²` compactly supported test `f` (any parity)
  `Re W_lam(f ⋆ f̃) = ∫ Θ_f dν − c|f̂(0)|²`, with
  `Θ_f = [(1+γ²)(|f̂(√γ)|² + |f̂(−√γ)|²)/2 − |f̂(0)|²]/γ` on the critical ordinates and, for even `f`,
  `Θ_f = [|f̂(0)|² − (1+γ²)|f̂(i√(−γ))|²]/(−γ)` on the cut.
  1. (cut removal) if `W_lam ≥ 0` on all even tests with `f̂(0) = 0`, the cut measure vanishes:
     `ν{ζ ≠ 1, γ < 0} = 0`;
  2. (converse) if the cut measure vanishes, `W_lam ≥ 0` on every test with `f̂(0) = 0`;
     so even mean-zero positivity ⟺ vanishing cut mass;
  3. (extension) if the cut measure vanishes, the Weil function extends holomorphically to
     `Re s > ½`; hence odd positivity, even mean-zero positivity and `Ψ ≥ 0` on `(½,∞)` give
     `λ = Λ` and RH (square-root transfer).

## Structural contribution

The odd spectral measure showed that cut mass enters every odd test with the positive weight
`(1+γ²)|f̂(i√(−γ))|²/(−γ)`, so no odd test can remove it; the frontier asked for cut removal from
the archimedean term and the prime support. Here the cut is identified exactly: on even mean-zero
tests the same cut mass enters with the NEGATIVE weight `−(1+γ²)|f̂(i√(−γ))|²/(−γ)`, while the
critical ordinates, the centre and `ζ = 1` enter nonnegatively and the Nevanlinna constant drops
out. A two-bump even test `f_L = b(·−L) − 2b + b(·+L)` has `f̂_L(v) = (2cos(Lv) − 2) b̂(v)` on the
critical line, with `4(1 − cos Lv)² ≤ 4L²v²`, but `f̂_L(ir) = (2cosh(Lr) − 2) b̂(ir)` on the cut with
`2cosh u − 2 ≥ u²/2`. So the critical contribution is `O(L²)` and the cut contribution is
`≤ −L⁴ r⁴ (∫b)² ν(cut_r)`: positivity forces `ν(cut_r) = 0`. This is the Paley–Wiener dichotomy
between the real and the imaginary axis (Landau's "real singularities dominate") realised inside
the Weil form. Consequences:

- `{odd-positive, cut-free} = {Weil-positive on the hyperplane f̂(0) = 0}`: the modulo-constants
  cone is the cut-free part of the odd cone, and the single real parameter separating it from the
  full cone is the central value `lim_{x↓½}(x−½)Ψ(x)`;
- the OWU Need "remove the real cut" is now the Need "even mean-zero positivity", a positivity
  statement on an explicit test family, and vanishing cut mass yields the holomorphic extension
  required by the square-root Herglotz transfer.

Exact Lean theorems (`formal/GaloisForLFunctions/RHTower/`, namespace `RHTower.OddResolvent`,
wired into `RHTower.lean`):

| Module | Theorem | Content |
|---|---|---|
| `WeilCutEvenMeanZeroDeficit.lean` | `re_weilFullFunctional_eq_integral_spectralWeight_sub` | `Re W_lam(f⋆f̃) = ∫Θ_f dν − c|f̂(0)|²` for every `C²` compact test |
| same | `spectralWeight_eq_of_ne`, `spectralWeight_eq_of_pos`, `spectralWeight_eq_of_neg_of_even` | evaluation of `Θ_f` for arbitrary tests; cut value for even tests |
| same | `tendsto_spectralWeight_bdryPt`, `spectralWeight_neg_one_nonneg_of_meanZero`, `spectralWeight_neg_one_le_of_forall_pos`, `spectralWeight_nonneg_of_meanZero_of_not_cut` | the centre by continuity; nonnegativity off the cut for mean-zero tests |
| same | `integrable_spectralWeight_circleMap` | `Θ_f` is `ν`-integrable |
| same | `twoBumpTest`, `paperFT_twoBumpTest`, `norm_paperFT_twoBumpTest_ofReal`, `paperFT_twoBumpTest_I_mul`, `integral_le_expMoment` | the two-bump even mean-zero family and its transform on both axes |
| same | `spectralWeight_twoBumpTest_le_of_pos`, `spectralWeight_twoBumpTest_le_of_cut` | `Θ_{f_L} ≤ 4L²(N₀²+N₂²)` on critical ordinates, `≤ −4((2cosh(r₀L)−2)∫b)²` on the cut at distance `≥ r₀` |
| same | `measure_cutSet_eq_zero`, `cut_measure_eq_zero_of_even_meanZero_nonneg` | cut removal from even mean-zero positivity |
| same | `weilFullFunctional_nonneg_of_cut_eq_zero`, `even_meanZero_nonneg_iff_cut_eq_zero` | converse and the equivalence |
| `WeilCutFreeHolomorphicExtension.lean` | `hasDerivAt_integral_nevKernel`, `differentiableOn_cutFreeExtension` | holomorphy of `∫ (γz−1)/(z+γ) dν` off `(−∞,0]` and of `Φ(s) = g((s−½)²)/(s−½)` on `Re s > ½` |
| same | `cutFreeExtension_eq_of_im_pos`, `cutFreeExtension_eq_weilFunction`, `exists_extension_of_cut_eq_zero` | agreement with the slit continuation and the Weil function |
| same | `exists_extension_of_weilPositiveOdd_of_even_meanZero_nonneg`, `eq_vonMangoldt_and_riemannHypothesis_of_even_meanZero_nonneg` | cut removal for odd-positive weights; `λ = Λ ∧ RH` with central nonnegativity |

## Paper proof

1. (Representation.) The odd spectral formula never used oddness except for `H(½) = |f̂(0)|² = 0`;
   for a general test the `c`-term is `c·(1/2π)∫F/(w−½) = c H(½) = c|f̂(0)|²`
   (`two_line_pair` at `z₀ = ½`, `Hfn_weilTest_critical` at `t = 0`).
2. (Evaluation.) With `H(½) = |f̂(0)|²`, `H(½ ± i√γ) = |f̂(±√γ)|²`,
   `H(½ ± r) = f̂(∓ir) conj f̂(±ir)` (`= |f̂(ir)|²` for even `f`), the partial fractions
   `K_ζ = −(1/γ) g_½/2 + ((1+γ²)/(2γ)) g_{½+ρ}` give the stated weights. For `f̂(0) = 0` the
   critical weight is `≥ 0`, the central weight is the limit along `bdryPt(1/(n+1))` and is `≥ 0`,
   `Θ_f(1) = 0`; for even `f` the cut weight is `−(1+γ²)|f̂(i√(−γ))|²/(−γ) ≤ 0`.
3. (Two-bump transform.) `f̂_L(z) = (e^{izL} + e^{−izL} − 2) b̂(z)`; on the real line this is
   `2(cos(vL) − 1) b̂(v)`, on the imaginary axis `(2cosh(rL) − 2)·∫b(u)e^{−ru}du` with
   `∫b(u)e^{−ru}du ≥ ∫b` for even nonnegative `b` (symmetrise and use `cosh ≥ 1`).
4. (Bounds.) `|b̂(v)| ≤ N₀`, `v²|b̂(v)| ≤ N₂` (two integrations by parts, `norm_paperFT_le_div`),
   so `(1+v⁴)|b̂(v)|² ≤ N₀² + N₂²`; `4(1−cos(vL))² ≤ 4L²v²` by `1 − cos u ≤ min(2, u²/2)`; hence
   `Θ_{f_L} ≤ 4L²(N₀²+N₂²)` on critical ordinates and at the centre. On the cut at distance
   `r ≥ r₀`: `Θ_{f_L} ≤ −(1+γ²)(2cosh(rL)−2)²(∫b)²/(−γ) ≤ −4((2cosh(r₀L)−2)∫b)²` since
   `−γ ≤ ¼` and `cosh` is monotone.
5. (Cut removal.) With `A = 4(N₀²+N₂²)`, `K_L = 4((2cosh(r₀L)−2)∫b)²`, `m = ν(cut_{r₀})`,
   `M = ν(S¹)`: `0 ≤ ∫Θ_{f_L} dν ≤ A L² M − (A L² + K_L) m`, so `K_L m ≤ A L² M`. Since
   `2cosh u − 2 ≥ u²/2`, `K_L ≥ r₀⁴ L⁴ (∫b)²`, hence `r₀⁴(∫b)² m L² ≤ A M` for every `L ≥ 0`,
   forcing `m = 0`. The cut is the countable union of the `cut_{1/(k+1)}`.
6. (Converse.) Without cut mass `Θ_f ≥ 0` `ν`-a.e. for every mean-zero test, so `W ≥ 0`.
7. (Extension.) For `ν` supported on `{γ ≥ 0} ∪ {1}`, `k(z,ζ) = (γz−1)/(z+γ)` (`z` at `ζ = 1`)
   has `∂_z k = (1+γ²)/(z+γ)²`; around `z₀ ∉ (−∞,0]` with `ε = |Im z₀|/2` or `Re z₀/2`,
   `|z+γ| ≥ ε` and `|z+γ| ≥ γ − (|z₀|+ε)`, which bound `|k|` and `|∂_z k|` uniformly in `γ ≥ 0`;
   dominated differentiation gives holomorphy of `g(z) = ∫k dν − c` off `(−∞,0]`, and
   `Φ(s) = g((s−½)²)/(s−½)` is holomorphic on `Re s > ½`. On the upper quadrant
   `Φ = Ψ` by the Nevanlinna representation (`I·hrKernel(½−Iz) = k(z,·)`), hence `Φ = Ψ = weilFunction`
   on `Re s > 1` by the identity theorem on the half-plane.

## Gates
- [x] 0 → 1  well-posed, source-pure
- [x] 1 → 2  paper proof above
- [x] 2 → 3  Lean modules audited individually with `lake --old env lean`, built with
  `lake build --old`, axioms of twelve theorems exactly `[propext, Classical.choice, Quot.sound]`

## Conjecture ledger
1. "Cut ≤ critical" from even mean-zero positivity does not force vanishing cut mass: refuted as a
   worry — scaling the test width makes the cut contribution grow like `L⁴` (cosh) while the
   critical contribution stays `O(L²)` (Fourier decay on the real line). Used.
2. Wide tests `f(x/T)` would need `T`-explicit real-line Fourier decay; replaced by two translated
   bumps, whose real-line transform is `L`-uniformly bounded by `2|b̂|`.
3. `convert` on `HasDerivAt.div` for `ℂ` leaves instance-mismatch goals; use `congr_deriv`.

## Validation
- `lake --old env lean` on both modules: no output.
- `lake build --old` on both modules: built.
- Axiom audit (scratch file, removed): twelve theorems, each `[propext, Classical.choice, Quot.sound]`.
- `scripts/formal_tools.py lint`: passed (pre-existing large-file warnings only).
- Umbrella: two imports appended to `RHTower.lean`; scratch files removed.

## Log
- 2026-10-16 — created; paper proof; two Lean modules compiled, audited, wired; moved to 3-formalized
