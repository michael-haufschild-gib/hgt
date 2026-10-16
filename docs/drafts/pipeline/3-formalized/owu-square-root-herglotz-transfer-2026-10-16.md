# OWU: Nevanlinna measure of the odd Weil function and the square-root Herglotz transfer

- **ID:** owu-sqrt-herglotz-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU
- **Statement:** For every odd-positive weight system the squared-variable Weil function
  `g(z) = a Ψ(½ + a)`, `z = a²`, is the Nevanlinna transform of a positive finite circle measure
  with no mass below ordinate `−¼` (critical ordinates, real cut, linear term only). If the Weil
  function extends holomorphically to `Re s > ½` and is nonnegative on the real half-line
  `s > ½`, it is Herglotz there, hence `lam = Λ` and RH.

## Structural contribution

Route OWU listed two needs after the slit continuation: remove the real cut `(½, 1]`, then prove
odd-only uniqueness `lam = Λ`, previously routed through the Riemann-kernel pairing
`W_lam(Φ′ ⋆ Φ̃′) = 0`, i.e. an odd `Ξ`-divisible prime-blind family. That family is obstructed by
the constant mode: every nonnegative combination of shifted-Gamma densities `|Q_j|²` is positive at
`r = 0`, while odd densities vanish there.

This card removes the second need. Uniqueness in the odd cone is reduced to the proved full-cone
uniqueness through the Herglotz bridge, by a pure complex-analysis law: a function with the
squared-variable sign law `Im(a F(a)) ≥ 0` on the first quadrant, holomorphic on `Re a > 0`, real
on `(0, ∞)` and nonnegative there, is a Carathéodory function of `a` (`Re F ≥ 0` on `Re a > 0`).
The odd cone's weakness, "dividing by the odd spectral factor loses positivity", is thus exactly
located: positivity survives division by `a` once the real-axis data is nonnegative.

Exact Lean theorems (all under `formal/GaloisForLFunctions/RHTower/`, wired into `RHTower.lean`):

| Module | Theorem | Content |
|---|---|---|
| `HerglotzRieszUnsymmetrized.lean` | `AtomDomination.exists_hrKernel_representation` | `Re Φ ≥ 0` on `Re s > ½`, no symmetry: `Φ = ∫ (ζ + w)/(ζ − w) dν + ic`, `Re Φ = ∫ P dν` |
| same | `AtomDomination.measure_ordinate_open_eq_zero_of_poisson` | Poisson support law for an unsymmetrised representation |
| `SquareRootNevanlinnaTransfer.lean` | `AtomDomination.re_nonneg_of_sqrt_sign_law` | squared-variable sign law + real nonnegativity ⟹ Carathéodory |
| `OddWeilHerglotzTransfer.lean` | `OddResolvent.exists_nevanlinna_measure_of_weilPositiveOdd` | unconditional Nevanlinna measure of the slit continuation, support `{γ ≥ −¼} ∪ {ζ = 1}` |
| same | `OddResolvent.re_nonneg_of_weilPositiveOdd_of_extension` | odd-positive + cut-free extension + `Ψ ≥ 0` on `(½, ∞)` ⟹ `Re Ψ ≥ 0` on `Re s > ½` |
| same | `OddResolvent.eq_vonMangoldt_and_riemannHypothesis_of_weilPositiveOdd_of_extension` | the same hypotheses ⟹ `lam = Λ` on `n ≥ 2` and RH |
| same | `OddResolvent.exists_re_neg_of_weilPositiveOdd_of_ne_vonMangoldt` | every odd fake with a cut-free extension is negative somewhere on `(½, ∞)` |

Residual open inputs for OWU: (i) cut removal; (ii) `Ψ ≥ 0` on `(½, ∞)`, equivalently the central
nonnegativity `lim_{x↓0} x Ψ(½ + x) ≥ 0` (the Nevanlinna constant is invisible to the odd quadratic
form). The pairing `W_lam(Φ′) = 0` and any odd blind family are no longer needed.

## Paper proof

Notation. `lam` odd-positive, `Ψ₀` the slit continuation
(`OddWeilPickContinuation.exists_weilFunction_slit_continuation`): holomorphic on `Re s > ½` minus
`(½, 1]`, equal to `weilFunction lam` on `Re s > 1`, with `Im s · Im((s − ½)Ψ₀(s)) ≥ 0` for
`Im s ≠ 0`. Put `F(a) = Ψ₀(½ + a)`.

1. (Square-root chart.) For `Re s > ½` put `z = i(s − ½)` (upper half plane) and `a = z^{1/2}`
   (principal branch), so `a ∈ Q₁ = {Re a > 0, Im a > 0}` and `a² = z`
   (`sqrtQ_mem_quadrant`, `sqrtQ_pow_two`, `sqrtQ_sq`). The chart `Φ(s) = −i a F(a)`
   (`oddChart`) is holomorphic on `Re s > ½` with `Re Φ(s) = Im(a F(a)) ≥ 0`.
2. (Unsymmetrised Herglotz–Riesz representation.) `exists_poissonRepresentation_halfPlane` gives a
   finite measure `ν` with `∫ P(discPt s, e^{iθ}) dν = Re Φ(s)`. The kernel integral
   `s ↦ ∫ (e^{iθ} + w)/(e^{iθ} − w) dν` is holomorphic (dominated differentiation, derivative bound
   `2/ε²`), its real part is the Poisson integral, so `Φ − (kernel integral)` is an imaginary
   constant: `Φ(s) = ∫ K(s, e^{iθ}) dν + ic`. With `γ = circleOrd ζ`,
   `K(s, ζ) = (1 + γ²)/(s − ½ − iγ) − iγ` whenever both denominators are nonzero
   (`hrKernel_eq_of_ne`), so in the variable `z`
   `g(z) := a F(a) = ∫ k(z, ζ) dν − c`, `k(z, ζ) = (γz − 1)/(z + γ)` for `ζ ≠ 1`, `k(z, 1) = z`
   (`I_mul_hrKernel_eq`, `I_mul_hrKernel_one`): the Nevanlinna representation with `t = −γ`.
3. (Poisson support law.) If `Re Φ(s) → 0` as `s → ½ + it` inside the half-plane for all `t` in
   an open `U`, then `ν{ζ ≠ 1, γ ∈ U} = 0`: the Poisson kernel at `½ + ε + it` is at least
   `1/(2ε)` on `|γ − t| ≤ ε`, so `ν` of that arc is at most `2ε Re Φ(½ + ε + it)`
   (`measure_ordinate_ball_le_of_poisson`); uniform smallness on compact subintervals
   (`exists_uniform_re_le`) and a covering by `O((b − a)/ε)` arcs finish.
4. (Unconditional support.) `g` is holomorphic and real on `z > ¼` (`s = ½ + √z > 1`, real
   Dirichlet series, `weilFunction_conj`), so `Re Φ → 0` at `½ + it`, `t < −¼`, and
   `ν{ζ ≠ 1, γ < −¼} = 0`.
5. (Cut-free case.) Let `Ψ` be holomorphic on `Re s > ½` with `Ψ = weilFunction` on `Re s > 1`.
   The identity theorem on `Q₁` transfers the sign law from the slit continuation to `Ψ`;
   `herglotz_conj` gives `Ψ(s̄) = conj Ψ(s)`, so `Ψ` is real on `(½, ∞)`. Now `g` is holomorphic
   and real on `(0, ∞)`, and step 3 gives `ν{ζ ≠ 1, γ < 0} = 0`.
6. (Boundary evaluation.) For `x₀ > 0` and `ζ` in the support `{γ ≥ 0} ∪ {1}`,
   `K(½ + ε − ix₀, ζ) = (1 − iγ(ε − ix₀))/(ε − i(x₀ + γ))` is bounded by `x₀ + 1 + 1/x₀` for
   `0 ≤ ε ≤ 1` (`norm_hrKernel_le_of_ordinate_nonneg`, `norm_hrKernel_one_le`), and the support
   avoids `discPt(½ − ix₀) = bdryPt(−x₀)` (`ne_discPt_of_ordinate_nonneg`). Dominated
   convergence along `½ + 1/(n+1) − ix₀` and continuity of `g` at `x₀` give
   `g(x₀) = ∫ k(x₀, ζ) dν − c`.
7. (Kernel positivity.) For `a = x + iy`, `x > 0`, `0 < x₀ ≤ |a|²`, `γ ≥ 0`:
   `(k(a², ζ) − k(x₀, ζ))/a = (1 + γ²)(a² − x₀)/(a (a² + γ)(x₀ + γ))` and
   `Re[(a² − x₀) ā (ā² + γ)] = x[(|a|² + γ)(|a|² − x₀) + 4 x₀ y²] ≥ 0`
   (`re_kernel_diff_div_nonneg`); for `ζ = 1`, `Re[(a² − x₀)/a] = x(|a|² − x₀)/|a|² ≥ 0`
   (`re_sq_sub_div_nonneg`).
8. (Transfer.) With `x₀ = |a|²`:
   `Re F(a) = Re[g(a²)/a] = g(x₀) Re(1/a) + ∫ Re[(k(a², ζ) − k(x₀, ζ))/a] dν ≥ 0`
   since `g(x₀) = √x₀ Ψ(½ + √x₀) ≥ 0`. Conjugation gives `Q₄`; the real axis is the hypothesis
   (`re_nonneg_of_sqrt_sign_law`).
9. (Conclusion.) `weilPositiveFull_of_herglotz` (absolute convergence on `Re s > 1` from the odd
   cone) gives `WeilPositiveFull lam`; `weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`
   gives `lam = Λ` and RH.

## Gates
- [x] 0 → 1  well-posed, source-pure (Lean corpus only)
- [x] 1 → 2  paper proof above, dependency-closed on corpus theorems
- [x] 2 → 3  Lean theorems listed above; each module audited individually with
  `lake --old env lean` and built with `lake build --old <module>`; axiom audit of all seven
  theorems reported exactly `[propext, Classical.choice, Quot.sound]`

## Conjecture ledger
1. Odd `Ξ`-divisible blind family from shifted Gammas: impossible, every nonneg combination of
   `|Q_j|²` is positive at `r = 0` (constant mode). Not pursued.
2. Cut removal from positivity alone: impossible, the cut enters every odd test as
   `+∫|f̂(ic)|² dσ_cut`, invisible to positivity. Needs arithmetic input; open.
3. Central nonnegativity `g(0⁺) ≥ 0` from positivity alone: not available, the constant of the
   Nevanlinna representation is invisible to the quadratic form. Open.
4. Symmetrising the chart to reuse the symmetric Herglotz–Riesz machinery: rejected, the
   conjugation `s ↦ s̄` corresponds to the diagonal reflection `a ↦ i ā`, which is not a symmetry
   of the odd data, and `Φ(s) + conj Φ(s̄)` loses the critical-line information.
5. Transfer odd → full through the square-root variable: proved (steps 1–8).

## Validation
- `lake --old env lean` on each of the three modules: no output.
- `lake build --old` on each module: built, no warnings.
- Axiom audit (scratch file, removed): seven theorems, each `[propext, Classical.choice, Quot.sound]`.
- `scripts/formal_tools.py lint`: the three modules are reachable from `RHTower`; remaining lint
  errors name eight untracked modules of other agents (`CHMDComplexWeilForm`, `CHMDPrimeRowBound`,
  `EvenSectorHermitianScalarization`, `PaperTheta*`, `HTGeometry.Even*`), untouched here;
  pre-existing large-file warnings only.
- `git diff --check`: no whitespace issues in the new files.
- Umbrella: three imports appended to `RHTower.lean` (lines 27350–27352), verified by grep.
- Scratch probes and the axiom file removed.

## Log
- 2026-10-16 — created; paper proof; three Lean modules compiled, audited, wired; moved to 3-formalized
