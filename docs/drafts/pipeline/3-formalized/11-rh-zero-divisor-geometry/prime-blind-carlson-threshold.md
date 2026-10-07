# Prime-blind measures and the Carlson threshold of log ℕ

- **ID:** prime-blind-carlson-threshold
- **Stage:** 3-formalized (Lean, unconditional, standard axioms)
- **Type:** THEOREM (Lean) + structural reading
- **Context:** the dual certificate of Weil-cone uniqueness, C-PIN. It is a weight `Ξ²h`, with `h > 0`, whose Dirichlet moments `∫ Ξ²h n^{−it} dt` vanish for all `n ≥ 2`. Johns' (2026) magic functions `lim_J Ξ²P_J(t²)`, which vanish at all prime powers, are the analogue in the positive-solution setting.

## Statement
Let `w : ℝ → ℂ` be measurable with `∫ |w(t)| e^{(π/2)|t|} dt < ∞`, and let `N ⊆ [2, ∞)` be a set of integers with `Σ_{n∈N} 1/n = ∞`, for example the primes. If `∫ w(t) n^{−it} dt = 0` for every `n ∈ N`, then `∫ w(t) e^{−itx} dt = 0` for every real `x`, so `w = 0`.

The constant `π/2` is sharp. For `b < π/2` put `c = π tan b`. Then `H(x) = sin(π eˣ) e^{−c eˣ}` is bounded and analytic in `|Im x| < b` and vanishes at every `log n`. Its inverse transform is a nonzero prime-blind function that decays at every rate `< b`. (This example is classical and not formalized.)

## Proof
- `G(ζ) = ∫ w(t) e^{−it log ζ} dt` satisfies `|e^{−it log ζ}| = e^{t arg ζ} ≤ e^{(π/2)|t|}` on `Re ζ > 0`. So it is bounded there by `∫|w|e^{(π/2)|t|}`, and it is analytic by dominated differentiation; on small balls, `|arg|` is bounded away from `π/2`.
- `G(n)` is the `n`-th Dirichlet moment, and `G(eˣ)` is the Fourier transform at `x`.
- The Cayley map turns `G` into a bounded analytic function on the disc vanishing at `(n−1)/(n+1)`.
- Jensen's formula (mathlib) bounds `Σ log(1/|a|)` over the zeros of a bounded analytic function that is not identically zero. Here `log((n+1)/(n−1)) ≥ 1/n`, so the zero sum diverges and `G ≡ 0`.

## Reading
1. **Degree-one exact criticality.** Stirling gives `|Ξ(t)|² ≍ |t|^{7/2}|ζ(½+it)|² e^{−π|t|/2}`, so the zero-killing factor `Ξ²` decays exactly at the Carlson rate of the node set `log ℕ`. The coincidence is `Γ_ℝ`'s decay `e^{−π|t|/4}` per factor against the divergence of `Σ1/n`, which is the pole of `ζ` at `1`.
2. **C-PIN multipliers are not tempered (corrected, row 553).** A C-PIN multiplier `h` (blind at every integer `n ≥ 2`) satisfies `∫ |t|^{7/2}|ζ(½+it)|²|h(t)| e^{−K√|t|} dt = ∞` for every `K`. So `h` is not polynomially bounded, and not even `O(e^{K√|t|})` in mean. The polynomial prefactor `|t|^{7/2}|ζ|²` of `Ξ²` does **not** make room: the earlier reading ("room `9/2`, bounded C-PIN admissible") was an artifact of a max-modulus Jensen bound.
3. **Magic functions.** Johns' limit `F_∞ = Ξ²P_∞(t²)`, if it vanishes at all prime powers, must have `∫|F_∞| e^{(π/2)|t|}(1+|t|)^{−a} = ∞` for every `a`. No polynomial bound on `P_∞` is consistent with full prime-power blindness.
4. **Higher degree.** For an L-function of degree `d ≥ 2`, `Ξ_L²` decays like `e^{−dπ|t|/2}`. Prime-blind multipliers must then grow at least like `e^{(d−1)π|t|/2}` times a non-tempered factor.

## Lean
Module `RHTower/PrimeBlindCarlsonThreshold` (namespace `RHTower.PrimeBlindCarlson`), wired after `WeilNullPotentialSignPartRigidity`. Axioms `[propext, Classical.choice, Quot.sound]`; zero messages.

| Claim | Declaration |
|-|-|
| Jensen bound from a circle-average bound; from a bound on the circle | `sum_log_le_of_circleAverage_le`, `sum_log_le_of_jensen` |
| Disc rigidity, zeros at `(n−1)/(n+1)`, `Σ1/n = ∞`, bounded | `eqOn_zero_of_discNode_zeros` |
| Half-plane rigidity, zeros at `n ∈ N`, bounded | `eqOn_zero_of_halfPlane_zeros` |
| `G` analytic under any weight dominating `(1+|t|)e^{(π/2−c)|t|}` for all `c > 0` | `DominatesSubcritical`, `analyticOnNhd_logFourier` |
| Rate `π/2`, divergent node set | `fourier_eq_zero_of_dirichletMoment_eq_zero`, `fourier_eq_zero_of_primeMoment_eq_zero` |
| Any polynomial room, divergent node set (primes) | `fourier_eq_zero_of_dirichletMoment_eq_zero_room`, `fourier_eq_zero_of_primeMoment_eq_zero_room` |
| `avg_{|z|=R} 1/|1−z| ≤ log(1/(1−R)) + 4` | `circleAverage_inv_norm_one_sub_le` |
| Disc rigidity with `avg log|f| ≤ B + D log(1/(1−R))`, density `κ`, `D < 2κ` | `eqOn_zero_of_discNode_zeros_density` |
| Room `e^{K√|t|}`, log-dense node set; all integers | `fourier_eq_zero_of_dirichletMoment_eq_zero_density`, `fourier_eq_zero_of_integerMoment_eq_zero_room` |

## Novelty
The analytic core is classical: the Blaschke condition (rate `π/2`, any polynomial room after division by `(ζ+1)^{⌈a⌉}`) and Carlson's theorem (room `e^{K√|t|}` at log-dense nodes). The new content is the identification of `Ξ²`'s decay with the Carlson rate of `log ℕ`, and its consequence that dual certificates of Weil-cone uniqueness are not tempered. External search found no source pairing the Weil-certificate decay with the Carlson / Blaschke threshold.

## Room beyond the rate (loop rows 548, 549, corrected in row 553)
**Correction.** Rows 548–549 (MUST-813/814) proved vanishing only for polynomial room `a < 2κ`, and read the bound `2κ` as a threshold ("integers cost Jensen density 2", "primes carry no polynomial constraint", "ζ's pole factor gives room `9/2`", "bounded C-PIN admissible", "entire degree-one L-data need growing multipliers when `φ(q)/q > 1/4`"). That bound came from applying Jensen with the maximum of `|f|` on the circle: under the plain Cayley map the angular growth `(π/2 − |arg ζ|)^{−a}` blows up along the whole circle. All these readings are withdrawn. The true picture:

**Theorem A** (`fourier_eq_zero_of_dirichletMoment_eq_zero_room`). For every `a ≥ 0` and every node set with `Σ1/n = ∞` (primes included), `∫|w|e^{(π/2)|t|}(1+|t|)^{−a} < ∞` and blindness force `ŵ ≡ 0`.
*Proof.* On `Re ζ ≥ 1`, `π/2 − |arg ζ| ≥ Re ζ/|ζ| ≥ 1/|ζ|`, so `|G(ξ+1)| ≤ C|ξ+1|^a`. Then `G(ξ+1)/(ξ+1)^{⌈a⌉}` is bounded on `Re ξ > 0` and vanishes at `n − 1`; the Blaschke condition fails; the identity theorem extends `G ≡ 0` from `Re ζ > 1`.

**Theorem B** (`fourier_eq_zero_of_dirichletMoment_eq_zero_density`, `fourier_eq_zero_of_integerMoment_eq_zero_room`). For every `K` and every node set of logarithmic density `κ > 0` (all integers included), `∫|w|e^{(π/2)|t| − K√|t|} < ∞` and blindness force `ŵ ≡ 0`.
*Proof.* `e^{K√s − δs} ≤ e^{K²/(4δ)}` gives `|G(ζ)| ≤ B e^{K²/(4(π/2−|arg ζ|))}`. Put `ζ = m + (1+z)/(1−z)` with `m > K²/(4κ)`; then `π/2 − |arg ζ| ≥ m/|ζ|` and `|ζ| ≤ m + 2/|1−z|`, so `log|f(z)| ≤ C + (K²/(2m))/|1−z|`. The circle average of `1/|1−z|` is `≤ log(1/(1−R)) + 4` (Jordan's inequality and `∫dθ/(ε+θ)`), so Jensen's formula with averages gives `(2κ − K²/(2m)) log X ≤ O(1)` at radius `(X−1)/(X+1)`. Logarithmic density survives the shift (`density_shift`).

**Sharpness (paper, not formalized).** `F(ζ) = sin(πζ) e^{−πcζ log ζ}` is analytic on `Re ζ > 0`, vanishes at every integer, and satisfies `log|F(re^{iφ})| ≤ πr[(1+cφ)sin φ − c cos φ log r]`. Its maximum over `r` at angle `π/2 − δ` is `exp(C/δ)`. The inverse transform `w` of `F(eˣ)` is blind at every integer, nonzero, and has `|w(t)| ≤ exp(−(π/2)|t| + C|t|/log|t|)`. So the integer threshold of the subexponential factor `ρ(t)` lies between `√t` (Theorem B) and `t/log t`.

**Conjecture C553 (open, paper).** Blindness at log-dense nodes with `|w(t)| ≤ e^{−(π/2)|t| + ρ(|t|)}` forces `ŵ ≡ 0` iff `∫^∞ ρ(t) t^{−2} dt < ∞` (for regular `ρ`). The vanishing half would follow from a Levinson–Sjöberg log-log bound near the imaginary axis, which applies when `∫_0 log ρ*(δ) dδ < ∞`, with `ρ*` the Legendre transform. The construction above sits exactly at the divergent side `ρ = t/log t`.

**Duality remark.** By Theorem B, `{n^{−it} : n ≥ 2}` is complete in every weighted space dual to the room `e^{K√|t|}`, so the constant `1` is a limit of Dirichlet polynomials without constant term there. A separating functional for C-PIN in that topology is therefore trivial (`φ ≡ 1`). Meaningful annihilators (MUST-809) live only in the almost-periodic setting, where mean value zero excludes `1`.

## Log
- 2026-10-07 (loop row 547): proved and formalized.
- 2026-10-07 (loop row 548): polynomial-room law added to the same module; analyticity lemmas generalized to the room weight `e^{(π/2)|t|}(1+|t|)^{−a}`.
- 2026-10-07 (loop row 549): density form (room `2κ`); the all-integer law re-derived as a corollary; telescoping replaced by `log_le_sum_inv_succ`.
- 2026-10-07 (loop row 553): correction. The `a < 2κ` thresholds were artifacts of the max-modulus Jensen bound. Replaced by Theorem A (any polynomial room, every divergent node set, via a shifted half-plane and division) and Theorem B (room `e^{K√|t|}` at log-dense nodes, via circle averages; Carlson's theorem). Sharpness construction at `t/log t` and conjecture C553 recorded. Declarations removed: `pi_div_two_sub_abs_arg_cayley_ge`, `eqOn_zero_of_discNode_zeros_room`, `norm_logFourier_comp_cayley_le`, `abs_mul_exp_le_roomWeight_mul`. `sum_log_inv_discNode` (cited in MUST-813) never existed in the final module.
