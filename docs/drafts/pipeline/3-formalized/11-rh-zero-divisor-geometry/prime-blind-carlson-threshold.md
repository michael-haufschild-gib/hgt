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
1. **Degree-one exact criticality.** Stirling gives `|Ξ(t)|² ≍ |t|^{7/2}|ζ(½+it)|² e^{−π|t|/2}`, so the zero-killing factor `Ξ²` decays exactly at the Carlson threshold of the node set `log ℕ`. The coincidence is `Γ_ℝ`'s decay `e^{−π|t|/4}` per factor against the divergence of `Σ1/n`, which is the pole of `ζ` at `1`.
2. **C-PIN lives on the threshold.** Every C-PIN multiplier satisfies `∫ |t|^{7/2}|ζ(½+it)|² |h(t)| dt = ∞`. In particular `h` cannot decay like `|t|^{−9/2−ε}`. Prime-blindness is possible only because of the polynomial prefactor `|t|^{7/2}|ζ|²`, i.e. the pole factor `s(s−1)` and the mean square of `ζ`. This is the structural reason why the corpus and Johns find "no slack": the certificate sits exactly where prime-blind positivity first becomes possible.
3. **Magic functions.** Johns' limit `F_∞ = Ξ²P_∞(t²)`, if it vanishes at all prime powers, must have `∫|F_∞| e^{(π/2)|t|} = ∞`. Any growth hypothesis that bounds `P_∞` too strongly is inconsistent.
4. **Higher degree.** For an L-function of degree `d ≥ 2`, `Ξ_L²` decays like `e^{−dπ|t|/2}`. Prime-blind multipliers must then grow at least like `e^{(d−1)π|t|/2}` up to polynomial factors: tempered C-PIN is a degree-one phenomenon.

## Lean
Module `RHTower/PrimeBlindCarlsonThreshold` (namespace `RHTower.PrimeBlindCarlson`), wired after `WeilNullPotentialSignPartRigidity`. Axioms `[propext, Classical.choice, Quot.sound]`; zero messages.

| Claim | Declaration |
|-|-|
| Jensen bound for nonzero zeros of a bounded analytic function on the disc | `sum_log_le_of_jensen` |
| Disc rigidity, zeros at `(n−1)/(n+1)`, `Σ1/n = ∞` | `eqOn_zero_of_discNode_zeros` |
| Half-plane rigidity, zeros at `n ∈ N` | `eqOn_zero_of_halfPlane_zeros` |
| `G` analytic and bounded on `Re ζ > 0` | `analyticOnNhd_logFourier`, `norm_logFourier_le` |
| **Main** | `fourier_eq_zero_of_dirichletMoment_eq_zero`, `fourier_eq_zero_of_primeMoment_eq_zero` |

## Novelty
The analytic core is classical: Carlson's theorem in Blaschke/Jensen form. The new content is the identification of `Ξ²`'s decay with the Carlson threshold of `log ℕ`, and its consequences: the growth law for C-PIN multipliers and magic functions, and degree-one criticality. Neither the corpus nor Johns (2026) states it. External search found no source pairing the Weil-certificate decay with the Carlson / Blaschke threshold.

## Polynomial room (loop row 548)
**Theorem** (`fourier_eq_zero_of_integerMoment_eq_zero_room`). Suppose `w` is blind at every integer `n ≥ 2`. Then already `∫|w(t)| e^{(π/2)|t|}(1+|t|)^{−a} dt < ∞` with `0 ≤ a < 2` forces `ŵ ≡ 0`.

**Proof.**
- The room gives `|G(ζ)| ≤ B e^{π/2} K (π/2 − |arg ζ|)^{−a}` (`norm_logFourier_le_room`).
- The Cayley image satisfies `π/2 − |arg cayley(z)| ≥ (1 − |z|)/4` (`pi_div_two_sub_abs_arg_cayley_ge`).
- The zero sum over `2 ≤ n ≤ X` telescopes exactly: `Σ log((n+1)/(n−1)) = log(X(X+1)/2)` (`sum_log_inv_discNode`).
- Jensen at radius `(X−1)/(X+1)` then gives `(2 − a) log(X+1) ≤ O(1)` (`eqOn_zero_of_discNode_zeros_room`).

**Reading.**
- For `w = Ξ²h`: `∫ |t|^{3/2+ε}|ζ(½+it)|²|h(t)| dt = ∞` for every `ε > 0`. A C-PIN multiplier cannot decay faster than `|t|^{−5/2}` (up to the mean of `|ζ|²`), whereas `Ξ²` itself leaves `9/2` of polynomial room.
- Blindness at the prime powers alone (Johns' magic functions) carries no polynomial constraint: `Σ_{p≤X}1/p ~ log log X` gives zero Jensen density.
- So the corpus's all-integer C-PIN is strictly more constrained than Johns' prime-power certificates. That the room `2` is sharp is not proved; it would follow from a prime-blind weight with room `a > 2`, e.g. a C-PIN multiplier decaying like `|t|^{−5/2+ε}`.

## Density form (loop row 549)
**Theorem** (`fourier_eq_zero_of_dirichletMoment_eq_zero_density`, disc form `eqOn_zero_of_discNode_zeros_density`). Let `N` have logarithmic density `κ`, in the form `Σ_{n∈N, 2≤n≤X} 1/(n+1) ≥ κ log X − C₀`. Blindness on `N` with room `a < 2κ` forces `ŵ ≡ 0`. Two corollaries:
- all integers: `κ = 1`, room `2` (via `Σ_{2≤n≤X} 1/(n+1) ≥ log((X+2)/3)`);
- prime powers: `κ = 0`, no polynomial room needed.

**Reading: the pole factor makes the room.** Stirling gives `|Ξ(t)|² ≍ |t|^{7/2}|ζ(½+it)|² e^{−π|t|/2}`. The factor `|s(s−1)|² ~ t⁴` from the pole of ζ at `1` (and of `Γ` at `0`) lifts the room from `½` to `9/2 ≥ 2`. So bounded C-PIN multipliers are admissible for ζ.

For an even primitive character `χ mod q` (entire L-function), `|Ξ_χ(t)|² ≍ |t|^{−1/2}|L(½+it,χ)|² e^{−π|t|/2}` has room `½`. Blindness at the integers coprime to `q` has density `κ = φ(q)/q`. For `φ(q)/q > 1/4`, every prime-blind zero-killing certificate for `L(s,χ)` therefore needs a multiplier growing at least like `|t|^{2φ(q)/q − 1/2}`.

This is consistent with large-conductor L-data being non-critical: there `lam = 0` is already Weil-positive. The coprime density and the Stirling exponents are standard and are not formalized here.

## Log
- 2026-10-07 (loop row 547): proved and formalized.
- 2026-10-07 (loop row 548): polynomial-room law added to the same module; analyticity lemmas generalized to the room weight `e^{(π/2)|t|}(1+|t|)^{−a}`.
- 2026-10-07 (loop row 549): density form (room `2κ`); the all-integer law re-derived as a corollary; telescoping replaced by `log_le_sum_inv_succ`.
