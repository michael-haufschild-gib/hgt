# Fejér–Riesz fails for mixed exponents: the unfolding obstruction

**Stage:** 3 — formalized in Lean 4 (unconditional; axioms `[propext, Classical.choice, Quot.sound]`).

Answers the open question of `several-conjugate-pairs-no-joint-profile.md`: is every nonnegative real
exponential polynomial with mixed real and imaginary exponents a sum of Hermitian squares
`∑ G_l G_l^*`? **No.** And the obstruction is exact, elementary, and explains both model cases.

## The unfolding

Write `λ = Re λ + i Im λ`. The character `t ↦ e^{λ t}` is the diagonal restriction of

```
  (t, u) ↦ e^{(Re λ) t} e^{i (Im λ) u} ,
```

which separates growth from phase. The **unfolding** of an exponential polynomial is the
corresponding two-variable function; the polynomial is recovered at `u = t`.

The unfolding is well defined — it depends on the function, not on the presentation. Characters with
distinct complex exponents are linearly independent (`exp_coeff_eq_zero`, proved by iterated
differentiation at the origin followed by Lagrange interpolation), so every relation among characters
descends to the same relation among unfolded characters (`unfold_eq_zero_of_eq_zero`).

## The obstruction

**Theorem.** If `f` is a sum of Hermitian squares of exponential polynomials, its unfolding is
nonnegative on all of `ℝ × ℝ`, not merely on the diagonal.
`unfoldSum_nonneg_of_isHermitianSOS`.

The proof is a phase shift. A Hermitian square is `∑_{j,k} v_j \bar v_k e^{(μ_j + \bar μ_k)t}`, and
the exponent `μ_j + \bar μ_k` has imaginary part `Im μ_j − Im μ_k`. So replacing each coefficient
`v_j` by `v_j e^{i (Im μ_j) φ}` multiplies the `λ`-term by `e^{i (Im λ) φ}` — exactly the unfolding —
and leaves a sum of squared moduli. **Any sum-of-squares certificate decouples growth from phase.**

## The counterexample

For `0 < λ < 1`, `γ > 0`, and `κ` with `λ cosh(κπ/(2γ)) ≥ 1` (such `κ` exists — `exists_kappa`):

```
  f(t) = 2λ cosh(κ (t − π/γ)) − 2 cos(γ t)  ≥ 0   on ℝ      (counterexample_nonneg)
  unfolding:  2λ cosh(κ (t − π/γ)) − 2 cos(γ u)             (cex_unfold)
  at (t,u) = (π/γ, 0):  2λ − 2 < 0                          (cex_unfold_neg_of_lt_one)
```

Hence `f` is **not** a sum of Hermitian squares (`not_isHermitianSOS_of_lt_one`).

The mechanism is geometric: the dip of `2λ cosh` is placed exactly halfway between two peaks of the
cosine, and made narrow enough that every point where `cos(γ t) > 0` lies outside it. On the diagonal
the dip is invisible; once the phase is freed it lines up with a peak.

Note the exponents here are `±κ, ±iγ` — commensurability plays no role, and no Hamel basis is needed.

## Why the model cases do factor

Both quoted examples have nonnegative unfoldings, so the obstruction is vacuous for them:

| function | unfolding | |
|---|---|---|
| `2e^{βt}(1 − cos γt)` | `2e^{βt}(1 − cos γu) ≥ 0` | `ext_unfold`, `ext_unfold_nonneg` |
| `cosh(at) − cos(bt)` | `cosh(at) − cos(bu) ≥ 0` | `cex_unfold_nonneg_of_one_le` at `λ = 1` |

and the first is exhibited as an explicit Hermitian square,
`2e^{βt}(1 − cos γt) = |{-i}(e^{(β+iγ)t/2} − e^{(β−iγ)t/2})|²` (`ext_isHermitianSOS`).

## The threshold

The witness family is sharp. `2λ cosh(κ(t − π/γ)) − 2 cos(γ u)` is nonnegative on the **plane**
exactly when `λ ≥ 1` (`cex_unfold_nonneg_of_one_le`, `cex_unfold_neg_of_lt_one`), whereas
nonnegativity on the **diagonal** only needs `λ cosh(κπ/(2γ)) ≥ 1`. The gap between those two
conditions is the gap between the Hermitian-square cone and the nonnegative cone, in one parameter.

## Consequence for the Beurling programme

For one conjugate pair the previous card characterised `R(t) ≥ 2e^{βt} cos(γ t)` by an arc criterion.
Unfolding that comparison gives `R(t) ≥ 2e^{βt} cos(γ u)`, i.e. `R(t) ≥ 2e^{βt}` for all `t` — the
**phase-blind** condition. So:

> the sum-of-Hermitian-squares relaxation of Beurling realizability is exactly the phase-blind
> relaxation, and its error is exactly the peak-versus-global gap already characterised.

Sums of squares are therefore the wrong certificate class for realizability with complex zeros: they
cannot see the peak lattice at all. The correct certificates remain the per-hump exponential profiles
of `LogConcaveSeparation`.

## Modules

```
formal/GaloisForLFunctions/HTGeometry/ComplexExpUnfolding.lean
formal/GaloisForLFunctions/HTGeometry/HermitianSOSUnfolding.lean
formal/GaloisForLFunctions/HTGeometry/HermitianSOSCounterexample.lean
formal/GaloisForLFunctions/HTGeometry/HermitianSOSExtremal.lean
```

## Open

* Is nonnegativity of the unfolding also **sufficient**? The unfolding of `f` is a signomial in one
  real and one angular variable, nonnegative on `ℝ_{>0} × 𝕋`; a Fejér–Riesz theorem there would give
  a converse. Two variables is exactly where psd = sos can fail, so this is not routine.
* The purely real-exponent analogue: for exponents spanning a ℚ-space of dimension `d ≥ 2` the same
  argument applies with ℚ-linear deformations of the exponents in place of the phase shift, which
  needs a Hamel basis and is not formalized here.
