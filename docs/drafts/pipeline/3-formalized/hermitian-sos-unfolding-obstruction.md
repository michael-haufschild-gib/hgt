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

## Several pairs: the certificate class collapses to the per-pair relaxation

For several conjugate pairs the unfolding uses a single phase variable, so a priori only the coupled
phases are freed.  **Bohr recurrence removes the coupling**: a finite family of characters returns
simultaneously to `1` at arbitrarily large times, whatever the frequencies — commensurable or not
(`exists_large_simultaneous_almostPeriod`).  Hence

> `R(t) − ∑_j 2 e^{β_j t} cos(γ_j t)` is a sum of Hermitian squares  ⟹  `R(t) ≥ ∑_j 2 e^{β_j t}`,

`phaseBlind_of_unfold_nonneg`, `multiPair_phaseBlind_of_isHermitianSOS`.  With all pairs on the
imaginary axis this reads `R(t) ≥ 2r` (`multiPair_const_bound`).

That right-hand side is **exactly the per-pair cost**.  `several-conjugate-pairs-no-joint-profile.md`
shows the per-pair relaxation is off by a factor `n−1`: the `n(n−1)` ordered pairs `(j,k)`, `j ≠ k`,
from `{0,…,n−1}` with terms `−cos((j−k)θ)` are jointly dominated by `n`, while per-pair certification
costs `n(n−1)`.  Therefore

> **sums of Hermitian squares certify only the per-pair relaxation of Beurling realizability, and
> are off by an unbounded factor.**

Together with the one-pair result the picture is complete: for `r = 1` the SOS cone is exactly the
phase-blind cone and the classification is sharp; for `r ≥ 2` the SOS cone is still only the
phase-blind cone, which is now unboundedly smaller than the nonnegative cone.

## Consequence for the Beurling programme

For one conjugate pair the previous card characterised `R(t) ≥ 2e^{βt} cos(γ t)` by an arc criterion.
Unfolding that comparison gives `R(t) ≥ 2e^{βt} cos(γ u)`, i.e. `R(t) ≥ 2e^{βt}` for all `t` — the
**phase-blind** condition. So:

> the sum-of-Hermitian-squares relaxation of Beurling realizability is exactly the phase-blind
> relaxation, and its error is exactly the peak-versus-global gap already characterised.

Sums of squares are therefore the wrong certificate class for realizability with complex zeros: they
cannot see the peak lattice at all. The correct certificates remain the per-hump exponential profiles
of `LogConcaveSeparation`.

## The converse holds for one conjugate pair

The obstruction is not merely necessary. For a comparison with a **single** pair it is the whole
story:

> `R(t) − 2e^{βt}cos(γ t)` is a sum of Hermitian squares  ⟸  `R(t) ≥ 2e^{βt}` for all `t`,

the hypothesis being exactly nonnegativity of the unfolding. `onePair_isSumHermitianSquares`.

Proof: split `R(t) − 2e^{βt}cos(γ t) = [R(t) − 2e^{βt}] + 2e^{βt}(1 − cos γ t)`. The second bracket
is the explicit Hermitian square above. The first is a nonnegative signomial with commensurable
exponents, `S(t) = e^{−mt} p(e^{ρ t})` with `p ≥ 0` on `(0,∞)`, and

**Theorem.** A nonnegative signomial with commensurable exponents is a sum of two squares of
signomials. `isSumHermitianSquares_signomial`.

which follows from the substitution `y ↦ y²` — turning nonnegativity on the half-line into
nonnegativity on the line — together with

**Theorem (mathlib gap, built here).** A real polynomial in one variable that is nonnegative on ℝ is
a sum of two squares of polynomials. `exists_sq_add_sq_of_nonneg`; half-line form
`exists_sq_add_sq_comp_sq`.

proved by induction on the degree: a nonconstant nonnegative polynomial has an irreducible factor of
degree one or two (`Irreducible.natDegree_le_two`); a linear factor forces a double root, because a
zero of a nonnegative function is a minimum and the derivative vanishes there; an irreducible
quadratic is `(X + b/2)² + (c − b²/4)` with positive constant term because it has no real root; and
`(u²+v²)(a²+b²) = (ua+vb)² + (ub−va)²` closes the induction. Neither mathlib nor the corpus had this.

Closure of the Hermitian-square cone under sums is `IsSumHermitianSquares.add`.

So for one conjugate pair the classification is complete: **sum of Hermitian squares ⟺ phase-blind
domination `R ≥ 2e^{βt}`**, strictly stronger than the arc criterion, with the gap measured by the
threshold family above.

## Modules

```
formal/GaloisForLFunctions/HTGeometry/ComplexExpUnfolding.lean
formal/GaloisForLFunctions/HTGeometry/HermitianSOSUnfolding.lean
formal/GaloisForLFunctions/HTGeometry/HermitianSOSCounterexample.lean
formal/GaloisForLFunctions/HTGeometry/HermitianSOSExtremal.lean
formal/GaloisForLFunctions/HTGeometry/UnivariateSumOfTwoSquares.lean
formal/GaloisForLFunctions/HTGeometry/OnePairSumOfSquares.lean
formal/GaloisForLFunctions/HTGeometry/MultiPairPhaseBlind.lean
```

## Open

* Whether the full multi-torus obstruction (deforming the exponents by an arbitrary ℚ-linear map,
  giving nonnegativity on `(ℝ_{>0})^a × 𝕋^b`) is strictly stronger than the phase-blind condition
  proved here. The ℚ-linear extension is elementary finite-dimensional linear algebra but is not
  formalized; the Bohr-recurrence route above reaches the phase-blind conclusion without it.
* Sufficiency beyond `W`-degree one. The unfolding of `f` is a signomial on `ℝ_{>0} × 𝕋`; the
  question is whether every such nonnegative signomial is a sum of Hermitian squares. Degree one in
  `W` is settled affirmatively above (and the degree-one Gram argument `p₀ ± 2p₁ = ∑ squares` works
  verbatim). Higher `W`-degree is a genuine two-variable psd-versus-sos question; note that the usual
  Newton-polytope obstruction is unavailable, because the `W` direction carries no Newton constraint
  and the only forced-diagonal `Z`-exponents are the two extremes, where the coefficient is a
  nonnegative trigonometric polynomial and Fejér–Riesz applies.
* The purely real-exponent analogue: for exponents spanning a ℚ-space of dimension `d ≥ 2` the same
  argument applies with ℚ-linear deformations of the exponents in place of the phase shift, which
  needs a Hamel basis and is not formalized here.
