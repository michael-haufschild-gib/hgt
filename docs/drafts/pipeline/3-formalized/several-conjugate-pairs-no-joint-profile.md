# Several conjugate pairs: no joint profile, and an unbounded per-pair gap

**Stage:** 3 — formalized in Lean 4 (unconditional; axioms `[propext, Classical.choice, Quot.sound]`).

Follows `complex-pair-peak-criterion-and-laguerre-rule.md`, which settled one conjugate pair exactly.
The question left open there was whether several pairs admit a joint profile, or whether the
finiteness reduction plus a per-pair relaxation already decides realizability. Both answers are no,
and both failures are now quantified.

## The setting

`R(t) = ∑ c_i e^{a_i t}` with every `c_i > 0`; comparison function
`C(t) = ∑_{k<r} 2 e^{β_k t} cos(γ_k t + δ_k)`. Realizability of a rational Beurling zeta with `r`
conjugate pairs of zeros is `C ≤ R` on `(0,∞)`.

## What survives: localization

**Envelope bound.** `C(t) ≤ 2r (e^{b₋ t} + e^{b₊ t})` for every `t`, where `b₋ ≤ β_k ≤ b₊`.
`multiPair_le_envelope`.

**Localization.** If some exponent of `R` is `< b₋` and some is `> b₊`, the set where `R` fails to
clear that envelope is bounded by
```
  T = max ( |log(4r/c_i)/(a_i − b₋)| , |log(4r/c_j)/(a_j − b₊)| ),   a_i < b₋ ≤ b₊ < a_j ,
```
so `C ≤ R` on ℝ ⟺ `C ≤ R` on `[−T, T]`. `envelope_exceptional_bounded`, `multiPair_le_iff_on_Icc`.
This is the one-pair reduction verbatim, for arbitrarily many pairs.

**Top layer.** Grouping exponents by real part, `F = ∑_m e^{β_m t} T_m(t)` with `T_m` real
trigonometric polynomials. If `F ≥ 0` then the top layer is nonnegative everywhere:
`bohrLayer_nonneg_of_nonneg`, proved from simultaneous Bohr recurrence
(`exists_large_atomicSymbol_revival`) — a negative value of `T_M` recurs at arbitrarily large times,
where the lower layers are exponentially negligible. This is the dominant-term principle of the
ultimate-positivity literature, made exact for this cone; it is not new mathematics.

## What fails: the joint profile

**The chord obstruction.** An exponential is log-affine, so if `A e^{μt}` dominates `C` at `t₁` and
`t₂` it dominates the geometric mean of `C(t₁), C(t₂)` at every point in between:
```
  min(C t₁, C t₂) ≤ A e^{μ t₃}   for   t₁ < t₃ < t₂ .
```
`min_le_of_exp_dominates`.

**Consequence.** Whenever `C` has two positive values straddling a nonpositive one — impossible for a
single cap on its own arc, generic for two pairs — there is a two-term positive exponential sum
`R(t) = λ cosh(K(t−t₃))` with `C ≤ R` on all of ℝ and **no** separating exponential on `[t₁,t₂]`.
`exists_expSum_no_separating`. So no criterion of the form "domination ⟺ one exponential separates"
can hold beyond one pair, for any choice of profile function.

## What replaces it: one profile per hump

The separation is complete exactly on the log-concave range. Define

> `LogTangentDominated C W`: at every `t₀ ∈ W` with `C t₀ > 0`,
> `C t ≤ C t₀ · exp( (C'(t₀)/C(t₀)) (t − t₀) )` for all `t ∈ W`.

**Hump theorem.** If `W = [u,v]` carries `C ≤ 0` at both endpoints, `C > 0` somewhere inside, and `C`
is log-tangent-dominated on `W`, then `C ≤ R` on `W` ⟺ a single exponential lies under `R` on all of
ℝ and above `C` on `W`. `exists_separating_of_le_on_hump`, converse `le_of_separating`.

**Piecewise criterion.** If the positivity set of `C` is covered by finitely many such humps, then
`C ≤ R` on ℝ ⟺ one separating exponential per hump. `le_iff_forall_separating`.

**The endpoint hypothesis is removable.** Requiring `C ≤ 0` at the endpoints was an artefact: it was
used only to place the maximiser of `C/R` in the interior. The first-order optimality condition on a
convex set replaces it — at a maximiser `t*` over `[u,v]`, interior or endpoint,
`(C'/C − R'/R)(t*)·(t − t*) ≤ 0` for every `t ∈ [u,v]`, which is exactly what the tangency argument
consumes (`deriv_mul_sub_nonpos_of_isMaxOn`). Hence separation holds on **any** interval of
log-tangent-domination: `exists_separating_of_le_on_interval`, with piecewise form
`le_iff_forall_separating_interval` requiring only

* a finite family of intervals `[u_k, v_k]`,
* log-tangent-domination of `C` on each,
* a cover of `{C > 0}`.

No endpoint conditions, no "positive somewhere inside". This is what makes the criterion usable: a
hump may now be **subdivided** at the inflection points of `log C`, so the criterion applies whenever
the positivity set is covered by intervals of log-concavity — which is always achievable, the only
remaining question being how many are needed.

**The cap is an instance.** `2 e^{βt} cos(γ(t−p))` is log-tangent-dominated on its arc
(`logTangentDominated_cap`, via `capFn_min`), so the one-pair criterion of the previous card is the
case of a single hump. The number of humps is what grows with the number of pairs; for pairs sharing
a real part it is bounded per period by the zeros of `C''C − (C')²`, a trigonometric polynomial.

## What fails worse: the per-pair relaxation

**Small witness.** `9/4 − 2cos t + 2cos 2t = (2cos t − 1/2)²  ≥ 0`, with equality at `cos t = 1/4`.
So the two pairs at frequencies `1, 2` with opposite signs are dominated by the constant `9/4`
(`two_cos_sub_two_cos_two_mul_le`, `exists_two_cos_sub_two_cos_two_mul_eq`), while any per-pair
split needs `4` (`per_pair_sum_ge_four`). The split really is into constants: two positive
exponential sums with constant total have every exponent zero
(`exponents_eq_zero_of_expSum_const`).

**The gap is unbounded.** Take the `n(n−1)` ordered pairs `(j,k)`, `j ≠ k`, from `{0,…,n−1}`, with
comparison terms `−cos((j−k)θ)`. Then

* joint: `∑_{j≠k} −cos((j−k)θ) ≤ n` for every `θ` (`offDiagonal_sum_le`) — because the full double
  sum is `‖∑_j e^{ijθ}‖² ≥ 0` (`sum_sum_cos_sub_nonneg`) and the diagonal contributes exactly `n`;
* per-pair: each term has supremum `1`, so certifying separately costs `n(n−1)`
  (`per_pair_cost_ge`).

The relaxation is therefore off by a factor `n−1`. The mechanism is Fejér/Dirichlet positivity: the
joint function is small precisely because the pairs interfere, and interference is exactly what a
per-pair certificate discards.

## Consequence for rational Beurling zetas

For `r ≥ 2` conjugate pairs the decision problem localizes to an explicit compact interval and to a
nonnegative top layer, but its *certificate* structure is genuinely different from `r = 1`: the
correct object is a finite family of profiles indexed by the humps of the comparison function, and
any attempt to decouple the pairs loses a factor growing linearly in their number. Coupling between
zeros is not a second-order correction to Beurling realizability — it is the leading term.

## Modules

```
formal/GaloisForLFunctions/HTGeometry/ExponentialCertificateGap.lean
formal/GaloisForLFunctions/HTGeometry/LogConcaveSeparation.lean
formal/GaloisForLFunctions/HTGeometry/MultiPairLocalization.lean
formal/GaloisForLFunctions/HTGeometry/TopLayerNonneg.lean
formal/GaloisForLFunctions/HTGeometry/PerPairGapUnbounded.lean
formal/GaloisForLFunctions/HTGeometry/IntervalSeparation.lean
```

## Open

* An effective bound on the number of log-concavity intervals needed to cover `{C > 0}` inside the
  localization interval. The intervals are delimited by the zeros of `C` and of `C''C − (C')²`, both
  exponential polynomials; the count is therefore a Pólya-type zero-density bound
  `(#terms − 1) + (length)·(imaginary width)/2π`, whose proof is complex-analytic (argument principle)
  or Sturm-theoretic (disconjugacy of `y'' + γ²y = 0` on intervals shorter than `π/γ`). Neither is
  formalized here. With that bound the criterion becomes an effective decision procedure.
* Whether a nonnegative exponential polynomial with mixed real and imaginary exponents is always a
  sum of Hermitian squares `∑ G_l G_l^*` with exponents in the half-set. The one-pair extremal
  `2e^{βt}(1−cos γt) = 4|sinh((β+iγ)t/2)|²` and `cosh(at) − cos(bt) = 2|sinh(t(a+ib)/2)|²` both are;
  no counterexample is known to us and no proof is given here.
