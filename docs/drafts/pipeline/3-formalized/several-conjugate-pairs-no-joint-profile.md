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
formal/GaloisForLFunctions/HTGeometry/SturmComparisonArch.lean
formal/GaloisForLFunctions/HTGeometry/ArchCount.lean
formal/GaloisForLFunctions/HTGeometry/SturmWindowCount.lean
formal/GaloisForLFunctions/HTGeometry/AccumulationZeros.lean
formal/GaloisForLFunctions/HTGeometry/ExpPolyIsolatedZeros.lean
formal/GaloisForLFunctions/HTGeometry/FiniteZeroSet.lean
formal/GaloisForLFunctions/HTGeometry/ZeroCountSturm.lean
formal/GaloisForLFunctions/HTGeometry/ZeroSetCount.lean
formal/GaloisForLFunctions/HTGeometry/SturmReduction.lean
formal/GaloisForLFunctions/HTGeometry/ZeroListBridge.lean
formal/GaloisForLFunctions/HTGeometry/RealExponentBase.lean
formal/GaloisForLFunctions/HTGeometry/ExpShift.lean
formal/GaloisForLFunctions/HTGeometry/SimpleZeroEnergy.lean
formal/GaloisForLFunctions/HTGeometry/HarmonicZeroCount.lean
formal/GaloisForLFunctions/HTGeometry/ExpPolyZeroCount.lean
```

## Open

* Whether the effective constants can be brought down to the classical ones. The bound proved here
  is `3^N (n + 2L + 1) − (2L + 1)` with `L = (b−a)γ₀/π`; Langer (1931) gives `n(r) ≤ n + r·w_n/2π`
  for complex zeros in a rectangle of height `r`, i.e. a *density constant of one*. The exponential
  factor here comes entirely from `card_zeros_le_split`, which pays `3M` per Sturm zero: two
  endpoints for each of the two pieces plus the split point. A split paying `M` would make the
  recursion additive and the bound polynomial in `N`. This is a defect of the descent, not of the
  mathematics.

* Whether a nonnegative exponential polynomial with mixed real and imaginary exponents is always a
  sum of Hermitian squares — see the last item of this card.

## Where this sits against the literature

The statement proved here is classical and the constants are worse than the classical ones. Pólya
(1920) and Schwengeler (1925) located the zeros of exponential sums on Pólya lines; Langer,
*On the zeros of exponential sums and integrals*, Bull. AMS 37 (1931), 213–239, proved
`|n(r) − w_n r/2π| ≤ n` for `1 + H₁e^{w₁z} + ⋯ + H_ne^{w_nz}` in a rectangle of height `r`;
Tijdeman (1971) and Voorhoeve (1976) give the general effective forms. Nothing below moves that
frontier. Its value is internal: an unconditional, self-contained, real-variable proof, localized to
a *prescribed* interval with *explicit* constants in `(n, γ₀, b−a)`, which the per-hump criterion of
this card can consume as a decision procedure.

The corpus already owned `CExpPoly.exists_zeroCount_linear` — a Jensen-based linear zero count for
complex exponential polynomials with polynomial coefficients. It is not a substitute: its constant
`K` and its anchor `z₀` are existentially quantified, so it says nothing about a prescribed interval
and nothing effective in the data.

## The degenerate count

The induction below reduces the support by the conjugate pair `± iγ`. When nothing survives the
reduction the reduced polynomial vanishes identically, no finite set contains its zeros, and
`card_zeros_le_reduce` does not apply. That branch is counted on its own, twice.

**By energy conservation** (`SimpleZeroEnergy`; this is the route the induction runs on). On that
branch `f'' + γ² f ≡ 0`, so the energy

```
  sturmEnergy f f' γ = f'² + γ² f²,    E' = 2 f' (f'' + γ² f) = 0
```

is constant (`sturmEnergy_const`). At a zero of `f` the energy equals `f'²`; if that vanished the
constant energy would be zero everywhere and `f ≡ 0`. So every zero of a nonzero solution is simple
(`deriv_ne_zero_of_sturm_zero`). A simple zero cannot be a local maximum, so two adjacent negative
arches are impossible (`not_two_negative_arches_of_simple`) — simplicity replaces the strict
positivity of the Sturm expression as the source of alternation.

The arch-length bound needs the matching weakening. `arch_length_ge` was stated under `0 < h`, but
its proof contradicts a point where the comparison forces `h ξ < 0`, so `0 ≤ h` already suffices;
`ArchCount` now carries the nonnegative hypothesis (and its mirror `h ≤ 0`), which is exactly what
makes it usable where `f'' + γ² f` vanishes identically. Assembling:

```
  zero_count_le_of_simple  :  (n : ℝ) ≤ 2 (b-a) γ / π + 1
  card_zeros_le_of_simple  :  (Z.card : ℝ) ≤ 2 (b-a) γ / π + 2
  card_zeros_le_of_sturm_zero :  the same for a nonzero solution of f'' + γ² f = 0
```

and, on the exponential-polynomial side, `card_zeros_degenerate_energy`, which checks that a
pair-supported polynomial has `f'' + γ² f ≡ 0` (every `sturmCoeff` dies) and applies the above.

**Sharply, by a determinant** (`HarmonicZeroCount`; exported alongside, half the density). On that
branch the polynomial *is* a harmonic. Two zeros of `A cos γt + B sin γt` impose a linear system in
`(A,B)` whose determinant is `sin(γ(t₂ − t₁))`; if `0 < γ(t₂−t₁) < π` that is strictly positive, so
`A = B = 0` (`harmonic_coeff_eq_zero`). Hence distinct zeros of a nonzero harmonic are at least
`π/γ` apart (`harmonic_gap`), and a `d`-separated subset of an interval of length `b−a` has at most
`(b−a)/d + 1` elements (`card_le_of_separated`, from `nsmul_le_of_disjoint_intervals` applied to the
consecutive gaps of the increasing enumeration):

```
  card_zeros_harmonic :  (Z.card : ℝ) ≤ (b − a) * γ / π + 1
```

This is sharp — `2 cos γt` attains it — and `card_zeros_degenerate_sharp` is its
exponential-polynomial form. Passing from the polynomial to the harmonic is termwise: an annihilated
exponent is `± iγ` (`eq_pair_of_sturmCoeff_eq_zero`), for such an exponent
`Re(c e^{iωt}) = Re c · cos ωt − Im c · sin ωt` (`re_term_imag`), and `cos` is even while `sin` is
odd, so both members of the pair contribute the same cosine and opposite sines
(`re_expCombo_of_pair`). No enumeration of the two-element support is needed.

Either bound closes the branch: the induction invariant absorbs `2L + 2` exactly as it absorbs
`L + 1`. In both cases vanishing of the coefficients would make the polynomial identically zero,
which `not_finset_covers_Icc` excludes.

## The induction, and the bound

Induction on the number `N` of non-real exponents (`card_zeros_expPoly`, `ExpPolyZeroCount`). At
`N = 0` all exponents are real and `card_zeros_le_realExponents` gives `|Z| + 1 ≤ |S|`. Otherwise
pick `y₀` with `Im y₀ ≠ 0`, set `γ = |Im y₀|`, translate the exponents by `Re y₀` — which changes
neither the zeros nor the imaginary parts — and apply `D² + γ²`. The shifted `y₀` is `± iγ`, so its
coefficient dies; every surviving exponent keeps a nonzero coefficient, and the surviving non-real
exponents inject into the previous ones minus `y₀`, so `N` drops. The zeros of the reduced polynomial
on `[a,b]` form a finite set by `finite_zeros_expPoly`, the induction hypothesis bounds it, and
`card_zeros_le_reduce` converts that into a bound for `Z`. If instead *nothing* survives,
`card_zeros_degenerate_energy` applies.

The recursion `B(N) = 2L + 3·B(N−1) + 2` with `B(0) = n − 1` and `L = (b−a)γ₀/π` is closed by

```
  B(N) = 3^N (n + 2L + 1) − (2L + 1),
```

which is the invariant carried through the induction (the step needs only `L ≥ 0`). Two usable
forms are exported, both dropping the hypothesis that `Z` is *all* the zeros — the full zero set is
finite and contains `Z`:

```
  card_zeros_le_expPoly :  (Z.card : ℝ) ≤ 3^n (n + 2L + 1) − (2L + 1)
  card_zeros_le_expPoly_linear :
      (Z.card : ℝ) ≤ (3^n (n+1) − 1) + 2 (3^n − 1) · L
```

The second is the same bound read as constant plus density, which is the Pólya shape: for fixed
support the real zero count grows at most linearly in the interval length, with slope controlled by
the spread of the imaginary parts. The identity between the two forms is exact, not an estimate.

## The Sturm engine

**Sturm comparison on a short arch.** If `g(p) = g(q) = 0`, `g > 0` on `(p,q)`, and `q − p < π/γ`,
then `g'' + γ² g` takes a strictly negative value on `(p,q)`. `exists_sturm_neg`; mirrored form
`exists_sturm_pos`.

The proof is the inhomogeneous Wronskian against `w(t) = sin(γ(t−p))`: `φ = g'w − gw'` has derivative
`(g'' + γ²g)w`, so if the Sturm expression never went negative then `φ` would be nondecreasing from
`φ(p) = 0`, while `φ(q) = g'(q)w(q) ≤ 0` because the arch descends at its right endpoint. That forces
`φ ≡ 0`, hence `g'' + γ²g ≡ 0` on the arch and `g'(q) = 0`; the energy `g'² + γ²g²` is then constant
and vanishes at `q`, so `g ≡ 0` — contradicting positivity. No ODE uniqueness theorem is used, only
the energy identity.

**Sign change between adjacent arches.** Two consecutive arches of opposite sign, each shorter than
`π/γ`, force `g'' + γ²g` to vanish between them. `exists_sturm_zero`.

Neither statement is in mathlib.

## The effective arch count

**Arch length.** Where `g'' + γ²g > 0` on `[a,b]`, every positive arch of `g` there has length at
least `π/γ`. `arch_length_ge`; mirrored `arch_length_ge_neg`.

**Arch number.** Hence at most `(b−a)γ/π` pairwise disjoint positive arches fit in `[a,b]`:

```
  card_arches_le :  (n : ℝ) ≤ (b - a) * γ / π
```

for any ordered disjoint family of `n` arches, via `nsmul_le_of_disjoint_intervals` — `n` ordered
disjoint subintervals each at least `d` long force `n·d ≤ b − a`.

Humps of a comparison function are exactly its positive arches, so this is the count that determines
how many separating exponentials `le_iff_forall_separating_interval` demands. It is effective and
explicit wherever the Sturm expression keeps one sign.

## The window dichotomy, and where the effective count stops

A **window** is a pair of adjacent arches — three consecutive zeros `p < m < q` with `g > 0` on
`(p,m)` and `g < 0` on `(m,q)`. Sturm comparison gives a per-window dichotomy:

> either `g'' + γ²g` vanishes inside the window, or the window spans at least `π/γ`.

`sturm_window_dichotomy`. Windows built from consecutive zeros are disjoint, so the two alternatives
are counted separately: `h`-zeros against the zero set of `h`, long windows against the interval
length. Where `h` does not vanish at all, only the second survives:
`card_windows_le : (k : ℝ) ≤ (b − a)·γ/π`.

This is the complete **descent step** of a Pólya-type bound `Z(f) ≤ 2Z(L_jf) + 2(b−a)γ_j/π + 1`,
where `L_j = D² − 2β_jD + (β_j²+γ_j²)` removes the `j`-th conjugate pair (every other exponent `λ`
is scaled by `(λ−β_j)² + γ_j² ≠ 0`, and the recursion bottoms out at a real exponential sum, counted
by `laguerre_zeroList_length_le`).

## The structural input, without real-analyticity

The descent needs to know that the zero set of `f` on `[a,b]` is discrete. That looked like a
real-analyticity project; it is not. Rolle suffices.

**Accumulation forces all derivatives to vanish.** Write `AccumZero f t₀` for "zeros of `f`
accumulate at `t₀`". If `f` is smooth then

```
  iteratedDeriv_eq_zero_of_accumZero :  AccumZero f t₀ → ∀ n, iteratedDeriv n f t₀ = 0
```

`AccumulationZeros`. The engine is `accumZero_deriv`: between `t₀` and a nearby zero, Rolle gives a
zero of `f'` **strictly closer** to `t₀`, so accumulation propagates from `f` to `f'`, and continuity
turns accumulation into vanishing at each stage. No analyticity, no identity theorem, no power
series.

**Identity theorem for exponential polynomials.** Differentiating an exponential polynomial
multiplies each coefficient by its exponent, so the vanishing derivatives at `t₀` are exactly the
power moments of the weights `C y · e^{y t₀}` over the distinct nodes `y`; Lagrange interpolation
(`coeff_eq_zero_of_forall_pow`, factored out of `exp_coeff_eq_zero`) forces those weights, hence the
coefficients, to vanish:

```
  coeff_eq_zero_of_accumZero :  (im part ≡ 0) → AccumZero (re ∘ F) t₀ → ∀ y ∈ S, C y = 0
```

`ExpPolyIsolatedZeros`, with the contrapositive `not_accumZero_of_coeff_ne` and the concrete
punctured-neighbourhood form `exists_punctured_zero_free`.

**Finiteness.** Isolated zeros on a compact interval are finitely many — an infinite zero set gives an
injective sequence, Bolzano–Weierstrass a convergent subsequence, and injectivity puts infinitely
many terms away from the limit, producing an accumulation point:

```
  finite_zeros_of_not_accumZero :  (∀ t₀ ∈ Icc a b, ¬ AccumZero f t₀) → {t ∈ Icc a b | f t = 0}.Finite
  finite_zeros_expPoly         :  a nonzero exponential polynomial has a finite zero set on [a,b]
```

`FiniteZeroSet`.

**Zeros are crossings or minima.** Where `f'' + γ²f > 0`, the function cannot attain the value `0` at
a local maximum (`not_isLocalMax_of_sturm_pos`): the first derivative vanishes there, the second is
then `h > 0`, so the derivative is positive just to the right and `f` strictly increases past `0`.
Hence `f` never touches zero from below, negative arches are separated by positive ones — which are
at least `π/γ` long — and the whole zero count is controlled by the positive arches that
`card_arches_le` bounds.

## The zero count

Assembling everything:

```
  zero_count_le :  (n : ℝ) ≤ 2 * ((b - a) * γ / π) + 1
```

for any family of `n + 1` consecutive zeros of `f` in `[a,b]`, where `f'' + γ² f > 0` throughout.
`ZeroCountSturm`.

Three steps. On each gap between consecutive zeros `f` has no zero, hence constant sign by the
intermediate value theorem (`sign_constant_of_no_zero`). Two adjacent gaps cannot both be negative —
the shared zero would be a local maximum, excluded by `not_isLocalMax_of_sturm_pos`
(`not_two_negative_arches`). So in each block of two consecutive gaps at least one is positive;
choosing one per block gives `⌊n/2⌋` pairwise disjoint positive arches, each at least `π/γ` long by
`arch_length_ge`, and `card_arches_le` bounds their number by `(b−a)γ/π`.

The choice function is the only subtlety: `σ j = 2j` if that gap is positive and `2j+1` otherwise,
which is well defined because a non-positive gap is negative and then its successor cannot also be
negative. Ordering `σ j + 1 ≤ σ j'` for `j < j'` follows from `σ j ≤ 2j+1 < 2j' ≤ σ j'`.

## From the family to the zero set, and the descent

**Enumeration.** An increasing enumeration of the finite zero set has no element of the set strictly
between consecutive values, which is exactly the gap-freeness hypothesis. Hence

```
  card_zeros_le :  (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 2
```

for `Z` the full zero set of `f` in `[a,b]`, where `f'' + γ² f > 0`. `ZeroSetCount`.
Negating `f` gives `card_zeros_le_neg`, and combining the two, `card_zeros_le_of_ne` needs only that
the Sturm expression does **not vanish** on the open interval — either sign.

**The descent step.** Splitting `[a,b]` at the zeros of the Sturm expression and inducting on their
number:

```
  card_zeros_le_split :  (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 3 * M + 2
```

where `M` bounds the number of zeros of `f'' + γ² f` in `(a,b)`. The induction peels the largest
Sturm zero `w`: above `w` the Sturm expression is zero-free, so `card_zeros_le_of_ne` applies on
`[w,b]`, while `[a,w]` carries one fewer Sturm zero and is handled by the hypothesis. The zero sets
of the two halves cover `Z`, and the lengths telescope.

This required weakening the arch and count hypotheses from `Icc a b` to `Ioo a b` — they were only
ever used at interior points — so that a subdivision at Sturm zeros leaves usable pieces.

## The base case

With every exponent real the polynomial is a real exponential sum and Laguerre's rule applies:

```
  card_zeros_le_realExponents :  Z.card + 1 ≤ S.card
```

`RealExponentBase`. Two observations make the passage automatic. For a real exponent,
`Re (C y · e^{y t}) = (Re C y) · e^{y t}` termwise, so no linear independence is needed to read off
the real form; and the coefficients are real anyway, because their imaginary parts form a vanishing
real exponential combination which `exp_coeff_eq_zero` kills (`coeff_re_of_real_exponents`).

The interface to Laguerre is `ZeroListBridge`: a finite zero set becomes a zero *configuration* by
sorting (`exists_isZeroList_of_finset` — each zero appears once, so the multiplicity counts are at
most one), and `signChanges c + 1 ≤ m` (`signChanges_add_one_le`) converts the sign-change bound into
a term count. Together:

```
  card_zeros_le_expSum :  Z.card + 1 ≤ m
```

for a real exponential sum with `m` nonzero terms and strictly increasing exponents.

## Normalisation: shifting the exponents

Translating every exponent by a real `β` multiplies the polynomial by the nowhere-zero `e^{−βt}`:

```
  shift_expCombo :  ∑_{z ∈ S − β} C(z+β) e^{zt} = e^{−βt} · ∑_{y ∈ S} C y e^{yt}
```

`ExpShift`. Hence the zero set (`shift_zero_iff`), real-valuedness (`shift_real`), the support size
(`shiftSupport_card`) and the imaginary parts (`shift_im_eq`) are all unchanged, while a chosen
exponent `y₀` lands on the imaginary axis at `i·Im y₀` (`shift_target`) — exactly where the Sturm
operator `D² + γ²` deletes it with its conjugate. Also recorded: `not_finset_covers_Icc`, that a
finite set cannot contain an interval, which is what rules out identically vanishing polynomials.

## The algebraic reduction

Applying `D² + γ²` to an exponential polynomial multiplies each coefficient by `y² + γ²`:

```
  sturmCoeff C γ y = C y * (y² + γ²)
  sturm_expr_expCombo :  (Re F)'' + γ² (Re F) = Re (∑ sturmCoeff C γ y · e^{y t})
```

`SturmReduction`. The factor vanishes exactly at `y = ± iγ` (`sturmCoeff_eq_zero_of_mem`,
`sturmCoeff_eq_zero_of_mem'`) and nowhere else (`sturmCoeff_ne_zero`, from the factorization
`y² + γ² = (y − iγ)(y + iγ)`), so the operator deletes one conjugate pair and rescales every other
term by a nonzero constant. The reduced polynomial is again real-valued (`sturm_expCombo_real`), so
the reduction can be iterated.

Combining with the splitting gives the descent in the form the recursion consumes:

```
  card_zeros_le_reduce :  (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 3 * M + 2
```

where `Z` is the zero set of the real exponential polynomial on `[a,b]` and `M` bounds the zeros of
the reduced one in `(a,b)`. Supporting this needed the derivative transfer
`iteratedDeriv_expCombo_eq_ofReal` — for a real-valued exponential polynomial, every derivative is
the real cast of the differentiated combination — extracted from `ExpPolyIsolatedZeros`.
* Whether a nonnegative exponential polynomial with mixed real and imaginary exponents is always a
  sum of Hermitian squares `∑ G_l G_l^*` with exponents in the half-set. The one-pair extremal
  `2e^{βt}(1−cos γt) = 4|sinh((β+iγ)t/2)|²` and `cosh(at) − cos(bt) = 2|sinh(t(a+ib)/2)|²` both are;
  no counterexample is known to us and no proof is given here.
