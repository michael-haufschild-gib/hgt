# Möbius--Laplace explicit forced-negativity window

- **ID:** `mobius-laplace-two-three-free-forced-negativity`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-SIDE SIGN LAW
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[PRIORITY UNVERIFIED] [NOT AN RH PROOF] [NO COMPUTATION]`
- **Lean status:** `[FORMALIZED]` in
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean`
- **Parent:** `mobius-laplace-critical-renewal-law.md`

## Statement

Put

```text
Phi(x)=sum_(n>=1) mu(n) exp(-n x),       x>0.
```

Two unconditional sign laws hold.

First, for every

```text
0 < x <= log(4/3),
```

there is a positive integer `k`, divisible by neither `2` nor `3`, such that

```text
Re Phi(kx) < 0.                                             (1)
```

Equivalently, every sufficiently fine positive dilation lattice contains a strictly negative
Möbius--Laplace value in its `6`-coprime sector.  Second, witness is forced to be `k=1` throughout
the nonempty explicit interval

```text
log(2)/5 <= x <= log(4/3),
```

so

```text
Re Phi(x) < 0.                                              (2)
```

In particular, `Re Phi(log(2)/5)<0`.  No zero of zeta, zero-density theorem, RH hypothesis,
simple-zero hypothesis, or numerical evaluation enters either proof.

Third, transform has an actual positive-axis zero in fixed exact bracket:

```text
there exists c with log(4/3) < c < 3 log(4/3) and Phi(c)=0.  (3)
```

Equivalently, ordinary generating-function coordinate `q=exp(-c)` lies in rational interval
`27/64<q<3/4`.

## Exact divisibility reindexing

The already proved absolutely convergent Lambert law is

```text
sum_(k>=1) Phi(kx)=exp(-x).                                  (4)
```

Multiplication by a fixed positive integer `m` is an equivalence from the positive integers to
the subtype of positive multiples of `m`.  Absolute convergence and exact reindexing therefore
give

```text
sum_(m|k) Phi(kx)=exp(-mx).                                  (5)
```

Inclusion--exclusion for the two prime divisibility predicates now yields

```text
sum_(2 does not divide k, 3 does not divide k) Phi(kx)
 = exp(-x)-exp(-2x)-exp(-3x)+exp(-6x).                       (6)
```

This is an identity of genuine absolutely convergent transform values, not only a formal identity
between four renewal masses.

## Strict sign on an explicit interval

Let `t=exp(-x)`.  The right side of `(6)` is

```text
t-t^2-t^3+t^6
 = t(t-1)(t^4+t^3+t^2-1).                                  (7)
```

If `0<x<=log(4/3)`, then

```text
3/4 <= t < 1.
```

The last factor in `(7)` is strictly positive.  Indeed,

```text
t^2 >= 9/16,
t^3 >= 27/64,
t^4 >= 81/256,

t^4+t^3+t^2-1 >= 333/256-1 = 77/256 > 0.                   (8)
```

Thus `(7)` is strictly negative.  If every `6`-coprime summand in `(6)` had nonnegative real part,
absolute convergence would make the real part of the whole sum nonnegative, a contradiction.
This proves `(1)`.

## Tail dominance and witness isolation

For every `y>=log 2`, put `q=exp(-y)<=1/2` and split off first nonzero atom:

```text
Phi(y)=q+sum_(n>=2) mu(n)q^n.
```

The exact geometric majorant gives

```text
|sum_(n>=2) mu(n)q^n|
 <= sum_(n>=2) q^n
 = q^2/(1-q)
 <= q.                                                       (9)
```

Hence `Re Phi(y)>=0` for every `y>=log 2`.  A positive integer divisible by neither `2` nor `3`
is either `1` or at least `5`.  If `x>=log(2)/5`, every eligible witness `k!=1` from `(1)` would
satisfy `kx>=log 2`, contradicting `(9)`.  Therefore `k=1`, proving `(2)`.

Window is genuinely nonempty: exact inequality `2<(4/3)^5` implies
`log(2)/5<log(4/3)` by strict monotonicity of logarithm.

Same estimate without specializing `q<=1/2` gives quantitative lower bound

```text
Re Phi(y) >= q-q^2/(1-q),        q=exp(-y).                 (10)
```

It is strict positive whenever `y>log 2`.

## Positive dilates and actual generating-function zero

Taking real parts in `(4)`, positive total `exp(-x)` forces at least one strictly positive
`Re Phi(kx)` on every positive dilation lattice.  More sharply, exact inequality

```text
2 < (4/3)^3
```

gives `log 2 < 3 log(4/3)`, so `(10)` proves

```text
Re Phi(3 log(4/3)) > 0.
```

At left endpoint, `(2)` gives strict negativity.  Transform is continuous on positive real axis;
every defining term is real and absolute convergence lets imaginary part pass through sum, so
`Phi(y)` itself is real.  Intermediate value theorem now proves actual complex equality `(3)`.
Exponentiating bracket reverses order and gives

```text
27/64 = exp(-3 log(4/3)) < exp(-c) < exp(-log(4/3)) = 3/4.
```

## Hostile audit

1. **Infinite-sum inference.**  A negative total implies a negative term only after real parts may
   pass through the sum.  Lean uses absolute summability of the full dilation family, preserves it
   under the `6`-coprime indicator, and maps the resulting `HasSum` through the continuous real-part
   functional.
2. **Divisibility partition.**  The proof does not assume that divisibility cylinders form a
   positive measure.  It constructs the equivalence between positive integers and multiples of
   `m`, proves `6|k` iff `2|k` and `3|k`, and performs signed inclusion--exclusion exactly.
3. **Endpoints and nonvacuity.**  At `x=log(4/3)`, inequality `(8)` is still strict.  At
   `x=log(2)/5`, tail dominance still excludes every `k>=5`.  Exact logarithmic comparison proves
   lower endpoint lies strictly below upper endpoint.
4. **Tail bound direction.**  Inequality `(9)` bounds modulus of full tail, so it controls negative
   real part without assuming transform is real.  Equality at `q=1/2` is harmless: witness has
   strict negative real part whereas tail result is nonnegative.
5. **No decay conclusion.**  Result controls sign on one compact positive interval, not magnitude
   as `x` tends to zero.  It does not prove Liflandsky's half-power bound or Mellin continuation.
6. **Complex versus real zero.**  Intermediate value theorem initially yields zero of real part.
   Separate absolute-sum argument proves imaginary part vanishes at every positive real scale, so
   resulting point is genuine zero of complex-valued transform.
7. **No concealed computation.**  Constants follow from exact rational inequalities, geometric
   majorization, factorization `(7)`, and monotonicity/continuity.

## Literature collision audit

Liflandsky's July 2026 paper defines the same discrete Möbius--Laplace transform and develops its
explicit formula and RH criterion, but its v2 text contains no Lambert renewal identity,
divisibility-restricted dilation law, forced negative-value theorem, explicit strict-negativity
interval, or positive-axis generating-function zero bracket.  Searches for exact transform
together with `negative interval`, `negative values`, `sign changes`, `dilation sum`, `real zero`,
and `generating function zero` found no matching statement.  Classical Lambert identity explains
`(4)` abstractly, so priority remains unverified; scientific claim is limited to concrete
all-fine-lattices theorem `(1)`, explicit base-scale interval `(2)`, and noncomputational zero
bracket `(3)`.

Primary source checked:

- S. Liflandsky, [*Explicit formula for the discrete Laplace transform of the Möbius function,
  related special functions, and a criterion for the Riemann hypothesis*](https://arxiv.org/abs/2607.09797),
  v2, 14 July 2026.

## Lean realization

The formal module proves:

```text
pnatMulEquivDvd
mobiusDiscreteLaplaceTransform_im_eq_zero
tsum_pnat_mobiusDiscreteLaplaceTransform_dvd
exists_mobiusDiscreteLaplaceTransform_dilate_re_pos
mobiusLaplaceTwoThreeFreeDilationSum
mobiusLaplaceTwoThreeFreeDilationSum_eq
mobiusLaplacePrimeDivisibilityCell00_two_three_neg
mobiusLaplaceTwoThreeFreeDilationSum_re_neg
exists_twoThreeFree_mobiusDiscreteLaplaceTransform_re_neg
mobiusDiscreteLaplaceTransform_re_ge_firstAtom_sub_geometricTail
mobiusDiscreteLaplaceTransform_re_nonneg_of_log_two_le
mobiusDiscreteLaplaceTransform_re_pos_of_log_two_lt
exists_twoThreeFree_mobiusDiscreteLaplaceTransform_re_neg_bounded
log_two_div_five_lt_log_four_thirds
mobiusDiscreteLaplaceTransform_re_neg_on_explicit_interval
mobiusDiscreteLaplaceTransform_re_neg_at_log_two_div_five
exists_mobiusDiscreteLaplaceTransform_pos_real_zero
exists_mobiusDiscreteLaplaceTransform_zero_with_exp_in_rational_interval
```

The proof uses no project axiom and no numerical certificate.

## Frontier consequence

These theorems rule out every proposed proof of half-plane control that postulates nonnegativity of
Möbius--Laplace transform on all positive dilates, even after deleting two smallest prime
divisibility sectors.  They additionally give exact compact interval where source transform itself
is strictly negative.  The paper-proved successor
`../../2-fully-proven/new_scientific_knowledge/mobius-laplace-landau-subcritical-oscillation.md`
now supplies cofinal two-sided excursions and infinitely many positive-axis zeros accumulating at
`0`: for every `epsilon>0`, every subcritical normalization
`x^(1/2-epsilon) Phi(x)` is unbounded in both signs.  Successful decay proof must still exploit
cancellation quantitatively; this lower oscillation law does not give sharp half-power upper
control.

## Gates

- [x] exact multiple-index reindexing
- [x] exact `2`--`3` inclusion--exclusion identity
- [x] explicit strict negative interval
- [x] negative summand extracted from absolute convergence
- [x] first-atom tail dominance beyond `log 2`
- [x] witness isolated to `k=1` on nonempty exact interval
- [x] explicit witness bound `k<log(2)/x`
- [x] positive value on every positive dilation lattice
- [x] genuine positive-axis transform zero in fixed exact bracket
- [x] equivalent rational `q`-interval for ordinary generating-function zero
- [x] Lean formalization
- [ ] independent priority audit by a specialist
- [x] cofinal zero-edge sign and subcritical amplitude control (paper)
- [ ] sharp half-power amplitude control
- [ ] half-power decay or Mellin wall
- [ ] RH
