# Remove damping uniformly on cofactor rectangles

- **ID:** twin-prime-cofactor-damping-removal
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / BRIDGE
- **Source:** [nonunit cofactor dispersion](../1-in-progress/twin-prime-nonunit-cofactor-dispersion.md).
- **Statement:** On every cofactor rectangle `ZW<=X`, the damped and undamped shifted correlations differ by at most `6 epsilon (1+log(X+2))^5` after normalization by `X`.

## Exact objects and domains

Let `X,Z,W` be positive integers, `Z,W>=2`, `ZW<=X`, and
`epsilon>0`. Put `H=1+log(X+2)` and

`V_(epsilon,Z)(n)
 = sum_(dm=n, 2<=m<=Z) mu(d)d^(-epsilon)(1-m^(-epsilon))/epsilon`,

`V_(0,Z)^log(n)=sum_(dm=n, 2<=m<=Z) mu(d) log m`,

`L_Z(n)=sum_(m|n, 2<=m<=Z) log m`.

The superscript distinguishes the logarithmic extension from
Lean's totalized expression at `epsilon=0`, whose value is zero.
Every sum is finite. The correlation can be restricted to odd
`n` throughout; all majorants below remain valid on that subset.

## Complete paper proof

### Coefficient deformation

For `d,m>=1` and `dm=n`,

`d^(-epsilon)(1-m^(-epsilon))/epsilon
 = integral_(0 to log m) exp(-epsilon(log d+t)) dt`.

On this integration interval, `0<=log d+t<=log n`. The elementary
inequality `0<=1-exp(-u)<=u` for `u>=0` therefore gives

`0<=log m-d^(-epsilon)(1-m^(-epsilon))/epsilon
 <=epsilon log n log m`.

Using `|mu(d)|<=1`, obtain

`|V_(epsilon,Z)(n)-V_(0,Z)^log(n)|<=epsilon log n L_Z(n)`

and `|V_(epsilon,Z)(n)|,|V_(0,Z)^log(n)|<=L_Z(n)`.
The product difference identity consequently gives, for `2<=n<=X`,

`|V_(epsilon,Z)(n)V_(epsilon,W)(n+2)
 -V_(0,Z)^log(n)V_(0,W)^log(n+2)|
 <=2 epsilon log(X+2) L_Z(n)L_W(n+2)`.

### The arithmetic count and its complete endpoint error

For positive `m,k`, write
`N_X(m,k)=#{2<=n<=X:m|n, k|n+2}`. If this set is nonempty,
`g=gcd(m,k)` divides `2`, so `g<=2`. All solutions lie in one
residue class modulo `lcm(m,k)=mk/g`. An interval of at most
`X` consecutive integers contains at most `X/lcm(m,k)+1`
members of that class. Thus, also when the set is empty,

`N_X(m,k)<=2X/(mk)+1`.

This pays the full physical endpoint error; no period-limit or
analytic distribution statement is used. Expanding the two
nonnegative divisor sums gives

`sum_(2<=n<=X) L_Z(n)L_W(n+2)
 <=2X (sum_(2<=m<=Z) log(m)/m)(sum_(2<=k<=W) log(k)/k)
   +(sum_(2<=m<=Z) log m)(sum_(2<=k<=W) log k)`.

For every integer `R>=2`, the decreasing-function integral bound
`sum_(1<=j<=R)1/j<=1+log R` follows from
`1/j<=integral_(j-1 to j)1/t dt` for `j>=2`. Hence

`sum_(2<=m<=R)log(m)/m<=log R(1+log R)`,
`sum_(2<=m<=R)log m<=R log R`.

Since `ZW<=X`, both cutoffs are at most `X`. Also `H>=1`.
The last displayed correlation majorant is therefore at most

`2X H^4+ZW H^2<=3X H^4`.

### Assembly

Sum the coefficient-deformation bound and divide by `X`. It yields

`(1/X) |sum_(2<=n<=X)
 [V_(epsilon,Z)(n)V_(epsilon,W)(n+2)
  -V_(0,Z)^log(n)V_(0,W)^log(n+2)]|
 <=6 epsilon H^5`.

The same estimate holds on the odd carrier. It is uniform over
the entire rectangle range, not just fixed cofactors.

Choose the explicit positive schedule `epsilon_X=H^(-6)`.
The error is at most `6/H`, which tends to zero. Independently,
the already-proved full-source diagonal estimate has error at
most `epsilon_X log^3(X+2)<=H^(-3)`. Thus this faster schedule
still resolves the actual prime-pair observable, with the same
squarefree projection as the existing Lean diagonal theorem.

## What this resolves

The short-cofactor research target may be formulated entirely
with the undamped row `mu*(log restricted to [2,Z])`. Moving
damping no longer belongs to its arithmetic input. The original
`log^(-4)` schedule was sufficient for the complete source but
does not make this particular absolute majorant tend to zero;
that does not refute cancellation on the original schedule.
The goal does not fix a schedule, so the faster one is admissible.

This deduction supplies no signed correlation saving. The
undamped row and the mixed/long-cofactor terms remain open.
Verdict **BRIDGE**, no scientific novelty claim.

## Dependency audit and formalization

Corpus search preceded source inspection. The checked joint-window
count in `PolynomialWindowTranslatedMomentTransfer.lean` proves
the residue-class counting mechanism, including its endpoint
error. The count above also uses only the elementary gap-two
compatibility `gcd(m,k)|2`. No external analytic theorem is needed.

The public Lean statement should parametrize the geometric
domain directly, for example `X=(Z+2)(W+2)+N`, and use the
explicit positive schedule. No analytic hypothesis is to be added.

- [x] Exact domains, complete paper proof and endpoint costs.
- [x] The faster schedule still resolves the original observable.
- [ ] Unconditional Lean certificate and axiom audit.
- [ ] Integrate with the nonunit cofactor target.

## Log

- 2026-10-23 — Previous goal turn classified **progress**: exact
  compensations and the full-height boundary were certified.
  This calculation removes moving damping from the next analytic
  target without assuming cancellation of either Möbius row.
