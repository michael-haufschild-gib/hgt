# Guarded Finite-Passport Compact-Open Closure

- **ID:** `guarded-finite-passport-compact-open-closure`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / INFINITE-JET IMAGE BOUNDARY
- **Scientific status:** `[NOVELTY UNVERIFIED]`. The construction is elementary, but the exact
  guarded closure statement and its source-selector consequence require parent-literature audit.
- **Statement:** A periodic real-even order-one entire function with an off-axis zero quartet and
  exact all-order equality of two period-partner completed-flux germs is a compact-open limit of
  aperiodic real-even order-one entire functions with the same quartet and zero-free imaginary
  axis whose partner germs agree to arbitrarily high finite order but are never equal.

## Goal

Classify the boundary between finite completed-flux passports and the infinite source image. The
theorem shows that coefficientwise or compact-open control supplies no positive separation margin:
the missing selector must read global source data at infinity, not merely the analytic germ on
larger and larger compact sets.

## Exact construction

Fix `a>0` and put

`A(z)=cosh(z-a) cosh(z+a)`,

`alpha=a+pi*i/2`,

`Q(z)=(z^2-alpha^2)(z^2-conj(alpha)^2)`.

For `N>=0`, let

`epsilon_N=exp(-(N+1)^2)`,

`P_N(z)=1+epsilon_N Q(z)^(N+1)`,

`F_N(z)=A(z)P_N(z)`.

Then `A` and every `F_N` are entire, real-even, and Schwarz-real. The four points
`{+/-alpha,+/-conj(alpha)}` are simple zeros of all of them. On the imaginary axis,

`A(iy)=|cosh(iy-a)|^2>0`,

`Q(iy)=|y^2+alpha^2|^2>0`,

so `F_N(iy)>0` for every real `y`.

The function `A` has period `pi*i`. Multiplication by the nonconstant polynomial `P_N` destroys
every nonzero period, while preserving exact entire order one.

## Finite contact and full separation

Let

`c=-alpha`, `d=-conj(alpha)=c+pi*i`.

The residue-filled logarithmic-flux germs of `A` at `c` and `d` agree identically because `A` is
`pi*i`-periodic. At both centers, `Q^(N+1)` has order `N+1`. Consequently the two correction germs

`-x P_N'(c+x)/P_N(c+x)` and `-x P_N'(d+x)/P_N(d+x)`

vanish through degree `N`. The completed-flux germs of `F_N` at `c` and `d` therefore have equal
Taylor coefficients in every degree `0<=n<=N`.

They cannot be equal as analytic germs. Equality would cancel the periodic `A` contribution and
give equality of the logarithmic derivatives of `P_N(z)` and `P_N(z+pi*i)`. Hence

`P_N(z+pi*i)=C P_N(z)`

for some nonzero constant `C`. Equality of leading coefficients gives `C=1`, making the
nonconstant polynomial `P_N` periodic, a contradiction.

## Compact-open convergence

For a compact set `K`, put `M_K=max_(z in K)|Q(z)|`. Then

`sup_(z in K)|F_N(z)-A(z)|
 <= sup_(z in K)|A(z)| exp(-(N+1)^2) M_K^(N+1)`.

The logarithm of the final factor is

`-(N+1)^2+(N+1)log M_K -> -infinity`,

with the case `M_K=0` immediate. Thus `F_N -> A` uniformly on every compact subset of `C`.

## Positive source-image consequence

Let `J_N` be the set of guarded aperiodic functions whose two selected partner flux germs agree
through degree `N`. Every `J_N` is nonempty, and the explicit sequence above approaches a guarded
periodic function in the exact all-order locus. Therefore the all-order locus lies on the
compact-open boundary of arbitrarily deep finite-passport realizers.

The source selector must consequently use a nonlocal arithmetic condition that remains meaningful
under the loss of compact-open separation: for example fixed Dirichlet/Bohr coefficients, an exact
prime-power representing distribution, or another condition at infinity. Merely strengthening
finite local convergence or imposing the elementary global guards cannot supply a positive gap.

## Gates

- [x] 0 -> 1: explicit source-pure statement, construction, and boundary interpretation.
- [x] Paper proof written; independent audit still required before stage 2.
- [ ] Parent-theory and literature audit of compact-open density/closure results for symmetric
  exponential-type entire functions.
- [ ] Lean formalization of the explicit family, finite contact, aperiodicity, and compact-open bound.

