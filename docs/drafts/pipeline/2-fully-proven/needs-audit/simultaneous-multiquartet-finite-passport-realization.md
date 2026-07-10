# Simultaneous Multi-Quartet Finite-Passport Realization

- **ID:** `simultaneous-multiquartet-finite-passport-realization`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / POSITIVE SIMULTANEOUS REALIZATION
- **Date:** 2026-07-11
- **Scientific status:** `[NOVELTY UNVERIFIED]`.  The theorem strictly strengthens the one-quartet
  finite-jet realization by imposing independently chosen finite contact depths at arbitrarily many
  off-line quartets in one exact-order-one function.  Its ingredients are elementary entire-function
  theory and simultaneous Hermite-flat multiplication, so scientific novelty remains provisional
  pending a broad literature audit and independent proof review.
- **Statement:** Given any nonempty finite list of jet depths, there is a real even, aperiodic entire
  function of exact order one whose critical-strip normalization has a zero-free real axis, contains
  one off-critical zero quartet for every listed depth, and at each quartet has identical
  functional-equation/Schwarz completed-flux jets through the prescribed depth but unequal full germs.

## Positive theorem

Let `r >= 1` and let `N_1,...,N_r` be nonnegative integers.  There is an entire function

`X : C -> C`

with the following properties.

1. `X(1-s)=X(s)` and `X(conj s)=conj(X(s))`.
2. `X` has exact entire order one and no nonzero period.
3. `X(t) != 0` for every real `t`.
4. There are pairwise distinct positive heights `a_1,...,a_r` such that all four points

   `1/4 +/- i a_j` and `3/4 +/- i a_j`

   are simple zeros of `X`.
5. For `rho_j=1/4+i a_j`, let `G_w^X` denote the residue-filled negative logarithmic-flux germ

   `G_w^X(x)=-1` at `x=0` and
   `G_w^X(x)=-x X'(w+x)/X(w+x)` away from `0`.

   Then

   `[x^n] G_(1-rho_j)^X = [x^n] G_(conj rho_j)^X` for every `0 <= n <= N_j`,

   but the two analytic germs are not equal.

Thus any finite collection of finite completed-flux passports at finitely many tested zeros is
simultaneously compatible with arbitrarily many off-critical quartets, even inside the real-even,
zero-free-real-axis, exact-order-one, aperiodic envelope.

## Construction

Choose distinct positive real numbers `a_1,...,a_r` and put

`b=1/4`, `lambda=pi/(2b)=2pi`, `alpha_j=a_j+i b`, `M_j=N_j+1`.

Define the periodic base

`B(z)=prod_j cosh(lambda(z-a_j)) cosh(lambda(z+a_j))`.

For each `j`, set

`Q_j(z)=(z^2-alpha_j^2)(z^2-conj(alpha_j)^2)`

and define the simultaneous flat multiplier

`R(z)=prod_j Q_j(z)^(M_j)`, `P(z)=1+R(z)`, `F(z)=B(z)P(z)`.

Finally put

`X(s)=F(-i(s-1/2))`.

The polynomial `P` is real and even.  The function `B` is real and even, and has period `2ib=i/2`.
Consequently `F` is real and even, which gives the two displayed symmetries of `X`.

## Quartet zeros and simultaneous flatness

The zeros of the first shifted `cosh` factor at `alpha_j` are simple because

`lambda(alpha_j-a_j)=i pi/2`,

while the companion factor is nonzero there.  Distinctness of the positive `a_j` shows that no
factor indexed by `k != j` vanishes at any of

`+/- alpha_j`, `+/- conj(alpha_j)`.

Hence these four points are simple zeros of `B`.  At each of them `Q_j=0`, so `R=0` and `P=1`;
they remain simple zeros of `F`.  Under `s=1/2+i z`, they become exactly

`1/4 +/- i a_j`, `3/4 +/- i a_j`.

Fix `j` and write

`c_j=-alpha_j`, `d_j=-conj(alpha_j)=c_j+2ib`.

These are the `z`-coordinates of `1-rho_j` and `conj rho_j`.  Since `B` has period `2ib`, its
residue-filled logarithmic-flux germs at `c_j` and `d_j` agree identically.

At both centers, `R` has exact vanishing order `M_j`: the `j`-th factor supplies that order and all
other factors are nonzero.  Therefore

`-x P'(c_j+x)/P(c_j+x)` and `-x P'(d_j+x)/P(d_j+x)`

both vanish to order at least `M_j=N_j+1`.  Adding these corrections to the equal base germs proves
equality of the two completed-flux Taylor coefficients through order `N_j`.  This holds
simultaneously for every `j`, with independently prescribed depths.

## Full-germ separation

Suppose the two completed-flux germs at `c_j` and `d_j` were equal.  The periodic base terms cancel,
so on a punctured neighborhood of zero

`P'(c_j+x)/P(c_j+x)=P'(d_j+x)/P(d_j+x)`.

Cross multiplication and the polynomial identity theorem give

`P'(z+2ib)P(z)=P(z+2ib)P'(z)`

for every `z`.  Thus `P(z+2ib)/P(z)` is constant away from the finite zero set and hence

`P(z+2ib)=C P(z)`

as a polynomial identity.  Equality of leading coefficients gives `C=1`.  A polynomial with a
nonzero period is constant, whereas `P=1+R` is nonconstant.  This contradiction proves that every
partner pair has unequal full germs.  Analyticity then supplies a finite, possibly depth-dependent,
first separating order beyond `N_j`.

## Zero-free real axis

For real `s`, the `z`-coordinate is purely imaginary, say `z=iy`.  Each shifted `cosh` factor is
nonzero there: its argument has nonzero real part `+/- lambda a_j`.  Moreover

`Q_j(iy)=(-y^2-alpha_j^2)(-y^2-conj(alpha_j)^2)=|y^2+alpha_j^2|^2>0`,

because `Im(alpha_j^2)=2a_jb != 0`.  Hence `R(iy)>0` and `P(iy)=1+R(iy)>1`.  Therefore

`X(s)=F(iy) != 0`

for every real `s`.

## Exact order one

The finite product `B` is an exponential polynomial of order at most one.  Along the positive real
axis its leading exponential is nonzero and grows like `exp(2 r lambda x)`, so its order is exactly
one.  Multiplication by the nonzero polynomial `P` preserves exact order one.  The affine change of
variable from `F` to `X` preserves entire order.

## Aperiodicity

Assume `h` is a period of `F`.  The zero set of `P` is finite, while for each `j` the base contributes
the two infinite arithmetic zero lines

`+/- a_j + ib(2k+1)`, `k in Z`.

All but finitely many translates of these zeros must again be zeros of `B`.  Iterating the period
shows first that `Re h=0`, since the finite set of real parts `{+/-a_j}` cannot contain an unbounded
arithmetic progression.  The common imaginary residue class of the base zeros then gives

`Im h in 2b Z`.

Thus `h` is a period of `B`.  From `F(z+h)=F(z)` and `B(z+h)=B(z)`, cancellation away from the
discrete zero set and the identity theorem give `P(z+h)=P(z)`.  A nonconstant polynomial has no
nonzero period, so `h=0`.  Hence `F`, and therefore `X`, is aperiodic.

## Attack and boundary cases

- `r=1` recovers the logical content of the existing one-quartet theorem, without needing its
  explicit first escape coefficient.
- Depth zero is allowed: `M_j=1`, so equality of the residue value is retained while a later
  coefficient separates.
- The common offset `b=1/4` puts the selected quartets strictly inside the critical strip and makes
  all other zeros of the periodic base lie outside that strip.  The polynomial multiplier may add
  further nonreal zeros, but never a real one.
- The theorem deliberately controls finitely many tested zeros.  It does not construct an infinite
  family with unbounded prescribed depths inside one function.
- The result does not imitate the Euler product or the arithmetic coefficients of `xi`.  Its force is
  exactly that every successful finite multi-zero passport must consume a genuinely global arithmetic
  source constraint absent from this entire-function envelope.

## RH-route consequence

This is a positive realization theorem, not merely an impossibility statement.  It identifies the
shape of the surviving RH constraint:

> A source-native selector must couple infinitely much Euler information to the zero divisor, or impose
> a global relation across infinitely many completed-flux orders.  Any rule factoring through finitely
> many zeros and finitely many local jet coefficients is realized by an off-critical exact-order-one
> function with all the elementary `xi` symmetries.

The theorem therefore sharpens the open core of `CompletedFluxGradedReality.lean`: the needed law is not
only all-order at one zero; it must resist simultaneous finite interpolation across every finite zero
packet.

## Parent-theory and novelty gate

- The flat multiplier is a finite Hermite-interpolation mechanism in an even real polynomial ring.
- Exact order, zero-lattice periodicity, and polynomial aperiodicity are classical entire-function
  tools.
- The simultaneous composition with independently prescribed depths, a zero-free real axis,
  exact-order-one growth, FE/Schwarz normalization, and arbitrarily many critical-strip quartets is the
  candidate new statement.
- No scientific-newness claim is made until equivalent simultaneous interpolation theorems and the
  mechanism have been checked broadly in entire-function, Laguerre--Polya, and Hermite-interpolation
  literature.

## Lean certificate: simultaneous local core

`formal/GaloisForLFunctions/RHTower/SimultaneousFiniteJetFlatness.lean` formalizes the reusable local
mechanism behind every selected quartet:

- `hermiteFlatFluxCorrection_eventuallyEq_neg_mul_logDeriv` identifies the factored correction with
  the actual normalized logarithmic derivative of `1+x^M u(x)`;
- `hermiteFlatFluxCorrection_order` proves exact analytic order `M` for every analytic unit `u`;
- `hermiteFlatFluxCorrection_iteratedDeriv_zero` and
  `hermiteFlatFluxCorrection_iteratedDeriv_escape_ne_zero` prove exact finite-prefix flatness and
  eventual escape;
- `hermiteFlatPerturbedGerm_pair_same_prefix` proves that two independent unit factors perturbing one
  analytic base have identical Taylor coefficients at every order below `M`.
- `simultaneousFlatProduct_shift_factorization` extracts the prescribed power at every center of an
  arbitrary finite quartet packet;
- `simultaneousFlatMultiplier_localFluxCorrection_order` proves that the full finite-product
  multiplier has exactly the independently assigned local correction order at each simple disjoint
  quartet.

The exact source check and exact Lake target build pass.  The listed declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  The global `cosh` envelope remains to be formalized,
so the card stays at stage 2.

## Gates

- [x] 0 -> 1: the simultaneous realization was stated positively and attacked at every global guard.
- [x] 1 -> 2: the construction, finite-jet contact, full-germ separation, symmetry, zero-free axis,
  exact order, and aperiodicity have complete paper proofs above.
- [ ] independent audit of the aperiodicity argument and the affine coordinate transfer.
- [ ] 2 -> 3: the simultaneous analytic-unit core and full finite-product instantiation are formalized
  and axiom-audited; the global `cosh` envelope, exact order, zero-free axis, and aperiodicity remain.
- [ ] literature and parent-theory audit sufficient for any scientific-novelty promotion.
