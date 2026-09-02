# Steinberg--Kummer cofinal splitting blowup

- **ID:** `ULF-SKSB-1`
- **Stage:** 2-fully-proven
- **Type:** unconditional quantitative theorem / diagonal-completion no-go
- **Lean:** not started; current pass audits Lean without writing or building it

## 1. Big-picture interpretation

`ULF-SKJS-1` says every complementary Steinberg cell is algebraically resolved by its first two
Kummer jets.  This theorem asks the question local algebra misses: can those resolutions be split
with one uniform source norm along the actual successor family?

No.  The augmentation of the second jet is `2 log(x_m) log(y_m)`, and it tends to zero.  Every
right inverse must divide by this scalar.  Local exactness therefore becomes cofinally
ill-conditioned.  The actual obstruction is not homology; it is loss of a uniform nullhomotopy.

## 2. Actual family and norm

For `m>=1`, put

`x_m = 3^m/(2^m+3^m)`,

`y_m = 2^m/(2^m+3^m)`.

Then `x_m+y_m=1`.  In the complex group algebra of positive rational scalings, put

`X_m=[x_m]`, `Y_m=[y_m]`,

`c_m=(X_m-1)(Y_m-1)`.

Let `D([q])=log(q)[q]` be the Kummer derivation and let `epsilon` be augmentation.  Give the finite
group algebra its coefficient `ell^1` norm.  Then `|epsilon(u)|<=||u||_1`.

## 3. Augmentation Hessian

Write `A_m=log x_m` and `B_m=log y_m`.  The calculation in `ULF-SKJS-1` gives

`epsilon(c_m)=0`,

`epsilon(Dc_m)=0`,

`epsilon(D^2c_m)=2 A_m B_m`.

### Theorem SKSB-1 — unavoidable inverse cost

If `u_0,u_1,u_2` satisfy

`u_0 c_m + u_1 Dc_m + u_2 D^2c_m = 1`,

then

`||u_2||_1 >= 1/(2 |A_m B_m|)`.

#### Proof

Apply augmentation.  Since it is an algebra map,

`epsilon(u_2) 2 A_m B_m=1`.

Both logarithms are nonzero, so

`|epsilon(u_2)|=1/(2|A_mB_m|)`.

Contractivity of augmentation gives the result.  QED.

## 4. Cofinal divergence

Put `r=2/3` and `L=log(3/2)>0`.  Then

`x_m=1/(1+r^m)`,

`y_m=r^m/(1+r^m)`.

Therefore

`|A_m|=log(1+r^m)<=r^m`,

`|B_m|=mL+log(1+r^m)<=mL+r^m`.

Hence

`|A_mB_m| <= r^m(mL+r^m) -> 0`.

### Corollary SKSB-2 — no diagonal uniformly bounded splitting

For any family of right inverses `S_m` of

`(u_0,u_1,u_2) |-> u_0c_m+u_1Dc_m+u_2D^2c_m`,

their operator norms are unbounded.  More precisely, the norm of `S_m(1)` is at least

`1/(2 r^m(mL+r^m))`.

Thus no cellwise/diagonal completion can turn local second-jet exactness into a bounded common
source resolution.

## 5. Fusion with current corpus

This lower bound is the algebraic source of three already formalized shadows.

1. The actual Steinberg half-density sources tend to zero while their selected images tend to a
   nonzero vector, forcing operator-norm blowup.
2. The signed completion route requires at least linear condition-number growth to screen an Xi
   divisor charge.
3. The prime-log lattice has no positive uniform spectral gap, although every local Tate circle is
   gapped.

It also predicts the fresh finite-jet result: adding any fixed number of bounded/nuclear observer
jets cannot repair a vanishing source Hessian.

## 6. No-go closure and positive survivor

- **Exact killing mechanism:** augmentation evaluates every local right inverse on the collapsing
  scalar `2 log(x_m)log(y_m)`.
- **Strongest positive survivor:** a viable completion must be genuinely off-diagonal.  It must
  couple cells before augmentation so that the induced interaction Hessian has a uniform lower
  frame bound on the quotient by its forced common mode.
- **Further corpus restriction:** the complete coherent Big-Witt cross-pair fibre has zero one-leg
  trace and its closure remains in that trace kernel.  Puncturing one edge recovers the signal but
  breaks complete coherence.  Hence the interaction cannot be an arbitrary graph completion or
  the already known coherent total compensator; it needs a source-canonical asymmetric incidence.

## 7. RH boundary

This theorem does not prove RH.  It converts the missing global law into a sharp quantitative
obligation: construct a pre-divisor cross-cell analysis operator whose common-mode quotient has a
uniform positive lower frame bound and whose functional-equation lift is information-neutral.
Existing formation-Laplacian and bounded-factorization theorems then give the exact RH closure.

## Log

- 2026-09-02 -- proved immediately after SKJS-1 by applying augmentation to every possible
  splitting and auditing the actual cofinal Steinberg family.
