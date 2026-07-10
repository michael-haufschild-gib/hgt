# Affine collapse and order-filtration boundary of the scalar weld

- **ID:** weld-affine-coefficient-collapse
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ROUTE NO-GO / FILTRATION OBSTRUCTION, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `../../3-formalized/weld-class-table.md`,
  `xi-theta-boundary-coboundary-no-go.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/WeldAffineTrivialization.lean`,
  `formal/GaloisForLFunctions/RHTower/WeldOrderFiltration.lean`,
  `formal/GaloisForLFunctions/RHTower/WeldBoundedSpectralGauge.lean`
- **Statement:** `[PROVED]` The scalar weld becomes exact in the minimal affine operator
  coefficients, and its explicit primitive remains covariant under the genuine functional-equation
  involution.  The weld therefore does not survive by FE symmetry alone.  It is instead the
  connecting boundary of the differential-order filtration and is nonzero modulo order-zero gauge;
  bounded realization on the fixed spectral `L²` forces precisely that gauge condition.

## Constraint

For the fixed Euler multiplier `M_p f(s)=p^(-s)f(s)` and archimedean derivation `D`,

`M_p^(-1) D M_p = D - log(p) I`.                                      (1)

The abstract class `weldClassHom(log p)` is nonzero with trivial scalar coefficients.  The actual
operator identity lives in the affine span `<D,I>`, where prime conjugation is nontrivial.  The
question is not merely whether the class is nonzero, but in which gauge category it is nonzero.

## The minimal affine coefficient module

Let `g=(m,n) in Z^2` and let `A=R D direct-sum R I`, with

`g . (aD+bI) = aD + (b-a n theta)I`.

For

`omega_theta(g,h)=theta m_g n_h`,

the scalar inclusion is `i_theta(r)=rI` and the affine one-cochain is

`b_theta(g)=m_g D-theta m_g n_g I`.

## Theorem A `[PROVED]`: absolute affine collapse

For every real `theta`,

`delta b_theta(g,h)=omega_theta(g,h) I`.                              (2)

### Proof

Write `g=(m,n)` and `h=(r,s)`.  Then

`g . b_theta(h)=rD+(-theta r s-theta r n)I`,

while

`b_theta(gh)=(m+r)D-theta(m+r)(n+s)I`.

Substitution in the coboundary cancels the derivation coordinate and every scalar term except
`theta m s`.  This is (2).  Therefore, for `theta != 0`,

`[omega_theta] != 0 in H^2(WeldGroup;R_trivial)`,

but

`[i_theta omega_theta] = 0 in H^2(WeldGroup;<D,I>_affine)`.

At a prime, `theta=log p != 0`.

## Theorem B `[PROVED]`: the affine action is forced by the fixed operators

For every positive integer `p`, every complex-differentiable `f`, and every `s`,

`p^s D(p^(-s)f)(s)-Df(s) = -log(p)f(s)`.                              (3)

The product rule gives the commutator identity, and multiplication by `p^s` gives (3).  Thus the
coefficient enlargement is the smallest span containing `D` and `I` closed under the concrete
prime conjugation; it was not chosen to manufacture exactness.

## Theorem C `[PROVED]`: every primitive has nonzero principal symbol

Assume `theta != 0`.  Every affine cochain `b` satisfying

`delta b=i_theta omega_theta`

obeys

`D-coefficient of b(partial)=1`.                                     (4)

### Proof

Evaluate the coboundary identity on `(partial,sigma)` and `(sigma,partial)`.  The group labels
commute.  Subtracting the scalar-coordinate equations cancels the common product value and all
order-zero terms.  Conjugation by `sigma` shifts `aD+cI` by `-a theta I`, whereas the cocycle
antisymmetry is `theta`.  Hence `theta*a=theta`; cancellation gives (4).

This proves that the derivation term in `b_theta` is forced, not a gauge choice.

## Theorem D `[FALSIFIED]`: functional-equation symmetry does not restore the class

The first candidate imposed coefficient reflection pointwise and concluded that a primitive could
not contain `D`.  That is not the functional equation because reflection acts on generator labels
as well as coefficients.

The genuine involution is

`tau(m,n)=(-m,-n)` and `R(aD+bI)=-aD+bI`.                             (5)

Here `D` reverses under `s -> 1-s`, and

`R M_p R = p^(-1) M_p^(-1)`,

so the noncentral weld label of the Euler multiplier also inverts.  A cochain is FE-covariant when

`R b(g)=b(tau g)`.

But

`b_theta(-m,-n)=(-m)D-theta m n I=R b_theta(m,n)`.                    (6)

Therefore the same primitive proving absolute exactness is genuinely FE-covariant.  The proposed
FE-relative class is zero.  The pointwise-fixed quotient was an invalid promotion and is retired.

## Theorem E `[PROVED]`: the weld is the order-filtration connecting boundary

Let the principal symbol be

`q(aD+bI)=a`.

Then the equivariant coefficient sequence

`0 -> R I --i_theta--> R D direct-sum R I --q--> R sigma(D) -> 0`     (7)

is exact.  Let

`ell(m,n)=m`.

The map `ell` is an additive one-cocycle, `q(b_theta(g))=ell(g)`, and (2) says that the boundary of
this lift is `i_theta omega_theta`.  Thus the scalar weld is precisely the connecting class of (7).

Define order-zero gauge cochains by `q(b(g))=0` for every `g`, and quotient closed affine
two-cochains only by coboundaries of such cochains.  For `theta != 0`, the weld class in this quotient
is nonzero: a vanishing class would supply an order-zero primitive, contradicting (4).  At every
prime rate, the scalar class is therefore:

- nonzero with scalar/order-zero coefficients;
- zero under arbitrary affine gauge;
- still zero under genuine FE-covariant affine gauge;
- nonzero under order-zero affine gauge.

This is a fixed filtration statement.  It builds no carrier and propagates no data.

## Theorem F `[PROVED]`: bounded spectral realization forces order zero

Let `H=L^2(R)` be the fixed critical-line spectral space and let `X` be coordinate multiplication,
the Fourier-side realization of the derivation direction.  For each natural `N`, set

`u_N=1_[N,N+1]` and `v_N=Xu_N=x 1_[N,N+1]`.

The interval has measure one, so `||u_N||_2=1`; pointwise on its support, `|x|>=N`, hence

`||v_N||_2>=N`.                                                       (8)

There is therefore no bounded operator `T` with `T u_N=v_N` for every `N`: boundedness would give
`N<=||T||` for every natural `N`.

More generally, suppose a bounded operator agrees with `aX+bI` on all `u_N`.  If `a!=0`, then the
bounded operator

`a^(-1)(T-bI)`

agrees with `X` on every `u_N`, contradicting (8).  Thus `a=0`.

This discharges the algebraic order-zero admissibility condition for bounded affine cochains on the
fixed spectral space: every data-bearing bounded realization of a cochain `b(g)=a_gD+c_gI` forces
`a_g=0` for every `g`.  Combining this with Theorem C gives, for every `theta!=0`,

`there is no bounded spectral affine primitive of omega_theta`.       (9)

In particular (9) holds at every prime rate `theta=log p`.  The escaping interval packets are only
test vectors proving unboundedness; they transport no datum and define no carrier.

## Attack and self-judgment

- `[DEGENERATE]` At `theta=0`, the cocycle and every version of the obstruction vanish.
- `[SURVIVES ARTIFICIAL-MODULE ATTACK]` Equation (3) forces the affine module.
- `[SURVIVES TYPE CHECK]` Both the scalar inclusion and principal symbol are equivariant, and (7) is
  formalized as an exact sequence.
- `[FALSIFIED FE ROUTE]` FE covariance admits the explicit primitive.  Completion symmetry alone
  contributes no surviving class here.
- `[SURVIVES PRIMITIVE-GAUGE ATTACK]` Every affine primitive has principal symbol one at `partial`.
- `[SURVIVES BOUNDEDNESS ATTACK]` On the fixed spectral `L^2`, every bounded realization of
  `aD+bI` has `a=0`; hence no bounded affine weld primitive exists at a nonzero rate.
- `[SURVIVES FLOW TEST]` The surviving statement is the connecting boundary of a fixed operator-order
  filtration, not a contour, orbit, window, depth, or carrier family.
- `[LIMIT DISCHARGED NEGATIVELY]` `weld-class-determines-area-not-j.md` proves that a weld class
  cannot naturally induce `J`, and that its positive local metric cannot produce an indefinite seam
  form by congruence pullback.

## Open core

The external `ClassInducesJ` relation is now retired as a mathematical target.  The class canonically
determines its alternating area form, while `J` must come from independent completed structure.  The
positive prime weld block is also too definite to generate an off-line Krein direction by pullback.

`weld-class-determines-area-not-j.md` also constructs the missing local indefinite operation: FE
coefficient reflection is anti-symplectic, and twisting the weld area by it gives exactly the
one-pair factored Krein hyperbolic block.

> `[OPEN CORE]` Construct the fixed arithmetic incidence map assembling these canonical prime-rate
> hyperbolic blocks from the completed FE divisor, and prove that its Gram is the existing global
> `factoredKreinForm`.  No carrier, evolution parameter, arbitrary pair selection, or external
> relation is allowed.

## Novelty and significance gates

- **NOVEL:** The scalar weld class, operator commutator, and FE parity were banked separately.  The
  new comparison falsifies their expected FE-relative combination and identifies the class instead
  as the explicit connecting boundary of the operator-order extension (7), with bounded spectral
  realizability proved to force the surviving gauge category.
- **SIGNIFICANT:** The result states exactly which fixed categorical restriction can preserve the
  weld: not completion or FE covariance, but boundedness, which excludes positive-order gauge.  It
  removes the order-zero admissibility Prop; the follow-on no-go identifies the remaining target as
  a non-split indefinite extension rather than a class-to-`J` map.

## Gates

- [x] 0 -> 1: coefficient action, genuine FE action, principal symbol, and degeneracy stated.
- [x] 1 -> 2: affine collapse, operator identity, primitive rigidity, FE-covariant collapse, exact
  filtration, connecting-boundary formula, order-zero nontriviality, and bounded spectral exclusion
  proved.
- [x] 2 -> 3: theorem families formalized in Lean.
- [ ] 3 -> 4: completed prime-log/divisor incidence map and global factored-Krein identity.
