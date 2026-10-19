# Additive shifts of the sextic character block

- **ID:** quasi-rh-shift-correlation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE, with a closed algebraic exceptional-set classification
- **Source:** [Fixed-strip task](quasi-rh-fixed-strip-improvement.md)
- **Statement:** Keep the fourth-moment character correlations produced by additive shifts, and separate their exact power degeneracies before completion.

## Arithmetic target

The common-ideal-one specialization of the cached detector's `GramJoint.jointExtension` contains a sextic character in each lattice variable. A pointwise cube-root-conductor block bound would require a scalar bound of shape `N^(1/2) q^(1/6+ε)`. The existing windowed `RHTower.Sieve.weyl_vdc` supplies the shift inequality, but its correlations still require arithmetic estimates. Complete character orthogonality alone does not provide this conductor saving.

For a finite field K and a multiplicative character χ with χ⁶=1, the shifted fourth-moment integrand is

`χ(x−a) χ(x−b) conjugate(χ(x−c) χ(x−d)) = χ(P(x))`,

where `P(X)=(X−a)(X−b)(X−c)^5(X−d)^5`. The equality includes the zeros of the factors: all exponents are positive and multiplicative characters vanish at zero.

## Closed paper proof: exact power degeneracies

More generally, let s,t be multisets of elements of any field, each of cardinality less than m, with m>0. Write `A_s=∏_{a∈s}(X−a)` and `P=A_s A_t^(m−1)`. Then P is an m-th power if and only if s=t.

If `P=Q^m`, the root multiplicity at u is

`count_s(u)+(m−1)count_t(u)=m count_roots(Q)(u)`.

Adding `count_t(u)` and reducing modulo m shows that the two counts are congruent. Both lie in `[0,m)`, so they are equal. This holds at every u, proving s=t. Conversely s=t gives `P=A_s^m`. The argument uses polynomial roots with multiplicity, not equality of the functions induced on a finite field; small field size does not invalidate it.

For m=6 and two shifts on either side, the exact exceptional condition is

`(a=c and b=d) or (a=d and b=c)`.

For a finite shift set S of cardinality H, there are exactly `2H²−H` exceptional ordered quadruples. The two matching graphs each have H² elements, and their intersection is the H tuples `(a,a,a,a)`. Thus the count retains collisions instead of assuming four distinct shifts. The same algebraic classification applies to cubic order at this moment; quadratic order needs a different classification because two repeated roots can already be a square.

## Closed paper proof: cross-ratio reduction

For a finite field K, put

`Cχ(a,b,c,d)=Σ_x χ((x−a)(x−b)/((x−c)(x−d)))`,
`Hχ(λ)=Σ_t χ(t(t−1)/(t−λ))`.

Assume `a≠b`, `a≠d`, `b≠d`, `c≠d`. Set `A=(b−d)/(b−a)`, `B=A(d−a)`, `λ=A(c−a)/(c−d)` and `k=(b−a)/(c−d)`. The permutation `t=A+B/(x−d)` of K has inverse `x=d+B/(t−A)`; the field's total inverse maps zero to zero, so `x=d` corresponds to `t=A`. For `x≠c,d`, direct factorization gives

`(x−a)(x−b)/((x−c)(x−d)) = k t(t−1)/(t−λ)`.

At `x=c` both character arguments vanish. At `x=d` the left argument vanishes and the right equals one. Summation therefore gives the exact identity

`Cχ(a,b,c,d)+1 = χ(k) Hχ(λ)`.

No distinctness between c and a or b is needed. The identity applies to every multiplicative character, not just order six. It retains the exceptional point at infinity; omitting its correction changes the sum. This is a complete-field identity and does not itself control a short interval or an Eisenstein shell.

For a nonprincipal character, the translation Gram kernel is

`Σ_λ conjugate(χ(u−λ)) χ(v−λ) = q·1[u=v]−1`.

Consequently, for `A(t)=χ(t(t−1))`,

`Σ_λ |Hχ(λ)|² = q Σ_t |A(t)|² − |Σ_t A(t)|² ≤ q(q−2)`.

The Gram identity follows by a fractional-linear permutation when u≠v and by counting the q−1 nonzero arguments when u=v. The inequality keeps the nonnegative Jacobi-sum term; it needs no unproved Weil bound. This offers complete-parameter average cancellation. A short-parameter application still needs a source-specific distribution or completion argument.

## Remaining analytic obligations

- Obtain a complete-sum estimate for the non-power sextic polynomials over the actual residue fields. The inspected native Stepanov theorem covers quadratic characters over square-cardinality fields; it is not this estimate.
- Retain the explicit exceptional count in the additive-shift fourth moment, including the coprimality masks at composite moduli.
- Transport the resulting estimate to the actual Eisenstein shell and fixed ray-class weights, with uniform conductor and smoothing costs.
- Check the final exponent before counting it toward `5/6`. An ordinary Burgess saving is weaker than the proposed Weyl-strength block estimate. `3/4` additionally requires changing the actual reflected-source bound.

## Calibration test

`Detector/CalibrationCancellation.calibration_coefficient_cancel` and `SourceCoefficient.sourceHighCoefficient_eq_bare` remove the auxiliary calibration from the normalized coefficient on its supported frequencies. The positive invariant is the explicit `bareSourceCoefficient`; varying calibration phases alone cannot be counted as cancellation in this coefficient. This does not rule out changing the excluded prime set, the detector weights, or bounding a genuinely mixed physical expression, whose support and normalization would need separate proofs.

## Gates

- [x] Dependency-closed paper proof of the power classification and exact exceptional count.
- [ ] Formalize the classification, count, and character integrand identity.
- [ ] Supply a source-applicable nonexceptional correlation estimate.
- [ ] Derive either requested zero strip from unconditional arithmetic estimates.

The algebraic classification is supporting mathematics, not a proof of either strip or a claim of external novelty.
