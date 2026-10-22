# Connes--Consani arithmetic-Jacobian prime fibre

## Claim labels

- `LITERATURE (Connes--Consani 2026, Theorem 1.3 / Proposition 7.3)`: for a rational
  prime `p`, the universal fibre over the periodic orbit is the mapping torus
  `(K^(p) x R)/((u,t) ~ (p u,t+log p))` and inherits a topological group structure.
- `NEW`: the canonical map from this twisted mapping torus to
  `(K^(p)/closure(<p>)) x (R/(log p)Z)` is surjective but not injective.
- `NEW NO-GO`: quotienting Frobenius before suspension cannot model the universal fibre; it
  erases the nonzero horizontal Frobenius class.

## Dependency-closed paper proof

Put `K^(p) = product_(l != p) Z_l^x`, `f_p = (p)_l`, `T = log p`, and use additive
notation on `K^(p)`.  In `G_p = Add(K^(p)) x R`, let `d_p = (f_p,T)`.  The mapping
torus is the additive quotient `G_p / Z d_p`; hence quotient addition, inverse, and quotient
topology give its canonical topological abelian group structure.  Since `d_p` vanishes in the
quotient, `[u,t]=[f_p^n u,t+nT]`, giving the stated Frobenius monodromy.

Let `H_p=closure(<f_p>)`.  The product of the quotient maps
`G_p -> Add(K^(p)/H_p) x (R/TZ)` kills `d_p`, so it descends to the mapping torus.
Both coordinate quotient maps are onto, hence the descended map is onto.  Its value on
`[(f_p,0)]` is zero.  This class is nonzero: if `(f_p,0)=n(f_p,T)`, the second coordinate and
`T>0` force `n=0`, while the first coordinate would force `f_p=1`; the diagonal prime is not
one in the away-prime local-unit product.  Therefore the descended map is not injective.

## Formal status

Formalized and target-built:

- `CCMConnesConsaniArithmeticJacobianPrimeFibre.lean`: literal prime mapping torus, Frobenius deck relation, and proof that the older quotient-product candidate is a proper non-injective receiver.
- `CCMConnesConsaniZetaCycleCompletedXiNaturality.lean`: exact zeta-cycle/completed-Xi spectral-fiber comparison, prime-cover fiber equivalence, and dyadic Big-Witt/prime-cover naturality.

All capstones are closed. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Open core after formalisation

Construct a global map from the full adelic arithmetic-Jacobian source into the completed-Xi
cohomological receiver. It must retain the nonzero horizontal Frobenius class and therefore cannot
factor through the collapsed quotient-product candidate. At the proven spectral level, prime covers
preserve the centered Xi label exactly; they do not induce `alpha -> p * alpha`.
