# CCM bounded-variation Muntz graph-domain extension

- **ID:** `ccm-bv-muntz-graph-domain-extension`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** the classical Muntz formula; Connes--Consani, *Spectral triples and
  zeta-cycles*, Lemma 6.1 and the proof of Theorem 6.4; Baez-Duarte and Burnol on `L2` Muntz
  operators
- **Statement:** The global CCM summation vector of a compactly supported bounded-variation source
  with zero integral belongs to `L2(d*u)` and to the maximal zeta-multiplier graph domain, even
  when the source has the endpoint jump created by zero extension. Its Mellin transform vanishes
  at every nontrivial zeta zero.

## Theorem

Let `f:[0,infinity)->C` have compact support in `[0,L]`, let its zero extension have bounded
variation, and suppose

```text
integral_0^infinity f(x) dx=0.                         (1)
```

For `u>0` define the finite sum

```text
E(f)(u)=u^(1/2) sum_(n>=1) f(nu).                     (2)
```

Then, writing `V=Var(f)`,

```text
|E(f)(u)| <= V u^(1/2),
supp E(f) subset (0,L],
||E(f)||_(L2(d*u)) <= V sqrt(L).                      (3)
```

For `Im z>-1/2`, put

```text
Psi_f(z)=integral_0^infinity f(x)x^(1/2-iz)d*x.       (4)
```

Both sides below are holomorphic in that half-plane, after removing the singularity at `z=i/2`,
and

```text
integral_0^infinity E(f)(u)u^(-iz)d*u
  =zeta(1/2-iz) Psi_f(z).                             (5)
```

Consequently `f` lies in the maximal zeta-multiplier graph domain and the Mellin transform of
`E(f)` vanishes at every spectral point

```text
z_rho=i(rho-1/2),   zeta(rho)=0,   0<Re rho<1.        (6)
```

## Proof

Partition the positive half-line into the intervals `((n-1)u,nu]`. On each interval, comparison
with the right-endpoint Riemann sum gives

```text
|u f(nu)-integral_((n-1)u)^(nu) f(x)dx|
  <=u Var_((n-1)u,nu](f).
```

Summing the finite nonzero terms and using `(1)` yields

```text
|sum_(n>=1) f(nu)| <= V.                              (7)
```

Equation `(3)` follows immediately from `(2)`, from the support condition, and from

```text
integral_0^L V^2 u d*u=V^2 L.
```

The bound `(3)` makes the left side of `(5)` holomorphic for `Im z>-1/2`. The same is true of
`Psi_f`: near zero its integrand is bounded by a constant times `x^(-1/2+Im z)dx`, and at infinity
the source is compactly supported. If `Im z>1/2`, absolute convergence permits interchange of the
sum and integral, followed by `x=nu`:

```text
integral E(f)(u)u^(-iz)d*u
 =sum_(n>=1) n^(-1/2+iz)
    integral f(x)x^(1/2-iz)d*x
 =zeta(1/2-iz)Psi_f(z).                               (8)
```

The only pole of the right side in `Im z>-1/2` is the apparent pole at `z=i/2`. But

```text
Psi_f(i/2)=integral_0^infinity f(x)dx=0,
```

so the pole is removable. Analytic continuation proves `(5)` throughout the half-plane.
Equation `(3)` and Mellin--Plancherel show on the real axis that

```text
integral_R |zeta(1/2-it)|^2 |Psi_f(t)|^2 dt<infinity,
```

which is exactly maximal multiplier graph-domain membership. Finally `z_rho` lies in
`-1/2<Im z<1/2`, and substituting it into `(5)` proves `(6)`.

## Application to the CCM prolate source

The CCM seed source `h_lambda` is a linear combination of two smooth prolate eigenfunctions on
`[-lambda,lambda]`, extended by zero outside, and is chosen to have zero integral. Its restriction
to the positive half-line satisfies the theorem. Resetting its value at the single point zero, as
in `ccm-restricted-summation-aperture-gauge.md`, changes neither its `L2` class nor `E(h_lambda)`
almost everywhere.

Thus the endpoint jump does **not** invalidate the global Muntz vector, the zeta-multiplier identity,
or divisor-radical membership. In the zero-side Weil sampling realization, `E(h_lambda)` vanishes
at every nontrivial zeta zero, including hypothetical off-line zeros. Whenever the cut vector and
its exterior tail lie in a common extension of the Weil form domain, the quotient identity in
`ccm-weil-exterior-tail-quotient-gate.md` therefore applies to the genuine prolate source rather
than only to a Schwartz surrogate.

The theorem supplies membership, not the cofinal estimate required by CCM. Its crude lower-tail
bound is only

```text
||1_(0,lambda^(-1)) E(h_lambda)||_2
  <=Var(h_lambda)/sqrt(lambda),                        (9)
```

whereas identification of the true Weil ground vector must be measured relative to the extremely
small constrained spectral gaps. The missing theorem is still a source-specific quantitative
Weil-form/sampling estimate, not mere finiteness of the graph norm.

## Route consequence

- `[CLOSED DOMAIN OBJECTION]` Zero extension of a prolate eigenfunction leaves the Schwartz class,
  but it does not leave the natural `L2` zeta-multiplier domain.
- `[OPEN]` Prove a cofinal rate for its exterior tail in the closed Weil form or discrete sampling
  topology, relative to the fixed-mode gap ladder.
- `[OPEN]` Transfer that rate to the projective ground-vector estimate needed for locally uniform
  determinant convergence.

## Novelty and significance verdict

The proof is a bounded-variation Riemann-sum estimate followed by the classical Muntz identity and
analytic continuation. More decisively, Connes--Consani Lemma 6.1 already proves the same
`O(u^(1/2))` estimate for bounded-variation zero-mean sources satisfying `f(u)=O(u^2)` at zero, and
their proof of Theorem 6.4 supplies the zeta multiplier continuation. The invisible central gauge
in `ccm-restricted-summation-aperture-gauge.md` produces exactly such a representative for the CCM
aperture vector. The present statement only observes that bounded behavior at zero is already
enough if one works with the ungauged source. Baez-Duarte and Burnol also develop substantially more
general `L2` Muntz frameworks. This is a useful route reconciliation, not new scientific knowledge.

## References

- A. Connes, C. Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715.
- L. Baez-Duarte, *A general strong Nyman--Beurling criterion for the Riemann hypothesis*,
  arXiv:math/0505453.
- J.-F. Burnol, *On Fourier and zeta(s)*, Forum Math. 16 (2004), 789--840.

## Lean decision

The formal tree has no Mellin--Plancherel interface for the CCM summation map, no analytic
continuation of the zeta multiplier identity, and no closed Weil sampling domain. Formalizing only
the Riemann-sum inequality would certify a wrapper rather than the route statement. No Lean file is
added.

## Gates

- [x] exact bounded-variation Riemann-sum discrepancy proved
- [x] global `L2(d*u)` membership of the zero-extended prolate summation vector proved
- [x] maximal zeta-multiplier graph-domain membership proved
- [x] vanishing at every nontrivial zeta zero proved
- [ ] cofinal exterior-tail estimate in the closed Weil/sampling topology
- [ ] relative true-Weil ground-vector transfer
- [ ] locally uniform normalized determinant convergence to `Xi`
