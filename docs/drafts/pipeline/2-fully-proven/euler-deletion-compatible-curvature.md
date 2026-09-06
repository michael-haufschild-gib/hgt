# Curvature under compatible multiplicative attenuation

- **ID:** EDCC
- **Stage:** 2-fully-proven; also formalized in Lean
- **Type:** THEOREM [PROVED HERE]
- **RH implication:** none established; this tests a proposed repair, not a qualifying RH architecture.

## Exact theorem

Let `b(1)=1`, let `b` be completely multiplicative, and assume `0<b(n)<=1` for
positive integers. Put `L_d=d/b(d)`, `A_d(n)=1-L_d*[d|n]`, and
`W_alpha(n)=b(n)^2*n^(-alpha)`, extended by zero at zero. For `alpha>1` this
mass is summable. Define the actual four-channel coefficient

```
k(n)=A_p(n)*A_q(n)^2+A_(pq)(n)*A_r(n)^2
     -A_q(n)*A_r(n)^2-A_p(n)*A_(qr)(n)^2.
```

For positive pairwise coprime `p,q,r`, the exact formula is

```
sum_n k(n)*W_alpha(n)
 = (sum_n W_alpha(n)) * q*b(q)*q^(-alpha)
   * (1-p*b(p)*p^(-alpha)) * (q/b(q)-1) * (1-r^(2-alpha)).
```

For labels greater than one, this gives the complete sign classification:
negative for `1<alpha<2`, zero at two, positive above two. The boundary two is
**not** the RH critical line: in the squared source `alpha=2*Re(s)` it corresponds
to `Re(s)=1`.

## Dependency-closed proof

Write `Z=sum_n W_alpha(n)` and `B_d=d*b(d)*d^(-alpha)`. The bound
`0<=W_alpha(n)<=n^(-alpha)` proves summability for `alpha>1`; the term at one
proves `Z>0`. Complete multiplicativity and reindexing the multiples as `d*m`
give

```
sum_(d|n) W_alpha(n)=b(d)^2*d^(-alpha)*Z,
sum_n A_d(n)*W_alpha(n)=(1-B_d)*Z.
```

Each first-moment sum is absolutely convergent: it is the difference of the full
mass and a constant times its divisibility subseries. For coprime labels,
`L_(pq)=L_p*L_q`, and the actual indicator coefficients satisfy

```
A_(pq)=A_p+A_q-A_p*A_q,
A_q^2=(L_q-1)+(2-L_q)*A_q.
```

Substitution into the four original channels gives the pointwise identity

```
k=(L_q-1)*(A_(pq)-A_q+L_r*(A_(qr)-A_(pqr))).
```

This also proves absolute summability of `k*W_alpha`. Its sum is
`(L_q-1)*Z*B_q*(1-B_p)*(1-L_r*B_r)`. Finally
`L_r*B_r=r^2*r^(-alpha)=r^(2-alpha)`, proving the displayed formula.

For `p,q,r>1`, every prefactor preceding `1-r^(2-alpha)` is strictly positive:
`Z>0`, `B_q>0`, `B_p<=p^(1-alpha)<1`, and `q/b(q)>1`.
The last factor is negative, zero, or positive according as `alpha` is below,
equal to, or above two. This proves all three signs and the exact zero boundary.

There is a stronger normalized invariant. Whenever `b(p)=b(q)=1`, dividing the
formula by `Z` gives exactly the normalized curvature of the original unattenuated
coefficients. This permits arbitrary changes at the third label and elsewhere
within the stated multiplicative class. In particular, `b(n)=c^(v_5(n))` for
every `0<c<=1` leaves the normalized `2,3,5` curvature exactly unchanged after
the compatible repair.

The fixed example `c=1/5` has deletion multiplier 25 at five. Its actual repaired
curvature is strictly negative at `alpha=3/2`, zero at two, and strictly positive
at three. This is a premise-free exported Lean theorem, derived symbolically;
no numerical experiment or external certificate enters the proof.

## Source-admission scope

The normalization is motivated by the independently proved one-prime admission
classification: changing a prime weight by `c` requires deletion multiplier `p/c`.
No claim is made that every contractive completely multiplicative weight has
bounded deletion prefixes or the same ordinary-convergence domain. Those stronger
claims require separate proofs. The current invariant concerns the displayed
absolutely convergent quadratic mass.

## Failed repair and positive survivor

The attempted repair attenuates the last prime and changes its deletion multiplier
compatibly. The two changes cancel in the decisive factor:
`(r/b(r))*(r*b(r)*r^(-alpha))=r^(2-alpha)`.
Thus the positive survivor is a normalization invariant and full sign
classification, rather than merely a failed numerical example. It supplies no
identity forced by a zeta zero and no exclusion of off-line zeros.

## Corpus and literature audit

Starting sources: `EulerDeletionPrimeAttenuation`,
`EulerDeletionFactorizationGraded`, `EulerDeletionFactorizationCurvature`, and
`EulerDeletionFullEnergyFactorization`, located by corpus search and read through
their actual statements and proof bodies. Searches for normalization,
multiplicative curvature, and deletion gauge did not identify this generalization;
search absence is not evidence of novelty. The actual parent statements and
proof bodies were inspected with `rg` and bounded file reads.

The underlying divisibility reindexing and coprime independence are classical:
Cranston and Peltzer, [On Properties of the Riemann Zeta Distribution](https://escholarship.org/content/qt4kv3q5r6/supp/r-zeta_072721.pdf),
section 3, equations (5)–(9), explicitly derive the unweighted laws. Their direct
extension to a summable completely multiplicative weight is the same elementary
argument. The particular compatible four-channel invariant was not located in
the searches performed; absence from all literature is **not certified**, and
this elementary generalization is not presented as a new RH architecture.

## Formal status

Module `EulerDeletionCompatibleCurvature`, namespace
`RHTower.DeletionCompatibleCurvature`, proves the actual pointwise linearization,
infinite reindexing, summability, factorization, strict signs, exact zero boundary,
normalized invariant, all positive fifth-prime attenuations, and fixed closed
example. [Build and axiom certificate](../3-formalized/euler-deletion-compatible-curvature.md).
