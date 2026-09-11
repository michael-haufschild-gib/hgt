# Curvature under compatible multiplicative attenuation

- **ID:** EDCC
- **Stage:** 3-formalized
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
example. the Lean certificate below.

## Lean certificate

**Stage:** 3-formalized. **RH implication:** none. **Novelty:** not certified.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionCompatibleCurvature.lean`.
Namespace: `RHTower.DeletionCompatibleCurvature`.

The module defines the actual coefficients `A_d(n)=1-(d/b(d))*[d|n]`, their
squared source mass `b(n)^2*n^(-alpha)`, and the original four curvature channels.
It proves their pointwise linearization, infinite divisibility reindexing, and
absolute summability before calculating their sum.

`curvature_eq` factors that sum into positive prefactors and `1-r^(2-alpha)`.
`curvature_neg`, `curvature_zero_at_two`, `curvature_pos`, and
`curvature_eq_zero_iff` give the complete sign and vanishing boundary for
pairwise coprime labels greater than one. These are general theorems with explicit
positivity, contractivity, multiplicativity, and convergence conditions; no
unproved arithmetic premise is supplied.

`normalized_curvature_invariant` proves exact equality with the original
normalized curvature whenever `b(p)=b(q)=1`.
`fifth_attenuation_normalized_curvature` instantiates every `0<c<=1` in the
actual coefficient family `c^(v_5(n))`. The premise-free
`fifth_attenuation_curvature_boundary` fixes `c=1/5` and proves multiplier 25,
negative curvature at `3/2`, zero at two, and positive curvature at three.

Validation: `lake env lean /tmp/hgt-compatible-curvature-Pe4gsu/Audit.lean`
passed. Eight axiom audits, covering the pointwise identity, infinite reindexing,
summability, factorization, zero boundary, two normalized invariants, and fixed
capstone, report only `propext`, `Classical.choice`, and `Quot.sound`.
Production matches the audited scratch body. The narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionCompatibleCurvature` passed.
Its umbrella import is wired. No full or umbrella build ran; no computational
experiment or external proof certificate was used. Repository-wide `scripts/formal_tools.py lint` passed with every module of this card wired into the `RHTower` umbrella; a later rerun failed only on another session's unwired module `RHTower.Sieve.MenonHarmonicBlockLevelSplitHM`, which names none of this card's modules. All owned Lean, build, and lint
processes completed.

The the paper proof above gives
the source-admission and literature boundaries. The result closes the
[compatible attenuation repair](../5-failed/euler-deletion-compatible-attenuation-repair.md)
with an exact positive invariant. It supplies no identity forced by a zeta zero
and does not exclude off-line zeros.
