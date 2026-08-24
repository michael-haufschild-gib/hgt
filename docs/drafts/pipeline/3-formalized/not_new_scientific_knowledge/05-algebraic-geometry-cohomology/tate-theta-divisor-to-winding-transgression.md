# Tate-theta divisor-to-winding transgression

- **ID:** `tate-theta-divisor-to-winding-transgression`
- **Stage:** 3-formalized
- **Type:** ANALYTIC BRIDGE / SOURCE-FACE RECONSTRUCTION REPAIR
- **Scientific status:** `[PAPER PROOF COMPLETE] [CLASSICAL PARENT]`
  `[LEAN FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [STRONG POSITIVE SUCCESSOR]`
  `[NOT AN RH RESULT]`
- **Foundational consumer:**
  `../../1-in-progress/hypertranscendental-source-face-vanishing-cycle-conservation.md`

## The theorem

For `0<q<1`, define the multiplicative theta function

```text
theta_q(y)=product_(n>=0)(1-q^n y)(1-q^(n+1)/y)
```

and the meromorphic function

```text
E_q(x)=-q^(1/4)
  theta_q(q^(-1/4)x) theta_q(q^(3/4)x) / theta_q(q^(1/4)x)^2.  (1)
```

Then:

```text
E_q(qx)=E_q(x);                                                (2)
div(E_q)=2[q^(1/4)]-2[q^(3/4)] on C^*/q^Z;                    (3)
E_q(x)->x locally uniformly on C^* as q->0+.                  (4)
```

For all sufficiently small `q`, `E_q(1)` is nonzero.  Hence

```text
G_(q,m)(x)=(E_q(x)/E_q(1))^m,  m in Z,                        (5)
```

is a pointed `q`-elliptic meromorphic gauge and

```text
G_(q,m)(x)->x^m locally uniformly on C^*.                     (6)
```

Every finite Laurent boundary character is therefore attained by a family of singular elliptic
gauges whose complete divisor escapes through the Tate node.

## Proof

The product immediately gives the quasiperiod law

```text
theta_q(qy)=-y^(-1)theta_q(y).                                (7)
```

The four theta parameters underlying `(1)` are

```text
q^(1/4), q^(-3/4); q^(-1/4), q^(-1/4).
```

Their numerator and denominator products are both `q^(-1/2)`, so the multipliers in `(7)` cancel,
proving `(2)`.  The zeros of `theta_q` are `q^Z`.  In the standard fundamental annulus, both
numerator zeros represent `q^(1/4)` and both denominator zeros represent `q^(3/4)`, proving `(3)`.

For `0<d<1`, the product converges locally uniformly on `C^*` and gives

```text
theta_q(q^d x)->1.                                           (8)
```

Separating the `n=0` factor gives

```text
q^(1/4)theta_q(q^(-1/4)x)->-x.                               (9)
```

The remaining product factors tend uniformly to one on compact annuli because their deviations
are dominated by geometric tails in `q^(n-1/4)` and `q^(n+1/4)`.  Substitution of `(8)`--`(9)` in
`(1)` proves `(4)`, and `(5)`--`(6)` follow.

## Exact charge conservation

Write `v_q(q^a)=a` on the chosen fundamental annulus.  The oriented escaping-divisor charge is

```text
chi_node(div E_q)
  =sum pole valuations-sum zero valuations
  =2(3/4)-2(1/4)=1.                                         (10)
```

The limiting unit `x` has winding one.  Consequently

```text
chi_node(div G_(q,m))=m=wind(x^m).                           (11)
```

This is an exact selection-to-production transgression: a singular divisor class on the smooth
elliptic fibre becomes a regular unit character on the punctured normalization of the nodal
fibre, with the integer charge preserved.

## No-go and maximal positive reconstruction theorem

```text
[NO-GO]
Interior divisor data plus one pointing is not uniformly conservative across a Tate cusp.  The
generic divisor in `(3)` disappears from every compact subset while the nonconstant pointed unit
`x^m` survives.
```

```text
[POSITIVE]
On the finite algebraic-character boundary, the observer
  (interior divisor, node charge, pointing)
is injective.  Omitting node charge leaves exactly the normalized kernel {x^m:m in Z}, and every
member of that kernel is attained by an escaping elliptic divisor family `(5)`.
```

Indeed an algebraic unit on `C^*` is `c x^m`; pointing fixes `c`, and node charge fixes `m`.

## Scientific role and novelty gate

The theta product, Tate uniformization, generalized-Jacobian torus, and divisor-slope law are
classical.  This card therefore makes no novelty claim.  Its role is decisive nonetheless: it
constructs the transverse reporter which source-only processing cannot create and proves the
finite-character existence and surjectivity part of the proposed two-face character conversion.

The candidate-new theorem begins only after coupling this classical transgression functorially to
the DA-relative characteristic module of a natural HT family, preserving its differential
filtration and presentation-independent connecting class.

Primary parent checks include the Tate curve, the slope formula for meromorphic functions on a
semistable skeleton, tropical Abel--Jacobi compatibility, and tropicalization of non-Archimedean
theta functions.  These parents explain the node charge and prevent promotion of `(1)`--`(11)` as
new mathematics.

## Lean formalization

Formal artifacts:

- `formal/GaloisForLFunctions/HTGeometry/MultiplicativeTheta.lean`
- `formal/GaloisForLFunctions/HTGeometry/QPochhammerZeroNome.lean`
- `formal/GaloisForLFunctions/HTGeometry/QPochhammerAnalytic.lean`
- `formal/GaloisForLFunctions/HTGeometry/MultiplicativeThetaDivisor.lean`
- `formal/GaloisForLFunctions/HTGeometry/TateThetaGauge.lean`
- `formal/GaloisForLFunctions/HTGeometry/TateThetaDegeneration.lean`
- `formal/GaloisForLFunctions/HTGeometry/TateThetaCompactOpen.lean`
- `formal/GaloisForLFunctions/HTGeometry/TateThetaDivisor.lean`
- `formal/GaloisForLFunctions/HTGeometry/TateThetaTransgression.lean`

Closed theorem endpoints include:

- `tateThetaGauge_mul_nome`: exact `q`-ellipticity.
- `meromorphicOrderAt_tateThetaGauge_exact`: exact divisor multiplicity `+2`, `-2`, or `0`
  at every point of `ℂˣ`.
- `tendstoLocallyUniformlyOn_tateThetaGauge_of_root_zero`: literal compact-open convergence
  `E_q → id` on `ℂˣ`.
- `tateThetaGauge_one_ne_zero`: pointing denominator is nonzero for every positive quarter nome.
- `tendstoLocallyUniformlyOn_pointedTateThetaGauge_of_root_zero`: compact-open convergence of
  every normalized integer-power gauge to `x ↦ x^m`.
- `eventually_tateTheta_divisor_avoids_compact` and
  `eventually_meromorphicOrderAt_pointedTateThetaGauge_eq_zero_on_compact`: complete divisor
  escape from every compact subset of `ℂˣ`.
- `winding_integral_laurentMonomial` and `tateTheta_nodeCharge_eq_boundaryWinding`: analytic
  winding integral and exact charge conservation.
- `LaurentBoundaryCharacter.not_injective_divisorPointingObserver` and
  `LaurentBoundaryCharacter.repairedObserver_injective`: closed no-go and maximal repaired
  observer theorem.

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/TateThetaTransgression.lean` passed.
- `lake build GaloisForLFunctions.HTGeometry.TateThetaTransgression` passed.
- `#print axioms` on all endpoints above reports only `propext`, `Classical.choice`, and
  `Quot.sound`; no project axiom and no `sorryAx` occurs.
- Modules are wired into `GaloisForLFunctions.HTGeometry`; umbrella build intentionally omitted.

## Gates

- [x] explicit `q`-elliptic gauge constructed
- [x] exact divisor computed
- [x] locally uniform cusp limit proved
- [x] every positive and negative boundary weight attained
- [x] node charge identified with limiting winding
- [x] no-go paired with an injective repaired observer
- [x] classical parent collision recorded
- [x] all dependency-closed classical claims formalized unconditionally in Lean
- [ ] functorial DA-filtered HT transgression constructed (candidate-new downstream consumer gate;
  not a theorem claimed by this classical Stage-2 card)
