# Source-rigged unseparated cofiber towers are the maximal common programme-4 calculus

- **ID:** `source-rigged-unseparated-cofiber-calculus`
- **Stage:** 1-in-progress
- **Type:** ABSTRACT THEOREM / CROSS-BENCHMARK CLASSIFICATION / UNIVERSAL-CONE NO-GO
- **Source:** `docs/reports/rh-status-1707.md`, programme 4
- **Scientific status:** `[CONJECTURE] [PARENT QUASI-ABELIAN MATHEMATICS] [NOT AN RH RESULT]`

## Exact construction

For a bounded linear map of Banach spaces `u:X->Y`, retain the quotient before Hausdorffization:

```text
UCoFib(u)=Y/uX,
p_u(y+uX)=inf_(x in X) ||y-u(x)||.                         (1)
```

Its canonical null and separated layers are

```text
Null(u)=closure(uX)/uX,
Sep(u)=Y/closure(uX).                                      (2)
```

There is a functorial exact sequence

```text
0 -> Null(u) -> UCoFib(u) -> Sep(u) -> 0.                  (3)
```

Consequently one definition distinguishes four phases:

```text
exact range:                 UCoFib=0;
dense proper range:          Null!=0, Sep=0;
closed proper range:         Null=0, Sep!=0;
nonclosed nondense range:    Null!=0, Sep!=0.              (4)
```

For a decreasing range tower `R_k subset Y`, set `Q_k=Y/R_k`. The transition and reconstruction
layers satisfy

```text
ker(Q_(k+1)->Q_k)=R_k/R_(k+1),                             (5)

ker(Y -> inverseLimit_k Y/R_k)=intersection_k R_k,         (6)

ker(Y -> inverseLimit_k Y/closure(R_k))
  =intersection_k closure(R_k).                            (7)
```

To retain ordinary versus bornological cofinality, the tower is **source-rigged** by its actual
presenting arrows and their lift-conditioning profile. Stagewise algebraic isomorphism is weaker
than controlled pro-isomorphism: inverse families must have uniformly bounded norms.

## Benchmark computation

### Gamma factorial wall

The completed diagonal factorial reporter has dense proper range. Therefore its cofiber is pure
null:

```text
UCoFib!=0, Null=UCoFib, Sep=0.                              (8)
```

Every finite restriction is bijective, but the inverse norms grow factorially. The ordinary
finite tower is stagewise exact while the controlled/bornological tower is not invertible.

### Multiple Gamma period incidence

For `R_k=range(M_w^k)`, the corpus proves

```text
R_(k+1) properSubset R_k,
closure(R_k)=B for every k>=1,
intersection_k R_k != 0.                                  (9)
```

Thus `(5)` retains every finite multiplicity layer, `Null(Q_k)=B/R_k` is nonzero,
`Sep(Q_k)=Y/B` is independent of `k`, and `(6)` retains the nonzero flat radical.

Bounded holomorphic evaluation has the sharper source pullback

```text
ev^(-1)(R_k)=z^k H^infinity,
ev^(-1)(B)=z H^infinity,
intersection_k z^k H^infinity=0.                           (10)
```

Hence the source retains finite Taylor multiplicity but has zero infinite flat pullback.

### Sonin/Euler essential corner

The compact ideal is closed in the bounded operators. Its Calkin quotient is therefore pure
separated:

```text
Null=0,
Sep=UCoFib=B(H)/K(H),                                      (11)
```

with the existing Sonin and Euler essential norms. A pure-null Gamma class cannot produce or
cancel a nonzero Sonin essential class under a bounded commutative comparison square, because the
induced source separated quotient is zero.

## Universal-cone no-go

A single cone comparing completion with inverse limit cannot be the programme-4 invariant. It is
zero on constant towers, while a constant Gamma cofiber can remain pure null and a constant Sonin
cofiber can remain nonzero and separated. Hausdorffizing first kills Gamma; retaining only the
unseparated quotient forgets Sonin's essential norm and Gamma's factorial conditioning.

The maximal common datum is therefore

```text
(source presentation, UCoFib tower, Null, Sep,
 transition kernels, inverse-limit kernel, lift conditioning).        (12)
```

It is a typed tuple with exact comparison maps, not unrelated marginal storage: `(3)`, `(5)`, and
`(6)`--`(7)` are the structural laws coupling all components.

## Parent-theory and anti-theatre gate

- Quasi-abelian categories and derived projective limits are the parent home for non-strict maps;
  writing `(3)` there is not new science.
- Standard Tate objects use admissible/strict maps and therefore exclude the nonclosed Gamma and
  multiple-Gamma ranges; closing the ranges destroys the null layers.
- Derived adic completion can see algebraic powered ideals but not topological null radicals or
  Calkin essential norms.
- The scientific contribution is only an actual source-rigged benchmark comparison or a new
  transferred theorem, not the definition `UCoFib`.

Primary parents:

- J.-P. Schneiders, *Quasi-abelian categories and sheaves*,
  `https://www.numdam.org/item/10.24033/msmf.389.pdf`.
- F. Prosmans, *Derived limits in quasi-abelian categories*,
  `https://hdl.handle.net/2268/20961`.
- O. Braunling, M. Groechenig, J. Wolfson, *Tate Objects in Exact Categories*,
  `https://arxiv.org/abs/1402.4969`.
- M. Porta, L. Shaul, A. Yekutieli, *On the Homology of Completion and Torsion*,
  `https://arxiv.org/abs/1010.4386`.

## Open core

1. Prove `(3)`, `(5)`, and the elementwise forms of `(6)`--`(7)` in Lean.
2. Package the existing Gamma, multiple-Gamma, and Sonin results as exact instances without
   duplicating their proofs.
3. Formalize the bounded-holomorphic finite-jet pullback strengthening in `(10)`.
4. Define controlled pro-isomorphism and prove the factorial inverse wall is not invertible there.
5. Construct a genuine source comparison arrow before naming any `BCDef_F`.

## Gates

- [x] one typed construction handles exact/dense/closed/mixed range
- [x] tower retains finite multiplicity and flat intersection
- [x] ordinary versus controlled cofinality isolated in the source rigging
- [x] compact/essential layer retained without conflating it with dense range
- [x] single exchange-cone proposal falsified
- [ ] dependency-closed paper proof
- [ ] hostile proof review
- [ ] external rediscovery verdict
- [ ] unconditional Lean formalization
- [ ] exact benchmark composition theorem
