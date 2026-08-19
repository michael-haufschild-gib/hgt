# Prime co-shifts have one arithmetic eigenline, and its regularized boundary complex has zero index

- **ID:** `prime-coshift-eigenline-regularized-boundary-complex`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); pivot foundation and index no-go
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** multiplicative isometries on `l2(N)`, the polylogarithm boundary expansion, and
  `additive-heat-aperture-zeta-zero-echo.md`
- **Statement:** The vector `(n^(-s))` is the unique common Hilbert eigenline of all prime
  multiplicative co-shifts when `Re(s)>1/2`, and no nonzero common Hilbert eigenvector exists when
  `Re(s)<=1/2`.  Regularized additive boundary evaluation restricts to multiplication by `zeta(s)`
  on this line.  Its two-term complex is acyclic off the zeta divisor and has one-dimensional kernel
  and cokernel on the divisor, so its Fredholm index is always zero.

## Multiplicative co-shifts

Let

```text
H = l2(N_(>=1))
```

with standard basis `(e_n)`.  For every prime `p`, define the multiplicative isometry

```text
V_p e_n = e_(pn).
```

Its adjoint is the co-shift

```text
(V_p^* x)_n = x_(pn).
```

For `s in C`, put

```text
L_s = {x in H : V_p^* x = p^(-s)x for every prime p}.
```

`[PROVED]` If `Re(s)>1/2`, then

```text
L_s = C Psi_s,
Psi_s = (n^(-s))_(n>=1).
```

If `Re(s)<=1/2`, then `L_s={0}`.

### Proof

Let `x in L_s`.  The co-shift equations say

```text
x_(pn)=p^(-s)x_n                                      (1)
```

for every prime `p` and every `n>=1`.  Iterating (1) along the unique prime factorization of `n`
gives

```text
x_n=n^(-s)x_1.                                        (2)
```

Thus every common eigenvector is a scalar multiple of `Psi_s`.  Conversely (1) holds termwise for
`Psi_s`.  Finally,

```text
||Psi_s||^2=sum_(n>=1)n^(-2 Re(s)),
```

which is finite exactly when `Re(s)>1/2`.  Equation (2) then also shows that below or on the wall a
common Hilbert eigenvector must have `x_1=0` and hence must vanish.  QED.

This realizes the particle side of the slit metaphor without an Euler product or analytic
continuation: the arithmetic state is fixed by the simultaneous prime constraints.

## The canonical closed all-prime row

Assume `Re(s)>1/2` and define

```text
R_s : Dom(R_s) subset H -> l2(Primes;H),
(R_s x)_p=(V_p^*-p^(-s)I)x,

Dom(R_s)
  ={x in H : sum_p ||(V_p^*-p^(-s)I)x||^2<infinity}.
```

`[PROVED]` The operator `R_s` is densely defined and closed, and

```text
ker R_s=L_s=C Psi_s.                                   (2a)
```

Every finite-support vector belongs to `Dom(R_s)`.  Indeed, `V_p^*x` is nonzero for only finitely
many primes dividing an index in the support of `x`, while the remaining square norm is bounded by

```text
||x||^2 sum_p p^(-2 Re(s))<infinity.
```

Hence the domain is dense.  To prove closedness, suppose `x_j->x` in `H` and `R_s x_j->y` in the
prime direct sum.  Coordinate projection at every prime is continuous, and each
`V_p^*-p^(-s)I` is bounded, so

```text
y_p=(V_p^*-p^(-s)I)x
```

for every `p`.  Since `y` belongs to the direct sum, `x` belongs to `Dom(R_s)` and `R_s x=y`.
The kernel identity is the common-eigenline theorem above.

This row is canonical and requires neither a prime ordering nor arbitrary summable weights.  It is
the concrete infinite constraint operator to use in place of an unspecified derived limit of
finite prime complexes.

## Source-defined additive boundary evaluation

Assume `1/2<Re(s)<1`.  For `x in L_s`, its circle boundary wave is

```text
F_x(theta)=sum_(n>=1)x_n exp(i n theta)
```

as an `L2` boundary function.  Since `x=x_1 Psi_s`, define its regularized additive boundary value
by the intrinsic singular subtraction

```text
RegEv_s(x)
  = lim_(theta->0)
      [F_x(theta)-x_1 Gamma(1-s)(-i theta)^(s-1)].      (3)
```

Jonquiere's local expansion proves that the limit exists and that

```text
RegEv_s(x)=x_1 zeta(s).                                (4)
```

Definition (3), rather than the right side of (4), is the source definition.  It uses the actual
common prime eigenline and the universal additive singular branch.  The additive heat-aperture
theorem supplies a positive quadratic measurement whose subleading echo is the corresponding
sesquilinear shadow of (3).

Consequently,

```text
RegEv_s=0 on L_s  iff  zeta(s)=0.                      (5)
```

## The balanced reduced boundary complex

Consider the two-term finite-dimensional complex

```text
0 -> L_s --RegEv_s--> C -> 0.                          (6)
```

Both nonzero terms have dimension one.  If `zeta(s)!=0`, equation (4) makes the differential an
isomorphism, so both cohomology groups vanish.  If `zeta(s)=0`, the differential is zero, and

```text
dim ker(RegEv_s)=1,
dim coker(RegEv_s)=1.                                  (7)
```

Therefore (6) detects the zeta divisor exactly by failure of acyclicity, but its Fredholm index is

```text
ind(RegEv_s)
  = dim ker(RegEv_s)-dim coker(RegEv_s)
  = 0                                                  (8)
```

for every `s` in the right Hilbert strip, including at every zero.

## Consequences

1. The original prime-slit metaphor has a literal operator realization: `Psi_s` is the unique
   all-prime common eigenline, and additive boundary evaluation is the aperture.
2. Zeros are genuine cohomology of a source-defined additive--multiplicative complex, not ordinary
   zeros of a positive density operator.
3. An ordinary Fredholm index cannot be the missing integer selector.  Kernel and cokernel are
   born together, so the Euler characteristic remains zero.
4. Determinant, torsion, or Fitting support sees the zero, but a scalar determinant alone does not
   locate it on the critical line.
5. Any live continuation must couple the closed row `R_s` to a source-defined additive trace and
   prove a genuine off-line coercive estimate.  Repackaging the one-dimensional reduction cannot
   supply RH.

## Lean status

The common-eigenline proof is elementary and formalizable from `l2` coordinate identities and
unique factorization.  The regularized boundary evaluation requires the same polylogarithm
asymptotic absent from the current Lean API.  No wrapper is added: formalizing only the
finite-dimensional zero-index conclusion would not advance the open route.

## Gates

- [x] common prime co-shift eigenspace classified exactly
- [x] Hilbert threshold proved exactly
- [x] canonical all-prime row proved densely defined and closed
- [x] regularized additive boundary map defined without inserting the zero divisor
- [x] boundary value identified with `zeta(s)`
- [x] cohomology and constant zero Fredholm index computed
- [ ] optional Lean formalization after the analytic boundary map has a substantive API

## 2026-08-19 — unconditional Lean formalization (stage 3)

Every displayed statement of this card is now Lean-proved with no hypotheses beyond the stated
half-plane conditions, and each capstone `#print axioms` reports only
`propext, Classical.choice, Quot.sound`.

**The model** — `formal/GaloisForLFunctions/RHTower/PrimeCoShiftModel.lean`

| Card item | Lean declaration |
|---|---|
| `H = l2(N_{>=1})` | `RHTower.PrimeCoShift.H` |
| `V_p e_n = e_{pn}` | `RHTower.PrimeCoShift.primeShift` |
| `(V_p^* x)_n = x_{pn}` | `RHTower.PrimeCoShift.primeCoShift`, `primeCoShift_apply` |
| `V_p^*` is the Hilbert adjoint of `V_p` | `primeCoShift_eq_adjoint` |
| `T_{p,s} = V_p^* - p^{-s}` | `rowOp` |
| `L_s` | `eigenSubmodule` |
| eq. (1) | `eigen_recursion` |
| eq. (2), `x_n = n^{-s} x_1` | `eigen_coordinate` |
| `Psi_s = (n^{-s})` and `Psi_s in L_s` | `groundState`, `groundState_mem_eigenSubmodule` |
| `L_s = C Psi_s` for `Re s > 1/2` | `eigenSubmodule_eq_span` |
| `L_s = 0` for `Re s <= 1/2` | `eigenSubmodule_eq_bot` |
| Hilbert threshold `sum n^{-2 Re s} < infinity` | `memℓp_groundFun`, `not_summable_rpow_inv_of_le` |

**The canonical closed all-prime row** —
`formal/GaloisForLFunctions/RHTower/PrimeCoShiftRowGraph.lean`

| Card item | Lean declaration |
|---|---|
| `R_s : Dom(R_s) -> l2(Primes;H)` | `rowGraph`, `RowSpace` |
| `Dom(R_s)` | `rowDomain`, `mem_rowDomain_iff` |
| densely defined (finite-support core) | `rowDomain_dense`, `truncate_mem_rowDomain` |
| closed | `isClosed_rowGraph` |
| eq. (2a) `ker R_s = L_s` | `rowGraph_kernel` |

**The regularized additive boundary evaluation and the balanced complex** —
`formal/GaloisForLFunctions/RHTower/PrimeCoShiftBoundaryComplex.lean`

| Card item | Lean declaration |
|---|---|
| `F_x(theta) = sum_n x_n e^{i n theta}` (partial sums) | `boundaryPartialSum` |
| `F_x(theta) = x_1 Li_s(e^{i theta})` | `tendsto_boundaryPartialSum` |
| eq. (3) and (4): `RegEv_s(x) = x_1 zeta(s)` | `tendsto_regularized_boundary`, `tendsto_regEv` |
| the differential of (6) | `regEv` |
| acyclic when `zeta(s) != 0` | `regEv_bijective`, `regEv_ker_eq_bot`, `regEv_range_eq_top` |
| eq. (7) on the divisor | `finrank_ker_regEv_of_zeta_eq_zero`, `regEv_eq_zero_of_zeta_eq_zero` |
| eq. (8) `ind(RegEv_s) = 0` | `regEv_index_zero` |
| eq. (5) `RegEv_s = 0` on `L_s` iff `zeta(s) = 0` | `regEv_eq_zero_of_zeta_eq_zero` + `regEv_bijective` |

The analytic input for `(4)` is the corpus-owned Jonquière boundary expansion
(`RHTower/JonquiereExpansion.lean`, `norm_expZeta_sub_jonquiere_le`) together with the
Abel-summation identification of the boundary Dirichlet series with `expZeta`
(`RHTower/DirichletAbel.lean`, `abelDirichlet_eq_expZeta`).  No new analytic hypothesis is
introduced.

## Gates

- [x] common prime co-shift eigenspace classified exactly
- [x] Hilbert threshold proved exactly
- [x] canonical all-prime row proved densely defined and closed
- [x] regularized additive boundary map defined without inserting the zero divisor
- [x] boundary value identified with `zeta(s)`
- [x] cohomology and constant zero Fredholm index computed
- [x] unconditional Lean formalization
