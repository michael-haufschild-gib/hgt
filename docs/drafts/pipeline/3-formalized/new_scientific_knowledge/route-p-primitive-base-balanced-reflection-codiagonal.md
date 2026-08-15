# Route P primitive base balanced-reflection codiagonal

- **ID:** `route-p-primitive-base-balanced-reflection-codiagonal`
- **Stage:** 3-formalized
- **Label:** `P-G184`
- **Source:** `rh-current-frontier-map.md`, Route P; W-H181 raw modular-conormal trace
- **Statement:** Cubically regularizing the balanced primitive Euler source/co-source codiagonal
  before summation gives exactly the complete P-G181 base Cauchy trace budget, cell by cell and
  globally. The value is independent of balanced reflection displacement, every finite base Gram
  trace is the corresponding finite source codiagonal, and total source trace is strictly below
  two. No Xi zero or divisor copy enters its definition or proof.

## Conjecture loop

The first conjecture was that P-G183's multiplicity split should be mirrored by a new modular
geometric-mean factorization on the primitive source. Corpus audit falsified novelty: the source
module already states that the positive common-test amplitude is the geometric mean, and
`EulerPrimitiveJointDepthBiorthogonalCommonTest.lean` already proves that source/co-source pairing
equals the von Mangoldt common-test kernel. That direction was dropped.

The pivot was to regularize the *balanced codiagonal itself*. Before regularization,

```text
L_a(p,e) conjugate(R_{-a}(p,e)) = Lambda(p^(e+1))/p^(e+1),
```

independently of `a`; its sum diverges. The P-G181 base self-kernel at primitive log-frequency
`lambda=(e+1)log p` is

```text
B(lambda,lambda)=1/(4 lambda^3).
```

Therefore the regularized cell is

```text
B(lambda,lambda) L_a(p,e) conjugate(R_{-a}(p,e))
 = Lambda(p^(e+1)) / [4 p^(e+1) log(p^(e+1))^3]
 = 1 / [4 (e+1)^3 p^(e+1) (log p)^2].                 (1)
```

Equation `(1)` is exactly `routePPrimitiveBaseCauchyCubicWeight (p,e)`, not merely a comparable
majorant. This conjecture passed scratch Lean and the exact leaf build.

## Theorem P-G184

For `a in R` and primitive Euler cell `i=(p,e)`, define

```text
Q_a(i)=B(lambda_i,lambda_i)
       L_a(i) conjugate(R_{-a}(i)).                              (2)
```

Then:

1. `Q_a(i)=routePPrimitiveBaseCauchyCubicWeight(i)` for every `a,i`;
2. `Q_a(i)=Q_b(i)` for every `a,b,i`;
3. `sum_i Q_a(i)` is absolutely summable and equals
   `routePPrimitiveBaseCauchyCubicTraceBudget`;
4. for every finite primitive packet and every ordinate label, its P-G181 base Gram trace equals
   the finite sum of `(2)`;
5. the real part of the total source codiagonal is strictly less than `2`.

### Proof

P-G181 gives

```text
B(lambda,lambda)=1/(4 lambda^3).
```

The dyadic collision self-kernel is `115/(864 lambda^3)`, hence

```text
B(lambda,lambda)=(216/115) C_collision(lambda,lambda).             (3)
```

The biorthogonal common-test theorem gives the balanced coefficient identity

```text
L_a(i) conjugate(R_{-a}(i))=Lambda(n_i)/n_i,                        (4)
```

while the already-proved cubic Euler diagonal identifies

```text
C_collision(lambda_i,lambda_i) L_a(i) conjugate(R_{-a}(i))
 =xiGammaEulerPrimitiveCubicLogMomentWeight(i).                     (5)
```

Multiplying `(5)` by `(216/115)` and using `(3)` proves the cellwise equality. Independence of
`a` follows immediately. Existing summability of the P-G181 weight permits termwise summation,
giving the exact total budget. Its finite matrix trace theorem gives the finite-packet identity.
Finally P-G181 already proves that this budget is `<2`. `QED`

## New knowledge and route consequence

W-H181 previously asked both for a source-native two-sided object and for its `<2` estimate. P-G184
separates those demands sharply:

- source object exists on the balanced reflection wall;
- cubic regularization must occur before summation;
- its complete trace is already exact and strictly subquantum;
- source trace is the same base Cauchy cube that the completed-Xi conormal residues see.

Thus arithmetic budget construction and estimation are no longer open. Remaining theorem is a
coefficient-faithful pole--Gamma continuation/boundary-value identity carrying this regularized
balanced codiagonal to the reflected completed-Xi raw conormal without introducing a zero list.
Any later argument that assumes a separate source norm bound is solving an obsolete problem.

## Hostile novelty and theatre audit

Internal search found the unregularized biorthogonal pairing, the collision regularizer, and the
P-G181 base budget separately, but no theorem identifying their balanced base codiagonal cellwise
and globally. The result is not RH and does not smuggle a divisor-side norm into the source: every
quantity in `(2)` is defined on `(prime, valuation-depth)` labels.

Closest external work found in primary-source search concerns Hardy-space biorthogonality and RH
completeness, not this von Mangoldt prime-depth cubic codiagonal: Calderaro--Manzur--Noor--Santos,
[Orthogonality questions in the Hardy space related to zeta zeros](https://arxiv.org/abs/2203.05030).
Connes--Consani's [Scaling Hamiltonian](https://arxiv.org/abs/1910.14368) is closer in spirit: it
shows why local-factor unitaries do not yield the desired inner-function positivity. It does not
contain `(1)`--`(5)` or the exact P-G181 budget identity. Connes's earlier
[trace-formula program](https://arxiv.org/abs/math/9811068) supplies broad absorption-spectrum
context, not this regularized source equality.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBaseBalancedReflectionCodiagonal.lean
```

Main declarations:

- `routePPrimitiveBaseBalancedReflectionCodiagonal`;
- `routePBaseCauchyCubicKernel_self_eq_collision_rescale`;
- `routePPrimitiveBaseBalancedReflectionCodiagonal_eq_weight`;
- `routePPrimitiveBaseBalancedReflectionCodiagonal_independent`;
- `summable_routePPrimitiveBaseBalancedReflectionCodiagonal`;
- `tsum_routePPrimitiveBaseBalancedReflectionCodiagonal_eq_budget`;
- `trace_routePPrimitiveBaseCauchyCubicKernelMatrix_eq_balanced_source`;
- `re_tsum_routePPrimitiveBaseBalancedReflectionCodiagonal_lt_two`.

Verification:

- `/tmp/pg184.lean`: `lake env lean /tmp/pg184.lean` passed;
- exact leaf build passed;
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan: clean;
- umbrella import wired; umbrella not built.

## Gates

- [x] paper proof dependency-closed
- [x] exact unconditional Lean formalization
- [x] scratch verification
- [x] exact leaf build
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] source-to-completed-Xi boundary-value continuation
- [ ] raw conormal residue trace inequality and RH
