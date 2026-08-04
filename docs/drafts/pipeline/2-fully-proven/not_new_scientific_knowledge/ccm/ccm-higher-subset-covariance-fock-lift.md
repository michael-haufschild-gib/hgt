# The local-ratio covariance anomaly has a canonical positive higher-subset Fock lift

- **ID:** `ccm-higher-subset-covariance-fock-lift`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent mechanisms:** the finite subset expansion of a product, Gram-kernel positivity, and the
  completed local-ratio covariance charge
- **Statement:** Every finite completed local-ratio covariance anomaly is the scalar readout of a
  canonical positive graded feature map indexed by subsets of at least two places. The degree-two
  grade carries the complete central covariance curvature; higher grades vanish to higher order on
  the diagonal. These carriers form a cofinal growing system, while the coefficient-one scalar
  readout has norm `sqrt(2^m-m-1)` for `m` places. Thus positivity is available before scalarization,
  but faithful cofinal scalarization is necessarily unbounded.

## 1. Higher-subset feature carrier

Let `V` be a finite set of places and let `u_v(t)` be their critical-line unitary local ratios,
normalized by `u_v(0)=1`. Put

```text
a_v(t)=u_v(t)-1.                                             (1)
```

Let

```text
P_>=2(V)={I subset V:|I|>=2},
H_V^cov=ell^2(P_>=2(V)).                                     (2)
```

Define the source-labeled feature vector

```text
V_V(t)_I=product_(v in I)a_v(t),       I in P_>=2(V).        (3)
```

The finite subset expansion gives

```text
product_(v in V)u_v(t)
 =1+sum_(v in V)a_v(t)+sum_(I in P_>=2(V))V_V(t)_I.          (4)
```

Hence the canonical multiplicative covariance anomaly is exactly the coefficient-one readout

```text
C_V(t)=sum_(I in P_>=2(V))V_V(t)_I.                          (5)
```

The definition uses no ordering, Gauss splitting, or prime--archimedean pairing.

## 2. Positive covariance kernel

The feature map `(3)` defines

```text
K_V^cov(x,y)
 =<V_V(x),V_V(y)>
 =sum_(I in P_>=2(V))conj(V_V(x)_I)V_V(y)_I.                (6)
```

For arbitrary nodes `t_j` and coefficients `c_j`,

```text
sum_(j,k)conj(c_j)c_k K_V^cov(t_j,t_k)
 =||sum_j c_j V_V(t_j)||^2>=0.                              (7)
```

Thus `(6)` is positive semidefinite. This is an actual positive lift of the signed scalar anomaly
`(5)`, not a claim that `(5)` itself is positive definite.

For an inclusion `V subset W`, extension by zero on the new subset coordinates gives an isometric
embedding

```text
H_V^cov -> H_W^cov.                                         (8)
```

The old coordinates of `V_W(t)` agree exactly with `V_V(t)`. Therefore the finite carriers form a
canonical directed system retaining every previously introduced incidence coordinate.

## 3. The degree-two grade carries the central curvature

The carrier splits orthogonally by subset size:

```text
H_V^cov=directSum_(k=2)^|V| H_V^(k),
H_V^(k)=ell^2({I subset V:|I|=k}).                          (9)
```

Suppose

```text
u_v'(0)=-i b_v,
b_v>0.                                                       (10)
```

Then every degree-`k` coordinate has a zero of order at least `k` at the central seam. In
particular, grades `k>=3` have zero second derivative, whereas for a pair `{v,w}`,

```text
(V_V(t)_{v,w})''|_(t=0)
 =2u_v'(0)u_w'(0)
 =-2b_vb_w.                                                  (11)
```

Summing `(11)` over the degree-two coordinates recovers exactly

```text
C_V''(0)=-2sum_(v<w)b_vb_w.                                 (12)
```

Thus the previously proved cofinal curvature charge lives entirely in the first relative grade
`H_V^(2)`. The higher grades are successively more diagonal-regular. This gives a precise positive
version of the three-grade CCM architecture:

```text
degree 0: base/completion;
degree 1: additive local Weil trace;
degree 2 and above: positive covariance Fock carrier.        (13)
```

## 4. Exact cofinal resource

If `m=|V|`, then

```text
dim H_V^cov
 =#P_>=2(V)
 =2^m-m-1.                                                   (14)
```

The readout in `(5)` is inner product with the all-ones vector. Its operator norm is therefore

```text
||readout_V||=sqrt(2^m-m-1).                                (15)
```

Consequently the canonical coefficient-one scalarization is not uniformly bounded as the number
of places grows. This is not a failure of the positive carrier: it identifies where the cofinal
resource resides. A successful construction must keep the graded coordinates through the
Hardy/Sonin compression, or introduce a source-defined weighting/relative trace whose loss of
readout norm is exactly compensated and whose divisor incidence remains faithful.

The degree-two carrier alone already has dimension

```text
binom(m,2),                                                   (16)
```

and carries all central curvature. It is therefore the minimal finite grade that a local
second-order covariance construction must expose.

## 5. CCM consequence

The positive lift closes the purely algebraic part of the covariance problem:

```text
completed local product
 -> canonical subset-graded feature carrier
 -> positive Gram kernel
 -> coefficient-one signed anomaly readout.                 (17)
```

What remains is analytic and divisor-sensitive:

1. identify the degree-two subset carrier with the compact Gauss-paired Hardy coboundary class;
2. prove that Sonin compression/relative trace supplies a cutoff-uniform weighting of `(9)`;
3. show that the resulting positive Schur kernel transports the shifted-Xi Pick negative index;
4. prove cofinal determinant/divisor convergence.

Any proposed bounded scalar covariance that skips `(9)` must explain how it replaces the exact
growing resource `(14)`--`(16)`.

## 5a. Finite Gauss-paired Hardy lift

The finite positive carrier survives Hardy compression. Let `P` be the Hardy projection, `Q=1-P`,
and write

```text
H(a)=Q M_a P.                                                (18)
```

For bounded symbols `a,b`, insertion of `P+Q=1` gives the exact product formula

```text
H(ab)=H(a)(P M_b P)+(Q M_a Q)H(b).                          (19)
```

Consequently the bounded symbols with compact lower Hardy corner form a unital algebra: if
`H(a)` and `H(b)` are compact, both terms on the right of `(19)` are compact.

For `m` finite primes, choose any Connes--Consani Gauss pairing

```text
w_j=g_j rho_(p_j),
product_j g_j=rho_infinity.                                  (20)
```

Every `w_j` is quasi-inner, so `H(w_j)` is compact. Constant phases can normalize `w_j(0)=1`
without changing quasi-innerness. Put `a_j=w_j-1`. Then

```text
H(a_j)=H(w_j)                                                (21)
```

is compact, and repeated use of `(19)` proves that

```text
H(product_(j in I)a_j)                                      (22)
```

is compact for every nonempty subset `I`.

Define the finite column operator

```text
mathcal H_F f
 =(H(product_(j in I)a_j)f)_(|I|>=2).                       (23)
```

Because the target sum is finite, `mathcal H_F` is compact. Its Gram operator

```text
G_F^Hardy=mathcal H_F^*mathcal H_F>=0                        (24)
```

is the canonical positive Hardy lift associated to the chosen Gauss pairing. If `S_F` is the row
operator summing the subset coordinates, then linearity and the subset expansion give

```text
H(C_F^paired)=S_F mathcal H_F,
||S_F||=sqrt(2^m-m-1).                                      (25)
```

Thus the finite Gauss-paired construction supplies all of the following simultaneously:

```text
labeled prime incidence;
compact Hardy covariance coordinates;
a positive Gram lift;
and the exact signed scalar anomaly readout.                 (26)
```

Different Gauss splittings and pairings give different pointed lifts `(23)`, but their degree-one
quantized differentials represent the same cyclic coinvariant class by the algebraic Gauss-descent
theorem. Pairing dependence is therefore legitimate lift data, not ambiguity in the additive local
Weil class.

The unresolved theorem is **uniform positive Gauss lifting**: choose or compare the finite lifts
`(23)` so that their weighted direct limit has a cutoff-independent relative trace or determinant
ideal, retains the nonzero covariance charge, and transports the shifted-Xi Pick index. Finite
compactness by itself supplies none of those uniform conclusions.

`[PROVED COFINAL TARGET IDENTIFICATION]` The infinitesimal half-unit analysis identifies the exact
degree-two limit required here. If `k_x` is the RKHS feature of the unconditional safe completed
kernel and `c_x(t)=exp(-xt)`, the target column is

```text
T_0 k_x=k_x tensor c_x.
```

Its leakage Gram is `J_safe(x,y)/(x+y)`, and RH is equivalent to contractivity of `T_0`. Thus the
uniform positive Gauss lift is no longer an unspecified weighted direct limit: it must converge to
this diagonal tensor operator and preserve its norm. See
`ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.

The formal prime-log carrier also fixes the admissible convergence topology.  Lean's
`not_summable_primeLogHerglotzTransportMassOrder_of_pos` and
`summable_primeLogCauchyPacketTransportEnergy_iff` exclude convergence through an uncoupled prime
`ell^2` space with any uniformly finite rational cancellation order.  Conversely,
`gammaDampedPrimeLogCauchyPacket_critical_carrierTransition` proves that the canonical Gamma
diagonal places the complete finite Cauchy core in the Hilbert domain.  Therefore the cofinal
statement to prove is specifically

```text
Gamma-sewn, channel-resolved finite Gauss columns
  -> relative graph convergence to T_0
  + uniform contractivity.                                (27)
```

Passing to the prime Hilbert norm before the Gamma sewing is not an admissible approximation of
the target.

## 6. Scope and classification

- `[PROVED]` The scalar readout identity, Gram positivity, grading, central-curvature localization,
  directed-system structure, dimension, and readout norm follow directly from `(1)`--`(16)`.
- `[PROVED]` Every finite Gauss pairing gives a compact subset-Fock Hardy column and positive Gram
  lift by `(18)`--`(25)`.
- `[NOT PROVED]` The finite feature kernel is not yet identified with the actual Sonin compression
  or a restricted-Weil kernel.
- `[NOT PROVED]` No uniform cofinal weighting, index transport, determinant convergence, or RH is
  proved.

The construction is the standard subset/tensor expansion of a finite product. Its significance is
route selection and exact carrier accounting, not a new parent-theory mechanism. It is classified
as a bridge.

## 7. Lean status

**Formalized unconditionally, 2026-08-04**, in
`formal/GaloisForLFunctions/RHTower/CCMSubsetCovarianceFock.lean`.

The previous decision said an "abstract wrapper around two standard atoms" would not certify the live
gate.  That was the wrong measurement of the card's own content: sections 1–4 and 5a are not one
wrapper but nine separate statements, and the *positivity*, the *grade localisation*, the *dimension
count*, the *readout norm*, and the *Hardy product formula* are each a proof, not a restatement.  All
of them are now in Lean, on top of the local-ratio layer of
`ccm-local-ratio-second-order-covariance-charge.md`.

- `covIndex`, `covFeature`, **`covarianceAnomaly_eq_readout`** — equations `(1)`–`(5)`.  Note that
  `covFeature` takes no ambient set: the coordinate `V_V(t)_I` genuinely does not depend on `V`, which
  is what makes `(8)` a triviality rather than a compatibility check.
- `powerset_filter_card_le_one`, `empty_notMem_image_singleton` — the low-degree complement, extracted
  once and reused for both the grading and the dimension count.
- `covKernel`, **`covKernel_quadratic_form`**, **`covKernel_quadratic_form_nonneg`** — equations
  `(6)`–`(7)`.  The proof is a triple sum interchange followed by `conj z * z = ‖z‖²`; no Hilbert space
  is needed, because the carrier is finite-dimensional.  The identity is stated as an *equality* with
  `sum_I ‖sum_j c_j V(t_j)_I‖²`, so it exhibits the positive lift rather than merely asserting
  semidefiniteness.
- **`covIndex_subset`**, **`sum_covIndex_extend`** — equation `(8)`: the directed system and the
  isometry of extension by zero.
- `covGrade`, **`sum_covIndex_eq_sum_grades`** — equation `(9)`, the grading by subset size, as the
  `Ico 2 (m+1)` decomposition of the carrier sum.  The `V = ∅` case has to be separated because
  `Ico 2 1` is empty.
- **`sum_powersetCard_two`** — the closed form of the degree-two grade sum,
  `sum_(|I| = 2) prod_(v in I) c_v = ((sum c)^2 - sum c^2)/2`, by induction on the place set through
  `Finset.powersetCard_succ_insert`.  This is the identity that was avoided in the anomaly module and
  is unavoidable here, because the card's `(12)` asks specifically for the grade-two localisation.
- **`tendsto_covFeature_div_pow`** — each degree-`k` coordinate vanishes to order exactly `k` at the
  seam, with jet `prod_(v in I) c_v`.
- **`tendsto_covFeature_div_sq_of_card_two`** (equation `(11)`),
  **`tendsto_covFeature_div_sq_of_three_le`** (equation `(10)` for the higher grades),
  **`tendsto_covarianceAnomaly_div_sq_eq_gradeTwo`** (equation `(12)`) — the quadratic jet of a
  degree-`k >= 3` coordinate is zero, that of a pair is `c_v c_w`, and the whole quadratic jet of the
  anomaly is the degree-two grade sum.  So the cofinal curvature charge lives entirely in `H^(2)`.
- **`card_covIndex`** (equation `(14)`), **`card_covGradeTwo`** (equation `(16)`) — the dimensions
  `2^m - m - 1` and `binom(m,2)`.
- **`norm_readout_le`**, **`norm_readout_ones`** — equation `(15)`, in the sharp two-sided form: the
  coefficient-one readout satisfies `|sum_I x_I| <= sqrt(dim) sqrt(sum_I |x_I|^2)` with equality at the
  all-ones vector.  Stating the bound *and* its attainment is what makes `sqrt(2^m - m - 1)` the norm
  rather than merely an upper bound, and hence what makes the unboundedness claim of section 4 a
  theorem.

Section 5a is formalized in the same module, as the algebra it is:

- `hardyCorner`, `sub_self_mul_sub_self`, **`hardyCorner_mul`** — equations `(18)`–`(19)`.  The product
  formula uses **only** idempotence of the projection, in an arbitrary ring with an arbitrary
  multiplicative symbol map; there is no analytic content in it at all.
- **`hardyCorner_mul_mem`**, **`hardyCorner_prod_mem`** — equations `(21)`–`(22)`: symbols whose corner
  lies in a two-sided ideal are closed under multiplication, hence every nonempty subset product has
  its corner in the ideal.  The card's compactness statement is this with the ideal of compact
  operators; representing the ideal abstractly is the honest formalization, because "quasi-inner implies
  compact" is imported from Connes--Consani and is not proved here.
- **`hardyCorner_sum`** — equation `(25)`'s identity `H(C_F) = S_F ∘ 𝓗_F`, i.e. additivity of the corner
  in the symbol.  Combined with `norm_readout_ones` this gives the full content of `(25)`: the readout
  is the row sum and its norm is `sqrt(2^m - m - 1)`.

The two atoms named in the earlier decision were not in fact what this card needs:
`finiteLocalEulerProduct_subsetExpansion` is the Euler-product expansion, not the `1 + a_v` subset
expansion, and `herglotz_rank_one_psd` is a rank-one positivity, not a Gram identity for a
subset-indexed feature map.  Both were re-proved in the form the card uses.

## Gates

- [x] scalar readout identity `(4)`–`(5)` proved
- [x] Gram positivity `(6)`–`(7)` proved
- [x] directed-system structure `(8)` proved
- [x] grading and central-curvature localization `(9)`–`(12)` proved
- [x] dimension and readout norm `(14)`–`(16)` proved
- [x] finite Gauss-paired Hardy product formula and compact-corner algebra `(18)`–`(25)` proved
- [x] Lean: readout identity, Gram positivity, directed system
- [x] Lean: grading, degree-two closed form, order-of-vanishing of every grade
- [x] Lean: dimension `2^m - m - 1`, degree-two dimension, sharp readout norm
- [x] Lean: Hardy corner product formula, ideal closure, additivity
- [ ] identify the degree-two carrier with the compact Gauss-paired Hardy coboundary class
- [ ] cutoff-uniform weighting of `(9)` from Sonin compression / relative trace
- [ ] transport of the shifted-Xi Pick negative index by the resulting positive Schur kernel
- [ ] cofinal determinant/divisor convergence
- [ ] uniform positive Gauss lifting: relative graph convergence to `T_0` with uniform contractivity

