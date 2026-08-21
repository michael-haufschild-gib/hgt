# Complete-history invariant metric cone

- **ID:** `complete-history-invariant-metric-cone`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / EXACT CLASSIFICATION / POSITIVE SURVIVOR
- **Source:** `../../1-in-progress/self-noncontainment-minimal-repair-law.md`
- **Statement:** Once one positive metric invariant under every closed history exists, all such
  metrics are exactly that metric multiplied by the positive self-adjoint units in the
  closed-history commutant.
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [REDISCOVERED] [LEAN COMPLETE]`

## Goal

Classify the complete positive-metric ambiguity left after all closed histories are specified.
This is the strongest exact positive survivor of the local metric-nonselection results. It does not
claim that history generates the first invariant metric, Lorentz signature, gravity, or dynamics.

## Setup

Let \(\Gamma\) be a group, let \(V=\mathbb C^n\), and let

\[
T:\Gamma\longrightarrow \operatorname{GL}(V)
\]

be a finite-dimensional representation. Define the cone of complete-history invariant positive
metrics

\[
\mathcal M(T)
=
\left\{
K\in M_n(\mathbb C):
K>0,\quad T_g^\dagger K T_g=K\ \text{for every }g\in\Gamma
\right\}.                                                     \tag{1}
\]

Fix \(H\in\mathcal M(T)\). Define the positive \(H\)-self-adjoint commutant cone

\[
\mathcal C_H(T)
=
\left\{
A\in\operatorname{GL}(V):
\begin{array}{l}
AT_g=T_gA\quad\text{for every }g\in\Gamma,\\
A^\dagger H=HA,\\
HA>0
\end{array}
\right\}.                                                     \tag{2}
\]

The last two clauses say exactly that \(A\) is positive and self-adjoint for the inner product
whose Gram matrix is \(H\).

## Theorem — complete-history metric-cone classification

`[PAPER-PROVED]`

Multiplication by \(H\) is a bijection

\[
\Phi_H:\mathcal C_H(T)\overset{\sim}{\longrightarrow}\mathcal M(T),
\qquad
\Phi_H(A)=HA,                                                 \tag{3}
\]

with inverse

\[
\Psi_H:\mathcal M(T)\overset{\sim}{\longrightarrow}\mathcal C_H(T),
\qquad
\Psi_H(K)=H^{-1}K.                                           \tag{4}
\]

Consequently,

\[
\mathcal M(T)=\{cH:c>0\}
\quad\Longleftrightarrow\quad
\mathcal C_H(T)=\{cI:c>0\}.                                  \tag{5}
\]

Thus the invariant positive metric is unique up to one positive scale exactly when the positive
self-adjoint part of the complete-history commutant is one ray.

## Proof

### 1. Every positive commutant factor gives an invariant metric

Take \(A\in\mathcal C_H(T)\) and put \(K=HA\). By definition, \(K>0\). For every \(g\),
commutation \(AT_g=T_gA\) and invariance of \(H\) give

\[
\begin{aligned}
T_g^\dagger K T_g
&=T_g^\dagger H A T_g\\
&=T_g^\dagger H T_g A\\
&=HA\\
&=K.
\end{aligned}
\]

Hence \(K\in\mathcal M(T)\), so \(\Phi_H\) is well-defined.

### 2. The ratio of two invariant metrics commutes with every history

Take \(K\in\mathcal M(T)\) and put \(A=H^{-1}K\). Positive-definite matrices are invertible, so
\(A\in\operatorname{GL}(V)\).

For every \(g\), invariance gives

\[
T_g^\dagger H T_g=H,
\qquad
T_g^\dagger K T_g=K.
\]

Since \(T_g\) is invertible, these identities are equivalent to

\[
HT_g=T_g^{-\dagger}H,
\qquad
KT_g=T_g^{-\dagger}K.                                       \tag{6}
\]

The first equation in `(6)` implies

\[
H^{-1}T_g^{-\dagger}=T_gH^{-1}.                             \tag{7}
\]

Therefore

\[
AT_g
=H^{-1}KT_g
=H^{-1}T_g^{-\dagger}K
=T_gH^{-1}K
=T_gA.                                                       \tag{8}
\]

Thus \(A\) belongs to the complete-history commutant.

### 3. The ratio has exactly the required positivity and adjointness

Because \(H\) and \(K\) are Hermitian,

\[
\begin{aligned}
A^\dagger H
&=(H^{-1}K)^\dagger H\\
&=K^\dagger(H^{-1})^\dagger H\\
&=KH^{-1}H\\
&=K\\
&=H(H^{-1}K)\\
&=HA.
\end{aligned}
\]

Also \(HA=K>0\). Hence \(A\in\mathcal C_H(T)\), so \(\Psi_H\) is well-defined.

### 4. The maps are inverse

For \(A\in\mathcal C_H(T)\) and \(K\in\mathcal M(T)\),

\[
\Psi_H(\Phi_H(A))
=H^{-1}(HA)
=A,
\qquad
\Phi_H(\Psi_H(K))
=H(H^{-1}K)
=K.
\]

This proves the bijection `(3)`--`(4)`.

### 5. Ray rigidity

Under the bijection, \(cI\) maps to \(cH\), and \(cH\) maps to \(cI\). Positivity on either side
forces \(c>0\). Therefore one cone is a positive ray exactly when the other is, proving `(5)`.
\(\square\)

## Exact spectator corollary

`[PAPER-PROVED]`

Suppose there is a nontrivial \(H\)-orthogonal projection \(P\) commuting with every \(T_g\).
For any \(a,b>0\),

\[
A_{a,b}=aP+b(I-P)
\]

is \(H\)-self-adjoint, positive, invertible, and belongs to the history commutant. If \(a\ne b\),
it is not scalar. Hence \(HA_{a,b}\) is a second invariant positive metric not proportional to
\(H\).

Indeed, \(H\)-orthogonality means \(P^\dagger H=HP\), so \(P\) and \(I-P\) have orthogonal ranges
for the \(H\)-inner product. Every \(v\) decomposes as

\[
v=Pv+(I-P)v
\]

and therefore

\[
\langle v,A_{a,b}v\rangle_H
=a\lVert Pv\rVert_H^2+b\lVert(I-P)v\rVert_H^2>0
\]

for \(v\ne0\). Its inverse is

\[
A_{a,b}^{-1}=a^{-1}P+b^{-1}(I-P).
\]

If \(P\) has nonzero range and nonzero kernel, \(A_{a,b}\) has eigenvalues \(a\) and \(b\) on
those two subspaces. Thus \(a\ne b\) makes it non-scalar.

This proves the precise relationship between history-invariant spectators and independent metric
weights. It does not prove the converse without an additional spectral/projection hypothesis on
the commutant.

## Connected-groupoid form

`[PAPER-PROVED COROLLARY]`

For a connected groupoid representation with invertible arrow transports, choose one root object.
A compatible metric field is determined by its root metric: transport defines every other fiber,
and root-loop invariance is exactly path independence. Applying the theorem to the root holonomy
classifies all compatible metric fields. Changing the root conjugates the representation and
congruently transports the classification; it does not select a preferred matrix presentation.

## Hostile boundary

1. `[REDISCOVERED]` The theorem is finite-dimensional invariant-form/commutant theory. It is a
   direct positive-cone refinement of the usual Schur-lemma mechanism, not new scientific
   knowledge.
2. The theorem is conditional on \(\mathcal M(T)\ne\varnothing\). It classifies an invariant
   positive form after existence; it does not derive positivity from raw obstruction data.
3. Irreducibility is sufficient for scalar complex commutant, but the exact criterion in `(5)` is
   only the positive self-adjoint commutant ray. These statements must not be conflated.
4. The theorem concerns positive Hermitian forms. Irreducible holonomy does not universally select
   an indefinite metric; split-signature counterexamples are known.
5. Uniformly bounded finite-dimensional representations admit an invariant positive form by
   compact-closure averaging, but that compact mechanism cannot itself produce Lorentz boosts.
6. Operational histories retain simultaneous-similarity gauge. The classification is covariant
   under that gauge and therefore reconstructs a metric object only up to congruent
   representation, as it should.
7. No Einstein dynamics, universal free fall, causal cone, Standard Model group, or physical
   prediction follows.

Primary parent boundary:

- R. Atkins, *Holonomy and four-dimensional manifolds*,
  <https://arxiv.org/abs/math/0609768>.
- F. Belgun and A. Moroianu, *On the irreducibility of locally metric connections*,
  <https://arxiv.org/abs/0907.3182>.

## Positive-survivor status

- **Exact killing mechanism that exposed it:** support, radicals, rank, one total weight, and
  complete endpoint histories do not select positive metric weights.
- **Strongest positive survivor:** all remaining global ambiguity is exactly the positive
  self-adjoint complete-history commutant.
- **New insight:** metric nonselection is not an amorphous failure. It is measured by one explicit
  cone; spectators enlarge that cone, while complete-history positive-commutant rigidity collapses
  it to one ray.
- **Scientific audit:** `[BRIDGE] [REDISCOVERED]`; useful for the physical programme only if a
  source law independently generates the first positive form and the history action.
- **Paper status:** dependency-closed proof above.
- **Lean status:** open; exact matrix theorem and groupoid-root corollary must be formalized before
  this card moves to Stage 3.

## Gates

- [x] 0 → 1: exact invariant-form classification isolated from physical interpretation
- [x] 1 → 2: matrix proof, ray criterion, spectator corollary, and groupoid reduction
  dependency-closed
- [x] 2 → 3: exact Lean theorem suite, direct check, axiom audit, lint, and targeted final build
- [ ] 3 → 4: not eligible as Nature result; supporting theorem only

## Lean target

Planned module:

```text
formal/GaloisForLFunctions/HTGeometry/CompleteHistoryInvariantMetricCone.lean
```

The formal target must include:

1. invariant positive-history metric predicate;
2. positive \(H\)-self-adjoint commutant-factor predicate;
3. construction \(A=H^{-1}K\);
4. commutation theorem `(8)`;
5. adjointness and positivity identities;
6. inverse constructions `(3)`--`(4)`;
7. ray-rigidity equivalence `(5)`; and
8. spectator two-weight family and non-proportionality; and
9. connected-history root transport and path-independence reduction; and
10. finite-sector weight family, projective injectivity, and the \(m-1\)-ratio corollary.

No weaker support theorem counts as formalization of this card.

## Log

- 2026-07-30 — extracted from the local metric-nonselection obstruction and proved on paper.
- 2026-07-30 — direct gravitational reading falsified by compact/noncompact role fracture; retained
  only as classification of the positive pre-causal history metric.
- 2026-07-30 — separated into one Stage-2 bridge card before Lean investment.

## Finite-sector separability corollary

`[PAPER-PROVED] [REDISCOVERED] [BRIDGE] [LEAN OPEN]`

Assume in addition that there are nonzero, pairwise \(H\)-orthogonal projections
\[
P_1,\ldots,P_m,\qquad
P_iP_j=0\ (i\ne j),\qquad
\sum_{j=1}^mP_j=I,
\tag{9}
\]
and that every \(P_j\) commutes with every complete-history transport \(T_g\). For every weight
vector \(w=(w_1,\ldots,w_m)\in\mathbb R_{>0}^m\), put
\[
A_w=\sum_{j=1}^m w_jP_j,
\qquad
K_w=HA_w.
\tag{10}
\]
Then \(K_w\) is an invariant positive metric. Moreover,
\[
K_w=cK_{w'}
\quad\Longleftrightarrow\quad
w_j=cw'_j\ \text{for every }j.
\tag{11}
\]
Consequently the projectivized invariant metric cone contains an injective
\((m-1)\)-parameter family. In particular, if \(m\ge2\), complete-history invariance cannot select
one metric ray.

### Proof

Pairwise \(H\)-orthogonality gives \(P_j^{\dagger}H=HP_j\). Hence
\[
A_w^\dagger H
=\sum_jw_jP_j^\dagger H
=\sum_jw_jHP_j
=HA_w.
\]
Commutation of every \(P_j\) with every \(T_g\) gives \(A_wT_g=T_gA_w\). For
\(v=\sum_jP_jv\ne0\),
\[
\langle v,A_wv\rangle_H
=\sum_jw_j\lVert P_jv\rVert_H^2>0.
\]
Also \(A_w^{-1}=\sum_jw_j^{-1}P_j\). Thus \(A_w\in\mathcal C_H(T)\), and the classification theorem
above makes \(K_w=HA_w\) an invariant positive metric.

If \(K_w=cK_{w'}\), invertibility of \(H\) gives \(A_w=cA_{w'}\). Restricting to the nonzero range
of \(P_j\) gives \(w_j=cw'_j\) for every \(j\). The converse is immediate. Modding out by one
common positive scalar leaves the \(m-1\) independent ratios
\[
\frac{w_2}{w_1},\ldots,\frac{w_m}{w_1}.
\]
\(\square\)

### Exact physical reading

Suppose a proposed physical realization identifies the \(m\) invariant summands with separately
preserved response sectors and identifies their kinetic coefficients with \(w_j=1/g_j^2\). Then
history invariance alone cannot determine the dimensionless coupling ratios \(g_i/g_j\). The
contrapositive is the useful no-go:

> A unique projective calibration of several force sectors requires complete physical history to
> cross every nontrivial orthogonal sector partition. Merely placing independently preserved
> sectors in one action, connection, algebra, or bundle cannot fix their relative strengths.

This is not a derivation of observed couplings, and it is not new representation theory. Simple
grand-unified groups and irreducible representations already exploit the same rigidity mechanism.
The new programme would have to derive the role-crossing history action from a source before a
unified algebra, spacetime, metric, or canonical normalization is supplied.

## Lean formalization — COMPLETE

Module: `formal/GaloisForLFunctions/HTGeometry/CompleteHistoryInvariantMetricCone.lean`, wired
into `GaloisForLFunctions.HTGeometry`, self-contained over mathlib.  `#print axioms` on every
capstone returns exactly `[propext, Classical.choice, Quot.sound]`.  All ten required targets are
present.

| Target | Lean declaration |
|---|---|
| 1. invariant positive-history metric predicate | `IsInvariantMetric` |
| 2. positive `H`-self-adjoint commutant-factor predicate | `IsCommutantFactor` |
| 3. construction `A = H⁻¹K` | `isCommutantFactor_inv_mul` |
| 4. commutation theorem `(8)` | the `commutes` field of `isCommutantFactor_inv_mul`, via `mul_transport_eq` and `inv_mul_transport_eq` |
| 5. adjointness and positivity identities | the `selfAdjoint` and `positive` fields of `isCommutantFactor_inv_mul`; `isInvariantMetric_mul` |
| 6. inverse constructions `(3)`–`(4)` | `isCommutantFactor_inv_mul_mul`, `mul_inv_mul`, `invariantMetric_image_eq` |
| 7. ray-rigidity equivalence `(5)` | `invariantMetric_eq_ray_iff` |
| 8. spectator two-weight family and non-proportionality | `isSectorSystem_pair`, `spectator_two_weight` |
| 9. connected-history root transport and path independence | `metricField_eq_root_transport`, `conjTranspose_transport_cancel`, `metricField_transport_congr` |
| 10. finite-sector weight family, projective injectivity, `m−1` ratios | `IsSectorSystem`, `sectorFactor`, `isCommutantFactor_sectorFactor`, `sectorFactor_eq_smul_iff` |

Three points worth recording.

*Transports need no invertibility hypothesis.*  `isUnit_det_transport` derives it: taking
determinants in `T_gᴴ K T_g = K` and cancelling `det K ≠ 0` gives
`conj(det T_g) · det T_g = 1`.

*The positivity of the sector family is a Gram argument, not a spectral one.*
`mul_sectorFactor_eq` rewrites `H A_w` as `∑_j w_j P_jᴴ H P_j`, `dotProduct_sector_term` turns each
quadratic form into `⟨P_j x, H P_j x⟩`, and `∑_j P_j = 1` forces some `P_j x ≠ 0` when `x ≠ 0`.
The `Finsupp`-based mathlib definition of `PosDef` is avoided throughout by working with
`posDef_iff_dotProduct_mulVec`.

*Path independence needs only the second transport to be invertible.*  In
`metricField_transport_congr` the loop identity is proved by conjugating with `c'` alone; the
first transport's invertibility never enters.
