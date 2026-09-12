# Route E entropy-complement physical-incidence fibre law

- **ID:** `ROUTE-E-ENTROPY-COMPLEMENT-PHYSICAL-INCIDENCE-001`
- **Stage:** 3-formalized
- **Type:** `[LEAN-CERTIFIED] [EXACT FIBRE CLASSIFICATION] [ROW-MASS IDENTIFICATION]`
- **Parent:** `route-e-entropy-complement-pair-stability-seam-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteEEntropyComplementPhysicalIncidence.lean`

## Exact cutoff fibre

Fix prime cutoff `P`. Suppose

\[
 q=tm,
 \qquad q\text{ is squarefree},
 \qquad p\mid t\Rightarrow p\le P,
 \qquad p\mid m\Rightarrow P<p.
\]

Then

\[
 t=\prod_{\substack{p\mid q\\p\le P}}p=L_P(q),
 \qquad
 m=\prod_{\substack{p\mid q\\P<p}}p=R_P(q).
\tag{1}
\]

Conversely `(L_P(q),R_P(q))` satisfies these conditions for every squarefree `q`. Hence fibre of
multiplication over a physical endpoint is exactly singleton. Low/rough factor labels do not create
physical capacity or a projection-collision term.

This statement is sharply scoped. It does not remove collisions between different pair-switch
histories or different source endpoints that reach the same receiver.

## Physical support collapse

Let `S(n,q)` be symmetric. Symmetrize two oriented upward certificates:

\[
 \mathcal R(n,q)=\operatorname{Up}(n,q)\lor\operatorname{Up}(q,n).
\]

Lean proves this is exactly

\[
\begin{aligned}
&n,q\text{ squarefree and }z\text{-friable},\\
&(n,q)=1,\qquad S(n,q),\\
&\Omega(q)=\Omega(n)+1\quad\text{or}\quad
  \Omega(n)=\Omega(q)+1.
\end{aligned}
\tag{2}
\]

Support itself is cutoff-free. Cutoff `P` remains available as a counting decomposition, and a
chosen raw weight may depend on intrinsic parts; neither changes endpoint set `(2)`. Relation
`(2)` is symmetric, loop-free, and every edge reverses squarefree Möbius sign.

For raw weight `W`, finite aperture `A`, and physical row mass

\[
 a_A(n)=\sum_{q\in A}\mathbf 1_{\mathcal R(n,q)}W(n,q),
\]

one has exactly

\[
 a_A(n)=\sum_{\substack{q\in A\\q\text{ satisfies }(2)}}W(n,q).
\tag{3}
\]

For `W=1`, row mass is cardinality of physical adjacent-grade endpoint shell.

## Consequence for proof chain

Row-normalizer problem is no longer an unidentified latent convolution. Its unweighted observable
is local additive-shell count `(3)`. Entropy-complement low/rough convolution is a method for
estimating this count, not an extra state space. Next source theorem must control weighted local
degree or reciprocal-degree edge variation for `(2)`, including squarefree, friable, coprime,
grade, aperture, and seam restrictions.

Existing `JointTuranKubilius.sum_sq_joint_deviation_le` controls a different object: prefix
variance of a product of two divisor-count observables. No current theorem identifies it with
`(3)` or transfers it to local reciprocal row-mass energy. Direct composition is therefore a
no-go; a new localization/convolution bridge remains live.

An alternative physical completion joins every squarefree shell endpoint with opposite Möbius
sign. Its row degree satisfies `2*d(n)=Q(n)-mu(n)*M(n)`, separating squarefree shell mass from the
local Möbius shell sum. See the
[sign-complete physical degree law](route-e-sign-complete-physical-degree-law.md). This removes
adjacent-grade concentration but exposes the Möbius short-interval second moment at the required
degree-regularity rate.

## Lean theorem map

- `routeE_cutoffSplit_recovers_intrinsicParts`
- `routeE_cutoffSeparatedSplit_iff_intrinsic`
- `routeE_cutoffSeparatedSplit_unique`
- `routeE_entropyComplement_pairRelation_iff_physical`
- `routeE_entropyComplement_pairRelation_reverses_moebius`
- `routeE_entropyComplementRawIncidence_comm`
- `routeE_entropyComplementRawIncidence_support_reverses_moebius`
- `routeE_entropyComplementPhysicalRowMass_eq_targetSum`
- `routeE_entropyComplementPhysicalRowMass_one_eq_card`

## Honest status

Exact finite factor-fibre classification, physical support collapse, raw-incidence symmetry, sign
reversal, and row-mass identification are formalized. No local shell lower bound, degree-gradient
energy estimate, pair-switch dispersion bound, normalized seam estimate, Mertens bound, or RH
proof is claimed.
