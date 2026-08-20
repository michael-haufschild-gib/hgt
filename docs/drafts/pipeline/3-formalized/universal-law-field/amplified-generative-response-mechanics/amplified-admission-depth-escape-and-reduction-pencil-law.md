# Amplified admission depth escape and reduction-pencil law

- **ID:** `ulf-agrm-reduction-pencil-depth-escape`
- **Stage:** 3-formalized
- **Type:** THEOREM / TWO-INDEX GENERATIVE-ADMISSION LAW
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ReductionPencilKPositivity`,
  `GaloisForLFunctions.HTGeometry.AmplifiedAdmissionGauge`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CLASSICAL CP PARENTS]`
  `[EXACT COFINAL MIGRATING OBSTRUCTION] [LEAN-CERTIFIED] [UMBRELLA-WIRED]`
  `[NO SORRY] [NO AXIOMS] [NOT RH]`
- **Statement:** Matrix amplification depth and source aperture are independent admission axes.
  The reduction pencil has exact `k`-positive gauge `min(k,n)`, so every fixed amplification level
  remains uniformly admissible while complete admission diverges cofinally.

## 1. Mechanism

Let `S,T` be finite-dimensional operator systems, let `Mu:S->T` be completely positive, and let
`Eta:S->T` be Hermiticity preserving. Define the level-`k` intervention gauge

\[
 \kappa_k(Eta\mid Mu)
 =\inf\{c\ge0:\operatorname{id}_{M_k}\otimes(Eta+cMu)\text{ is positive}\}.
 \tag{AGR.1}
\]

Define the complete gauge

\[
 \kappa_{\mathrm{cp}}(Eta\mid Mu)=\sup_{k\ge1}\kappa_k(Eta\mid Mu).
 \tag{AGR.2}
\]

These are intervention gauges, not new CP distances. Their field role is to remember the
amplification variable which scalar GRM forgets.

### Theorem 1.1 — amplified conservation and data processing

The sequence `kappa_k` is nondecreasing. Moreover

\[
 \boxed{Eta+cMu\text{ is completely positive}
 \Longleftrightarrow c\ge\sup_k\kappa_k(Eta\mid Mu).}
 \tag{AGR.3}
\]

If `A` and `B` are completely positive pre- and post-comparisons, then

\[
 \boxed{
 \kappa_k(BEta A\mid BMu A)\le\kappa_k(Eta\mid Mu)}
 \tag{AGR.4}
\]

for every `k`. Thus a completely positive observer may erase an amplified obstruction but cannot
create one.

### Proof

`(k+1)`-positivity implies `k`-positivity by restricting to a matrix corner, proving monotonicity.
Complete positivity means positivity at every amplification, giving `(AGR.3)` directly from the
common feasible upper ray. If `Eta+cMu` is `k`-positive, then

\[
 \operatorname{id}_{M_k}\otimes B\circ(Eta+cMu)\circ A
\]

is a composition of positive amplifications because `A` and `B` are completely positive. Taking
infima proves `(AGR.4)`. QED.

Endpoint attainment in `(AGR.3)` uses finite dimensionality: every `k`-positive cone is closed,
so every nonempty feasible upper ray contains its infimum. If one level has no feasible
coefficient, both sides of `(AGR.3)` have the corresponding infinite/false extended-order value.

## 2. Exact reduction-pencil threshold

For `n>=1`, write `M_n=M_n(C)` and define

\[
 T_n(X)=\operatorname{Tr}(X)I_n,
 \qquad Eta_n(X)=-X,
 \qquad Phi_{n,c}=Eta_n+cT_n.
 \tag{AGR.5}
\]

### Theorem 2.1

For every `k,n>=1` and real `c`,

\[
 \boxed{
 Phi_{n,c}\text{ is }k\text{-positive}
 \Longleftrightarrow c\ge\min(k,n).}
 \tag{AGR.6}
\]

Consequently

\[
 \boxed{\kappa_k(Eta_n\mid T_n)=\min(k,n),
 \qquad \kappa_{\mathrm{cp}}(Eta_n\mid T_n)=n.}
 \tag{AGR.7}
\]

### Proof

It suffices to test `id_(M_k) tensor Phi_(n,c)` on rank-one positive operators, because every
positive matrix is a finite sum of such operators. Let

\[
 \psi\in C^k\otimes C^n
\]

have Schmidt rank `r` and Schmidt decomposition

\[
 \psi=\sum_{j=1}^r s_j e_j\otimes f_j,
 \qquad s_j>0.
 \tag{AGR.8}
\]

Let

\[
 rho=\operatorname{Tr}_{C^n}|\psi\rangle\langle\psi|
     =\sum_{j=1}^r s_j^2|e_j\rangle\langle e_j|.
\]

Then

\[
 (\operatorname{id}\otimes Phi_{n,c})(|\psi\rangle\langle\psi|)
 =c\,rho\otimes I_n-|\psi\rangle\langle\psi|.
 \tag{AGR.9}
\]

On the support of `rho tensor I_n`, the rank-one subtraction criterion says

\[
 c\,rho\otimes I_n-|\psi\rangle\langle\psi|\ge0
 \Longleftrightarrow
 c\ge\langle\psi|(rho^{-1}\otimes I_n)|\psi\rangle.
 \tag{AGR.10}
\]

The right side is

\[
 \sum_{j=1}^r s_j^2s_j^{-2}=r.
 \tag{AGR.11}
\]

Every vector in `C^k tensor C^n` has Schmidt rank at most `min(k,n)`, so
`c>=min(k,n)` is sufficient. A maximally entangled vector of Schmidt rank `min(k,n)` proves
necessity. This proves `(AGR.6)`.

For maps out of `M_n`, `n`-positivity is equivalent to complete positivity by Choi's theorem;
therefore the complete threshold is `n`. QED.

## 3. Cofinal migrating-depth theorem

Let source aperture `n` and amplification depth `k` vary independently.

### Theorem 3.1

For every fixed `k>=1`,

\[
 \boxed{\sup_{n\ge1}\kappa_k(Eta_n\mid T_n)=k<+\infinity.}
 \tag{AGR.12}
\]

But

\[
 \boxed{
 \sup_{n\ge1}\kappa_{\mathrm{cp}}(Eta_n\mid T_n)
 =\sup_n n=+\infinity.}
 \tag{AGR.13}
\]

At aperture `n`, the sharp rejecting witness first appears at Schmidt/amplification depth `n`.
Hence the obstruction migrates along the diagonal `(n,k)=(n,n)`.

### Proof

Substitute `(AGR.7)`:

\[
 \sup_n\min(k,n)=k,
 \qquad \sup_n n=+\infinity.
\]

Sharpness in Theorem 2.1 is witnessed by a Schmidt-rank-`n` maximally entangled vector. QED.

## 4. Exact false-promotion theorem

The family proves the strict implication failure

\[
 \boxed{
 \bigl(\forall k\ \exists C_k<\infinity\ \forall n:\kappa_k(Eta_n\mid T_n)\le C_k\bigr)
 \not\Longrightarrow
 \exists C<\infinity\ \forall n:\kappa_{\mathrm{cp}}(Eta_n\mid T_n)\le C.}
 \tag{AGR.14}
\]

Thus all of the following are insufficient for complete/cofinal admission:

- positivity at one fixed matrix level;
- `k`-positivity at every separately fixed level;
- a level-dependent bound `C_k`;
- finite-aperture complete positivity without one aperture-uniform threshold.

The required datum is one joint bound on the product-directed set of aperture and amplification.

## 5. Fusion with Generative Response Mechanics

The scalar grammar extends to

\[
 \boxed{
 \text{generate}\to\text{center}\to\text{amplify}
 \to\text{reconstruct}\to\text{admit}\to\text{cofinalize}.}
 \tag{AGR.15}
\]

This adds a real law, not a route label:

1. **source/intervention organ:** `Eta` is a Hermitian law variation;
2. **positive Gram/kernel organ:** level one tests ordinary positivity;
3. **adaptive/all-degree organ:** matrix amplification detects entangled joint tests invisible at
   lower levels;
4. **whole-space/cofinal organ:** aperture growth asks for one bound over the product order;
5. **positive carrier organ:** complete positivity is the hypothesis needed for a Stinespring/GNS
   realization rather than a merely positive scalar shadow.

The phase-kernel theorem is the commutative level-one face. The present theorem proves why that
face cannot alone control noncommutative/all-degree receivers.

## 6. Frontier predictions

This law makes four falsifiable predictions before any route identification.

1. A fixed-degree positivity theorem cannot orient every adaptive `U` hyperedge unless the route
   comparison is proved completely positive at all relevant amplification levels.
2. Finite Gram positivity in `C1`, `G`, or `P` cannot promote to a positive carrier without an
   aperture-uniform complete gauge.
3. Whole-ground coercivity in `O` may fail through witnesses whose required matrix depth grows
   with aperture, even when every fixed-depth sector is uniformly controlled.
4. Singular descent in `L/R/CCM-FU` can erase the obstruction by a non-complete positive quotient;
   scalar positivity of the descended class does not prove source positivity.

These are theorem-driven design constraints. Literal route comparison functors realizing the
amplification variable are not yet constructed, so no route theorem is claimed here.

## 7. RH selection boundary

Only after constructing a pre-divisor arithmetic operator system may one ask whether its reflected
horizontal intervention has finite complete gauge. A legitimate selection theorem would have to
prove

\[
 \boxed{
 \sup_{\text{aperture }n}\sup_{\text{amplification }k}
 \kappa_{n,k}(Eta_\rho\mid Mu)<+\infinity
 \Longleftrightarrow \operatorname{Re}\rho=\tfrac12.}
 \tag{AGR.16}
\]

No such arithmetic operator system or equivalence currently exists. In particular, identifying
Hankel degree with matrix amplification without a literal complete-order comparison would be
fitting. The theorem narrows the selector: **uniform complete admission on the product-directed
source**, not positivity in another fixed route.

## 8. Hostile boundaries

1. CP-distance and `k`-positive robustness are established parent mathematics; no novelty claim is
   made for `(AGR.1)`--`(AGR.7)`.
2. The reduction pencil is not an RH source.
3. Matrix amplification is not automatically the same as derivative order, Hankel order, prime
   aperture, or homological degree.
4. Separate boundedness in each variable does not imply a joint bound; `(AGR.14)` is the exact
   counterexample.
5. Complete positivity can still erase source labels; it is an admission law, not coefficient
   faithfulness.
6. No literal all-route comparison or RH implication is claimed.

## 9. Literature parents

- Hou--Li--Poon--Qi--Sze, *Criteria and new classes of k-positive maps*, arXiv:1211.0386,
  Proposition 6.2 gives the generalized reduction threshold.
- Kian, *A Hierarchy of Deviation from Complete Positivity and Optimal Entanglement Witnesses*,
  arXiv:2506.03773, supplies CP-distance and the hierarchy `d_k`.
- Choi's theorem and Schmidt-rank witnesses supply the standard finite-dimensional receiver theory.

## 10. Gates

- [x] exact amplification gauge typed;
- [x] reduction-pencil threshold proved;
- [x] cofinal migrating-depth theorem proved;
- [x] false-promotion theorem proved;
- [x] scalar phase-kernel law placed as level-one face;
- [x] rank-one pencil and Choi threshold certified in Lean;
- [x] fixed-depth/diagonal false-promotion capstone certified in Lean;
- [x] full intermediate `k`-positive reduction-map threshold in Lean
      (`redPencil_posSemidef_forall_iff`, `isLevelPositive_reduction_iff`);
- [x] amplified gauge, monotonicity, complete-positivity criterion and data processing in Lean
      (`levelGauge`, `levelGauge_mono`, `levelFeasible_eq_Ici`,
      `isCompletelyPositiveMap_iff_forall_levelGauge_le`, `levelGauge_comp_le`);
- [x] exact profile, cofinal migration and false promotion in Lean
      (`levelGauge_reduction`, `completeGauge_reduction`, `isGreatest_fixed_depth_reduction`,
      `completeGauge_reduction_not_bddAbove`, `reduction_false_promotion`);
- [ ] literal arithmetic operator-system realization — **explicitly not claimed** by this card
      (§7: "No such arithmetic operator system or equivalence currently exists");
- [ ] RH selection theorem — **explicitly not claimed** by this card (§7).
