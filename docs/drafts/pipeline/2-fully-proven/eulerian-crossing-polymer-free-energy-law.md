# Eulerian crossing polymers have a cubic-density free-energy tax

- **ID:** `eulerian-crossing-polymer-free-energy-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** THEOREM (paper) / static-Gaussian crossing-memory bridge
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, obligation O4
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [PHYSICAL ACTIVITY INTERFACE OPEN]`
- **Statement:** If nontrivial crossing-memory polymers are Eulerian, then their compatible-gas
  free energy at replica density `k = kappa n` is `O(kappa^3 n)`, so it cannot erase a linear
  planar action gap at sufficiently small fixed density.

## Goal

Close the "collective signed free energy of extensively many small components" left open after
equations `(O4.16)--(O4.22)` of the parent card.  The result must sum every compatible collection,
not merely show that each component is logarithmic.  It does not assert the still-missing physical
activity domination after cavity dressing and the nonlinear circuit Bellman step.

## Theorem A -- compatible-polymer partition bound

Let `V` be finite and let `P` be a finite family of nonempty subsets of `V`.  Give every
`gamma in P` an activity `w_gamma >= 0`.  A subfamily is compatible when its members are pairwise
disjoint, and put

\[
 Z(P,w)=\sum_{F\subseteq P\,\text{compatible}}\prod_{\gamma\in F}w_\gamma .       \tag{1}
\]

Then

\[
 \boxed{Z(P,w)\leq\exp\!\left(\sum_{\gamma\in P}w_\gamma\right).}                \tag{2}
\]

### Proof

All summands are nonnegative, so deleting compatibility only enlarges `(1)`.  Expanding a finite
product gives

\[
 Z(P,w)\leq\sum_{F\subseteq P}\prod_{\gamma\in F}w_\gamma
 =\prod_{\gamma\in P}(1+w_\gamma)
 \leq\prod_{\gamma\in P}e^{w_\gamma}
 =e^{\sum_\gamma w_\gamma}.
\]

This retains every compatible collection and uses no independence assumption.  QED.

## Theorem B -- Eulerian cubic-density law

Assume every polymer has at least three vertices.  Suppose `n>0`, `q>0`, `0<=x<1`, and for every
integer `v>=3`,

\[
 \sum_{\substack{\gamma\in P\\|\gamma|=v}}w_\gamma
 \leq {n\over q^2}{x^v\over v^2}.                                  \tag{3}
\]

Then

\[
 \boxed{\log Z(P,w)
 \leq {n\over q^2}{x^3\over9(1-x)}.}                               \tag{4}
\]

### Proof

Theorem A and `(3)` give

\[
 \log Z\leq\sum_{v\ge3}{n\over q^2}{x^v\over v^2}
 \leq {n\over9q^2}\sum_{v\ge3}x^v
 ={n\over q^2}{x^3\over9(1-x)}.
\]

All sums may be stopped at `|V|`; extending by nonnegative terms gives the displayed geometric
series.  QED.

## Corollary C -- local-support activity and survival of a linear gap

Let `|V|=k<=kappa n`.  Suppose each size-`v` polymer has activity at most

\[
 w_\gamma\leq A^v v^{v-2}\left({q^2\over n}\right)^{v-1}.           \tag{5}
\]

Using `binom(k,v)<=(e k/v)^v`, the total size-`v` activity is at most

\[
 {n\over q^2}{(eAq^2k/n)^v\over v^2}
 \leq {n\over q^2}{(eAq^2\kappa)^v\over v^2}.                      \tag{6}
\]

Thus Theorem B applies with `x=eAq^2 kappa`.  In particular, for `x<=1/2`,

\[
 \boxed{\log Z\leq {2e^3A^3q^4\over9}\,\kappa^3n.}                 \tag{7}
\]

If a normalized planar/cavity contribution supplies a factor `exp(-eta k)`, take
`k=floor(kappa n)`, `n>=2/kappa`, and assume

\[
 {2e^3A^3q^4\over9}\kappa^2\leq{\eta\over4}.                      \tag{8}
\]

Then `k>=kappa n/2`, and `(7)--(8)` give

\[
 \boxed{e^{-\eta k}Z\leq e^{-\eta\kappa n/4}.}                    \tag{9}
\]

Hence an extensive number of small Eulerian crossing components does not destroy exponential
decay: its free-energy tax begins at order `kappa^3 n`, while the surviving action is order
`kappa n`.

## Physical interface and hostile audit

1. The abstract gas is fully summed.  No "all components are logarithmic, therefore harmless"
   inference is used.
2. Pairwise incompatibility can only lower the partition function, so overlap correlations cannot
   invalidate `(2)`.
3. The exponent is cubic because a nonempty connected simple Eulerian graph contains a cycle and
   therefore has at least three vertices.  If one- or two-vertex memory survives the physical
   return/carrier excision, the theorem does not apply and the tax can be linear.
4. The tree-exposure bound `(O4.16)` gives `(5)` before dressing, with `A=1`.  The remaining
   physical obligation is to prove that exact planar-cavity dressing, replica joins, seed parity,
   and the bounded Bellman reporter multiply each connected activity by at most `A^v` for one
   constant `A` independent of `n,k,v`.
5. Equation `(9)` is not yet a static-Hamiltonian complexity theorem.  It closes the collective
   polymer summation once the activity interface is supplied; it does not supply that interface.
6. The product expansion and `1+u<=e^u` are standard polymer-gas combinatorics.  Candidate new
   content is the Eulerian/local-support application: the parent frontier's apparently extensive
   crossing memory has a cubic-density, rather than linear-density, action cost.

## Gates

- [x] 0 -> 1: exact object and falsifier identified
- [x] 1 -> 2: dependency-closed proof above
- [ ] 2 -> 3: formalize Theorems A--C in Lean
- [ ] Physical composition: prove the uniform dressed-activity bound `(5)`

## Log

- 2026-08-20 -- Conjecture loop: occurrence-probability control was insufficient at `k=Theta(n)`;
  compatible-gas resummation proved the cubic-density free-energy law and isolated one exact
  dressed-activity interface.
