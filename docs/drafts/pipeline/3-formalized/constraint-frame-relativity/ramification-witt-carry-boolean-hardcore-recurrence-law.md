# Ramification binary Kummer carry, Boolean collision boundary, and marked three-storey holonomy law

- **ID:** `cfr-ramification-witt-carry`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / KUMMER--WITT ADMISSION-BOUNDARY BRIDGE / MARKED HISTORY CALIBRATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [HOSTILE-AUDITED] [SOURCE-DERIVED] [BOOLEAN-WITT CARRY] [ROUTE-E ADMISSION BOUNDARY] [MARKED HOLONOMY CALIBRATION] [NOT INTRINSIC CURVATURE] [NOT ORIENTATION] [NOT PHYSICAL TIME] [NOT RH] [FORMALIZED IN LEAN]`
- **Formalized companion:** `ramification-witt-carry-boolean-hardcore-recurrence-law-formalized.md`
- **Statement:** For two successive quadratic ramification stages, the Kummer extension is the
  length-two Witt thickening of the Boolean prime lattice. Its canonical digit carry is Boolean
  intersection. Hard-core multiplication is exactly its zero-carry locus; retaining rejected
  collision labels recovers the full carry. The same extension admits a marked three-storey
  history realization, but that realization adds no independent constitutive invariant.

## Goal

Make one source composition class appear without fitting in arithmetic residue and a non-Fourier
collision boundary, then test a marked history realization of that same class. Use the robust cell
`r=s=2`. Ordinary Route-E hard-core multiplication sees only the zero-carry locus; a
collision-labelled enrichment is required to retain the full carry subset.

## 1. Boolean lattice as the special fibre

Fix a finite prime aperture `F`. Let

\[
 \mathbb B_F=\mathcal P(F)
\]

with addition `S+T=S triangle T` (symmetric difference) and multiplication `ST=S intersect T`.
This is the Boolean ring `F_2^F`, canonically identified with

\[
 \mathsf K_2(F)=(\mathbb Z/2\mathbb Z)^F.
\tag{WC.1}
\]

The two-stage Kummer sequence is

\[
 0\longrightarrow\mathsf K_2(F)\xrightarrow{\times2}
 \mathsf K_4(F)\longrightarrow\mathsf K_2(F)\longrightarrow0.
\tag{WC.2}
\]

Let `sigma:B_F->K_4(F)` send a subset to its `0/1` characteristic vector.

### Theorem 1.1 — Boolean meet is the Kummer carry

For all `S,T subset F`,

\[
 \boxed{
 \sigma(S)+\sigma(T)
 =\sigma(S\triangle T)+2\sigma(S\cap T)
 \quad\text{in }(\mathbb Z/4)^F.}
\tag{WC.3}
\]

Thus the section defect is

\[
 \boxed{\kappa_2(S,T)=S\cap T.}
\tag{WC.4}
\]

Writing a mod-four vector uniquely as `(S,A)=sigma(S)+2sigma(A)`, addition is

\[
 \boxed{
 (S,A)\star(T,B)
 =(S\triangle T,
   A\triangle B\triangle(S\cap T)).}
\tag{WC.5}
\]

Consequently `K_4(F)` is the additive group of the length-two Witt ring

\[
 W_2(\mathbb F_2^F)\cong(\mathbb Z/4)^F,
\tag{WC.6}
\]

and `(WC.4)` is the first Witt carry polynomial.

### Proof

Coordinatewise, `1+1=0+2` in `Z/4`, while `1+0=1` and `0+0=0`. This is exactly `(WC.3)`.
Adding `2sigma(A)+2sigma(B)` uses symmetric difference because a double overlap contributes four,
which is zero mod four; this proves `(WC.5)`. Formula `(WC.5)` is the standard length-two
2-typical Witt addition law over a Boolean `F_2`-algebra. `[PROVED HERE]`

The class is nonzero: `kappa_2({p},{p})={p}`. Changing the set-theoretic section alters the
cocycle by a coboundary but cannot split `(WC.2)`.

More explicitly, for nonempty `F`, `(WC.2)` is nonsplit. A group section would lift a nonzero
basis element of order two to an element of `K_4(F)` reducing to one in that coordinate, but every
such lift has order four. Associativity of `(WC.5)` is the cocycle identity

\[
 \boxed{
 \kappa_2(S,T)\triangle\kappa_2(S\triangle T,R)
 =\kappa_2(T,R)\triangle\kappa_2(S,T\triangle R).}
\tag{WC.6a}
\]

Coordinatewise, both sides equal the parity of the three pair products. Thus the representative
depends on the binary digit section, while its extension class does not.

## 2. Literal shell hard-core law

For squarefree integers `k,l` supported on `F`, put `S=supp(k)` and `T=supp(l)`. Then

\[
 v(kl)\bmod4
 =\mathbf1_{S\triangle T}+2\mathbf1_{S\cap T}.
\tag{WC.7}
\]

Let `tilde a_m` be the unitalized fixed shell stream from the ramification cards.

### Theorem 2.1 — shell activity is zero carry

For every `m>=2`,

\[
 \boxed{
 \widetilde a_m((kl)^m)=1
 \quad\Longleftrightarrow\quad
 \kappa_2(S,T)=\varnothing.}
\tag{WC.8}
\]

### Proof

In `(kl)^m`, primes in `S triangle T` have exponent `m`, while primes in `S intersect T` have
exponent `2m`. If the intersection is empty and `kl>1`, the maximal exponent is `m`; if both are
one, unitalization gives value one. If the intersection is nonempty, the maximal exponent is
`2m`, so the level-`m` stream vanishes. `[PROVED HERE]`

Thus Route-E hard-core exclusion is not an added Fock convention in this chart. It is the
zero-carry locus of the source Kummer--Witt extension. The full carry remembers the collision set,
not only whether a collision occurred.

Writing `g=gcd(k,l)` and `k triangle l=kl/g^2`, the stronger integer identity is

\[
 \boxed{
 k^m l^m=(k\mathbin{\triangle}l)^m g^{2m}
 =n_{S\triangle T}\,P_2(n_{S\cap T}).}
\tag{WC.8a}
\]

The second factor is the exact discarded repeat-occupancy datum. Ordinary hard-core multiplication
is defined only when this factor is trivial. Therefore admitted Route-E multiplication is flat;
the full subset-valued cocycle lives on its collision boundary. A collision-labelled ideal or
multigrading is required to carry that full class inside an enlarged Route-E doctrine.

## 3. Gibbs collision predictions

Fix `sigma>=0`. Under the finite Boolean Gibbs law, each prime is occupied independently with

\[
 q_p={p^{-\sigma}\over1+p^{-\sigma}}.
\tag{WC.9}
\]

More generally, let `S,T` be independent samples with respective one-prime probabilities
`q_p,u_p`, independent across primes, and let `Kappa=S intersect T`.

### Theorem 3.1 — exact carry statistics

\[
 \boxed{
 \mathbb E|\Kappa|=\sum_{p\in F}q_pu_p,}
\tag{WC.10}
\]

and

\[
 \boxed{
 \mathbb P(\Kappa=\varnothing)
 =\prod_{p\in F}(1-q_pu_p).}
\tag{WC.11}
\]

### Proof

The event `p in Kappa` is the intersection of two independent Bernoulli events and has probability
`q_pu_p`. Linearity of expectation gives `(WC.10)`. These intersection events are independent
across primes, so their simultaneous absence has probability `product_p(1-q_pu_p)`.
`[PROVED HERE]`

For two replicas of the same Gibbs law `(WC.9)`, this specializes to

\[
 \boxed{
 \mathbb E|\Kappa|=\sum_{p\in F}q_p^2,
 \qquad
 \mathbb P(\Kappa=\varnothing)
 =\prod_{p\in F}{1+2p^{-\sigma}\over(1+p^{-\sigma})^2}.}
\tag{WC.11a}
\]

The unconditional carry probability `q_p^2` is not the escort transform. Conditional on zero
outer residue `p notin S triangle T`, it becomes

\[
 \mathbb P(p\in\Kappa\mid p\notin S\triangle T)
 ={q_p^2\over q_p^2+(1-q_p)^2}
 =\mathcal R_2(q_p).
\tag{WC.11b}
\]

By `(WC.8)`, `(WC.11)` is exactly the probability that multiplying two independent squarefree
states remains in the active level-`m` shell after applying the `m`-th power diagonal.

## 4. Marked three-storey history realization

For `S subset F`, let `1_S in Z^F` be its characteristic vector. Consider the marked discrete
history

\[
 h_S(n)=n\mathbf1_S\in\mathbb Z^F,
\tag{WC.12}
\]

and its projections to `K_4(F)` and `K_2(F)`.

### Theorem 4.1 — finite quotient holonomy

If `S` is nonempty, then:

1. the mod-two observer closes after two steps;
2. the mod-four lift does not close after two steps, but lands at the kernel point `2 sigma(S)`;
3. the mod-four lift closes after four steps;
4. the integral history never closes and `||h_S(n)||_2=n sqrt(|S|)`;
5. the one-loop holonomy is the carry

\[
 \boxed{
 h_S(2)\bmod4=2\sigma(\kappa_2(S,S))=2\sigma(S).}
\tag{WC.13}
\]

### Proof

Reduce `n 1_S` modulo two and four. At `n=2`, its mod-two value is zero and its mod-four value is
`2 sigma(S)`, nonzero for nonempty `S`; at `n=4` the mod-four value is zero. The norm formula is
immediate. Finally, `kappa_2(S,S)=S intersect S=S`. `[PROVED HERE]`

This is an exact finite model of closed observer projection, delayed law lift, and open marked
history. It is the regular cyclic realization of the already-known extension class, not an
independent recurrence mechanism. It supplies no physical clock, action, complexity, black-hole,
or wormhole theorem.

## 5. CFR consequence

One source class now has three exact presentations:

\[
 \boxed{
 \text{Kummer/Witt extension carry}
 \longleftrightarrow
 \text{collision-labelled hard-core boundary}
 \longleftrightarrow
 \text{recurrence-lift holonomy}.}
\tag{WC.14}
\]

This is more than an atlas analogy. The maps and equalities are explicit and use no RH target.
It supplies the first source-derived identification of a genuine Kummer extension class with a
non-Fourier Route-E admission-boundary label. The marked history is a third gauge of the same
class, not third independent evidence.

The architecture suggested by this exact chart is **Witt-thickened constraint geometry**:

- Boolean incidence is the special fibre;
- hidden higher residue digits are infinitesimal/thickened law directions;
- carries are extension/transition data;
- finite quotient recurrence is a coarse quotient of the marked thickened history;
- an observer that keeps only the first digit necessarily erases collision history.

This is a local CFR chart, not yet the universal field. No result identifies higher Witt digits
with HT prolongation, Stokes contact, cofinal topology, or physical interior length.

## 6. Conjecture / proof / fail loops

1. **Boolean hard-core exclusion is independent of ramification composition.** Failed by
   `(WC.8)`. **Survivor:** it is exactly the zero-carry locus.
2. **Support sees only whether carry is nonzero.** Failed in the quadratic cell: `(WC.4)` recovers
   the full carry subset. **Survivor:** `r=s=2` is the robust full-class bridge; general factors
   need colored residue digits.
3. **Observed finite quotient recurrence closes the marked law history.** Failed by `(WC.13)`.
   **Survivor:** each base return advances a kernel holonomy.
4. **Carry holonomy is physical time or wormhole length.** Not proved. **Survivor:** it is a finite
   source-marked recurrence delay and universal-cover cost lower bound only.
5. **This bridge supplies orientation.** Failed: Boolean meet is unsigned. **Survivor:** signed
   exterior orientation remains an independent observer organ.

## 7. Scope and parents

- Finite `F` is used for probability and finite history norms. The algebraic identities extend
  coordinatewise to the full finite-support prime lattice.
- The full carry bridge is proved only for two quadratic stages. General `r,s` require full colored
  residue labels; support alone is insufficient.
- The section `sigma` is the least nonnegative digit section. Other sections change the cocycle
  representative by a coboundary, not its extension class.
- Ordinary Route-E multiplication contains only the zero-carry locus. Full-class language always
  means the collision-labelled admission boundary, not the admitted hard-core algebra alone.
- The architecture is classical truncated Witt arithmetic applied to the HGT shell source. Current
  parents include Bauer on mod-two carry/Bockstein ([arXiv:2403.12119](https://arxiv.org/abs/2403.12119))
  and Pakianathan--Yalcin on 2-power extensions and quadratic maps
  ([arXiv:1007.2390](https://arxiv.org/abs/1007.2390)).
- No exterior sign, Hall allocation, directed Route-E seam, Stokes contact, physical action, Xi
  condition, or RH theorem is asserted.
- No Lean file has been written or built.

## Lean-return notes

- Reuse the Boolean divisor-lattice and Kummer exponent parents.
- Formalize `(WC.3)` coordinatewise before packaging finite subsets.
- Keep probability and recurrence consequences in separate later modules.
- No Lean file has been written or built.

## Gates

- [x] full Kummer carry class on a source-native finite chart
- [x] Route-E Boolean zero-carry and collision-boundary realization
- [x] exact Gibbs carry predictions
- [x] marked finite-quotient holonomy realization of the same class
- [x] explicit multi-gauge comparison
- [x] hostile interpretation acceptance
- [ ] collision-labelled Route-E totalization and source-composition coherence
- [ ] signed orientation/contact/topology realization
- [ ] presentation/Morita invariance beyond marked prime lattice
- [ ] Lean formalization

## Log

- 2026-08-09 — constructed after Kummer extension audit identified Boolean intersection as the
  exact quadratic carry and truncated Witt addition law.
- 2026-08-09 — hostile audit separated admitted zero-carry Route-E multiplication from its
  collision-labelled boundary and demoted marked recurrence to a gauge of the same extension.
