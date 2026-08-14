# Ramification Gibbs--GNS defect, spectral--information fusion, and boundary-work law

- **ID:** ULF-FEM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Programme:** Formation-Excess Mechanics
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE-NATIVE FORMATION] [FIVE-ORGAN FUSION] [JOINT RECONSTRUCTION] [CROSSED WORK COCYCLE] [RELATIVE PROPERNESS] [NO LEAN IN THIS PASS] [NOT RH]

## 1. Source formation

For an integer (m\ge12), let

\[
 A_m=\{n\ge2:\max_p v_p(n)=m\},
 \qquad
 a_m(n)=\mathbf1_{A_m}(n),
 \tag{FE.1}
\]

and, for (\Re z>1),

\[
 S_m(z)=\sum_{n\in A_m}n^{-z}.
 \tag{FE.2}
\]

Fix an integer (r\ge2).  The source power map

\[
 P_r:A_m\longrightarrow A_{rm},
 \qquad P_r(k)=k^r,
 \tag{FE.3}
\]

is injective.  Define its excess

\[
 X_{m,r}=A_{rm}\setminus P_r(A_m)
 \tag{FE.4}
\]

and excess Dirichlet series

\[
 C_{m,r}(z)=\sum_{N\in X_{m,r}}N^{-z}.
 \tag{FE.5}
\]

Every exponent of an (r)-th power is divisible by (r), and taking the unique positive
(r)-th root recovers (A_m).  Hence

\[
 \boxed{A_{rm}=P_r(A_m)\sqcup X_{m,r}}
 \tag{FE.6}
\]

and

\[
 \boxed{S_{rm}(z)=S_m(rz)+C_{m,r}(z).}
 \tag{FE.7}
\]

The excess is nonempty: (2^{rm}3\in A_{rm}) but is not an (r)-th power.

## 2. Positive measure formation

For real (\sigma>1), define the finite positive atomic measures

\[
 \mu_{m,\sigma}
 =\sum_{n\in A_m}n^{-\sigma}\delta_{\log n},
 \tag{FE.8}
\]

\[
 \eta_{m,r,\sigma}
 =\sum_{N\in X_{m,r}}N^{-\sigma}\delta_{\log N}.
 \tag{FE.9}
\]

Finiteness follows from domination by (\sum_{n\ge2}n^{-\sigma}).  Let

\[
 d_r:\mathbb R\to\mathbb R,
 \qquad d_r(x)=rx.
 \tag{FE.10}
\]

### Theorem 2.1 -- unnormalized formation identity

For every (m\ge12,r\ge2,\sigma>1),

\[
 \boxed{
 \mu_{rm,\sigma}
 =(d_r)_*\mu_{m,r\sigma}+\eta_{m,r,\sigma}.}
 \tag{FE.11}
\]

The two measures on the right have disjoint supports.  Their masses are

\[
 Z^{\mathrm{in}}_{m,r}(\sigma)=S_m(r\sigma),
 \qquad
 Z^{\mathrm{ex}}_{m,r}(\sigma)=C_{m,r}(\sigma),
 \tag{FE.12}
\]

and the total mass is (S_{rm}(\sigma)).

#### Proof

The atom (k\in A_m) contributes (k^{-r\sigma}\delta_{r\log k}) to the pushforward.  This is
exactly the target atom ((k^r)^{-\sigma}\delta_{\log(k^r)}).  These are precisely the inherited
atoms (P_r(A_m)); the remaining target atoms are exactly (FE.9).  Disjointness and the mass
formulas follow from (FE.6). ∎

Normalize

\[
 P_{m,\sigma}=\frac{\mu_{m,\sigma}}{S_m(\sigma)},
 \qquad
 I_{m,r,\sigma}=(d_r)_*P_{m,r\sigma},
 \qquad
 Q_{m,r,\sigma}=\frac{\eta_{m,r,\sigma}}{C_{m,r}(\sigma)}.
 \tag{FE.13}
\]

The witness above makes (C_{m,r}(\sigma)>0), so all three probabilities are defined.  Put

\[
 \alpha_{m,r}(\sigma)
 =\frac{S_m(r\sigma)}{S_{rm}(\sigma)},
 \qquad
 \beta_{m,r}(\sigma)
 =\frac{C_{m,r}(\sigma)}{S_{rm}(\sigma)}.
 \tag{FE.14}
\]

Then (0<\alpha,\beta<1) and (\alpha+\beta=1).

### Corollary 2.2 -- canonical mixture formation

\[
 \boxed{
 P_{rm,\sigma}
 =\alpha_{m,r}(\sigma)I_{m,r,\sigma}
 +\beta_{m,r}(\sigma)Q_{m,r,\sigma}.}
 \tag{FE.15}
\]

This is not an arbitrary mixture model: the source power map, shell support, and Mellin weight fix
both conditional laws and both coefficients.

## 3. GNS and cross-fibre spectral fusion

Use the canonical coordinate realizations

\[
 \mathcal H_m=\ell^2(A_m),
 \qquad
 \mathcal H_{m,r}^{\mathrm{ex}}=\ell^2(X_{m,r}).
 \tag{FE.16}
\]

Let (e_n) denote the coordinate basis and define

\[
 T_r:\mathcal H_m\to\mathcal H_{rm},
 \qquad T_re_k=e_{k^r}.
 \tag{FE.17}
\]

It is an isometry.  Its range projection and defect projection are

\[
 R_r=T_rT_r^*,
 \qquad
 Q_r=1-R_r.
 \tag{FE.18}
\]

The cyclic probability vectors are

\[
 \Omega_{m,\sigma}
 =\sum_{n\in A_m}\sqrt{P_{m,\sigma}(n)}e_n,
 \tag{FE.19}
\]

and similarly (\Omega^{\mathrm{ex}}_{m,r,\sigma}).  Define the positive diagonal clock

\[
 D_me_n=(\log n)e_n
 \tag{FE.20}
\]

on its maximal domain.

### Theorem 3.1 -- orthogonal formation fusion

There are exact orthogonal decompositions

\[
 \boxed{
 \mathcal H_{rm}
 =T_r\mathcal H_m\oplus\mathcal H_{m,r}^{\mathrm{ex}},}
 \tag{FE.21}
\]

\[
 \boxed{
 \Omega_{rm,\sigma}
 =\sqrt{\alpha_{m,r}(\sigma)}\,T_r\Omega_{m,r\sigma}
 +\sqrt{\beta_{m,r}(\sigma)}\,\Omega^{\mathrm{ex}}_{m,r,\sigma},}
 \tag{FE.22}
\]

and

\[
 \boxed{
 D_{rm}T_r=rT_rD_m,
 \qquad
 D_{rm}\cong rD_m\oplus D_{m,r}^{\mathrm{ex}}.}
 \tag{FE.23}
\]

In particular,

\[
 \boxed{
 \langle\Omega_{rm,\sigma},Q_r\Omega_{rm,\sigma}\rangle
 =\beta_{m,r}(\sigma).}
 \tag{FE.24}
\]

#### Proof

The coordinate basis of (A_{rm}) is the disjoint union of the inherited and excess bases, proving
(FE.21).  On an inherited coordinate (k^r), the target probability is

\[
 \frac{k^{-r\sigma}}{S_{rm}(\sigma)}
 =\alpha_{m,r}(\sigma)
   \frac{k^{-r\sigma}}{S_m(r\sigma)}.
\]

On an excess coordinate it is (\beta) times the normalized excess probability.  Taking positive
square roots gives (FE.22).  Finally,

\[
 D_{rm}T_re_k
 =(\log k^r)e_{k^r}
 =r(\log k)T_re_k,
\]

first on finitely supported vectors and then on maximal domains.  The second block is the restriction
to the invariant excess coordinates.  Projecting (FE.22) onto that block gives (FE.24). ∎

This is a literal source realization of a cross-fibre scale law.  It does not contradict the
same-fibre pure-point Mautner no-go: (T_r) is isometric but not onto, and the target has a nonzero
defect sector.

### Corollary 3.2 -- characteristic fusion

For every real (t),

\[
 \boxed{
 \frac{S_{rm}(\sigma+it)}{S_{rm}(\sigma)}
 =\alpha_{m,r}(\sigma)
   \frac{S_m(r(\sigma+it))}{S_m(r\sigma)}
 +\beta_{m,r}(\sigma)
   \frac{C_{m,r}(\sigma+it)}{C_{m,r}(\sigma)}.}
 \tag{FE.25}
\]

#### Proof

Pair (e^{-itD_{rm}}\) against the three cyclic vectors in (FE.22), or divide (FE.7) at
(z=\sigma+it) by (S_{rm}(\sigma)).  Orthogonality kills cross terms. ∎

### Corollary 3.3 -- heat-trace valuation

For (t>1), all three positive heat operators are trace class and

\[
 \boxed{
 \operatorname{Tr}e^{-tD_{rm}}
 =\operatorname{Tr}e^{-rtD_m}
 +\operatorname{Tr}e^{-tD_{m,r}^{\mathrm{ex}}}.}
 \tag{FE.26}
\]

The three traces are respectively (S_{rm}(t)), (S_m(rt)), and (C_{m,r}(t)).

#### Proof

Each operator is positive diagonal and its trace is the sum of its diagonal entries.  The sums
converge by (t>1).  The basis partition (FE.6) proves the identity. ∎

## 4. Joint reconstruction

### Theorem 4.1 -- marked spectral reconstruction

The marked spectral packet

\[
 (\mathcal H_{rm},D_{rm},\Omega_{rm,\sigma},Q_r)
 \tag{FE.27}
\]

reconstructs all of the following:

1. the target probability (P_{rm,\sigma});
2. the inherited/excess support partition;
3. the masses (\alpha_{m,r}(\sigma),\beta_{m,r}(\sigma));
4. both conditional laws (I_{m,r,\sigma},Q_{m,r,\sigma}); and
5. the unnormalized measures after adjoining the marked total mass (S_{rm}(\sigma)).

Equivalently, the scalar spectral measure of (D_{rm}) in (\Omega_{rm,\sigma}), together with the
commuting marked projection (Q_r), reconstructs the normalized formation completely.

#### Proof

The eigenvalues (\log n) are distinct because logarithm is injective on positive integers.  The
spectral mass of (\{\log n\}) in the cyclic vector is

\[
 |\langle e_n,\Omega_{rm,\sigma}\rangle|^2=P_{rm,\sigma}(n),
\]

so the target law is recovered atom by atom.  The diagonal projection (Q_r) marks precisely the
excess atoms.  Its cyclic expectation is (\beta); (1-Q_r) has expectation (\alpha).  Restricting
and renormalizing the recovered masses gives the two conditional laws.  Multiplication by the
marked total mass recovers the unnormalized measure. ∎

### Corollary 4.2 -- exact loss of unmarked normalization

The normalized packet without (S_{rm}(\sigma)) cannot reconstruct the absolute coefficient scale:
replacing (\mu_{rm,\sigma}) by (c\mu_{rm,\sigma}), (c>0), leaves
(P_{rm,\sigma}), the GNS packet, (\alpha), (\beta), and both conditionals unchanged.

Thus joint reconstruction is exact only for the stated marked packet.  This is an information-loss
boundary, not a proof gap.

## 5. Information fusion and canonical formation work

For probabilities (P,Q) on a countable set, use

\[
 D(P\|Q)=\sum_xP(x)\log\frac{P(x)}{Q(x)},
 \tag{FE.28}
\]

with value (+\infty) when (P) charges a (Q)-null atom.  For two Bernoulli laws write

\[
 d_{\mathrm{Ber}}(a\|b)
 =a\log\frac ab+(1-a)\log\frac{1-a}{1-b}.
 \tag{FE.29}
\]

### Theorem 5.1 -- exact information chain

For (\sigma,\tau>1),

\[
 \boxed{
 \begin{aligned}
 D(P_{rm,\sigma}\|P_{rm,\tau})
 ={}&d_{\mathrm{Ber}}(\alpha_{m,r}(\sigma)\|\alpha_{m,r}(\tau))\\
 &+\alpha_{m,r}(\sigma)
 D(P_{m,r\sigma}\|P_{m,r\tau})\\
 &+\beta_{m,r}(\sigma)
 D(Q_{m,r,\sigma}\|Q_{m,r,\tau}).
 \end{aligned}}
 \tag{FE.30}
\]

Every displayed divergence is finite.

#### Proof

On inherited atoms (P_{rm,\sigma}=\alpha_\sigma I_\sigma) and
(P_{rm,\tau}=\alpha_\tau I_\tau); on excess atoms the corresponding expressions are
(\beta_\sigma Q_\sigma) and (\beta_\tau Q_\tau).  Split (FE.28) over the disjoint supports and
expand the logarithms.  The coefficient-only terms sum to (FE.29), and the remaining terms are the
two conditional divergences.  Pushforward by the injection (d_r) preserves the inherited
divergence, giving the middle line of (FE.30).

For example, on a shell atom (n), the logarithmic likelihood ratio between temperatures
(\sigma) and (\tau) is a constant plus ((\tau-\sigma)\log n).  Its absolute expectation is finite
because every logarithmic moment of a Dirichlet series converges in (\Re z>1).  The same argument
applies after restriction to the excess. ∎

Define the formation work by asking how costly it is to mistake the inherited conditional law for
the full target law:

\[
 W_{m,r}(\sigma)
 =D(I_{m,r,\sigma}\|P_{rm,\sigma}).
 \tag{FE.31}
\]

### Theorem 5.2 -- exact work, affinity, and total variation

\[
 \boxed{
 W_{m,r}(\sigma)
 =-\log\alpha_{m,r}(\sigma)
 =\log S_{rm}(\sigma)-\log S_m(r\sigma)>0.}
 \tag{FE.32}
\]

Moreover,

\[
 \boxed{D(P_{rm,\sigma}\|I_{m,r,\sigma})=+\infty,}
 \tag{FE.33}
\]

\[
 \boxed{\operatorname{Aff}(P_{rm,\sigma},I_{m,r,\sigma})=\sqrt\alpha,}
 \tag{FE.34}
\]

and, with total variation (\frac12\|P-Q\|_1),

\[
 \boxed{\operatorname{TV}(P_{rm,\sigma},I_{m,r,\sigma})=\beta.}
 \tag{FE.35}
\]

#### Proof

On inherited support (P_{rm,\sigma}=\alpha I_{m,r,\sigma}), so the likelihood ratio
(I/P) is the constant (1/\alpha).  This proves (FE.32).  The reverse divergence is infinite
because the full target gives positive mass (\beta) to excess atoms on which (I) is zero.
For affinity,

\[
 \sum_{\mathrm{inherited}}\sqrt{P I}
 =\sum\sqrt{\alpha}\,I=\sqrt\alpha.
\]

The inherited contribution to the (L^1) distance is (1-\alpha=\beta), and the excess
contribution is another (\beta), proving (FE.35). ∎

## 6. Formation composition and crossed conservation

Let (s\ge2).  Iterated power formation gives the disjoint three-layer refinement

\[
 \boxed{
 A_{srm}
 =P_{sr}(A_m)
 \sqcup P_s(X_{m,r})
 \sqcup X_{rm,s}.}
 \tag{FE.36}
\]

At temperature (\sigma>1), the unnormalized layer masses are

\[
 S_m(sr\sigma),
 \qquad C_{m,r}(s\sigma),
 \qquad C_{rm,s}(\sigma).
 \tag{FE.37}
\]

Their sum is (S_{srm}(\sigma)).

### Theorem 6.1 -- multiplicative survival and additive work

\[
 \boxed{
 \alpha_{m,sr}(\sigma)
 =\alpha_{rm,s}(\sigma)\,\alpha_{m,r}(s\sigma).}
 \tag{FE.38}
\]

Consequently,

\[
 \boxed{
 W_{m,sr}(\sigma)
 =W_{rm,s}(\sigma)+W_{m,r}(s\sigma).}
 \tag{FE.39}
\]

#### Proof

Directly from (FE.14),

\[
 \alpha_{rm,s}(\sigma)\alpha_{m,r}(s\sigma)
 =\frac{S_{rm}(s\sigma)}{S_{srm}(\sigma)}
  \frac{S_m(rs\sigma)}{S_{rm}(s\sigma)}
 =\frac{S_m(sr\sigma)}{S_{srm}(\sigma)}.
\]

This is (\alpha_{m,sr}(\sigma)).  Applying (-\log) proves (FE.39). ∎

### Corollary 6.2 -- associative refinement of all fused shadows

The coefficient split, positive measure split, orthogonal GNS sum, diagonal spectral valuation, and
KL information chain refine according to the same three masses (FE.37).  Refining first by (s)
and then by (r), or directly by (sr), gives identical final summands and identical total work.

#### Proof

Equation (FE.36) is an equality of disjoint sets.  Restricting one positive atomic measure to its
three subsets is independent of parenthesization.  Coordinate (\ell^2) sends disjoint unions to
orthogonal sums; trace is additive; the proof of Theorem 5.1 can be applied successively to the same
three-way partition.  The scalar work identity is Theorem 6.1. ∎

The parameter transport (\sigma\mapsto s\sigma) is load-bearing.  Ordinary unshifted additivity is
false in general.

## 7. Normalization-wall coercivity and relative properness

The shell theorem (S_j(z)=\zeta(z)H_j(z)), with (H_j) holomorphic near (1) and
(H_j(1)>0), gives

\[
 S_j(\sigma)\longrightarrow+\infty
 \qquad(\sigma\downarrow1).
 \tag{FE.40}
\]

For (r\ge2), (S_m(r\sigma)\to S_m(r)<\infty).

### Theorem 7.1 -- boundary formation law

As (\sigma\downarrow1),

\[
 \boxed{
 \alpha_{m,r}(\sigma)\to0,
 \quad \beta_{m,r}(\sigma)\to1,
 \quad W_{m,r}(\sigma)\to+\infty,}
 \tag{FE.41}
\]

\[
 \boxed{
 \operatorname{Aff}(P_{rm,\sigma},I_{m,r,\sigma})\to0,
 \quad
 \operatorname{TV}(P_{rm,\sigma},I_{m,r,\sigma})\to1.}
 \tag{FE.42}
\]

As (\sigma\to+\infty),

\[
 \boxed{
 \alpha_{m,r}(\sigma)\to1,
 \quad \beta_{m,r}(\sigma)\to0,
 \quad W_{m,r}(\sigma)\to0.}
 \tag{FE.43}
\]

#### Proof

The first line follows from (FE.40), finiteness of (S_m(r)), and (FE.14); (FE.42) then follows
from Theorem 5.2.

For the second limit, the unique smallest atom of (A_{rm}) is (2^{rm}), and it lies in the
inherited image of (2^m).  Multiply numerator and denominator of (\alpha) by
(2^{rm\sigma}).  The leading term in each becomes (1).  Every other term tends to zero and is
dominated, for any fixed (\sigma_0>1), by the summable majorant
((2^{rm}/n)^{\sigma_0}).  Dominated convergence gives ratio (1).  The remaining limits follow. ∎

### Corollary 7.2 -- relative properness of the normalization wall

Fix (\Sigma>1).  The continuous map

\[
 W_{m,r}:(1,\Sigma]\longrightarrow[0,+\infty)
 \tag{FE.44}
\]

is proper.  Equivalently, every bounded-work subset of ((1,\Sigma]) is bounded away from
(\sigma=1).

#### Proof

Dirichlet series are continuous on (\Re z>1), so (W) is continuous.  If
(K\subset[0,+\infty)) is compact, it is bounded above.  By (FE.41), (W^{-1}(K)) is separated
from (1).  It is closed in ((1,\Sigma]), hence closed in a compact interval
([1+\varepsilon,\Sigma]), and is compact. ∎

This is a genuine global formation/properness theorem near the normalization boundary.  It does not
make (W) a global selector: (W\to0) at the opposite low-temperature end.

## 8. Fourth-organ prediction: Kummer participation

Let

\[
 \mathsf K_r=\bigoplus_p\mathbb Z/r\mathbb Z
\]

be the valuation-residue group.  The inherited power image is residue (0).  For
(\gamma\in\mathsf K_r), let

\[
 A_\gamma(\sigma)
 =\sum_{\substack{n\in A_{rm}\\[v(n)]_r=\gamma}}n^{-\sigma},
 \tag{FE.45}
\]

and let (\Pi_\gamma) be the coordinate projection onto that sector.  The existing Kummer
Parseval invariant is

\[
 \mathcal V_{m,r}(\sigma)
 =\sum_{\gamma\ne0}A_\gamma(\sigma)^2.
 \tag{FE.46}
\]

### Theorem 8.1 -- GNS collision prediction

\[
 \boxed{
 \sum_{\gamma\ne0}
 \|\Pi_\gamma\Omega_{rm,\sigma}\|^4
 =\frac{\mathcal V_{m,r}(\sigma)}{S_{rm}(\sigma)^2}.}
 \tag{FE.47}
\]

Conditioned on formation excess,

\[
 \boxed{
 \sum_{\gamma\ne0}
 \left(\frac{A_\gamma(\sigma)}{C_{m,r}(\sigma)}\right)^2
 =\frac{\mathcal V_{m,r}(\sigma)}{C_{m,r}(\sigma)^2}.}
 \tag{FE.48}
\]

Thus the normalized Kummer Parseval energy is exactly the collision probability, or exponential
Rényi-(2) concentration, of the excess-sector label.

#### Proof

The squared norm of the sector projection is its target probability:

\[
 \|\Pi_\gamma\Omega_{rm,\sigma}\|^2
 =\frac{A_\gamma(\sigma)}{S_{rm}(\sigma)}.
\]

Square and sum over (\gamma\ne0) to obtain (FE.47).  Dividing the same sector masses by total
excess mass instead gives (FE.48). ∎

This theorem was predicted from the GNS formation split and then checked against the independently
constructed Kummer Parseval organ.  It is a bridge, not a claim that Kummer phase is caused by GNS.

## 9. Hostile conjecture loops

1. **Orthogonal splitting is the new field.** Failed.  It is Wold/recollement machinery.
   **Survivor:** source fixes the weights, work, and composition law.
2. **The inherited GNS fibre at the same temperature embeds spectrally.** Failed.  The correct source
   fibre is (P_{m,r\sigma}), and its clock is multiplied by (r).
3. **Positive normalization forgets only a harmless scalar.** Failed.  It irreversibly loses absolute
   coefficient scale; Theorem 4.1 needs marked total mass for full recovery.
4. **Direct and iterated work add without parameter transport.** Failed.  The exact law is (FE.39).
5. **Finite work can approach the normalization wall.** Failed by Theorem 7.1.
   **Survivor:** relative properness on every bounded upper-temperature chart.
6. **Properness selects RH.** Failed.  The wall here is (\sigma=1), and no theorem identifies it
   with the physical critical-line defect.
7. **Kummer Parseval is an independent scalar.** Failed after marking the sector decomposition.
   **Survivor:** it is the GNS sector-collision statistic (FE.47)--(FE.48).
8. **Heat-trace fusion is a withheld prediction.** Failed epistemically: its analytic identity was
   already known in the corpus.  **Survivor:** it confirms that one support formation controls both
   analytic and spectral valuations.

## 10. Literature and significance boundary

Generic ingredients are established:

- Wold/product-system decomposition: Solel--Suryawanshi, arXiv:2601.09391;
- earlier product-system Wold theory: Skalski--Zacharias, arXiv:math/0702649;
- Markov categories and sufficient statistics: Fritz, arXiv:1908.07021;
- relative-entropy chain rules: Fang--Fawzi--Renner--Sutter, arXiv:1909.05826;
- arithmetic endomotive image/complement geometry: Yalkinoglu, arXiv:1105.5022.

Therefore no novelty is assigned to direct sums, KL chain rules, or Wold projections.  The exact
research content is the simultaneous source-derived realization:

\[
 \text{ramification formation}
 \Rightarrow
 \text{positive Mellin weights}
 \Rightarrow
 \text{GNS/spectral/information fusion}
 \Rightarrow
 \text{crossed work cocycle}
 \Rightarrow
 \text{normalization-wall properness}.
\]

This closes one literal source-generated vertical comparison and one positive/proper work gate in
Formation Holonomy Mechanics.  It remains insufficient as a universal field or RH proof until a
second heterogeneous source realization and an RH-bearing selection landing are proved.

## 11. Dependency and formalization ledger

- Source support split and analytic excess: existing Stage-3 ramification-excess theorem.
- Shell Mellin measure, GNS clock, and normalization pole: existing Stage-3 marked Euler-shell
  theorem.
- Kummer Parseval identity: existing Stage-3 Kummer-phase theorem.
- New paper proofs here: normalized formation mixture, GNS cyclic fusion, joint reconstruction, KL
  chain, exact work/affinity/TV, crossed work cocycle, relative properness, and Kummer participation
  identity.
- Lean status: **not formalized in this research pass**.  Current goal explicitly audits Lean
  read-only and does not write or build Lean.
- RH status: no critical-line selection consequence.

