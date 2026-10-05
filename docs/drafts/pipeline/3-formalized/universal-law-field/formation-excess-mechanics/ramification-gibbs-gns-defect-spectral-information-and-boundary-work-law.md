# Ramification Gibbs--GNS defect, spectral--information fusion, and boundary-work law

- **ID:** ULF-FEM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Formation-Excess Mechanics
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE-NATIVE FORMATION] [FIVE-ORGAN FUSION] [JOINT RECONSTRUCTION] [CROSSED WORK COCYCLE] [RELATIVE PROPERNESS] [LEAN-PROVED] [NOT RH]

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
- Lean status: fully formalized, unconditionally: see the Lean certificate below.
- RH status: no critical-line selection consequence.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.RamificationShellFormation`, `GaloisForLFunctions.HTGeometry.RamificationGNSFusion`, `GaloisForLFunctions.HTGeometry.RamificationSpectralFusion`, `GaloisForLFunctions.HTGeometry.RamificationInformationChain`, `GaloisForLFunctions.HTGeometry.RamificationBoundaryWork`, `GaloisForLFunctions.HTGeometry.RamificationKummerParticipation`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.RamificationShellFormation` (§§1–2),
`GaloisForLFunctions.HTGeometry.RamificationGNSFusion` and `GaloisForLFunctions.HTGeometry.RamificationSpectralFusion`
(§§3–4), `GaloisForLFunctions.HTGeometry.RamificationInformationChain` (§§5–6),
`GaloisForLFunctions.HTGeometry.RamificationBoundaryWork` (§7, §9) and
`GaloisForLFunctions.HTGeometry.RamificationKummerParticipation` (§8).  Corpus inputs: the shell indicator and its
residue at `σ = 1` (`RHTower.shellIndicator`, `RHTower.shellMellin`, `RHTower.tendsto_shellMellin_residue`,
`RHTower.shellResidue_pos`), the Euler-shell source (`EulerShell`, `eulerShellSum`, `eulerShellSeries`,
`eulerShellSource`, `shellPhase`), the support split and composition
(`HTGeometry.ConstraintFrameRelativity.powerImageSupport_eq_image`,
`HTGeometry.ConstraintFrameRelativity.excessSupport_mul_eq_union`,
`HTGeometry.ConstraintFrameRelativity.excessSupport_disjoint_image`,
`HTGeometry.ConstraintFrameRelativity.excessLSeries_cocycle`), the trace-class Gram calculus
(`rightGram_traceClass`) and Laplace determinacy (`LaplaceTomography.measure_eq_of_laplace_eq_succ`).  Names
below are in `GaloisForLFunctions.HTGeometry` unless fully qualified; `FormationExcess` is the new namespace.
`A_m = EulerShell m`, `X_{m,r} = FormationExcess.ExcessShell m r`, `S_m(σ) = eulerShellSum m σ`,
`C_{m,r}(σ) = FormationExcess.excessSum m r σ`, `α = FormationExcess.survival`, `β = FormationExcess.excessFraction`,
`ℓ²(A) = LpDiagonal.LpTwo A`, `Ω_{m,σ} = FormationExcess.shellVector`, `W = FormationExcess.formationWork`.
Results hold for every `m ≥ 1` except the normalization wall (§7, §9 loop 4), which uses the card's `m ≥ 12`.

| Claim | Lean declaration |
|-|-|
| (FE.1)–(FE.2) the shells `A_m` and their Dirichlet series | `EulerShell`, `eulerShellSum`, `eulerShellSeries`, `RHTower.shellIndicator` |
| (FE.3) the power map `P_r : A_m → A_{rm}` is injective | `FormationExcess.shellPow`, `FormationExcess.shellPow_val`, `FormationExcess.shellPow_injective` |
| (FE.4)–(FE.6) `A_{rm} = P_r(A_m) ⊔ X_{m,r}`, the `r`-th powers of `A_{rm}` are exactly `P_r(A_m)` | `FormationExcess.ExcessShell`, `FormationExcess.shellSplit`, `FormationExcess.exists_shellPow_eq`, `FormationExcess.powImageEquiv`, `HTGeometry.ConstraintFrameRelativity.powerImageSupport_eq_image` |
| (FE.5), (FE.7) `S_{rm}(z) = S_m(rz) + C_{m,r}(z)` (real and complex) | `FormationExcess.excessSum`, `FormationExcess.excessSeries`, `FormationExcess.eulerShellSum_split`, `FormationExcess.eulerShellSeries_split` |
| the excess is nonempty: `2^{rm}·3` | `FormationExcess.excessWitness`, `FormationExcess.excessSum_pos` |
| (FE.8)–(FE.10) the atomic measures `μ_{m,σ}`, `η_{m,r,σ}` (finite) and the dilation `d_r` | `FormationExcess.atomic`, `FormationExcess.shellMeasure`, `FormationExcess.excessMeasure`, `FormationExcess.dilate`, `FormationExcess.shellMeasure_univ`, `FormationExcess.excessMeasure_univ` |
| Theorem 2.1, (FE.11) `μ_{rm,σ} = (d_r)_* μ_{m,rσ} + η_{m,r,σ}` with disjoint supports | `FormationExcess.shellMeasure_formation`, `FormationExcess.formation_mutuallySingular`, `FormationExcess.inheritedSupport` |
| (FE.12) masses `S_m(rσ)`, `C_{m,r}(σ)`, total `S_{rm}(σ)` | `FormationExcess.shellMeasure_univ`, `FormationExcess.excessMeasure_univ`, `FormationExcess.eulerShellSum_split` |
| (FE.13)–(FE.14) normalized laws; `0 < α, β < 1`, `α + β = 1` | `FormationExcess.shellLaw`, `FormationExcess.inheritedLaw`, `FormationExcess.excessLaw`, `FormationExcess.isProbabilityMeasure_shellLaw`, `FormationExcess.isProbabilityMeasure_inheritedLaw`, `FormationExcess.isProbabilityMeasure_excessLaw`, `FormationExcess.survival_pos`, `FormationExcess.excessFraction_pos`, `FormationExcess.survival_lt_one`, `FormationExcess.excessFraction_lt_one`, `FormationExcess.survival_add_excessFraction` |
| Corollary 2.2, (FE.15) `P_{rm,σ} = α I + β Q` | `FormationExcess.shellLaw_mixture` |
| (FE.16)–(FE.18) `T_r e_k = e_{k^r}` isometric; `R = T T*`, `Q = 1 - R` | `FormationExcess.powIsometry`, `FormationExcess.powIsometry_single`, `FormationExcess.splitInl`, `FormationExcess.splitInr`, `FormationExcess.adjoint_splitInl`, `FormationExcess.adjoint_splitInr`, `FormationExcess.rangeProj`, `FormationExcess.defectProj`, `FormationExcess.defectProj_apply` |
| (FE.19) cyclic probability vectors | `FormationExcess.shellVector`, `eulerShellSource_v`, `norm_eulerShellSource_v`, `FormationExcess.excessVector`, `FormationExcess.norm_excessVector` |
| (FE.20) the logarithmic clock on its maximal domain | `FormationExcess.clockDomain`, `FormationExcess.clockMap`, `FormationExcess.shellLog`, `FormationExcess.excessLog` |
| Theorem 3.1, (FE.21) `ℓ²(A_{rm}) = T_r ℓ²(A_m) ⊕ ℓ²(X_{m,r})` orthogonally | `FormationExcess.inner_splitInl_splitInr`, `FormationExcess.splitInl_add_splitInr`, `FormationExcess.inner_extendSum`, `FormationExcess.norm_sq_extendSum` |
| (FE.22) `Ω_{rm,σ} = √α T_r Ω_{m,rσ} + √β Ω^{ex}` | `FormationExcess.shellVector_fusion` |
| (FE.23) `D_{rm} T_r = r T_r D_m`, `D_{rm} ≅ r D_m ⊕ D^{ex}` on maximal domains | `FormationExcess.shellClock_intertwining`, `FormationExcess.shellClock_split`, `FormationExcess.mem_clockDomain_iff`, `FormationExcess.clockMap_split`, `FormationExcess.clockMap_splitInl` |
| (FE.24) `⟨Ω_{rm,σ}, Q_r Ω_{rm,σ}⟩ = β` | `FormationExcess.inner_defectProj_shellVector`, `FormationExcess.inner_rangeProj_shellVector` |
| Corollary 3.2, (FE.25) characteristic fusion; GNS form | `FormationExcess.characteristic_fusion`, `FormationExcess.gns_characteristic` |
| Corollary 3.3, (FE.26) heat operators positive, trace class, `Tr e^{-tD_{rm}} = Tr e^{-rtD_m} + Tr e^{-tD^{ex}}` | `FormationExcess.heatOp`, `FormationExcess.rpow_neg_eq_exp_neg_log`, `FormationExcess.diag_traceClass`, `FormationExcess.heatOp_traceClass`, `FormationExcess.heatTrace_fusion` |
| Theorem 4.1 (1) the scalar spectral measure of `D_{rm}` in `Ω_{rm,σ}` is `P_{rm,σ}`, atom by atom (simple eigenvalues) | `FormationExcess.spectralMeasure`, `FormationExcess.spectralMeasure_shellVector`, `FormationExcess.atomic_singleton`, `FormationExcess.shellLog_injective` |
| Theorem 4.1 (2)–(4) the marked projection gives the partition, `α`, `β` and both conditional laws | `FormationExcess.defectProj_apply`, `FormationExcess.spectralMeasure_splitInl`, `FormationExcess.spectralMeasure_splitInr`, `FormationExcess.spectralMeasure_rangeProj`, `FormationExcess.spectralMeasure_defectProj`, `FormationExcess.inner_rangeProj_shellVector`, `FormationExcess.inner_defectProj_shellVector` |
| Theorem 4.1 (5) with the marked mass, the unnormalized measure | `FormationExcess.shellMeasure_eq_mass_smul_spectral` |
| Corollary 4.2 exact loss of unmarked normalization | `FormationExcess.normalizeMeasure`, `FormationExcess.normalizeMeasure_smul`, `FormationExcess.smul_ne_self` |
| (FE.28)–(FE.29) discrete divergence, Bernoulli divergence, affinity, total variation | `FormationExcess.klTerm`, `FormationExcess.klDiv`, `FormationExcess.klDiv_of_summable`, `FormationExcess.klDiv_eq_top`, `FormationExcess.berDiv`, `FormationExcess.affinity`, `FormationExcess.totalVariation` |
| the laws as atom masses on `A_{rm}`: `α P_{m,rσ}` on inherited, `β Q` on excess atoms | `FormationExcess.shellProb`, `FormationExcess.excessProb`, `FormationExcess.inheritedProb`, `FormationExcess.shellProb_inl`, `FormationExcess.shellProb_inr`, `FormationExcess.inheritedProb_inl`, `FormationExcess.inheritedProb_inr` |
| Theorem 5.1, (FE.30) the exact information chain; all divergences finite | `FormationExcess.information_chain`, `FormationExcess.information_chain_finite`, `FormationExcess.klDiv_dirichlet`, `FormationExcess.summable_dirichlet_kl`, `FormationExcess.log_dirichletProb_div` |
| (FE.31)–(FE.32) `W = D(I‖P_{rm,σ}) = -log α = log S_{rm}(σ) - log S_m(rσ) > 0` | `FormationExcess.formationWork`, `FormationExcess.work_eq` |
| (FE.33) `D(P_{rm,σ}‖I) = +∞` | `FormationExcess.reverse_work_eq_top` |
| (FE.34) `Aff(P_{rm,σ}, I) = √α` | `FormationExcess.affinity_eq` |
| (FE.35) `TV(P_{rm,σ}, I) = β` | `FormationExcess.totalVariation_eq` |
| (FE.36) the three-layer refinement `A_{srm} = P_{sr}(A_m) ⊔ P_s(X_{m,r}) ⊔ X_{rm,s}`; `P_s P_r = P_{sr}` | `HTGeometry.ConstraintFrameRelativity.excessSupport_mul_eq_union`, `HTGeometry.ConstraintFrameRelativity.excessSupport_disjoint_image`, `FormationExcess.shellPow_shellPow_val` |
| (FE.37) layer masses sum to `S_{srm}(σ)` | `FormationExcess.threeLayer_masses` |
| Theorem 6.1, (FE.38)–(FE.39) multiplicative survival, additive work with transport | `FormationExcess.survival_comp`, `FormationExcess.work_comp` |
| Corollary 6.2 the refinements agree in every shadow (coefficients, traces, inherited divergence summand) | `HTGeometry.ConstraintFrameRelativity.excessLSeries_cocycle`, `FormationExcess.threeLayer_masses`, `FormationExcess.inherited_summand_comp` |
| §6 unshifted additivity is false in general | `FormationExcess.not_unshifted_additivity` |
| (FE.40) `S_j(σ) → +∞` as `σ ↓ 1`; `S_m(rσ) → S_m(r)` | `FormationExcess.tendsto_eulerShellSum_atTop`, `FormationExcess.eulerShellSum_eq_shellMellin`, `FormationExcess.continuousAt_eulerShellSum` |
| Theorem 7.1, (FE.41)–(FE.42) the wall limits | `FormationExcess.wall_limits`, `FormationExcess.wall_affinity_tv`, `FormationExcess.tendsto_survival_wall` |
| Theorem 7.1, (FE.43) the low-temperature limits (unique smallest atom `2^m`, dominated convergence) | `FormationExcess.lowTemperature_limits`, `FormationExcess.tendsto_scaled_shellSum`, `FormationExcess.two_pow_le_of_shell` |
| Corollary 7.2, (FE.44) `W` continuous and proper on `(1, Σ]` | `FormationExcess.continuousOn_formationWork`, `FormationExcess.work_bounded_away`, `FormationExcess.work_isCompact_preimage` |
| (FE.45)–(FE.46) valuation residues, sector masses, Kummer–Parseval invariant; inherited = residue `0` | `FormationExcess.kummerVec`, `FormationExcess.kummerVec_eq_zero_iff`, `FormationExcess.kummerVec_ne_zero_iff`, `FormationExcess.sectorMass`, `FormationExcess.kummerParseval`, `FormationExcess.sectorProj`, `FormationExcess.tsum_sectorMass_ne_zero` |
| Theorem 8.1, (FE.47) `Σ_{γ≠0} ‖Π_γ Ω‖⁴ = V/S_{rm}²` via `‖Π_γ Ω‖² = A_γ/S_{rm}` | `FormationExcess.norm_sq_sectorProj`, `FormationExcess.kummer_collision` |
| Theorem 8.1, (FE.48) | `FormationExcess.kummer_collision_excess` |
| §9 loop 2: the inherited fibre at the same temperature is not the source fibre | `FormationExcess.shellProb_ne_of_two_le` |
| §9 loops 3, 4, 5, 7, 8 | `FormationExcess.normalizeMeasure_smul`, `FormationExcess.not_unshifted_additivity`, `FormationExcess.work_bounded_away`, `FormationExcess.kummer_collision`, `FormationExcess.heatTrace_fusion` |

§9 loops 1 and 6, §10 and §11 are commentary and state what is not claimed.

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
