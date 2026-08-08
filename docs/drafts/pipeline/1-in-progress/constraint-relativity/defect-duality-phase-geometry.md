# Defect-Duality Phase Geometry

- **ID:** `defect-duality-phase-geometry`
- **Stage:** 1-in-progress
- **Working name:** **Defect-Duality Phase Geometry (DDPG)**
- **Role:** local nonsemisimple phase chart inside Polarized Law-Kernel Geometry
- **Type:** LOCAL NONSEMISIMPLE PHASE CHART / EXTENSION-STACK PROGRAM
- **Status:** `[LOCAL CHART ONLY] [EXACT FINITE LOCAL THEOREM]`
  `[UNIVERSAL EXTENSION-PHASE CLAIM FALSIFIED] [CLASSICAL EXTENSION-STACK PARENTS]`
  `[NO RH CLAIM] [NO LEAN WRITTEN]`
- **Paper anchor:**
  `../../2-fully-proven/constraint-relativity/phase-subdiscriminant-kahler-smith-stratification-law.md`.
- **Higher replacement:** `source-framed-polarized-law-kernel-geometry.md`.

## Founding reinterpretation

> **Phase is not primarily a number on unit circle. Phase is rule gluing an observer defect to its
> dual inside relative-law defect. Scalar angle, determinant, norm-square, and branch support are
> shadows of this gluing.**

For finite split source order `A`, self-dual observer normalization `O`, trace-dual lattice
`A^sharp`, and observer defect `C=O/A`, put

\[
 L_{A,O}=A^\sharp/A.
\]

Trace duality gives the universal lattice-law sandwich

\[
 A\subset O\subset A^\sharp,
 \qquad
 0\to C\to L_{A,O}\to C^\dagger\to0.
 \tag{DD.1}
\]

Only in the split monogenic hypersurface model proved in the paper anchor is there a canonical
identification

\[
 L_{A,O}\cong\Omega_{A/R}.
 \tag{DD.1a}
\]

For general split orders `(DD.1a)` is false. Thus DDPG's universal object is the trace-law defect
`L_(A,O)`; Kähler phase is a privileged monogenic realization.

Thus finite source--observer phase state is extension class

\[
 [\xi_{A,O}]\in\operatorname{Ext}_R^1(C^\dagger,C),
 \tag{DD.2}
\]

not merely determinant of a chosen middle-term realization.

This changes roles of three corpus faces:

\[
 \boxed{
 \begin{array}{rcl}
 \text{arithmetic/source} &:& A\text{ and its chronology},\\
 \text{spectral/observer} &:& C=O/A,\\
 \text{geometric/law} &:& L_{A,O}=A^\sharp/A,\\
 \text{Kähler realization} &:& L_{A,O}\cong\Omega_{A/R}\text{ under monogenic hypersurface hypotheses},\\
 \text{phase} &:& [\xi_{A,O}]\text{ gluing }C^\dagger\text{ to }C.
 \end{array}}
 \tag{DD.3}
\]

Support equality loses extension. Discriminant loses internal Smith distribution. Positivity can
select chamber without selecting horizon.

## 1. Finite phase stack

For finite-length torsion `R`-module `C`, define groupoid

\[
 \mathcal P_R(C)
 =\left[
 \operatorname{Ext}_R^1(C^\dagger,C)
 /\bigl(\operatorname{Aut}C\times\operatorname{Aut}C^\dagger\bigr)
 \right].
 \tag{DD.4}
\]

Object is exact sequence

\[
 0\to C\to M\to C^\dagger\to0;
 \tag{DD.5}
\]

morphisms are isomorphisms of extensions. Stratify by Smith partition `mu(M)`. Total length is
conserved:

\[
 |\mu(M)|=2\operatorname{length}(C).
 \tag{DD.6}
\]

Classical Hall/Littlewood--Richardson theory constrains possible middle partitions. DDPG does not
claim invention of extension stack or its orbit classification. New question is which strata are
selected by source orders and how source histories transport between them.

## 2. Monogenic phase realization map

Fix common-contact observer type

\[
 C_{N,r}=\bigoplus_{j=1}^{N-1}R/(a^{rj}).
 \tag{DD.7}
\]

Fix a common-contact parameter `c` with `v(c)=r` and define lift-framed configuration space

\[
 \widetilde{\operatorname{Conf}}_N(R)
 =\{(u_1,\ldots,u_N)\in(R^\times)^N:\bar u_i\ne\bar u_j\text{ for }i\ne j\}.
 \tag{DD.8a}
\]

Each lift configuration `u=(u_1,...,u_N)` constructs source order

\[
 A_u=R[T]/\prod_i(T-c u_i),
 \tag{DD.8}
\]

and exact phase-realization map

\[
 \widetilde\Phi_{N,r}:\widetilde{\operatorname{Conf}}_N(R)
 \longrightarrow\mathcal P_R(C_{N,r}),
 \qquad
 u\longmapsto[\xi_{A_u,O}].
 \tag{DD.9}
\]

Residues alone do not determine source order or extension class: different lifts with same
`lambda_i=bar u_i` may differ in higher normal jets. Therefore no intrinsic map from
`Conf_N(k)` exists without lift data. If `R=k[[a]]` with a chosen constant coefficient section,
constant lifts `u_i=lambda_i` define a restricted map from `Conf_N(k)`.

Middle Smith stratum is controlled by Kähler determinantal minors. Distinguished equations are
phase subdiscriminants

\[
 H_k(\lambda)
 =\det\left(\sum_i\lambda_i^{p+q}\right)_{0\le p,q<k}.
 \tag{DD.10}
\]

Exact finite theorem proves:

1. all real distinct nodes lie in maximal-gluing stratum
   `mu=(2r,4r,...,2r(N-1))`;
2. complex nodes can cross `H_k=0` without sheet collision;
3. cube roots yield `mu=(3r,3r)` rather than `(2r,4r)`;
4. fourth roots yield `mu=(4r,4r,4r)` rather than `(2r,4r,6r)`;
5. observer type `C_(N,r)` and total discriminant length remain unchanged.

For constant tangent nodes and `N=3`, this is complete classification: `H_2!=0` gives
`mu=(2r,4r)`; `H_2=0` forces nodes, after affine change, to cube-root triple and gives
`mu=(3r,3r)`. Richer constant-tangent phase topology begins at `N>=4`.

This is phase wall crossing without ordinary discriminant zero.

## 3. Candidate topology from determinantal depth

On isomorphism classes, define determinantal depth subsets

\[
 \mathcal P_{\ge d_\bullet}
 =\{[\xi]:v(D_k(M_\xi))\ge d_k\text{ for every }k\}.
 \tag{DD.11}
\]

These are standard Smith/Fitting valuation strata, not yet a new topology. A genuine quotient-stack
topology must specify families, specialization, and continuity and prove that `(DD.11)` are its
closed depth loci. Pullback along `widetilde Phi_(N,r)` gives determinantal stratification of
lift-framed tangent-node phase space. Wall crossing changes persistence partition while conserving
total length `(DD.6)`.

Candidate local time datum is ordered sequence

\[
 \mu(t_-),\quad [\xi(t_0)],\quad\mu(t_+),
 \tag{DD.12}
\]

plus holonomy inside fixed stratum. Scalar determinant cannot reconstruct `(DD.12)`.

## 4. Defect-duality admissibility principle

**Definition DD-E.** A source--observer chart is *defect-dual* only after it supplies a
source-forced duality `D`, observer defect `C_O`, middle law defect `K_(S,O)`, and functorial exact
sequence

\[
 0\to C_O\to K_{S,O}\to D(C_O)\to0,
 \tag{DD.13}
\]

Coordinate change must act by a morphism of these extensions. This is a typing rule, not a theorem
that every category or every preferred cotangent module has such a sequence. Split trace-dual lattice
charts satisfy it canonically with `K_(S,O)=L_(A,O)`. The monogenic hypersurface chart additionally
identifies `K_(S,O)` with `Omega_(A/R)`.

A proposed realization is falsified when its middle module has incompatible length, support, or
pairing with the canonical duality sandwich.

### Exact scope counterexample

Let `R=C[[a]]`, `O=R^3`, and

\[
 A=R(1,1,1)+aR^3\subset O.
 \tag{DD.13a}
\]

Then `C=O/A\cong(R/(a))^2`. Hence the trace-dual sandwich has

\[
 \operatorname{length}_R L_{A,O}
 =2\operatorname{length}_R C=4.
 \tag{DD.13b}
\]

On the other hand

\[
 A\cong R[x,y]/(x^2-ax,\ y^2-ay,\ xy).
\]

Differentiating the three relations and reducing in the `R`-basis `1,x,y` gives

\[
 \Omega_{A/R}\cong R/(a^2)\oplus R/(a^2)\oplus R/(a),
 \qquad
 \operatorname{length}_R\Omega_{A/R}=5.
 \tag{DD.13c}
\]

Indeed `(2x-a)dx=0`, `(2y-a)dy=0`, and `y dx+x dy=0`; multiplication by `x,y` leaves two
`a^2`-torsion generators `dx,dy` and one `a`-torsion generator `y dx=-x dy`. Therefore
`Omega_(A/R)` is not `L_(A,O)` and cannot occupy `(DD.13)` in general. This is exact anti-theatre
boundary: DDPG may universalize trace-dual extension geometry, not Kähler different.

## 5. Candidate field equation

Extension stack is kinematics. Dynamics must come from source before phase target. Proposed typed
equation is

\[
 \boxed{
 \nabla_{\mathrm{src}}[\xi]
 =\mathcal J_{\mathrm{src}}
 \quad\text{in tangent/derived category of }\mathcal P_R(C).}
 \tag{DD.14}
\]

Requirements:

1. `J_src` constructed from source operations independently of `widetilde Phi`, divisor, or desired wall;
2. conservation of total defect follows from duality, not assumed criticality;
3. wall-crossing law predicts intermediate Fitting changes;
4. generalized-prime systems test whether arithmetic source chooses special orbit;
5. no use of tautological Koszul differential `d(e_p)=f_p` as selector.

For RH corpus this must compare to actual Route-L curvature
`Omega_(mu,Gamma)=S_mu G_Gamma D`, not replace it. Required advance is source map from literal
rational-Witt/Milnor object into phase-extension tangent that forces Route-L flatness or a specified
wall by independent identity.

## 6. Direct operator/holographic Ext transfer is false

Equation `(DD.1)` suggests precise structural analogy:

\[
 \text{boundary-visible defect }C
 +\text{dual boundary }C^\dagger
 +\text{gluing phase }[\xi]
 =\text{interior trace-law defect }L_{A,O}.
 \tag{DD.15}
\]

This analogy is not universal. Every short exact sequence of finite-dimensional complex vector
spaces splits, so `Ext_C^1(C^*,C)=0`; same holds for Hilbert spaces with bounded closed-range maps.
Proper subfactor inclusion is not ideal quotient, and modularly invariant expected inclusion splits
as operator space by conditional expectation. Physical gluing can nevertheless be nonzero through
symplectic cross-pairing or Hamiltonian/modular transport.

Therefore `(DD.15)` is only nonsemisimple DVR chart. Higher physical object must retain split
polarization, pairing, generator, frame, and filtration as in Polarized Law-Kernel Geometry.

Repaired transfer gate:

1. start with finite operator-algebra/code inclusion and independently defined boundary defect;
2. construct source-forced dual and relative-law/interior module;
3. identify exact polarization, allowing split middle term;
4. construct pairing/symplectic form and source frame;
5. construct modular/Hamiltonian generator and filtration;
6. prove comparison to arithmetic nonsemisimple chart;
7. compare one measurable recovery/complexity quantity to Smith/persistence distance.

If only post-hoc identification is possible, physical interpretation fails. Brown--Susskind length
cannot be equated to polarized/persistence distance without this transfer.

## 7. Predictions

1. Same boundary/spectral defect and same total discriminant can encode different interior/law
   depth profiles; determinant-only reconstruction is incomplete.
2. Real positivity selects maximal-gluing chamber but cannot select radial horizon.
3. Three or more phase legs are first place nontrivial internal redistribution can occur; `N=2`
   has one bar and no redistribution at fixed total length.
4. One-clock path can read scalar subdiscriminant and approaches every independently reachable wall
   arbitrarily closely along prime Kronecker orbit; exact crossing is separate arithmetic question.
5. Infinite-prime limit cannot be ordinary determinant line: extension lengths and top degree drift;
   source must supply Tate/pro topology and polarization.
6. Any proposed observer/law identification only on reduced support loses dual half and extension
   phase.
7. Cotangent/Kähler and trace-law defects need not agree. Under split relative-Gorenstein DVR
   hypotheses with infinite residue field, equality is equivalent to monogenicity, not merely lci.

## 8. Conjecture--attack loops

1. **Phase equals determinant orientation.** Failed by cube/fourth-root Smith redistribution.
2. **Observer defect determines law defect.** Failed: fixed `C` admits different middle partitions.
3. **Complex phase requires metric.** Failed: Kähler Smith/subdiscriminant walls are algebraic.
4. **Real positivity forces horizon.** Failed: all-Fitting square holds for every nonzero radial
   parameter.
5. **All extension-stack strata are monogenically realizable.** Open; likely false. Characterize
   image of `widetilde Phi_(N,r)`.
6. **Actual prime phase torus meets nonreal walls.** Proved for three primes by exact radius
   criterion; `(101,103,107)` is explicit.
7. **Kronecker prime time orbit meets walls.** Closure statement is proved: unique factorization plus
   Kronecker density gives `inf_t |H_2(t)|=0` for explicit prime triple. Exact finite-time zero remains
   open and requires exponential-polynomial analysis.
8. **Finite phase stack has canonical infinite limit.** Failed for naive determinant; Tate/source
   topology required.
9. **Holographic interior is nontrivial Ext class of boundary defect.** False in ordinary
   finite/Hilbert/operator charts; extensions split while symplectic gluing can remain nonzero.
10. **Extension current forces RH.** Open and presently unsupported; any definition using critical
    line or Xi zero is circular.
11. **Every split-order Kähler defect is trace-dual middle term.** False by
    `(DD.13a)--(DD.13c)`. Positive survivor: `L_(A,O)=A^sharp/A` is universal; equality with
    `Omega_(A/R)` is extra geometry whose exact hypothesis must be classified.

## 9. Novelty boundary

Occupied parents include extension stacks, Hall algebras, finite-length modules over DVR,
Littlewood--Richardson classification, trace-dual lattices, differents, discriminants, Smith theory,
Hermite subdiscriminants, persistence, and determinant gerbes.

Exact categories with duality already have Hall modules encoding self-dual extension structure:
https://arxiv.org/abs/1212.0531. Current 2025 self-dual Hall/Hopf work further blocks novelty from
duality-plus-extension language alone: https://arxiv.org/abs/2503.04125.

Potentially unoccupied residue is exact package:

> source-order/normalization sandwich producing canonical self-dual trace-law extension;
> monogenic Kähler realization and complex phase as conserved Smith-depth redistribution;
> source-history transport on resulting extension strata; and comparison to heterogeneous
> arithmetic/operator realizations.

Only first two finite-local clauses are paper-proved. Global field and physics transfer remain
conjectural. Search absence is not priority proof.

## Lean-return note

No Lean work authorized. Later formalization should begin with exact sequence from trace-dual lattice,
not extension-stack program. Reuse finite-length module/Smith infrastructure after corpus search.

## Gates

- [x] exact finite source-order example
- [x] nontrivial phase wall with conserved determinant
- [x] real-chamber law and complex countermodels
- [x] actual three-prime phase-torus wall and one-clock wall closure
- [ ] characterize lift-framed monogenic realization image
- [ ] classify when `A^sharp/A\cong Omega_(A/R)` beyond hypersurfaces
- [ ] prove source-current dynamics
- [ ] infinite/Tate phase stack
- [x] direct operator/holographic Ext transfer falsified
- [ ] polarized law-kernel operator/arithmetic transfer theorem
- [ ] external specialist priority review

## Log

- 2026-08-08 -- opened after canonical trace-dual sandwich showed phase is extension gluing rather
  than scalar determinant angle.
- 2026-08-08 -- hostile audit separated universal trace-law middle `A^sharp/A` from Kähler
  different. Three-sheet nonmonogenic order has respective lengths `4` and `5`; residue
  configuration was replaced by lift-framed configuration.
