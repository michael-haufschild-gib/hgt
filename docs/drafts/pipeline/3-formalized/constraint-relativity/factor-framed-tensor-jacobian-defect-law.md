# Factor-framed tensor Jacobian defect law

- **ID:** `factor-framed-tensor-jacobian-defect-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / FACTOR-FRAMED JACOBIAN DEFECT / EXACT INFINITE FAMILY
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [CLASSICAL INGREDIENTS]`
  `[NOVELTY UNVERIFIED] [NO RH CLAIM] [LEAN COMPLETE]`
- **Field card:** `../../1-in-progress/constraint-relativity/source-soldering-bivariant-law-geometry.md`.
- **Parent classification:**
  `gorenstein-trace-kahler-monogenic-equivalence-and-corank-two-splitting-law.md`.

## Setup

Let `R` be DVR with uniformizer `a`, fraction field `K`, residue field `k`, and `2 in R^times`.
For `d>=1`, put

\[
 B_i=R[f_i]/(f_i^2-a^2),
 \qquad
 A_d=B_1\otimes_R\cdots\otimes_RB_d,
 \qquad
 F=\prod_{i=1}^d f_i.
 \tag{1}
\]

Equivalently, after `f_i=2x_i-a`, each factor is monogenic order
`R[x_i]/(x_i(x_i-a))`. Generic normalization is split `K^(2^d)`.

Each factor has unit-normalized generator-framed trace--Kähler soldering

\[
 s_i:\Omega_{B_i/R}\xrightarrow{\sim}B_i^\sharp/B_i,
 \qquad
 df_i\longmapsto[f_i^{-1}].
 \tag{2}
\]

Tensor source produces factor-compatible map

\[
 s_d:\Omega_{A_d/R}\longrightarrow A_d^\sharp/A_d,
 \qquad
 df_i\longmapsto[f_i^{-1}].
 \tag{3}
\]

Compatibility is literal. Put `C_i=bigotimes_(j!=i)B_j`, so `A_d=C_i tensor_R B_i`. Canonical
cotangent summand and trace-defect transport are

\[
 \alpha_i:A_d\otimes_{B_i}\Omega_{B_i/R}\longrightarrow\Omega_{A_d/R},
 \tag{3a}
\]

\[
 \beta_i:A_d\otimes_{B_i}(B_i^\sharp/B_i)\longrightarrow A_d^\sharp/A_d,
 \qquad
 c\otimes[q/f_i]\longmapsto[cq/f_i].
 \tag{3b}
\]

Then

\[
 \boxed{s_d\circ\alpha_i
 =\beta_i\circ(A_d\otimes_{B_i}s_i)}
 \tag{3c}
\]

on generators, hence everywhere.

## Theorem

Trace dual and cotangent laws are

\[
 A_d^\sharp=F^{-1}A_d,
 \qquad
 L_d:=A_d^\sharp/A_d\cong A_d/(F),
 \tag{4}
\]

\[
 K_d:=\Omega_{A_d/R}
 \cong\bigoplus_{i=1}^d A_d/(f_i)\,df_i.
 \tag{5}
\]

Under identification `(4)`, map `(3)` is

\[
 \boxed{
 s_d((u_i)_i)=\sum_{i=1}^d u_i\frac{F}{f_i}\pmod F.}
 \tag{6}
\]

Its mixed trace-pole cokernel is

\[
 \boxed{
 \operatorname{coker}s_d
 \cong
 A_d\Big/\left(\frac F{f_1},\ldots,\frac F{f_d}\right).}
 \tag{7}
\]

As `R`-module this has exact Smith decomposition

\[
 \boxed{
 \operatorname{coker}s_d
 \cong
 \bigoplus_{t=0}^{d-2}
 \left(R/(a^{2(d-1-t)})\right)^{\binom dt}.}
 \tag{8}
\]

In particular

\[
 \boxed{
 \operatorname{length}_R\operatorname{coker}s_d
 =2^d(d-2)+2.}
 \tag{9}
\]

Source and target of `s_d` both have length `d2^d`, hence

\[
 \boxed{
 \operatorname{length}_R\ker s_d
 =\operatorname{length}_R\operatorname{coker}s_d.}
 \tag{10}
\]

Consequently `s_1` is isomorphism, but `s_d` has nonzero kernel and cokernel for every `d>=2`.
Tensoring individually exact monogenic laws produces source-forced mixed sector.

For `d>=2`, tensor order itself is nonmonogenic. Indeed

\[
 A_d/aA_d
 \cong
 k[\bar f_1,\ldots,\bar f_d]/(\bar f_1^2,\ldots,\bar f_d^2)
 \tag{10z}
\]

is local Artin algebra with embedding dimension `d`, whereas monogenic local Artin `k`-algebra has
embedding dimension at most one.

Map is source-framed gradient of multiplicative trace different. Define `R`-derivation

\[
 \nabla_F:A_d\longrightarrow A_d/(F),
 \qquad
 \nabla_F(f_i)=\frac F{f_i}.
 \tag{10a}
\]

It is well-defined because

\[
 \nabla_F(f_i^2-a^2)=2f_i\frac F{f_i}=2F=0\pmod F.
 \tag{10b}
\]

Universal map on Kähler differentials induced by `nabla_F` is exactly `s_d` under `(4)`. Hence

\[
 \boxed{
 \operatorname{coker}s_d
 =A_d/(F,\nabla_F(f_1),\ldots,\nabla_F(f_d))}
 \tag{10c}
\]

is relative critical/Jacobian algebra of factor-framed trace-different potential `F`. Since `F`
already belongs to gradient ideal, `(10c)` agrees with `(7)`.

At closed horizon, its `k`-dimension is

\[
 \boxed{
 \dim_k\left((\operatorname{coker}s_d)/a(\operatorname{coker}s_d)\right)
 =\sum_{t=0}^{d-2}\binom dt=2^d-d-1.}
 \tag{10d}
\]

More precisely, let `Delta^(d-1)` be simplex on vertex set `{1,...,d}`. Equation `(16)` gives
face-persistence decomposition

\[
 \boxed{
 \operatorname{coker}s_d
 \cong
 \bigoplus_{T\subseteq[d],\ |T|\le d-2}
 R/(a^{2\operatorname{excodim}T})\,f_T,
 \qquad
 \operatorname{excodim}T=d-1-|T|.}
 \tag{10e}
\]

Here `excodim(T)` is simplex codimension minus one, equivalently number of missing directions beyond
first. Thus every face below facets carries bar whose depth is twice excess codimension. Closed
fibre is commutative squarefree face algebra with square-zero vertices

\[
 \boxed{
 (\operatorname{coker}s_d)/a
 \cong
 k[f_1,\ldots,f_d]/
 \left(f_i^2,\ \prod_{j\ne i}f_j\ (1\le i\le d)\right).}
 \tag{10f}
\]

Its basis is faces of `(d-3)`-skeleton. Product of disjoint faces is union when union remains in
skeleton and is zero otherwise; overlapping faces vanish because `f_i^2=0`.

For `d=2`, exact anomaly is

\[
 \operatorname{coker}s_2
 \cong A_2/(f_1,f_2)
 \cong R/(a^2),
 \qquad
 \operatorname{length}\ker s_2=2.
 \tag{11}
\]

For `d=3`,

\[
 \operatorname{coker}s_3
 \cong R/(a^4)\oplus(R/(a^2))^3,
 \qquad
 \operatorname{length}=10.
 \tag{12}
\]

## Proof

For one factor, monogenic trace formula gives `B_i^sharp=f_i^(-1)B_i`. Trace pairing on tensor
product is tensor product of factor trace pairings, so

\[
 A_d^\sharp=\bigotimes_iB_i^\sharp=F^{-1}A_d.
\]

Multiplication by `F` identifies quotient `A_d^sharp/A_d` with `A_d/(F)`, proving `(4)`.

Presentation `(1)` has independent relations `f_i^2-a^2`. Differentiation gives
`2f_i df_i=0`; because `2` is a unit, `f_i df_i=0`. Complete-intersection presentation therefore
gives `(5)`. Element `f_i^(-1)=(F/f_i)/F` lies in `A_d^sharp`, and multiplication by `f_i` sends it
to `1 in A_d`; hence `(3)` is well-defined. Multiplying target by `F` turns `(3)` into `(6)`, and
its cokernel is `(7)` because `F=f_i(F/f_i)` already lies in displayed ideal. Replacing any factor
soldering by unit multiple scales corresponding generator `F/f_i` by unit, so ideal and cokernel
are unchanged under those frame renormalizations.

It remains to compute `(8)`. Ring `A_d` is free over `R` with basis

\[
 f_S=\prod_{j\in S}f_j,
 \qquad S\subseteq\{1,\ldots,d\}.
 \tag{13}
\]

Put `G_i={1,...,d}\setminus{i}`. For basis vector `f_S`,

\[
 f_{G_i}f_S
 =a^{2|G_i\cap S|}f_{G_i\triangle S}.
 \tag{14}
\]

Fix target basis vector `f_T`. Unique source producing it under generator `f_(G_i)` is
`S=G_i triangle T`; exponent in `(14)` is

\[
 |G_i\cap(G_i\triangle T)|
 =d-1-|T|+\mathbf1_{i\in T}.
 \tag{15}
\]

If `|T|<=d-1`, choose `i notin T`, so minimal exponent is `d-1-|T|`; if `T` is full set,
minimal exponent is zero. Images in `(14)` are pure basis multiples, therefore ideal in `(7)` is

\[
 \bigoplus_{|T|\le d-2}a^{2(d-1-|T|)}Rf_T
 \oplus
 \bigoplus_{|T|\ge d-1}Rf_T.
 \tag{16}
\]

Quotient by `(16)` proves `(8)`. Its length is

\[
 \sum_{t=0}^{d-2}2(d-1-t)\binom dt
 =\sum_{k=2}^d2(k-1)\binom dk
 =2^d(d-2)+2,
\]

proving `(9)`.

Finally, `A_d/(f_i)` is `2^(d-1)` free copies of `R/(a^2)`, so each summand in `(5)` has length
`2^d` and `length(K_d)=d2^d`. Multiplication by `f_i` on `A_d` has determinant valuation `2^d`;
multiplication by `F=prod_i f_i` has determinant valuation `d2^d`. Hence
`length(L_d)=d2^d`. Additivity of length in kernel--image--cokernel sequence gives `(10)`. QED.

Exact determinant agreement is stronger than equal length. From `(5)` and `(4)`,

\[
 \boxed{
 \operatorname{Fitt}_0^{A_d}(K_d)
 =\prod_i(f_i)=(F)
 =\operatorname{Fitt}_0^{A_d}(L_d).}
 \tag{17}
\]

Thus determinant/Fitting shadow remains identical while factor-framed Jacobian defect is nonzero.

## Theorem 2: heterogeneous contact-depth law

Let `r_1,...,r_d` be positive integers and replace `(1)` by

\[
 B_i^{(r_i)}=R[f_i]/(f_i^2-a^{2r_i}),
 \qquad
 A_{\mathbf r}=\bigotimes_iB_i^{(r_i)},
 \qquad
 F=\prod_i f_i.
 \tag{18}
\]

Every factor again has exact unit-normalized soldering `df_i mapsto [f_i^(-1)]`, and tensor map
has same formulas `(3)--(7)`. For `T subseteq[d]`, let missing set `M=[d] setminus T` and define

\[
 w_{\mathbf r}(T)
 =2\left(\sum_{j\in M}r_j-\max_{j\in M}r_j\right)
 \tag{19}
\]

when `M` is nonempty, with `w_r([d])=0`. Then exact weighted Smith law is

\[
 \boxed{
 \operatorname{coker}s_{\mathbf r}
 \cong
 \bigoplus_{T\subseteq[d],\ |T|\le d-2}
 R/(a^{w_{\mathbf r}(T)})\,f_T.}
 \tag{20}
\]

Equivalently, indexing by missing sets,

\[
 \boxed{
 \operatorname{length}_R\operatorname{coker}s_{\mathbf r}
 =2\sum_{\substack{M\subseteq[d]\\|M|\ge2}}
 \left(\sum_{j\in M}r_j-\max_{j\in M}r_j\right).}
 \tag{21}
\]

Source and target still have equal length

\[
 \operatorname{length}_R K_{\mathbf r}
 =\operatorname{length}_R L_{\mathbf r}
 =2^d\sum_i r_i,
 \tag{22}
\]

so kernel has same length as cokernel. Exact Fitting equality `(17)` also persists. Closed-horizon
dimension remains `2^d-d-1`, but normal depths now retain heterogeneous contact weights.

### Proof

Only Smith valuation changes. Basis `f_S` still exists, while `(14)` becomes

\[
 f_{G_i}f_S
 =a^{2\sum_{j\in G_i\cap S}r_j}f_{G_i\triangle S}.
 \tag{23}
\]

For fixed target `T`, unique source is `S=G_i triangle T`, so exponent is

\[
 2\sum_{j\notin T,\ j\ne i}r_j.
 \tag{24}
\]

If missing set `M` has at least one element, minimum over `i` is achieved by choosing missing index
of maximal `r_i`, giving `(19)`. If `|M|<=1`, minimum is zero, so full face and facets vanish from
quotient. Pure-basis image argument from `(16)` proves `(20)`, and summing bar lengths gives `(21)`.

Module `A_r/(f_i)` consists of `2^(d-1)` copies of `R/(a^(2r_i))`, hence its length is
`2^d r_i`, proving first equality `(22)`. Determinant valuation of multiplication by `f_i` on
`A_r` is also `2^d r_i`; sum over `i` gives second equality. Kernel--cokernel length equality and
Fitting formula follow as before. QED.

Weighted interpretation is exact:

> face missing constraints `M` stores total missing contact depth after removing single largest
> depth. One missing direction is absorbable; every additional missing direction contributes to
> joint obstruction.

## Corollary: exact truncated hard-core Fock realization

Take `R=C[[a]]` and closed horizon `a=0`. Let

\[
 \mathcal H_{\le d-2}
 =\operatorname{span}\{|T\rangle:T\subseteq[d],\ |T|\le d-2\}
 \subset(\mathbb C^2)^{\otimes d}.
 \tag{25}
\]

Let `P` be orthogonal projection to `(25)` and `sigma_i^+` hard-core raising operator on factor
`i`. Define compressed creators

\[
 A_i=P\sigma_i^+P.
 \tag{26}
\]

Then `A_i^2=0`, operators commute, and every product of `d-1` distinct creators is zero. Map

\[
 \boxed{
 (\operatorname{coker}s_d)/a
 \xrightarrow{\sim}
 \operatorname{Alg}(A_1,\ldots,A_d),
 \qquad
 f_i\longmapsto A_i}
 \tag{27}
\]

is algebra isomorphism. For real weights `lambda_i`, number Hamiltonian

\[
 H_\lambda=\sum_i\lambda_iN_i\big|_{\mathcal H_{\le d-2}}
 \tag{28}
\]

generates exact phase transport

\[
 \boxed{
 e^{itH_\lambda}A_Te^{-itH_\lambda}
 =e^{it\sum_{i\in T}\lambda_i}A_T,}
 \qquad A_T=\prod_{i\in T}A_i.
 \tag{29}
\]

For `lambda_i=log p_i` at distinct primes, this is literal prime phase clock on endogenous face
topology.

### Proof

On basis `|T>`, operator `A_i` adds vertex `i` exactly when `i notin T` and resulting cardinality
is at most `d-2`; otherwise it gives zero. Hence squares vanish, different creators commute, and
all `(d-1)`-fold products vanish. Relations are exactly `(10f)`, so algebra homomorphism `(27)`
exists. Monomials `A_T` with `|T|<=d-2` are linearly independent because
`A_T|emptyset>=|T>`. They also span generated algebra, proving isomorphism. Projection `P` and
Hamiltonian commute. Standard number-operator commutator gives
`e^(itH)A_i e^(-itH)=e^(it lambda_i)A_i`; multiply commuting factors to get `(29)`. QED.

This is finite type-I quantum realization only. It does not produce a nonsemisimple DVR wall,
half-sided modular horizon, black-hole surface, wormhole interior, or complexity law. Any such
claim requires independent cofinal/operator comparison.

## Exact significance

This is nonformal source-composition anomaly. Every factor lies on monogenic law-equivalence locus,
yet tensor product leaves that locus and generates mixed pole invisible to any factor separately.
Anomaly is not determinant mismatch: source and target lengths remain equal. It is kernel/cokernel
defect whose size grows as `2^d(d-2)+2`. Equation `(10c)` identifies it as critical algebra
of joint trace orientation, while no factor alone has critical soldering. Equation `(10e)` shows
joint criticality generates endogenous persistent simplex topology: face excess codimension becomes
normal depth.

This supplies concrete model for multi-source constraint uncertainty:

> individually exact law identifications need not compose; tensor-framed joint source creates new
> carrier whose rank/depth is not present in any factor.

Weighted law `(19)` makes statement heterogeneous in normal depth and predicts precise persistence
under unequal source scales. It does not yet treat factors of different algebraic doctrines.

It does not prove universal novelty or RH selection. Map is factor-framed. Removing generator/source
frame, comparing with Grothendieck fundamental classes, and testing presentation independence are
open priority gates.

## Conjecture--attack loops

1. **Tensor of exact solderings remains exact.** False for every `d>=2`.
2. **Only determinant changes.** False: determinant lengths stay equal while mixed kernel/cokernel
   appear.
3. **Mixed anomaly is isolated at two factors.** False: `(8)--(9)` give all `d` and exponential
   growth.
4. **Mixed anomaly selects critical line.** False: theorem is source algebra independent of Xi.
5. **Surviving conjecture:** trace-versus-deformation defects of multi-source composition form
   higher obstruction complex whose first mixed term is critical algebra of joint
   trace orientation and whose completion shadows are corpus route no-gos.

## Lean formalization and novelty boundary

Tensor trace duality, complete-intersection differentials, monomial bases, and Smith decompositions
are classical. Exact infinite Smith formula appears new to corpus; external priority is
unverified. Closest serious collision is bivariant Hochschild/Grothendieck-duality fundamental-class
composition (https://arxiv.org/abs/1202.4367); actual categorical cross-effects require cubical
functor calculus (https://arxiv.org/abs/1101.1025), not constructed here. Whether `(7)` is already
canonical fundamental-class defect remains open.

All proved algebraic, length, Fitting, nonmonogenic, closed-fibre, trace-dual, Kähler, hard-core
creator, and phase statements are formalized in the factor-framed Lean module family. The literal
`ℂ[[X]]`, depth-one closed fibre is ring-equivalent to the full compressed creator algebra. See the
same-directory `-formalized.md` companion for exact declarations and verification.

## Gates

- [x] dependency-closed paper proof
- [x] exact all-`d` anomaly module
- [x] heterogeneous contact-depth extension
- [x] exact finite quantum phase realization of closed-horizon face algebra
- [x] exact length growth
- [x] nonmonogenic second family
- [ ] presentation/source-frame independence
- [ ] comparison with fundamental-class formalism
- [ ] literal arithmetic source realization
- [x] Lean formalization

## Log

- 2026-08-08 -- hostile naturality attack replaced formal edge coboundary by exact tensor-source
  framed Jacobian defect; solved its Smith module and growth for all tensor powers.
