# Congruence-order trace--Kähler exterior-square discrepancy law

- **ID:** `congruence-order-trace-kahler-exterior-square-nonmetricity-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / TRACE--KÄHLER DISCREPANCY / EXTERIOR-SQUARE LAW
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [NO RH CLAIM] [NO LEAN WRITTEN]`
  `[CLASSICAL INGREDIENTS] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent field:** `../../1-in-progress/constraint-relativity/source-soldering-bivariant-law-geometry.md`.
- **Phase card:** `../../1-in-progress/constraint-relativity/defect-duality-phase-geometry.md`.

## Statement

Let `R` be a discrete valuation ring with uniformizer `a`, fraction field `K`, and residue field
`k`. Fix `N>=2` and assume `2N` is a unit in `R`. Put

\[
 O=R^N,
 \qquad
 A=R\mathbf 1+aO\subset O,
 \qquad
 C=O/A.
 \tag{1}
\]

Use coordinate trace on `K^N`, let `A^sharp` be trace-dual lattice, and define trace-law defect

\[
 L=A^\sharp/A.
 \tag{2}
\]

Then, with `m=N-1`,

\[
 \boxed{C\cong k^m,}
 \tag{3}
\]

\[
 \boxed{L\cong\bigl(R/(a^2)\bigr)^m,}
 \tag{4}
\]

whereas cotangent-law defect is

\[
 \boxed{
 \Omega_{A/R}
 \cong
 \bigl(R/(a^2)\bigr)^m
 \oplus
 \bigl(R/(a)\bigr)^{\binom m2}.}
 \tag{5}
\]

At closed horizon, multiplication by `a` canonically identifies `C` with square-zero ideal `V`
of `A/aA`, and

\[
 \boxed{
 \Omega_{A/R}/a\Omega_{A/R}
 \cong
 C\oplus\bigwedge_k^2 C.}
 \tag{6}
\]

Thus trace-law and cotangent-law barcodes agree exactly for `N=2`. Beginning at `N=3`, cotangent
response contains source-forced pair-interaction sector of dimension

\[
 \boxed{\binom{N-1}{2}.}
 \tag{7}
\]

No comparison map `L->Omega_(A/R)` is asserted. Equation `(5)` is invariant-factor comparison;
equation `(6)` is canonical closed-fibre exterior-square law.

Equation `(6)` is internal canonical decomposition of cotangent fibre. Since no comparison map
`L->Omega_(A/R)` is constructed, `Lambda^2 C` is not asserted to be canonical quotient of
`Omega_(A/R)` by `L`.

## Proof of observer defect

Since `aO subset A`, reduction modulo `a` gives

\[
 C=O/(R\mathbf1+aO)
 \cong k^N/k\mathbf1
 \cong k^m.
 \tag{8}
\]

This is standard `A_(N-1)` observer/root space. QED.

## Proof of trace-law Smith type

For `y in K^N`, coordinate trace pairing is `Tr(xy)=sum_i x_i y_i`. Therefore

\[
 A^\sharp
 =\{a^{-1}z:z\in R^N,\ \sum_i z_i\in aR\}.
 \tag{9}
\]

Anchor last sheet and put

\[
 b_i=a^{-1}(e_i-e_N)\quad(1\le i\le m),
 \qquad
 b_N=e_N.
 \tag{10}
\]

These form an `R`-basis of `A^sharp`. An `R`-basis of `A` is

\[
 \mathbf1,\ ae_1,\ldots,ae_m.
 \tag{11}
\]

In basis `(10)`, inclusion matrix of `(11)` is block matrix

\[
 M=
 \begin{pmatrix}
 a\mathbf1_m & a^2I_m\\
 N & a\mathbf1_m^{\mathsf T}
 \end{pmatrix}.
 \tag{12}
\]

Pivot `N` is a unit. Eliminating first column leaves Schur block

\[
 a^2\left(I_m-N^{-1}\mathbf1_m\mathbf1_m^{\mathsf T}\right).
 \tag{13}
\]

Matrix in parentheses is invertible: it acts as identity on sum-zero hyperplane and as
`N^(-1)` on line spanned by `mathbf1_m`, because `N=m+1`. Hence `(12)` is equivalent over `R`
to

\[
 \operatorname{diag}(1,a^2,\ldots,a^2).
 \tag{14}
\]

Its cokernel is `(4)`. QED.

## Proof of cotangent Smith type

Put `x_i=ae_i` for `1<=i<=m`. There is exact presentation

\[
 A\cong
 R[x_1,\ldots,x_m]
 /\left(x_i^2-ax_i,\ x_ix_j\ (i<j)\right).
 \tag{15}
\]

Indeed every monomial reduces to `R`-span of `1,x_1,...,x_m`, whose evaluation in `O` is
linearly independent. Differentiating relations gives

\[
 (2x_i-a)dx_i=0,
 \qquad
 x_jdx_i+x_idx_j=0
 \quad(i<j).
 \tag{16}
\]

Multiplying first relation by `x_i` and using `x_i^2=ax_i` gives

\[
 a\,x_idx_i=0.
 \tag{17}
\]

Original relation gives `2x_i dx_i=a dx_i`. Multiply it by `a` and use `(17)`; since `2` is a
unit,

\[
 a^2dx_i=0.
 \tag{17a}
\]

Multiplying it by `x_j`, `j!=i`, gives

\[
 a\,x_jdx_i=0.
 \tag{18}
\]

Consequently `Omega_(A/R)` is generated over `R` by `dx_i` and

\[
 z_{ij}=x_jdx_i=-x_idx_j\quad(i<j),
 \tag{19}
\]

with annihilators `a^2` and `a`, respectively.

To prove no additional relations occur, define

\[
 M_\Omega
 =\bigoplus_i(R/(a^2))E_i
 \oplus\bigoplus_{i<j}(R/(a))Z_{ij}.
 \tag{20}
\]

Give it `A`-action by

\[
 x_iE_i=\frac a2E_i,
 \qquad
 x_jE_i=
 \begin{cases}
 Z_{ij},&i<j,\\
 -Z_{ji},&j<i,
 \end{cases}
 \qquad
 x_\ell Z_{ij}=0.
 \tag{21}
\]

Relations in `(15)` hold on this module. Assignment `d(x_i)=E_i` is an `R`-derivation because
it kills differentials in `(16)`. Universal property gives `Omega_(A/R)->M_Omega`. Conversely
`E_i mapsto dx_i`, `Z_ij mapsto x_jdx_i` defines `A`-linear map back. They are inverse on
generators, proving `(5)`. QED.

## Proof of canonical horizon exterior square

Let `B=A/aA`. Image `V` of `aO` in `B` satisfies

\[
 B\cong k\oplus V,
 \qquad V^2=0.
 \tag{22}
\]

Multiplication by `a` gives canonical isomorphism

\[
 C=O/A\xrightarrow{\sim}aO/aA=V.
 \tag{23}
\]

Base change for Kähler differentials yields

\[
 \Omega_{A/R}/a\Omega_{A/R}\cong\Omega_{B/k}.
 \tag{24}
\]

For square-zero algebra `B=k+V`, differentials are quotient of

\[
 B\otimes_kV\cong V\oplus(V\otimes_kV)
 \tag{25}
\]

by Leibniz relations `v dw+w dv=0`. Since `2` is invertible, these kill symmetric square and
leave exterior square. Thus

\[
 \Omega_{B/k}\cong V\oplus\bigwedge_k^2V.
 \tag{26}
\]

Combine `(23)--(26)` to obtain `(6)`. QED.

## Theorem: tangent-head soldering obstruction

Assume `N>=3` and `N-2` is also a unit in `R` (in particular, take `R=C[[a]]`). Henceforth `b_i`
denotes class in `L` of basis vector from `(10)`. Write

\[
 \bar b=N^{-1}\sum_{k=1}^m b_k.
 \tag{26a}
\]

Action of source generators on `L` is

\[
 a^2b_i=0,
 \qquad
 x_jb_i=0\ (j\ne i),
 \qquad
 x_ib_i=a(b_i-\bar b).
 \tag{26b}
\]

Let maximal ideal

\[
 \mathfrak m_A=(a,x_1,\ldots,x_m).
 \tag{26c}
\]

Then `A/mathfrak m_A\cong k`.

Then `mathfrak m_A L=aL`, and every `A`-linear map

\[
 \varphi:\Omega_{A/R}\longrightarrow L
 \tag{26d}
\]

satisfies

\[
 \boxed{\operatorname{im}\varphi\subset aL.}
 \tag{26e}
\]

More precisely,

\[
 \boxed{
 \operatorname{Hom}_A(\Omega_{A/R},L)
 \cong
 \operatorname{Hom}_k(\Omega_{A/R}/\mathfrak m_A\Omega_{A/R},aL)
 \cong\operatorname{Mat}_{m\times m}(k),}
 \tag{26f}
\]

but natural tangent-head map

\[
 \operatorname{Hom}_A(\Omega_{A/R},L)
 \longrightarrow
 \operatorname{Hom}_k(
 \Omega_{A/R}/\mathfrak m_A\Omega_{A/R},
 L/\mathfrak m_A L)
 \tag{26g}
\]

is identically zero. In particular there is no `A`-linear surjection, isomorphism, or nonzero
tangent-frame lift from cotangent law to trace law.

### Proof

In `L=A^sharp/A`, identity

\[
 \mathbf1=Ne_N+a\sum_kb_k
\]

gives `e_N=-a bar b`. Since `e_i=e_N+ab_i`,

\[
 x_ib_i=e_i=a(b_i-\bar b).
\]

Coordinate multiplication gives `x_jb_i=0` for `j!=i`; `(14)` gives `a^2b_i=0`. This proves
`(26b)` and `mathfrak m_A L=aL`.

Put `ell_i=varphi(dx_i)` and write its head

\[
 \ell_i\equiv\sum_k t_{ki}b_k\pmod{aL},
 \qquad t_i=t_{ii}.
 \tag{26h}
\]

Apply relation `(2x_i-a)dx_i=0`. Since `mathfrak m_A(aL)=0`, equation `(26b)` gives

\[
 a\left(2t_i(b_i-\bar b)-\sum_kt_{ki}b_k\right)=0.
 \tag{26i}
\]

Multiplication by `a` identifies `L/aL` with `aL`, so in `L/aL`

\[
 \sum_kt_{ki}b_k=2t_i(b_i-\bar b).
 \tag{26j}
\]

Compare `i`-th coordinate:

\[
 t_i=2(1-N^{-1})t_i=\frac{2m}{N}t_i,
\]

hence `((m-1)/N)t_i=0`. Units `N` and `m-1=N-2` force `t_i=0`, and `(26j)` then forces every
`t_ki=0`. Thus `ell_i in aL`; the `dx_i` generate over `A`, proving `(26e)`.

Conversely `mathfrak m_A` annihilates `aL`, so every `k`-linear map from
`Omega/mathfrak m_A Omega` to `aL` induces an `A`-linear map: quotient map followed by chosen
`k`-map is `A`-linear because source quotient and target carry action through
`A/mathfrak m_A=k`. Relations `(16)` have coefficients in `mathfrak m_A`, so
`Omega/mathfrak m_A Omega\cong k^m`; also `aL\cong k^m`. This proves `(26f)`. Since every image lies
in `aL=mathfrak m_A L`, reduction to head is zero, proving `(26g)`. QED.

Failure already occurs at first infinitesimal thickening. Action tables give

\[
 \mathfrak m_A^2L=0,
 \qquad
 \mathfrak m_A^2\Omega_{A/R}=0.
 \tag{26j1}
\]

Indeed `mathfrak m_A Omega` is generated over `k` by `a dx_i` and `z_ij`, all annihilated by
`mathfrak m_A`. Hence both modules factor through `A/mathfrak m_A^2`, and reduction

\[
 \operatorname{Hom}_{A/\mathfrak m_A^2}(\Omega,L)
 \longrightarrow
 \operatorname{Hom}_k(\Omega/\mathfrak m_A\Omega,L/\mathfrak m_A L)
 \tag{26j2}
\]

is zero. Every residue-frame isomorphism fails to lift across single square-zero thickening
`A/mathfrak m_A^2 -> A/mathfrak m_A`. Corresponding first soldering-obstruction space is

\[
 \boxed{
 \mathcal N_0
 :=\operatorname{coker}(26j2)
 \cong\operatorname{Mat}_{m\times m}(k).}
 \tag{26j3}
\]

## Theorem: Dedekind--Kähler different hierarchy

Assume `N>=3`. Define Dedekind different as colon ideal in total quotient algebra

\[
 \mathfrak D_D
 =\{d\in K^N:dA^\sharp\subset A\}.
 \tag{26j4}
\]

As ideals inside `A subset O`, Dedekind and Kähler differents are

\[
 \boxed{
 \mathfrak D_D=a^2O,}
 \tag{26k}
\]

\[
 \boxed{
 \mathfrak D_K=\operatorname{Fitt}_0^A\Omega_{A/R}=a^mO.}
 \tag{26l}
\]

Therefore:

- at `N=3` (`m=2`), `mathfrak D_D=mathfrak D_K`, yet tangent-head soldering `(26g)` is zero;
- at `N>=4`, `mathfrak D_K subsetneq mathfrak D_D`.

### Proof

If `d in mathfrak D_D`, then `d in A` because `1 in A^sharp`. Also `db_i in A`. Vector
`db_i=(d_i/a)e_i-(d_N/a)e_N` has zero third coordinate since `N>=3`; membership in
`A=R1+aO` forces both displayed nonzero coordinates divisible by `a`. Hence every `d_i` and `d_N`
is divisible by `a^2`, proving `mathfrak D_D subset a^2O`. Conversely basis `(10)` gives
for every `d in a^2O`, both `de_N` and `db_i` lie in `aO subset A`, proving `(26k)`.

For `(26l)`, relations `(16)` give presentation

\[
 A^{m+\binom m2}\longrightarrow A^m\longrightarrow\Omega_{A/R}\longrightarrow0,
 \tag{26m}
\]

so `Fitt_0^A(Omega)` is generated by `m x m` Jacobian minors. Every entry lies in `aO`, hence all
minors lie in `a^mO`. For fixed `j<=m`, choose `i!=j`; rows `d(x_ix_j)` plus square rows
`d(x_k^2-ax_k)` for `k!=i` give exact determinant

\[
 \pm x_j\prod_{k\ne i}(2x_k-a)=\pm a^m e_j.
 \tag{26n}
\]

All-square minor is

\[
 P=\prod_k(2x_k-a)
 =(-1)^{m-1}a^m\sum_{j\le m}e_j+(-1)^ma^me_N.
 \tag{26o}
\]

Subtract first-sheet generators from `(26n)` to obtain `a^m e_N`. Since `m>=2`, `a^mO subset A`;
maximal minors generate all `a^mO`. QED.

Case `N=2` is exceptional and monogenic: `L\cong Omega_(A/R)`, and formula `(26l)` is not asserted
there.

## Exact trace--Kähler discrepancy consequences

Trace-law and cotangent-law lengths are

\[
 \operatorname{length}_R L=2m,
 \qquad
 \operatorname{length}_R\Omega_{A/R}=2m+\binom m2.
 \tag{27}
\]

Therefore scalar discrepancy is

\[
 \boxed{
 \nu(A,O)
 :=\operatorname{length}_R\Omega_{A/R}
 -\operatorname{length}_R(A^\sharp/A)
 =\binom{N-1}{2}.}
 \tag{28}
\]

More information survives than scalar `(28)`: trace side has `m` depth-two bars, while cotangent
side adds exactly `binom(m,2)` depth-one bars. Independently, `Omega/aOmega` has canonical summand
`Lambda^2 C`; without `L->Omega` there is no canonical trace/cotangent quotient.

Three-sheet case is sharper than length discrepancy: Kähler and Dedekind differents agree exactly,
but every source-linear comparison loses tangent head by `(26e)--(26g)`. Determinant equality is
not only incomplete; it cannot be soldered to directional response inside source module category.

For `N=3`, this recovers hostile counterexample

\[
 L\cong(R/(a^2))^2,
 \qquad
 \Omega_{A/R}\cong(R/(a^2))^2\oplus R/(a).
 \tag{29}
\]

Hence universal trace-law extension cannot be identified with cotangent response once three sheets
interact, even though both have same support and same generic étale fibre.

## Constraint Relativity interpretation

This is first exact local law separating five corpus faces without analogy:

| Face | Exact object |
|---|---|
| arithmetic/source | congruence order `A=R1+aO` |
| spectral/observer | `C=k^N/k1` |
| duality/trace law | `L=A^sharp/A`, depth-two standard sector |
| geometry/response | `Omega_(A/R)` |
| cotangent pair sector | `Lambda^2 C` at horizon |
| topology | depth-two plus depth-one persistence barcode |

Newtonian/monogenic charts conflate trace law and differential response. General field must retain
both and their mismatch. Exterior-square sector is metric-free antisymmetric cotangent-response
sector and candidate input to later curvature; this theorem constructs no connection or curvature
tensor. It begins only with three observer directions. If a later realization promotes this
antisymmetric cotangent sector to a differential two-form on control space, its pullback to a
one-dimensional clock vanishes; such promotion is not part of this theorem.

For RH corpus, theorem gives no critical-line selection. It predicts a precise failure mode: any
multi-prime chart modeled by a congruence collision and identified only through trace/discriminant
must miss `Lambda^2` response sector. A literal arithmetic comparison producing this order or its
analogue remains open and cannot be inserted as axiom.

## Conjecture--attack loops

1. **Trace duality defect always equals cotangent defect.** False for every `N>=3` by `(5)`.
2. **Their total lengths at least agree.** False; excess is `(28)`.
3. **Cotangent fibre has only one-body directions.** False; it has internal `Lambda^2 C` sector.
4. **Pair sector appears already for two sheets.** False; `Lambda^2 k=0` and `L=Omega` for `N=2`.
5. **Discriminant/support sees pair sector.** False; both laws have same support, while tracial
   length has valuation `2m` and
   `Fitt_0^R(Omega_(A/R))=(a^(2m+binom(m,2)))`.
6. **This proves RH or physical curvature.** False. It is generalized finite-order theorem.
7. **Equal Dedekind and Kähler differents permit directional identification.** False at `N=3`:
   differents equal while every tangent-head map is zero.
8. **Surviving conjecture:** for broad source--observer charts, trace-law/cotangent mismatch is
   controlled by derived relation-execution sectors whose first horizon layer is an exterior power
   of observer defect.

## Novelty boundary

Kähler differentials, codifferents, square-zero algebras, cotangent complexes, fibre-product orders,
Smith theory, and exterior powers are classical. Complete-intersection/cotangent-homology criteria
are also occupied. Relevant primary parents include:

- https://arxiv.org/abs/math/9909192
- https://arxiv.org/abs/2104.08999
- https://arxiv.org/abs/2204.10427
- https://arxiv.org/abs/2305.10022
- https://arxiv.org/abs/2307.02315
- https://arxiv.org/abs/2604.01992

Broad search found no exact collision for coupled statement `(3)--(7)`: normalization observer,
trace-dual Smith type, full Kähler Smith type, and canonical exterior-square horizon sector for
diagonal congruence order. Search absence is not priority proof. Honest label is
`[PAPER-PROVED] [NOVELTY UNVERIFIED]`.

## Lean-return note

No Lean work authorized. Later formalization should use explicit finite free bases, trace pairing,
Smith reduction of `(12)`, quotient-algebra presentation `(15)`, and universal derivation. Likely
files: finite free modules, Kähler differentials, exterior powers, and matrix equivalence corpus;
search exact local names before edits.

## Gates

- [x] dependency-closed paper proof
- [x] general `N` family, not isolated counterexample
- [x] positive exterior-square survivor
- [x] no RH/physics overclaim
- [ ] hostile independent proof audit
- [ ] specialist novelty review
- [ ] Lean formalization

## Log

- 2026-08-08 -- generalized hostile three-sheet counterexample to all diagonal congruence orders;
  found source-forced `Lambda^2` horizon response sector.
