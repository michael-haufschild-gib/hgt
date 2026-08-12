# Unitriangular conservative-repair genealogy, cofinal phase, and compact-repair law

- **ID:** ULF-CRGM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / ROUTE-INDEPENDENT MECHANISM
- **Source:** ULF-ALM-1, ULF-ALM-2, ULF-MPE-1, and ULF-FLPM-3
- **Statement:** A stationary sequence of individually conservative certified repairs is exactly
  unitriangular at every finite depth, but its Hilbert completion undergoes an invertible / dense
  nonclosed / hidden-lineage phase transition; compact local formation repairs precisely the
  finite-kernel phase and never the critical phase.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CLASSICAL OPERATOR INGREDIENTS]`
  `[NEW ULF COUPLING] [LEAN PENDING] [NOT RH] [NO SOURCE SELECTOR]`

## Goal

Close the missing cofinal extension of conservative-repair mechanics. The theorem must start from a
repair certificate, not an arbitrary operator chosen after completion, and must determine exactly
when finite semantic equivalence survives as global formation/properness.

## Gates

- [x] 0 -> 1: source grammar, exact operator, and falsifiers identified
- [x] 1 -> 2: all finite, cofinal, admission, compact-repair, and reciprocal claims proved below
- [ ] 2 -> 3: Lean formalization under `HTGeometry/UniversalLawField`
- [ ] 3 -> 4: standalone publication/priority audit

## 1. Certified repair grammar

Let `H_N=C^(N+1)` with orthonormal basis `e_0,...,e_N`. Let `B_N` be the backward truncated shift

\[
 B_Ne_0=0,
 \qquad
 B_Ne_n=e_{n-1}\quad(1\le n\le N).
 \tag{GR.1}
\]

Fix `alpha>=0`. The sequential certificate

\[
 e_n\sim\alpha e_{n-1}
 \tag{GR.2}
\]

is represented by the **genealogy formation operator**

\[
 G_{\alpha,N}=I-\alpha B_N.
 \tag{GR.3}
\]

Its zeroth column is the old semantic carrier and its `n`-th column for `n>=1` is the repair
syzygy `e_n-alpha e_(n-1)`.

Define the finite semantic reader

\[
 b_{\alpha,N}(x)=\sum_{n=0}^N\alpha^n x_n.
 \tag{GR.4}
\]

## Theorem 2.1 -- finite conservative genealogy

For every `N` and every `alpha>=0`:

1. `G_(alpha,N)` is invertible, with
   \[
   G_{\alpha,N}^{-1}=\sum_{k=0}^{N}\alpha^k B_N^k;
   \tag{GR.5}
   \]
2. the semantic reader obeys the exact conservation identity
   \[
   \boxed{b_{\alpha,N}G_{\alpha,N}=\pi_0;}
   \tag{GR.6}
   \]
3. consequently every finite certified repair history is a change of presentation: all nonzero
   repair coordinates are semantic-null and the old carrier is recovered exactly;
4. the inverse bounds separate the future phases:
   \[
   \begin{array}{ll}
   0\le\alpha<1:&\|G_{\alpha,N}^{-1}\|\le(1-\alpha)^{-1},\\
   \alpha=1:&\|G_{1,N}^{-1}\|\ge\sqrt{N+1},\\
   \alpha>1:&\|G_{\alpha,N}^{-1}\|\ge\alpha^N.
   \end{array}
   \tag{GR.7}
   \]

### Proof

Since `B_N^(N+1)=0`, multiplying the finite geometric series in `(GR.5)` by
`I-alpha B_N` gives the identity on both sides.

For `z in H_N`, use `(Gz)_n=z_n-alpha z_(n+1)` for `n<N` and `(Gz)_N=z_N`.
Then

\[
 \sum_{n=0}^{N-1}\alpha^n(z_n-\alpha z_{n+1})+\alpha^Nz_N=z_0,
\]

which proves `(GR.6)`.

When `alpha<1`, `(GR.5)` and `||B_N||<=1` give the geometric upper bound. For the other two
cases apply the inverse to `e_N`:

\[
 G_{\alpha,N}^{-1}e_N
 =e_N+\alpha e_{N-1}+\cdots+\alpha^Ne_0.
 \tag{GR.8}
\]

Its norm is `sqrt(N+1)` at `alpha=1` and at least `alpha^N` above one. QED.

## 3. Cofinal genealogy

Let `H=ell^2(N_0)` with unilateral forward shift `S e_n=e_(n+1)` and backward shift `B=S*`.
Put

\[
 G_\alpha=I-\alpha B.
 \tag{GR.9}
\]

## Theorem 3.1 -- complete cofinal phase trichotomy

### Subcritical chamber: `0<=alpha<1`

`G_alpha` is a bounded isomorphism and

\[
 G_\alpha^{-1}=\sum_{k\ge0}\alpha^kB^k,
 \qquad
 \|G_\alpha^{-1}\|\le(1-\alpha)^{-1}.
 \tag{GR.10}
\]

### Critical chamber: `alpha=1`

`G_1` is injective and has dense, proper, nonclosed range. The unit vectors

\[
 u_N=(N+1)^{-1/2}\sum_{n=0}^Ne_n
 \tag{GR.11}
\]

satisfy

\[
 \|G_1u_N\|=(N+1)^{-1/2}\longrightarrow0.
 \tag{GR.12}
\]

Thus no genuine hidden lineage exists, but finite normalized histories become arbitrarily close to
one.

### Supercritical chamber: `alpha>1`

`G_alpha` is surjective and has the one-dimensional kernel

\[
 \boxed{\ker G_\alpha=\mathbb C g_\alpha,\qquad
 g_\alpha=(1,\alpha^{-1},\alpha^{-2},\ldots).}
 \tag{GR.13}
\]

It has the bounded right inverse

\[
 R_\alpha=-\alpha^{-1}(I-\alpha^{-1}S)^{-1}S,
 \qquad
 \|R_\alpha\|\le(\alpha-1)^{-1}.
 \tag{GR.14}
\]

The marked hidden lineage has

\[
 \|g_\alpha\|^2=\frac{\alpha^2}{\alpha^2-1},
 \tag{GR.15}
\]

which diverges as the critical wall is approached from above.

### Proof

Below one, the Neumann series proves `(GR.10)`.

At one, `G_1x=0` makes the coordinates of `x` constant, so square summability forces `x=0`.
The adjoint is `I-S`; its kernel is zero because the zeroth coordinate of `Sy=y` forces `y_0=0`
and then all coordinates vanish. Hence `ran G_1` is dense. Equations `(GR.11)--(GR.12)` show
that `G_1` is not bounded below. An injective bounded operator with closed range is bounded below,
so the range is not closed; in particular it is proper.

Above one, solving `x_n-alpha x_(n+1)=0` gives `(GR.13)`, and the geometric vector lies in
`ell^2` exactly because `alpha>1`. The factorization

\[
 G_\alpha=-\alpha B(I-\alpha^{-1}S)
 \tag{GR.16}
\]

shows surjectivity because `I-alpha^(-1)S` is invertible and `B S=I`. Multiplication verifies
`G_alpha R_alpha=I`, and the Neumann bound gives `(GR.14)`. The geometric series gives
`(GR.15)`. QED.

## 4. Source-admission law

On finitely supported sequences define the algebraic semantic reader

\[
 b_\alpha(x)=\sum_{n\ge0}\alpha^n x_n.
 \tag{GR.17}
\]

## Theorem 4.1 -- semantic conservation versus continuous admission

For every `alpha>=0`,

\[
 b_\alpha G_\alpha z=z_0
 \qquad(z\in c_{00}).
 \tag{GR.18}
\]

The reader `b_alpha` extends continuously to `ell^2` if and only if `alpha<1`.

### Proof

Equation `(GR.18)` is the same finite telescope as `(GR.6)`. If `alpha<1`, the coefficient
sequence `(alpha^n)` is square summable, so Cauchy--Schwarz gives continuity. At `alpha=1`, the
unit vectors `u_N` of `(GR.11)` satisfy `b_1(u_N)=sqrt(N+1)`, so no bounded extension exists. If
`alpha>1`, already `|b_alpha(e_N)|=alpha^N` is unbounded on unit vectors. QED.

Thus algebraic semantic conservation survives in every chamber, while the admitted Hilbert
observer exists only below the wall. Completion changes the law, not the finite equations.

## 5. Compact-repair classification

Let `A:H->Y` be compact and form the joint observer

\[
 T_{\alpha,A}x=(Ax,G_\alpha x).
 \tag{GR.19}
\]

## Theorem 5.1 -- compact local formation repairs exactly one chamber

1. If `alpha<1`, `T_(alpha,A)` is bounded below for every `A`, because `G_alpha` already is.
2. If `alpha=1`, `T_(1,A)` is not bounded below for any compact `A`.
3. If `alpha>1`, `T_(alpha,A)` is bounded below if and only if
   \[
   A g_\alpha\ne0.
   \tag{GR.20}
   \]
   In particular one rank-one compact observer repairs the completed genealogy, and no observer
   annihilating the born lineage can do so.

### Proof

The first clause is immediate from `(GR.10)`.

For the critical clause, the vectors `u_N` are weakly null: the assertion is immediate against
finitely supported test vectors and follows for every `ell^2` test vector by density and
`||u_N||=1`. Compactness gives `Au_N->0`; `(GR.12)` gives `G_1u_N->0`. Hence the joint map is not
bounded below.

Above one, `G_alpha` is surjective with closed range and finite kernel `C g_alpha`. The
compact--cofinal fusion theorem says `(A,G_alpha)` is bounded below exactly when `A` is injective
on that kernel, which is precisely `(GR.20)`. Directly, restrict `G_alpha` to
`g_alpha^perp`; this restriction is a bounded bijection onto `H`, hence has bounded inverse. The
orthogonal decomposition `x=u+t g_alpha` shows that `G_alpha x` controls `u`, while `Ax` controls
the remaining scalar `t` exactly when `A g_alpha` is nonzero. QED.

### Explicit joint recovery

Let

\[
 A_\alpha x=\frac{\langle x,g_\alpha\rangle}{\|g_\alpha\|}
 \tag{GR.21}
\]

and let `J_alpha:H->g_alpha^perp` be the inverse of
`G_alpha|_(g_alpha^perp)`. Then

\[
 \boxed{x=J_\alpha(G_\alpha x)
 +\frac{A_\alpha x}{\|g_\alpha\|}g_\alpha.}
 \tag{GR.22}
\]

This is exact joint reconstruction from the cofinal genealogy plus one compact local coordinate.

## 6. Reciprocal boundary law

For `alpha>0`, coefficient inversion satisfies

\[
 \boxed{G_\alpha=-\alpha B G_{1/\alpha}^*.}
 \tag{GR.23}
\]

At finite depth let `P_N` be projection onto the terminal basis vector `e_N`. Then

\[
 \boxed{G_{\alpha,N}=-\alpha B_NG_{1/\alpha,N}^*+P_N.}
 \tag{GR.24}
\]

The projections `P_N` converge strongly to zero but have norm one. Consequently:

\[
 \operatorname{ind}G_\alpha=
 \begin{cases}
 0,&0\le\alpha<1,\\
 \text{undefined (non-Fredholm)},&\alpha=1,\\
 1,&\alpha>1.
 \end{cases}
 \tag{GR.25}
\]

### Proof

Since `BS=I`,

\[
 -\alpha B(I-\alpha^{-1}S)=I-\alpha B.
\]

This proves `(GR.23)`. In finite dimension `B_NS_N=I-P_N`, which gives `(GR.24)`.
Strong convergence of `P_N` follows from square summability of coordinates; its norm is one.
The index values follow from Theorem 3.1. QED.

This is not the information-neutral common-kernel lift of packet formation. Reciprocal genealogy
passes through a one-sided boundary map; its index is retained information. Confusing these two
actions would erase the mechanism.

## 7. New unconditional leverage

The theorem supplies conclusions unavailable from the parent theorems separately.

1. **Finite exactness diagnostic.** Uniform finite inverse bounds occur exactly in the chamber where
   the algebraic semantic reader extends continuously.
2. **Critical nonrepairability.** The only scalar wall has no genuine hidden kernel and cannot be
   repaired by any compact local formation, despite exactness of every finite genealogy.
3. **Postcritical repairability.** Once a genuine finite hidden lineage is born, one compact
   coordinate restores exact global reconstruction.
4. **Inverse blow-up is ambiguous.** Both critical and supercritical finite inverses diverge, but the
   limits are different: dense nonclosed range versus surjective range with finite kernel.
5. **Reciprocity has a port.** Inversion exchanges stable and hidden-lineage phases only after a
   coisometric boundary factor. Finite terminal corrections escape strongly but not in norm.

These give a route-independent formation/properness test for any proposed infinite repair process:
compute its certificate operator, not only its finite semantic quotient or endpoint symmetry.

## 8. Conjecture-to-failure loops

### Loop A -- finite conservative repairs stay globally equivalent

**False.** Every `G_(alpha,N)` is invertible, while `G_1` has dense nonclosed proper range and
`G_alpha` has a kernel for `alpha>1`.

**Survivor:** bounded invertibility of the completed certificate operator is the correct global
equivalence law.

### Loop B -- compact observation repairs every cofinal defect

**False.** At the critical wall every compact observer vanishes on the weakly null approximate
lineage `u_N`.

**Survivor:** compact repair is possible exactly for closed-range genealogies with finite kernel,
and it must detect that kernel.

### Loop C -- criticality means a carrier is born

**False.** `ker G_1=0`.

**Survivor:** criticality is a nonseparated approximate-lineage phase; the actual carrier appears
only above threshold.

### Loop D -- reciprocal action is automatically information-neutral

**False for genealogy completion.** Equation `(GR.23)` contains the coisometry `B`, and the index
jumps.

**Survivor:** common-kernel packet action is information-isometric, while one-sided certificate
reciprocity carries a boundary port. The two laws coexist and must be typed separately.

### Loop E -- this selects the critical wall

**False.** The critical wall is precisely the chamber no compact local observer can properize.

**Survivor:** a source selecting the wall must also generate a noncompact critical transducer or a
different completion. Criticality without that producer is an obstruction, not a proof.

## 9. Literature and significance boundary

The operator theorem is a scalar Toeplitz/weighted-shift calculation. Finite-section stability,
Fredholm index, coherent presentations, Tietze transformations, Squier completion, and polygraphic
syzygies are established subjects. Relevant parents include:

- Roch, *Finite sections of truncated Toeplitz operators*, arXiv:1401.5237;
- Guiraud--Malbos--Mimram, *A Homotopical Completion Procedure with Applications to Coherence of
  Monoids*;
- Kraus--von Raumer, *A Rewriting Coherence Theorem with Applications in Homotopy Type Theory*,
  arXiv:2107.01594;
- Ara et al., *Polygraphs: From Rewriting to Higher Categories*, arXiv:2312.00429.

The new HGT/ULF content is the exact coupling:

```text
certified conservative promotion
  + finite semantic conservation
  + admitted Hilbert completion
  + compact/cofinal joint reconstruction
  + reciprocal boundary bookkeeping.
```

No external novelty claim is made. The theorem is significant because it converts four previously
separate field constraints into one source-generated formation law and produces the sharp critical
nonrepairability prediction.

## 10. Exact scope and next gate

This theorem assumes a stationary scalar certificate. It does not classify nonstationary or
operator-valued genealogies, construct an arithmetic certificate sequence, derive positivity,
prove hypertranscendence, select a completion, or imply RH.

The next gate is the nonstationary source-cocycle theorem in the Stage-1 programme. Only after a
pre-target source constructs its certificate cocycle and its critical noncompact transducer may
genealogy properness enter an RH selection argument.

## 11. Lean status

No Lean file was written or built during this research phase. Read-only corpus audit found reusable
infrastructure for unilateral shifts, conservative-repair kernel splittings, dense/nonclosed-range
criteria, compact--cofinal fusion, and Toeplitz index defects. Formalization remains mandatory
before this card may enter Stage 3 or count as Lean-proven.

## Log

- 2026-08-12 -- conjecture isolated from iterative conservative-repair grammar.
- 2026-08-12 -- hostile internal audit separated it from existing finite repair, generic block
  diagonal, and global semi-Fredholm theorems.
- 2026-08-12 -- broad arXiv audit confirmed classical operator and rewriting parents; coupling
  retained as new ULF mechanism, with no priority claim.
- 2026-08-12 -- dependency-closed finite/cofinal/admission/compact-repair/reciprocal proof completed.
