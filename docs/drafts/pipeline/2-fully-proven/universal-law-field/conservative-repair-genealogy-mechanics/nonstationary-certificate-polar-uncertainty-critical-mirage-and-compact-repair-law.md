# Nonstationary certificate-polar uncertainty, critical mirage, and compact-repair law

- **ID:** ULF-CRGM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CONSERVATION AND PROPERNESS LAW
- **Source:** ULF-CRGM-1
- **Statement:** Every positive nonstationary conservative-repair genealogy has reciprocal semantic
  and lineage profiles whose finite energies obey a sharp uncertainty product; cofinally they
  cannot both be Hilbert-admitted, and a broad critical class is invisible to every compact repair.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [NONSTATIONARY] [SHARP CONSERVATION]`
  `[CRITICAL COMPACT-REPAIR NO-GO] [CLASSICAL WEIGHTED-SHIFT INGREDIENTS]`
  `[LEAN PENDING] [NOT RH]`

## Goal

Replace the stationary scalar parameter of ULF-CRGM-1 by an arbitrary source certificate stream.
Derive a route-independent conservation identity rather than merely reclassifying the spectrum of
one Toeplitz operator.

## Gates

- [x] 0 -> 1: reciprocal source profiles and exact finite telescope found
- [x] 1 -> 2: uncertainty, equality, cofinal admission, critical mirage, compact no-go, and
  exponential-dichotomy chambers dependency-closed below
- [ ] 2 -> 3: Lean formalization under `HTGeometry/UniversalLawField`
- [ ] 3 -> 4: standalone publication and external priority audit

## 1. Source grammar and finite genealogy

Let

\[
 a=(a_1,a_2,\ldots),
 \qquad
 0<a_n\le M<\infty,
 \tag{CP.1}
\]

be a positive bounded certificate stream. The `n`-th conservative repair declares

\[
 e_n\sim a_ne_{n-1}.
 \tag{CP.2}
\]

Put

\[
 A_0=1,
 \qquad
 A_n=\prod_{j=1}^na_j,
 \qquad
 Q_n=A_n^{-1}.
 \tag{CP.3}
\]

On `H_N=C^(N+1)` define the weighted backward certificate operator

\[
 (W_Nx)_n=
 \begin{cases}
 a_{n+1}x_{n+1},&n<N,\\
 0,&n=N,
 \end{cases}
 \qquad
 G_N=I-W_N.
 \tag{CP.4}
\]

Define semantic and lineage packets

\[
 b_N=(A_0,\ldots,A_N),
 \qquad
 q_N=(Q_0,\ldots,Q_N).
 \tag{CP.5}
\]

The first is a covector; the second is a vector. Their roles are forced by the same certificates.

## Theorem 2.1 -- exact finite formation and sharp polar conservation

For every `N`:

1. `G_N` is unitriangular and invertible;
2. semantic conservation is exact:
   \[
   \boxed{b_NG_N=\pi_0;}
   \tag{CP.6}
   \]
3. `q_N` is the unique normalized interior lineage:
   \[
   (G_Nq_N)_n=0\quad(n<N),
   \qquad
   G_Nq_N=Q_Ne_N;
   \tag{CP.7}
   \]
4. semantic and lineage energies obey
   \[
   \boxed{
   \|b_N\|_2^2\,\|q_N\|_2^2
   =\Big(\sum_{n=0}^NA_n^2\Big)
    \Big(\sum_{n=0}^NQ_n^2\Big)
   \ge(N+1)^2;}
   \tag{CP.8}
   \]
5. equality in `(CP.8)` holds if and only if
   \[
   A_0=A_1=\cdots=A_N=1,
   \tag{CP.9}
   \]
   equivalently `a_1=...=a_N=1`.

### Proof

The weighted backward shift is nilpotent on `H_N`, so

\[
 G_N^{-1}=I+W_N+\cdots+W_N^N.
\]

For `x in H_N`, use `A_na_(n+1)=A_(n+1)` to telescope:

\[
 b_NG_Nx
 =\sum_{n=0}^{N-1}A_n(x_n-a_{n+1}x_{n+1})+A_Nx_N
 =x_0.
\]

Similarly `a_(n+1)Q_(n+1)=Q_n`, proving `(CP.7)`. Since `A_nQ_n=1`,
Cauchy--Schwarz gives

\[
 (N+1)^2
 =\Big(\sum_{n=0}^NA_nQ_n\Big)^2
 \le\Big(\sum_{n=0}^NA_n^2\Big)
      \Big(\sum_{n=0}^NQ_n^2\Big).
\]

Equality holds exactly when the two positive vectors are proportional. Then
`A_n=cQ_n`, so `A_n^2=c` for every `n`. Since `A_0=1`, `c=1` and every `A_n=1`.
The converse is immediate. QED.

## 3. Cofinal bipolar admission

On `H=ell^2(N_0)` define

\[
 (Wx)_n=a_{n+1}x_{n+1},
 \qquad
 G=I-W.
 \tag{CP.10}
\]

The bound in `(CP.1)` makes `W` bounded. On `c_00`, define the algebraic semantic reader

\[
 b(x)=\sum_{n\ge0}A_nx_n.
 \tag{CP.11}
\]

## Theorem 3.1 -- reciprocal admission and hidden-lineage classification

1. `bGx=x_0` for every finitely supported `x`.
2. `b` extends continuously to `ell^2` if and only if
   \[
   A=(A_n)\in\ell^2.
   \tag{CP.12}
   \]
3. The completed genealogy kernel is
   \[
   \boxed{
   \ker G=
   \begin{cases}
   \{0\},&Q=(Q_n)\notin\ell^2,\\
   \mathbb C Q,&Q=(Q_n)\in\ell^2.
   \end{cases}}
   \tag{CP.13}
   \]
4. The range of `G` is dense for every positive bounded certificate stream.
5. The two polar admissions are mutually exclusive:
   \[
   \boxed{A\in\ell^2\Longrightarrow Q\notin\ell^2,
   \qquad Q\in\ell^2\Longrightarrow A\notin\ell^2.}
   \tag{CP.14}
   \]
6. More quantitatively, every finite depth satisfies
   \[
   \max\{\|b_N\|_2,\|q_N\|_2\}\ge\sqrt{N+1}.
   \tag{CP.15a}
   \]
   Hence the larger polar packet diverges along every cofinal sequence.

### Proof

The first clause is the finite telescope. The Riesz representation theorem gives the second.
Solving `Gx=0` yields

\[
 x_{n+1}=x_n/a_{n+1},
 \qquad
 x_n=x_0Q_n,
\]

which proves `(CP.13)`. For density, solve `G^*y=0`. Its zeroth coordinate gives `y_0=0`, and
the recurrence `y_n=a_ny_(n-1)` then gives `y=0`; hence
`closure(ran G)=(ker G*)^perp=H`.

If both `A` and `Q` were square summable, then both sequences would tend to zero, contradicting
`A_nQ_n=1`. The last clause follows from `(CP.8)`. QED.

This is an exact formation uncertainty law: continuous semantic recovery and admitted hidden
lineage are reciprocal polar phases of one certificate stream, not independent decorations.

## 4. Critical-mirage theorem

Assume

\[
 Q\notin\ell^2,
 \qquad
 \frac{Q_N}{(\sum_{n=0}^NQ_n^2)^{1/2}}\longrightarrow0.
 \tag{CP.15}
\]

Put

\[
 L_N=\Big(\sum_{n=0}^NQ_n^2\Big)^{1/2},
 \qquad
 u_N=L_N^{-1}\sum_{n=0}^NQ_ne_n.
 \tag{CP.16}
\]

## Theorem 4.1 -- critical approximate lineage and compact-repair impossibility

Under `(CP.15)`:

1. `||u_N||=1` and `u_N` converges weakly to zero;
2. the genealogy residual is exactly
   \[
   \boxed{Gu_N=(Q_N/L_N)e_N\longrightarrow0;}
   \tag{CP.17}
   \]
3. `G` is injective with dense, proper, nonclosed range;
4. for every Hilbert space `Y` and every compact operator `K:H->Y`, the joint formation
   \[
   x\longmapsto(Kx,Gx)
   \tag{CP.18}
   \]
   is not bounded below;
5. therefore no finite-rank or compact local observer can properize this critical genealogy.

### Proof

The norm and residual formula follow from `(CP.7)`. Since `Q` is not square summable, `L_N` tends
to infinity. Against a finitely supported test vector, the inner product with `u_N` tends to zero;
density and `||u_N||=1` extend this to every test vector, proving weak convergence.

Theorem 3.1 gives injectivity and density. Equation `(CP.17)` proves that `G` is not bounded below.
An injective bounded operator with closed range is bounded below, so its dense range is nonclosed
and proper. Finally compactness and weak convergence give `Ku_N->0`; together with `(CP.17)` this
shows `(K,G)` is not bounded below. QED.

The residual-ratio hypothesis is sharp for this canonical approximate-lineage construction. It is
automatic whenever the last reciprocal weight does not asymptotically carry all cumulative
lineage energy; in particular it holds for bounded `Q_n`, polynomial growth, and stationary
critical certificates.

## 5. Exponential-dichotomy chambers

For `n,k>=0` write the transfer product

\[
 P(n,k)=\prod_{j=1}^ka_{n+j},
 \qquad P(n,0)=1.
 \tag{CP.19}
\]

## Theorem 5.1 -- uniform stable and unstable genealogy phases

### Stable phase

If there are `C>=1` and `0<r<1` such that

\[
 P(n,k)\le Cr^k
 \qquad(n,k\ge0),
 \tag{CP.20}
\]

then `G` is boundedly invertible. More precisely,

\[
 G^{-1}=\sum_{k\ge0}W^k,
 \qquad
 \|G^{-1}\|\le1+\frac{Cr}{1-r}.
 \tag{CP.21}
\]

The semantic profile `A` lies in `ell^2`, so continuous recovery is admitted.

### Unstable phase

Assume all `a_n` are bounded below away from zero and there are `C>=1`, `0<r<1` with

\[
 P(n,k)^{-1}\le Cr^k
 \qquad(n,k\ge0).
 \tag{CP.22}
\]

Then `G` is surjective with one-dimensional kernel `C Q`. It has a bounded right inverse of norm at
most

\[
 m^{-1}\Big(1+\frac{Cr}{1-r}\Big),
 \qquad m=\inf_na_n>0.
 \tag{CP.23}
\]

Consequently, for every compact `K:H->Y`, the joint formation `(K,G)` is bounded below if and only
if

\[
 KQ\ne0.
 \tag{CP.24}
\]

### Proof

The norm of `W^k` is `sup_n P(n,k)`. Thus `(CP.20)` makes the Neumann series absolutely convergent
in operator norm and proves `(CP.21)`. Taking `n=0` gives exponential decay of `A_n`.

For the reciprocal direction define the bounded weighted forward right inverse of `W` by

\[
 Re_n=a_{n+1}^{-1}e_{n+1}.
 \tag{CP.25}
\]

Then `WR=I`, and `||R^k||=sup_nP(n,k)^(-1)`. Hence `(I-R)^(-1)=sum_(k>=0)R^k` converges with the
stated bound. The factorization

\[
 G=-W(I-R)
 \tag{CP.26}
\]

shows that

\[
 -R(I-R)^{-1}
 \tag{CP.27}
\]

is a bounded right inverse of `G`. Taking `n=0` in `(CP.22)` shows `Q in ell^2`, so Theorem 3.1
gives the one-dimensional kernel. The compact-repair conclusion is the compact--cofinal fusion
classification applied to this closed-range, finite-kernel operator. QED.

## 6. Functional-equation polarity

Certificate inversion `a_n -> a_n^(-1)` exchanges

\[
 A_n\longleftrightarrow Q_n,
 \tag{CP.28}
\]

and swaps `(CP.20)` with `(CP.22)`. It therefore exchanges continuous semantic admission with
hidden-lineage admission, stable invertibility with surjective finite-defect formation, and cokernel
orientation with kernel orientation.

This is not the common-recovery information isometry of packet formation. It is a polar duality of
the source certificates. Equation `(CP.8)` is the conserved quantity transported by this polarity.

## 7. New unconditional leverage

The theorem produces five route-independent tests.

1. **Source certificate test.** Compute prefix products before studying endpoint laws. They already
   decide which of semantic recovery and hidden lineage can enter the Hilbert completion.
2. **Sharp finite conservation.** Every depth pays the exact reciprocal uncertainty `(CP.8)`;
   balanced certificates uniquely minimize the product.
3. **Cofinal exclusion.** No ordinary `ell^2` formation carries both a continuous global semantic
   reader and a genuine hidden lineage.
4. **Critical repair test.** The residual ratio `(CP.15)` constructs a canonical weakly null
   approximate lineage and rules out every compact repair at once.
5. **Postcritical recovery.** Uniform reciprocal contraction births one hidden line, and exactly one
   compact coordinate detecting it restores global reconstruction.

This distinguishes critical mirage from genuine carrier birth without invoking any RH route.

## 8. Conjecture-to-failure loops

### Loop A -- nonstationary genealogy needs a fitted spectral radius

**False.** Prefix products and their reciprocals are source-derived directly from the repair
certificates. The sharp uncertainty identity needs no spectrum.

**Survivor:** use the polar product packets first; introduce operator spectra only for stronger
closed-range conclusions.

### Loop B -- semantic and lineage information can coexist after completion

**False in the ordinary Hilbert formation.** Equation `(CP.14)` forbids it.

**Survivor:** any theory retaining both must use a doubled/Tate/indefinite formation, change weights,
or mark one side outside the Hilbert completion. This is now a precise construction obligation.

### Loop C -- every injective dense genealogy is critical

**False.** Dense range alone does not imply nonclosedness.

**Survivor:** `(CP.15)` is a source-checkable sufficient condition producing normalized approximate
lineage. No universal converse is claimed.

### Loop D -- compact repair can regularize an approximate lineage

**False.** Weakly null approximate lineages are erased by every compact map.

**Survivor:** a critical repair must itself be noncompact or change the admitted completion.

### Loop E -- the sharp uncertainty equality proves selection

**False.** Equality at every finite depth selects `a_n=1`, but that is precisely the stationary
critical genealogy with nonclosed range and no compact properization.

**Survivor:** balanced polarity is a variational characterization of the wall, not a reason the
source must occupy it and not a proof that the wall is admissible.

## 9. Literature and hostile significance audit

Weighted backward-shift eigenvectors, spectra, finite sections, and exponential dichotomies are
classical. Current parents include D'Aniello--Maiuriello, *On the spectrum of weighted shifts*,
arXiv:2210.01510, alongside Toeplitz finite-section and operator-valued frame literature cited in
ULF-CRGM-1.

The new ULF synthesis is the interpretation and exact coupling of:

```text
source repair certificates
  -> reciprocal semantic/lineage packets
  -> sharp finite uncertainty
  -> cofinal admission exclusion
  -> critical compact-repair no-go
  -> postcritical one-coordinate recovery.
```

No external priority claim is made. Significance rests on the conservation law and its formation
consequences, not on rediscovering weighted-shift spectra.

## 10. Exact scope and next gate

The theorem treats positive scalar certificates on one lineage chain. It does not handle branching,
operator-valued certificates, sign/phase cancellation, higher syzygies, source-selected weights,
or an arithmetic completion. It proves no RH statement.

The next gate is an operator-valued certificate-polar theorem. Its finite conservation should be a
trace/determinant or singular-value inequality, and its critical no-go must survive bounded
source-preserving changes of frame. Only then should the programme attempt a literal arithmetic
genealogy.

## 11. Lean status

No Lean was written or built in this research phase. Read-only corpus audit found the needed generic
ingredients but not this variable-certificate conservation theorem. Formalization is mandatory
before promotion to Stage 3.

## Log

- 2026-08-12 -- reciprocal prefix profiles extracted from nonstationary repair grammar.
- 2026-08-12 -- sharp finite uncertainty, equality classification, cofinal exclusion, critical
  compact no-go, and exponential-dichotomy chambers proved.
- 2026-08-12 -- weighted-shift literature audit completed; classical ingredients separated from
  new ULF coupling.
