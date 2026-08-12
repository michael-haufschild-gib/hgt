# Operator-certificate semantic--lineage fusion, unitary gauge, and polar-energy law

- **ID:** ULF-CRGM-3
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / COORDINATE-FREE FUSION LAW
- **Source:** ULF-CRGM-2
- **Statement:** An operator-valued conservative-repair history carries canonical semantic and
  lineage packets whose composite is exactly depth times the identity; their Hilbert--Schmidt
  energies satisfy a sharp gauge-invariant uncertainty law, with equality exactly for unitary
  certificate transport.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [OPERATOR-VALUED] [EXACT RECONSTRUCTION]`
  `[SHARP CONSERVATION] [UNITARY GAUGE] [PARTIAL HIDDEN-LINEAGE CLASSIFICATION]`
  `[LEAN PENDING] [NOT RH]`

## Goal

Lift scalar certificate-polar mechanics to a coordinate-free finite-dimensional fibre. The result
must construct one genuine fusion law and identify its exact equality chamber, rather than append
another list of route analogies.

## Gates

- [x] 0 -> 1: operator prefix transports and dual packets typed
- [x] 1 -> 2: fusion, sharp energy, equality, gauge covariance, cofinal exclusion, kernel, and
  compact critical no-go dependency-closed below
- [ ] 2 -> 3: Lean formalization under `HTGeometry/UniversalLawField`
- [ ] 3 -> 4: publication and external priority audit

## 1. Operator-valued repair grammar

Let `V` be a `d`-dimensional complex Hilbert space, `d>=1`. Let

\[
 C_n:V\longrightarrow V\qquad(n\ge1)
 \tag{OP.1}
\]

be invertible certificate maps with

\[
 \sup_n\|C_n\|<\infty.
 \tag{OP.2}
\]

The repair law is

\[
 e_n(v)\sim e_{n-1}(C_nv).
 \tag{OP.3}
\]

Define prefix transports

\[
 A_0=I_V,
 \qquad
 A_n=C_1C_2\cdots C_n.
 \tag{OP.4}
\]

On `V^(N+1)` define the finite genealogy

\[
 (G_Nx)_n=
 \begin{cases}
 x_n-C_{n+1}x_{n+1},&n<N,\\
 x_N,&n=N.
 \end{cases}
 \tag{OP.5}
\]

Define the **semantic packet** and **lineage packet**

\[
 \mathcal B_N:V^{N+1}\longrightarrow V,
 \qquad
 \mathcal B_N(x)=\sum_{n=0}^NA_nx_n,
 \tag{OP.6}
\]

\[
 \mathcal Q_N:V\longrightarrow V^{N+1},
 \qquad
 (\mathcal Q_Nv)_n=A_n^{-1}v.
 \tag{OP.7}
\]

They are forced by the same certificates. No metric optimization or target endpoint is used to
choose them.

## Theorem 2.1 -- exact semantic and lineage identities

For every finite depth `N`:

1. `G_N` is unitriangular and invertible;
2. semantic conservation is
   \[
   \boxed{\mathcal B_NG_N=\pi_0;}
   \tag{OP.8}
   \]
3. lineage transport cancels every interior repair:
   \[
   \boxed{G_N\mathcal Q_Nv=(0,\ldots,0,A_N^{-1}v);}
   \tag{OP.9}
   \]
4. semantic and lineage packets fuse to exact joint reconstruction:
   \[
   \boxed{\mathcal B_N\mathcal Q_N=(N+1)I_V.}
   \tag{OP.10}
   \]

### Proof

Strict upper block triangularity of `I-G_N` proves finite invertibility. The identity

\[
 A_nC_{n+1}=A_{n+1}
\]

makes `(OP.8)` telescope. The identity

\[
 C_{n+1}A_{n+1}^{-1}=A_n^{-1}
\]

proves `(OP.9)`. Finally every summand in the composite is

\[
 A_nA_n^{-1}=I_V,
\]

so their sum is `(N+1)I_V`. QED.

The normalized lineage packet `(N+1)^(-1)Q_N` is therefore a canonical right inverse of the
semantic packet. This is the exact formation/recovery fusion law.

## 3. Sharp polar-energy conservation

Give all operator spaces their Hilbert--Schmidt norm. Put

\[
 E_N^{\mathrm{sem}}=\|\mathcal B_N\|_{\mathrm{HS}}^2
 =\sum_{n=0}^N\|A_n\|_{\mathrm{HS}}^2,
 \tag{OP.11}
\]

\[
 E_N^{\mathrm{lin}}=\|\mathcal Q_N\|_{\mathrm{HS}}^2
 =\sum_{n=0}^N\|A_n^{-1}\|_{\mathrm{HS}}^2.
 \tag{OP.12}
\]

## Theorem 3.1 -- sharp semantic--lineage uncertainty

For every `N`:

\[
 \boxed{
 E_N^{\mathrm{sem}}E_N^{\mathrm{lin}}
 \ge d^2(N+1)^2.}
 \tag{OP.13}
\]

Equality holds if and only if every prefix transport `A_n` is unitary. Equivalently, equality holds
if and only if every certificate map `C_n`, `1<=n<=N`, is unitary.

### Proof

The Hilbert--Schmidt inner product and `(OP.10)` give

\[
 \langle\mathcal B_N^*,\mathcal Q_N\rangle_{\mathrm{HS}}
 =\operatorname{tr}(\mathcal B_N\mathcal Q_N)
 =d(N+1).
 \tag{OP.14}
\]

Cauchy--Schwarz proves `(OP.13)`.

Equality holds exactly when `Q_N=c B_N*` for some nonnegative scalar `c`. Comparing the zeroth
blocks gives `I_V=cI_V`, hence `c=1`. Comparing every block then gives

\[
 A_n^{-1}=A_n^*,
\]

which says that every `A_n` is unitary. Since `A_0=I`, all prefix transports are unitary exactly
when `C_n=A_(n-1)^(-1)A_n` is unitary at every stage. QED.

Thus unitary transport is not postulated as the neutral gauge. It is the unique equality chamber
of the source-derived semantic--lineage energy law.

## 4. Local gauge covariance

Choose arbitrary unitary frames `U_n:V->V` and put

\[
 C_n'=U_{n-1}C_nU_n^*.
 \tag{OP.15}
\]

Let `D_U` be the block-diagonal unitary on `ell^2(N_0;V)` or on `V^(N+1)` given by
`(D_Ux)_n=U_nx_n`.

## Theorem 4.1 -- repair gauges and invariant work

The transformed prefix maps and packets satisfy

\[
 A_n'=U_0A_nU_n^*,
 \tag{OP.16}
\]

\[
 G_N'D_U=D_UG_N,
 \tag{OP.17}
\]

\[
 \mathcal B_N'D_U=U_0\mathcal B_N,
 \qquad
 D_U^*\mathcal Q_N'U_0=\mathcal Q_N.
 \tag{OP.18}
\]

Consequently `(OP.10)`, both polar energies, the uncertainty defect

\[
 \Delta_N=E_N^{\mathrm{sem}}E_N^{\mathrm{lin}}-d^2(N+1)^2,
 \tag{OP.19}
\]

and the equality chamber are invariant under every local unitary change of repair frame.

### Proof

Cancellation of adjacent `U_n*U_n` factors proves `(OP.16)`. Substitution proves
`(OP.17)--(OP.18)`. Unitary invariance of Hilbert--Schmidt norm proves the final claims. QED.

This gives a precise meaning to local gauge in this mechanics: a gauge changes coordinates at each
repair stage but cannot change semantic--lineage work.

## 5. Cofinal packets and partial hidden lineage

On

\[
 \mathcal H=\ell^2(\mathbb N_0;V)
\]

let

\[
 (Gx)_n=x_n-C_{n+1}x_{n+1}.
 \tag{OP.20}
\]

Define the admitted hidden-lineage space

\[
 V_-=\left\{v\in V:
 \sum_{n=0}^{\infty}\|A_n^{-1}v\|^2<\infty\right\}.
 \tag{OP.21}
\]

## Theorem 5.1 -- cofinal exclusion and kernel realization

1. The algebraic semantic packet extends to a bounded map `B:H->V` if and only if
   \[
   \sum_{n=0}^{\infty}\|A_n\|_{\mathrm{HS}}^2<\infty.
   \tag{OP.22}
   \]
2. The full lineage packet extends to a bounded map `Q:V->H` if and only if
   \[
   \sum_{n=0}^{\infty}\|A_n^{-1}\|_{\mathrm{HS}}^2<\infty.
   \tag{OP.23}
   \]
3. Conditions `(OP.22)` and `(OP.23)` cannot both hold.
4. The kernel is canonically the admitted hidden-lineage space:
   \[
   \boxed{
   V_-\xrightarrow{\ \cong\ }\ker G,
   \qquad
   v\longmapsto(A_n^{-1}v)_{n\ge0}.}
   \tag{OP.24}
   \]
5. The range of `G` is dense.

### Proof

For the semantic packet, the adjoint sends `v` to `(A_n^*v)_n`. Since `V` is finite-dimensional,
boundedness is equivalent to square summability on an orthonormal basis, which is exactly
`(OP.22)`. The lineage statement is identical. If both held, the left side of `(OP.13)` would stay
bounded as `N` tends to infinity while its right side diverges, a contradiction.

Solving `Gx=0` recursively gives `x_n=A_n^(-1)x_0`, proving `(OP.24)`. Finally `G*y=0` has zeroth
coordinate `y_0=0`; invertibility of every certificate and induction give `y=0`. Hence
`closure(ran G)=(ker G*)^perp=H`. QED.

The scalar dichotomy becomes a rank-valued law: `dim V_-` is the number of genuine completed
lineage directions.

## 6. Directional critical mirage

Fix nonzero `v in V`. Put

\[
 L_N(v)^2=\sum_{n=0}^N\|A_n^{-1}v\|^2,
 \qquad
 u_N(v)=L_N(v)^{-1}(A_n^{-1}v)_{0\le n\le N},
 \tag{OP.25}
\]

extended by zero above depth `N`. Assume

\[
 L_N(v)\longrightarrow\infty,
 \qquad
 \frac{\|A_N^{-1}v\|}{L_N(v)}\longrightarrow0.
 \tag{OP.26}
\]

## Theorem 6.1 -- compact observers cannot repair a critical lineage direction

Under `(OP.26)`:

1. `||u_N(v)||=1` and `u_N(v)` converges weakly to zero;
2. `||Gu_N(v)||->0`;
3. for every compact `K:H->Y`, the joint map `(K,G)` is not bounded below.

### Proof

All interior blocks cancel and the terminal residual is `A_N^(-1)v/L_N(v)`. The divergence of
`L_N(v)` gives weak convergence by finite-head approximation. Compactness then gives
`Ku_N(v)->0`, while `(OP.26)` gives `Gu_N(v)->0`. QED.

This is a directional theorem. Other fibre directions may already carry genuine hidden lineage or
stable semantic recovery. The field must retain the whole subspace filtration, not one scalar
critical parameter.

## 7. Closed-range compact repair

Assume `ran G` is closed. Since it is dense, it is all of `H`; `(OP.24)` gives a finite-dimensional
kernel isomorphic to `V_-`.

## Theorem 7.1 -- minimal compact repair rank

For compact `K:H->Y`, the joint formation `(K,G)` is bounded below if and only if

\[
 K|_{\ker G}\text{ is injective}.
 \tag{OP.27}
\]

Therefore:

1. a compact repair exists;
2. every finite-rank repair has rank at least `dim V_-`;
3. rank `dim V_-` is sufficient;
4. the minimal compact repair rank is exactly the hidden-lineage dimension.

### Proof

The equivalence is the compact--cofinal fusion theorem. Injectivity from a vector space of dimension
`dim V_-` requires target/range rank at least that dimension. Orthogonal projection onto `ker G`,
followed by any isometric embedding into a space of that dimension, is finite-rank and injective on
the kernel. QED.

Thus carrier multiplicity is operational: it is exactly the local compact information needed to
restore global properness after a closed-range cofinal formation.

## 8. Conjecture-to-failure loops

### Loop A -- scalar product profiles were a one-dimensional accident

**False.** They are the rank-one case of the exact operator fusion `(OP.10)`.

**Survivor:** semantic recovery and lineage are adjoint polar packets of any invertible certificate
history.

### Loop B -- neutral gauge must be declared externally

**False.** The equality case of `(OP.13)` forces all prefix transports, hence all certificates, to
be unitary.

**Survivor:** unitarity is characterized variationally as zero semantic--lineage work.

### Loop C -- one scalar index describes every cofinal failure

**False.** `V_-` may have any dimension from zero to `d`, and directional critical mirages can
coexist with admitted lineage in other directions.

**Survivor:** the correct invariant is a filtration of fibre directions by transfer growth and
admission.

### Loop D -- a finite endpoint packet reconstructs the history for free

**False.** Exact reconstruction `(OP.10)` pays the sharp energy product `(OP.13)`, which grows
quadratically in depth.

**Survivor:** reconstruction and cost are one conservation law, not separate axioms.

### Loop E -- this is already an RH selection mechanism

**False.** No source in the theorem chooses the certificate stream or its completion. Unitary
equality characterizes neutral transport but does not force an arithmetic source to be neutral.

**Survivor:** any future selection theorem must derive certificates and show why its source
minimizes or quantizes the invariant defect `Delta_N`.

## 9. External and internal boundary

The proof uses finite-dimensional Hilbert--Schmidt duality, weighted operator shifts, and
semi-Fredholm reconstruction. Those ingredients are classical. Operator-weighted shifts are treated,
for example, by Bourhim, *Local spectra of operator weighted shifts*, arXiv:math/0304045. Coherent
presentations and syzygies are covered by the polygraphic literature cited in ULF-CRGM-1.

The internal corpus previously contained:

- one-step conservative kernel birth;
- finite collective repair thresholds;
- generic finite-to-cofinal nonclosed-range examples;
- compact--cofinal fusion classification;
- common-kernel packet information isometry.

It did not contain `(OP.10)`, the sharp inequality `(OP.13)`, its unitary equality classification,
or the exact hidden-lineage/minimal-compact-rank law for operator certificates. These are the new
unconditional deltas.

## 10. Exact scope and next gate

The fibre is finite-dimensional and certificates are invertible and uniformly bounded. The theorem
does not construct certificates from arithmetic, treat branching/higher syzygies, classify closed
range in the general nonstationary case, derive positivity, or imply RH.

The next gate is a source-normal branching certificate complex whose first differential is `G` and
whose higher critical-branching differential is generated by the born lineage packet. A valid
construction must reproduce `(OP.10)` on every chain and make the higher conservation law a
consequence, not an added axiom.

## 11. Lean status

No Lean was written or built in this research phase. The proof is dependency-closed on paper and is
eligible for later formalization. Read-only audit found finite-dimensional matrix, direct-sum,
conservative-repair, compact-fusion, and shift infrastructure, but no existing declaration proving
this packet fusion or equality classification.

## Log

- 2026-08-12 -- operator prefix transport and dual packets constructed.
- 2026-08-12 -- exact fusion and sharp unitary-gauge equality theorem proved.
- 2026-08-12 -- cofinal hidden-lineage and minimal compact-repair rank laws proved.
- 2026-08-12 -- hostile audit retained mechanism synthesis without external novelty claim.
