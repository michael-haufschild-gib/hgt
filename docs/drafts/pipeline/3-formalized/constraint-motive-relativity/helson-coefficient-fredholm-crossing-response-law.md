# Helson coefficient-faithful Fredholm crossing response law

- **ID:** `cmr-helson-coefficient-fredholm-crossing-response`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / GLOBAL SPECTRAL RECEIVER
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [NOT RH]`
  `[PORT NOT SOURCE-SELECTED] [LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:** `helson-coefficient-fredholm-crossing-response-law-formalized.md`
  (same directory).
- **Field successor:**
  `../../1-in-progress/constraint-motive-relativity/determinantal-constraint-holography-and-singular-reporter-correspondence-conjecture.md`.
- **Rank-law companion:**
  `valuation-coframe-operation-defect-rank-and-determinant-line-law.md`.

## 1. Result in one sentence

A divisor-weighted coefficient stream has a coefficient-faithful trace-class Helson realization
whose simple Fredholm walls carry exact divisor-convolution response covectors; this constructs a
genuine scalar spectral receiver, but not the source operation or threshold selecting that wall.

## 2. Helson realization

Let

\[
 d(n):=\#\{(j,k)\in\mathbb N^2:jk=n\}
\]

be the number of ordered factor pairs; numerically this equals the ordinary divisor function.
Define

\[
 \ell^1_d:=\left\{a=(a_n)_{n\ge1}:\|a\|_{1,d}
 =\sum_{n\ge1}d(n)|a_n|<\infty\right\}.
\tag{HFR.1}
\]

For `a in ell^1_d`, define on `ell^2(N)`

\[
 K_a(j,k):=a_{jk}.
\tag{HFR.2}
\]

### Theorem 2.1 — trace class and coefficient faithfulness

For every `a in ell^1_d`:

1. `K_a` is trace class and

   \[
   \|K_a\|_1\le\sum_{n\ge1}d(n)|a_n|;
   \tag{HFR.3}
   \]
2. the realization is linear and coefficient faithful:

   \[
   a_n=\langle e_1,K_ae_n\rangle;
   \tag{HFR.4}
   \]
3. if `a` is real, `K_a` is self-adjoint.

#### Proof

Let `E_{jk}=|e_j><e_k|`. It is rank one with trace norm `1`. The nuclear series

\[
 K_a=\sum_{j,k\ge1}a_{jk}E_{jk}
\tag{HFR.5}
\]

converges absolutely in trace norm because

\[
 \sum_{j,k}|a_{jk}|=\sum_nd(n)|a_n|<\infty.
\]

Its matrix entries are `(HFR.2)` and the triangle inequality gives `(HFR.3)`. Taking the `(1,n)`
entry proves `(HFR.4)`. If `a_n` is real, then `K_a(k,j)=a_{kj}=a_{jk}=overline{K_a(j,k)}`. QED.

## 3. Divisor-convolution response

For `u in ell^2(N)`, define

\[
 W_u(n):=\sum_{jk=n}\overline{u_j}u_k.
\tag{HFR.6}
\]

### Lemma 3.1

For every `n`, `|W_u(n)|<=||u||_2^2`.

#### Proof

Using the divisor set and Cauchy--Schwarz,

\[
 |W_u(n)|
 \le\left(\sum_{j\mid n}|u_j|^2\right)^{1/2}
     \left(\sum_{j\mid n}|u_{n/j}|^2\right)^{1/2}
 \le\|u\|_2^2.
\]

The substitution `j -> n/j` identifies the two finite sums. QED.

### Theorem 3.2 — simple eigenvalue response

Let `a,h in ell^1_d` be real. Suppose `mu` is a simple isolated eigenvalue of the compact
self-adjoint operator `K_a`, with normalized real eigenvector `u`. For the affine family
`K(t)=K_a+tK_h`, the unique local eigenvalue branch `mu(t)` through `mu` satisfies

\[
 \dot\mu(0)=\langle u,K_hu\rangle
 =\sum_{n\ge1}h_nW_u(n).
\tag{HFR.7}
\]

The series is absolutely convergent.

#### Proof

Trace-norm convergence implies operator-norm differentiability. Choose a circle enclosing `mu` and
no other point of `sigma(K_a)`. For sufficiently small `t`, the Riesz projection

\[
 P(t)=\frac{1}{2\pi i}\int_\gamma(z-K(t))^{-1}\,dz
\]

is `C^1` and rank one. Then `u(t)=P(t)u/||P(t)u||` is a `C^1` normalized eigenvector branch, and
the corresponding eigenvalue branch is `C^1`. Differentiate
`K(t)u(t)=mu(t)u(t)` at zero and pair with `u`. Self-adjointness cancels the two terms containing
`dot u`, yielding `dot mu(0)=<u,K_hu>`. Expanding the absolutely trace-norm convergent series gives

\[
 \langle u,K_hu\rangle
 =\sum_{j,k}h_{jk}\overline{u_j}u_k
 =\sum_nh_nW_u(n).
\]

Absolute convergence follows from Lemma 3.1 and `sum_n|h_n|<=sum_nd(n)|h_n|`. QED.

The covector `W_u` is not fitted from `h`: it is fixed by the independently chosen simple
eigenline of `K_a`.

## 4. Fredholm wall and crossing orientation

Throughout this section let `a,h in ell^1_d` be real, fix `tau in R setminus {0}`, and put

\[
 A_a:=\tau I-K_a,
 \qquad
 \Delta_\tau(a):=\det_F(I-\tau^{-1}K_a).
\tag{HFR.8}
\]

The Fredholm determinant exists because `K_a` is trace class.

### Theorem 4.1

1. `A_a` is Fredholm of index zero.
2. `Delta_tau(a)=0` iff `tau` is an eigenvalue of `K_a`.
3. If `tau` is simple with normalized eigenvector `u`, then the crossing form of
   `A(t)=tau I-K_{a+th}` on its one-dimensional kernel is

   \[
   \Gamma_{a,\tau}(h)
   =\langle u,\dot A(0)u\rangle
   =-\sum_nh_nW_u(n).
   \tag{HFR.9}
   \]
4. Under the simple-eigenvalue hypothesis of item 3, the map

   \[
   \Gamma_{a,\tau}:\ell^1_d(\mathbb R)\longrightarrow\mathbb R,
   \qquad h\longmapsto-\sum_nh_nW_u(n),
   \tag{HFR.9a}
   \]

   is a continuous nonzero covector. Hence, near `a`, the simple-wall locus is a `C^1`
   codimension-one hypersurface cooriented by `Gamma_(a,tau)`. A path with velocity `h` is
   transverse exactly when `Gamma_(a,tau)(h)!=0`, and its oriented crossing sign is
   `sign Gamma_(a,tau)(h)`.

#### Proof

`A_a` is an invertible scalar operator plus a compact operator, hence Fredholm of index zero.
The basic trace-class Fredholm determinant criterion gives item 2. Since
`dot A(0)=-K_h`, item 3 follows from Theorem 3.2. Lemma 3.1 gives

\[
 |\Gamma_{a,\tau}(h)|\le\sum_n|h_n|\le\|h\|_{1,d},
\]

so the covector is continuous. Let `m=min{j:u_j!=0}`. For `h` supported at `m^2`,
`W_u(m^2)=|u_m|^2>0`, because every other factorization of `m^2` contains an index below `m`.
Thus the covector is nonzero. On a neighborhood `U subset ell^1_d(R)` of `a` for which `gamma`
remains in the resolvent set, define

\[
 P(b)=\frac{1}{2\pi i}\int_\gamma(z-K_b)^{-1}\,dz,
 \qquad
 \mu(b)=\operatorname{tr}(K_bP(b)).
\]

Since `b -> K_b` is continuous linear into trace class and resolvent inversion is analytic, `P`
and `mu` are `C^1`; `rank P(b)=1`, and

\[
 D\mu_a[h]=\langle u,K_hu\rangle.
\]

Hence `D(tau-mu)_a=Gamma_(a,tau)!=0`, so the Banach implicit-function theorem gives the
hypersurface claim. Its derivative is `(HFR.9a)`, which gives transversality and the oriented path
sign. QED.

This is an exact spectral law event. It does not choose `tau`, the base stream `a`, or the
eigenbranch from arithmetic data.

## 5. Normalized Mellin coefficients

Let `sigma` be real and define

\[
 X_\sigma:=\left\{x:\sum_nd(n)|x_n|n^{-\sigma}<\infty\right\},
 \qquad
 \|x\|_{X_\sigma}:=\sum_nd(n)|x_n|n^{-\sigma},
 \qquad Z(x):=\sum_nx_nn^{-\sigma}.
\tag{HFR.10a}
\]

`X_sigma` is a real Banach space, isometrically identified with `ell^1_d` by
`x -> (x_n n^(-sigma))_n`. Moreover

\[
 |Z(x)|\le\|x\|_{X_\sigma},
\]

so `Z` is continuous and `{x:Z(x)>0}` is open.

Let a nonnegative stream `c in X_sigma` satisfy

\[
 Z(c):=\sum_nc_nn^{-\sigma}>0,
 \qquad
 p_n(c):=Z(c)^{-1}c_nn^{-\sigma},
 \qquad
 p(c)\in\ell^1_d.
\tag{HFR.10}
\]

For an admitted real intervention `h in X_sigma`, put `H(h)=Z(h)`. Then `H(h)` converges absolutely
and the corresponding weighted derivative belongs to `ell^1_d`. Differentiation occurs in the
open signed ambient set `{x in X_sigma:Z(x)>0}`; cone-preserving source paths may be restricted
separately. Then

\[
 Dp_c[h]_n
 =\frac{n^{-\sigma}}{Z(c)}
  \left(h_n-\frac{H(h)}{Z(c)}c_n\right).
\tag{HFR.11}
\]

### Corollary 5.1 — projective response

Suppose `tau` is a simple eigenvalue of `K_{p(c)}` with normalized eigenvector `u`. Define the
wall gap `Omega(c)=tau-mu(c)` for its local eigenvalue branch. Then

\[
 D\Omega_c[h]
 =-\sum_nDp_c[h]_nW_u(n).
\tag{HFR.12}
\]

Moreover `p(lambda c)=p(c)` for every `lambda>0`; hence radial scaling is in the kernel of
`Dp_c` and of `(HFR.12)`.

#### Proof

Differentiate the quotient in `(HFR.10)` to obtain `(HFR.11)`, and note explicitly that

\[
 Dp_c[h]
 =\frac{(h_nn^{-\sigma})_n}{Z(c)}
  -\frac{Z(h)}{Z(c)}p(c)\in\ell^1_d.
\]

Apply `(HFR.7)` to the induced
coefficient intervention and use `Omega=tau-mu`. Projective invariance is immediate from numerator
and denominator scaling by the same `lambda`. QED.

The source intervention and the eigenvector weight remain distinct inputs. Equation `(HFR.12)` is
a represented coefficient-to-spectral response, not a declaration that every source current is a
Fredholm current.

## 6. Exact limitations and countermodels

1. **Coefficient positivity does not imply operator positivity.** For example choose
   `a_1=0,a_2=1` and all other coefficients zero. On `span(e_1,e_2)`, `K_a` contains the block
   `[[0,1],[1,0]]`, with eigenvalues `1,-1`.
2. **A threshold can be fitted.** For any nonzero compact self-adjoint `K_a`, choosing `tau` equal
   to one of its eigenvalues manufactures a wall. Source selection of `tau` is additional data.
3. **The eigenbranch can be fitted.** Distinct simple eigenlines give distinct `W_u`. A valid
   arithmetic realization must specify the line before the tested intervention.
4. **Strong summability is real.** Coefficient faithfulness alone does not imply `(HFR.1)`. The
   theorem makes no claim for the divergent half-density prime stream without a different
   completion or regularization.
5. **Scalar receiver is not raw exactifier.** For two or more independently coframed prime
   classes, the companion rank law forbids a single scalar crossing form from being the full
   exactification anomaly.
6. **No local Stokes comparison is constructed.** Equality between `(HFR.9)` and a Gamma--Stokes
   boundary response remains an open field-level compatibility theorem.

## 7. Route-independent consequence

This theorem closes one earlier ambiguity in the field programme: exact coefficient intervention
can produce a genuine spectral wall response before any Xi specialization. The remaining problem
is not “invent some Fredholm response.” It is:

1. derive the base operator, threshold, and simple eigenline from the same pre-zero source law;
2. lift the scalar response to the finite-cutoff coframe determinant required by the rank theorem;
3. identify its determinant orientation with an independently constructed local Gamma--Stokes
   orientation line.

That target simultaneously adds source selection, finite-cutoff determinant data, and an
independent local comparison absent from this scalar theorem; no implication ordering among named
routes is claimed.

## 8. Literature boundary

Multiplicative Hankel/Helson operators, their spectral theory, trace-class Fredholm determinants,
simple-eigenvalue perturbation, and crossing forms are parent mathematics. Relevant parents
include:

- Perfekt--Pushnitski, *On Helson matrices: moment problems, non-negativity, boundedness, and finite
  rank*,
  <https://arxiv.org/abs/1611.03772>;
- Brevig et al., *The multiplicative Hilbert matrix*,
  <https://arxiv.org/abs/1411.7294>;
- Chavan--Sahu--Sinha, *Helson matrices induced by measures*,
  <https://arxiv.org/abs/2407.04124>;
- Soares, *Hecke triangle groups, transfer operators and Hausdorff dimension* (twisted Selberg
  zeta Fredholm determinants),
  <https://arxiv.org/abs/2005.11808>;
- Gesztesy et al., *The index formula and the spectral shift function for relatively trace class
  perturbations*,
  <https://arxiv.org/abs/1004.1582>.

Local comparison parents include Fischler--Rivoal on arithmetic `E`-operators
(<https://arxiv.org/abs/1406.5995>), Jiang--Luo on local Gamma/Hankel transforms
(<https://arxiv.org/abs/2108.03565>), and Abbes--Saito on epsilon factors
(<https://arxiv.org/abs/0809.0180>). None of the cited results supplies the source-selected
global-to-local determinant compatibility conjectured by the field card.

## 9. Scope and formalization note

This is a dependency-closed paper theorem and a classical functional-analytic bridge. It makes no
novelty claim, no RH claim, and no claim that a Helson operator is the unique spectral receiver.

Formalized unconditionally in Lean 4; see the companion certificate. The trace-class limit and the
whole of `(HFR.2)--(HFR.12)` are formalized directly in the infinite-dimensional setting, without
passing through finite-rank truncations. The Fredholm determinant itself is not constructed: the
wall condition `Delta_tau(a)=0` is formalized in its Fredholm-alternative form.

## Gates

- [x] trace-class realization proved
- [x] coefficient faithfulness proved
- [x] divisor-response bound proved
- [x] simple eigenvalue derivative proved
- [x] Fredholm wall and crossing orientation proved
- [x] normalized projective response proved
- [x] positivity, threshold, eigenline, summability, and rank-one limitations stated
- [x] local Stokes compatibility left explicitly open
- [x] Lean formalization completed unconditionally

## Log

- 2026-08-09 — extracted after broad Helson, transfer-operator, arithmetic Stokes, and Fredholm
  literature audit. Accepted as global spectral receiver; rejected as standalone source selector.
- 2026-08-12 — formalized unconditionally in Lean 4 and promoted to stage 3.
