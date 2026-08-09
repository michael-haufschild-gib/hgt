# Constitutive-jet factorization and withheld-observer prediction law

- **ID:** `cfr-constitutive-jet-factorization`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / ROUTE-INDEPENDENT FIELD GATE
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LITERAL EULER-SHELL COUNTERMODEL] [NOT RH] [FORMALIZED IN LEAN]`
- **Formalized companion:** `constitutive-jet-factorization-and-withheld-observer-prediction-law-formalized.md`
- **Statement:** A withheld infinitesimal observer is determined by calibrated observers exactly when its response kills their common vertical tangent kernel; continuous cofinal prediction requires a uniform response inequality, not merely finite-level factorization.

## Goal

Turn “predict a withheld route” into a coordinate-free theorem rather than a slogan. The theorem
must distinguish four cases:

1. no constitutive realization of the withheld observer is defined;
2. a calibrated-invisible source intervention changes it;
3. a factor exists but is not source-canonical;
4. a source-natural factor exists and gives an actual prediction.

Only the fourth is a CFR field law.

## 1. Linearized constitutive setup

Let `k` be a field. At a source point `s`, let `V` be the finite-dimensional tangent space of
declared source interventions. Let

\[
 A_i:V\longrightarrow W_i,\qquad i=1,\ldots,r,
\]

be calibrated observer differentials and put

\[
 A=(A_1,\ldots,A_r):V\longrightarrow W:=\bigoplus_i W_i.
\tag{CJ.1}
\]

Let `B:V->Z` be the differential of a withheld observer, constructed on the same source
interventions before looking for a relation to `A`. Put

\[
 K_A=\ker A=\bigcap_i\ker A_i.
\tag{CJ.2}
\]

This is the vertical tangent space invisible to all calibrated observers.

## 2. Exact factorization theorem

### Theorem 2.1 — withheld response criterion

The following are equivalent.

1. `B` is constant on every fibre of `A`.
2. `K_A subset ker B`.
3. There is a unique linear map

   \[
    \overline B:\operatorname{im}A\longrightarrow Z
   \]

   such that `B=bar B A`.
4. On algebraic duals,

   \[
    \operatorname{im}B^*\subseteq\operatorname{im}A^*.
   \tag{CJ.3}
   \]

If these conditions fail, there exists `h in V` with

\[
 A_i h=0\quad\text{for every }i,
 \qquad
 Bh\ne0.
\tag{CJ.4}
\]

Thus no rule depending only on calibrated first-order responses can predict the withheld response.

### Proof

If `B=bar B A`, then `A(v)=A(v')` implies `B(v)=B(v')`, and in particular
`ker A subset ker B`. Conversely, if `ker A subset ker B`, define

\[
 \overline B(Av)=Bv.
\]

If `Av=Av'`, then `v-v' in ker A subset ker B`, so this is well defined. It is linear, unique on
`im A`, and satisfies `B=bar B A`.

For a subspace `M subset V`, write

\[
 M^\circ=\{\varphi\in V^*: \varphi|_M=0\}.
\]

In finite dimension,

\[
 (\ker A)^\circ=\operatorname{im}A^*,
 \qquad
 (\ker B)^\circ=\operatorname{im}B^*.
\]

Therefore `ker A subset ker B` is equivalent, after taking annihilators and reversing inclusion,
to `(CJ.3)`. If the
kernel inclusion fails, choose `h in ker A\setminus ker B`; then `(CJ.4)` holds. `[PROVED HERE]`

### Corollary 2.2 — presentation covariance

Suppose a group `G` acts on `V,W,Z` and `A,B` are equivariant. When Theorem 2.1 holds, the canonical
factor `bar B:im A->Z` is equivariant.

### Proof

For `g in G` and `Av in im A`, equivariance gives

\[
 \overline B(gAv)=\overline B(A(gv))=B(gv)=gBv=g\overline B(Av).
\]

`[PROVED HERE]`

This is the minimal presentation-invariance law. Extending `bar B` from `im A` to all of `W` is
generally nonunique and is not part of the theorem.

## 3. Quantitative and cofinal form

Let `V,W,Z` now be Hilbert spaces and let `A,B` be bounded. A bounded factor
`bar B:closure(im A)->Z` satisfying `B=bar B A` exists if and only if there is `C<infinity` with

\[
 \|Bv\|\le C\|Av\|\qquad(v\in V).
\tag{CJ.5}
\]

When `im A` is closed and `ker A subset ker B`, the factor on `im A` is uniquely

\[
 \overline B_0=BA^\dagger|_{\operatorname{im}A},
\tag{CJ.6}
\]

where `A^dagger` is the Moore--Penrose inverse.

### Proof

A bounded factor immediately implies `(CJ.5)` with `C=||bar B||`. Conversely, the kernel argument
in the proof of Theorem 2.1 is dimension-free: `(CJ.5)` implies `ker A subset ker B`, so
`bar B(Av)=Bv` is well defined on `im A`. Inequality `(CJ.5)` makes this factor bounded, hence it
extends uniquely to `closure(im A)`.
If `im A` is closed, `A^dagger Av` is the orthogonal projection of `v` to `(ker A)^perp`; because
`B` kills `ker A`, `BA^dagger Av=Bv`. Thus `(CJ.6)` is the unique factor on `im A`. Its zero
extension `BA^dagger:W->Z` on `(im A)^perp` has minimal operator norm among bounded extensions of
that factor to all of `W`: any extension agrees with it on `im A`, while the zero extension adds no
orthogonal-domain contribution. `[PROVED HERE]`

### Countertheorem 3.1 — finite prediction need not survive aperture

Let `V=W=Z=ell^2(N)`, choose positive `lambda_n->0`, and put

\[
 A(x_n)=(\lambda_nx_n),\qquad B=I.
\]

Every finite coordinate restriction `A_N` is invertible, hence `B_N` factors through `A_N`.
Globally `ker A=0`, so algebraic factorization still holds, but no bounded factor exists.

### Proof

The only factor on `im A` sends `A e_n=lambda_n e_n` to `e_n`, so its norm is at least
`lambda_n^-1` for every `n`. This diverges. Equivalently, `(CJ.5)` fails on `v=e_n`.
`[PROVED HERE]`

Thus cofinal prediction requires a uniform constitutive response bound. Finite factorization and
pointwise injectivity do not suffice.

## 4. Literal Euler-shell vertical mode

Fix `m>=12` and `sigma>1`. Put

\[
 V=c_{00}(\mathbb N_{\ge1}),\qquad W=\mathbb C^{\mathcal P},\qquad Z_0=\mathbb C.
\]

The maps below are algebraic maps on finite-support coefficient interventions; no completion of
`W` is declared. Let

\[
 a_m(1)=0,\qquad
 a_m(n)=\mathbf1_{\max_p v_p(n)=m}\quad(n\ge2),
 \qquad
 Z=\sum_n a_m(n)n^{-\sigma},
\]

and let `P` be the normalized atomic measure on `log n` with mass `Z^-1 a_m(n)n^-sigma`. The
normalization and first logarithmic moment are finite because

\[
 0<Z\le\sum_{n\ge1}n^{-\sigma}<\infty,
 \qquad
 \sum_n a_m(n)(\log n)n^{-\sigma}
 \le\sum_{n\ge1}(\log n)n^{-\sigma}<\infty.
\tag{CJ.6a}
\]

The pure-prime skeleton reporter on coefficient interventions is

\[
 A(h)=(h_{p^m})_p.
\tag{CJ.7}
\]

The normalized Mellin phase response at time `t` is

\[
 B_t(h)
 ={1\over Z}\left(
   \sum_n h_n n^{-\sigma-it}
   -\Bigl(\sum_n h_n n^{-\sigma}\Bigr)
      \int e^{-itx}\,dP(x)
  \right).
\tag{CJ.8}
\]

### Theorem 4.1 — prime-skeleton calibration does not predict full-shell response

There is a finite-support intervention `h` such that `A(h)=0` but `B_t(h) ne 0` for some real
`t`. Consequently `(CJ.8)` does not factor through the pure-prime reporter `(CJ.7)`.

### Proof

Take the two mixed shell atoms

\[
 N_1=2^m3,
 \qquad
 N_2=2^m5.
\]

Both satisfy `max_p v_p(N_j)=m`, and neither is a prime power. Hence `A(e_(N_j))=0`. The mean
`mu=int x dP(x)` cannot equal both distinct numbers `log N_1` and `log N_2`; choose `N` among them
with `log N ne mu` and put `h=e_N`. The finite first moment in `(CJ.6a)` permits differentiation at
`t=0` by dominated convergence and gives

\[
 {d\over dt}\bigg|_{t=0}B_t(e_N)
 =-{iN^{-\sigma}\over Z}(\log N-\mu)\ne0.
\]

Therefore `B_t(e_N)` is nonzero for some `t`, proving the claim. `[PROVED HERE]`

This is not an RH statement. It says the literal four-axis prime skeleton is not a constitutive
generator for the full shell observer.

## 5. Formation gap versus observer defect

The theorem forces a typed hierarchy.

1. **Formation gap:** `B` is not defined on the same source intervention space. No kernel,
   curvature, or factorization statement is yet meaningful.
2. **Vertical mode:** `B` exists but `ker A` is not contained in `ker B`; `(CJ.4)` is an exact
   counter-intervention.
3. **Unstable factor:** finite factors exist but `(CJ.5)` fails cofinally.
4. **Constitutive prediction:** a source-derived, presentation-natural factor is constructed before
   the withheld formula and satisfies `(CJ.5)` on the declared completion.

Current Route-E and structural Stokes responses are in case 1 relative to the literal Euler-shell
card: no source-natural map from shell coefficient interventions to moving incidence/contact data
has been constructed. Calling that absence “curvature” would be theatre.

## 6. Field consequence

The four CFR directions are kinematic coordinates on a law space. They do not replace a
constitutive section from source interventions into that law space. At a source point, the first
field datum is its constitutive jet; route responses are its observer projections. A withheld
prediction is exactly a source-natural factorization of such jets, with the uniform estimate
`(CJ.5)` at cofinal level.

This statement is classical linear and functional analysis. Its role is foundational, not a
novelty claim: it makes the anti-theatre criterion exact and tells the research programme what must
be constructed next.

## Lean-return notes

- Finite theorem: kernels, ranges, dual annihilators, quotient factorization.
- Quantitative theorem: `B` factors continuously through `A` iff the response inequality holds.
- Diagonal countermodel: finite restrictions factor; global bounded factor fails.
- Euler-shell instantiation needs the existing shell-support and normalized-response files.
- No Lean file has been written or built.

## Gates

- [x] coordinate-free prediction criterion
- [x] presentation-equivariant factor
- [x] cofinal stability criterion
- [x] finite/global countermodel
- [x] literal HGT vertical-mode counterexample
- [x] explicit formation-gap distinction
- [ ] source-natural non-Mellin constitutive map
- [ ] withheld Route-E or Stokes prediction
- [ ] Lean formalization

## Log

- 2026-08-09 — extracted after the literal four-axis Euler-shell frame proved flat on its prime skeleton and failed to manufacture non-Mellin route structure.
