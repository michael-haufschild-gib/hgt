# Finite-reporter admission, hyperbolic reduction, and composition law

- **ID:** `cmr-finite-reporter-admission-hyperbolic-composition`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CHU TRANSITION LAW]`
  `[SERIAL COMPOSITION] [PRIME-PORT INSTANTIATION] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Parent field:**
  `../../1-in-progress/constraint-motive-relativity/polarized-constraint-duality-geometry.md`.
- **Corpus parent:** `prime-port-algebraic-continuous-separation-law.md`.
- **External categorical parents:** Shulman, *The 2-Chu-Dialectica construction and the
  polycategory of multivariable adjunctions*, arXiv:1806.06082; Kawase, *Double categories of
  profunctors*, arXiv:2504.11099v4.
- **Statement:** A finite algebraic reporter port survives a completion exactly through its
  continuous subspace. Algebraic and completed hyperbolic reductions are related by a Chu mate;
  the lost reporters form a perfect hyperbolic pair, and losses through serial completions carry a
  canonical exact filtration.

## 1. Setup

Let `k=R` or `C`. Let `j:X_0->X` be a linear map with dense image in a Hausdorff locally convex
space `X`. Let

\[
 L\subset X_0^\vee
\tag{FR.1}
\]

be a finite-dimensional space of algebraic reporters, and define the algebraic constraint

\[
 I=L^\perp
 =\{x\in X_0:\lambda(x)=0\text{ for every }\lambda\in L\}.
\tag{FR.2}
\]

Define the admitted reporter subspace

\[
 L_X=\{\lambda\in L:\lambda=\widetilde\lambda\circ j
 \text{ for some continuous }\widetilde\lambda\in X'\}.
\tag{FR.3}
\]

The continuous extension is unique by density of `j(X_0)`.

## 2. Finite-reporter admission theorem

### Theorem 2.1

The completed constraint and quotient are

\[
 \boxed{
 \overline{j(I)}
 =\bigcap_{\lambda\in L_X}\ker\widetilde\lambda,}
\tag{FR.4}
\]

\[
 \boxed{
 X/\overline{j(I)}\cong L_X^\vee,}
\tag{FR.5}
\]

and restriction gives the typed continuous-annihilator isomorphism

\[
 \boxed{
 \operatorname{res}_j:
 \overline{j(I)}^\perp_X\xrightarrow{\sim}L_X,
 \qquad\phi\longmapsto\phi\circ j.}
\tag{FR.6}
\]

Algebraically,

\[
 X_0/I\cong L^\vee.
\tag{FR.7}
\]

Under these identifications, the primal comparison and contravariant reporter comparison are

\[
 \rho_X:L^\vee\longrightarrow L_X^\vee,
 \qquad \rho_X(\xi)=\xi|_{L_X},
\tag{FR.8}
\]

\[
 \iota_X:L_X\hookrightarrow L.
\tag{FR.9}
\]

They obey the Chu compatibility equation

\[
 \langle\rho_X(\xi),\lambda\rangle
 =\langle\xi,\iota_X(\lambda)\rangle.
\tag{FR.10}
\]

Their exact loss pair is

\[
 \ker\rho_X\cong(L/L_X)^\vee,
 \qquad
 \operatorname{coker}\iota_X\cong L/L_X.
\tag{FR.11}
\]

For a vector space `V`, write `H(V)=V direct-sum V^vee` with symmetric hyperbolic form and
alternating cotangent form

\[
 h((x,\alpha),(y,\beta))=\alpha(y)+\beta(x),
 \qquad
 \omega((x,\alpha),(y,\beta))=\alpha(y)-\beta(x).
\tag{FR.11a}
\]

Define the algebraic and continuous cotangent doubles

\[
 H_{\rm alg}(X_0)=X_0\oplus X_0^\vee,
 \qquad H_c(X)=X\oplus X',
\]

with alternating evaluation form `(FR.11a)`. Regard `I` and `N=closure(j(I))` as subspaces of
their primal summands. Direct calculation gives

\[
 I^\omega=X_0\oplus I^\perp,
 \qquad I^\omega/I\cong(X_0/I)\oplus I^\perp,
\]

\[
 N^\omega=X\oplus N^\perp_X,
 \qquad N^\omega/N\cong(X/N)\oplus N^\perp_X.
\]

Hence the algebraic and continuous hyperbolic reductions are

\[
 \operatorname{Red}_0(I)\cong
 L^\vee\oplus L=\mathbb H(L^\vee),
\tag{FR.12}
\]

\[
 \operatorname{Red}_X(\overline I)\cong
 L_X^\vee\oplus L_X=\mathbb H(L_X^\vee),
\tag{FR.13}
\]

and the loss is the perfect hyperbolic pair

\[
 \boxed{
 \mathfrak K_X\cong
 (L/L_X)^\vee\oplus(L/L_X)
 =\mathbb H((L/L_X)^\vee).}
\tag{FR.14}
\]

This is the loss pair of the contravariant Chu mate, not the kernel of one covariant map between
the two doubles. Explicitly, for
`xi in ker(rho_X)=(L_X)^perp subset L^vee` and `[lambda] in L/L_X`,

\[
 \langle\xi,[\lambda]\rangle=\xi(\lambda)
\tag{FR.14a}
\]

is well-defined and perfect.

The transition is invertible exactly when `L_X=L`, meaning every algebraic reporter in the marked
port is admitted continuously.

## 3. Proof

Every admitted extension `tilde(lambda)` vanishes on `j(I)`, hence on its closure. This gives the
inclusion from left to right in `(FR.4)`.

Suppose `x` does not lie in `closure(j(I))`. Hahn--Banach separation gives `phi in X'` that
vanishes on `closure(j(I))` but not on `x`. Its pullback `phi after j` vanishes on `I`. Because
`I=L^perp` and `L` is finite-dimensional, the algebraic double-annihilator identity gives

\[
 I^\perp=L.
\tag{FR.15}
\]

Thus `phi after j` lies in `L_X`, and `x` does not lie in the intersection on the right of
`(FR.4)`. This proves equality.

Evaluation defines

\[
 E_X:X\longrightarrow L_X^\vee,
 \qquad E_X(x)(\lambda)=\widetilde\lambda(x).
\tag{FR.16}
\]

Its kernel is `(FR.4)`. It is surjective: if its range were proper, a nonzero element of
`(L_X^vee)^vee=L_X` would annihilate the range, hence its continuous extension would vanish on all
of `X`, contradiction. The first isomorphism theorem gives the algebraic map in `(FR.5)`. Equip
`L_X^vee` with its unique finite-dimensional Hausdorff vector-space topology. Choose a
finite-dimensional linear section `s:L_X^vee->X` of `E_X`. It is continuous, so its composite
with the quotient map is a continuous inverse; `(FR.5)` is a topological linear isomorphism.

Restriction from `X'` to `X_0^vee` maps `closure(j(I))^perp_X` into `L_X` by `(FR.4)`. It is
injective by density of `j(X_0)` and surjective by the definition of `L_X`, proving `(FR.6)`.

The algebraic evaluation map `X_0->L^vee` is surjective by the same finite-dimensional transpose
argument and has kernel `I`, proving `(FR.7)`. The natural map from `(FR.7)` to `(FR.5)` is
restriction `(FR.8)`, whose transpose is inclusion `(FR.9)`; `(FR.10)` follows by evaluation.

The standard exact sequence

\[
 0\longrightarrow L_X\longrightarrow L\longrightarrow L/L_X\longrightarrow0
\tag{FR.17}
\]

dualizes exactly in finite dimension to

\[
 0\longrightarrow(L/L_X)^\vee
 \longrightarrow L^\vee\longrightarrow L_X^\vee\longrightarrow0.
\tag{FR.18}
\]

This proves `(FR.11)`. Hyperbolic cotangent reduction by a subspace `I` gives
`H(X_0/I)` algebraically and `H(X/closure I)` continuously. Substituting `(FR.5)` and `(FR.7)`
gives `(FR.12)--(FR.14)`.

## 4. Serial doctrine-composition law

Consider two serial dense doctrine changes whose admitted reporter spaces form a flag

\[
 L_2\subseteq L_1\subseteq L_0.
\tag{FR.19}
\]

The primal maps are restrictions

\[
 L_0^\vee\longrightarrow L_1^\vee\longrightarrow L_2^\vee,
\]

and the reporter maps are the reverse inclusions. The total and stepwise reporter losses fit into

\[
 0\longrightarrow L_1/L_2
 \longrightarrow L_0/L_2
 \longrightarrow L_0/L_1
 \longrightarrow0,
\tag{FR.20}
\]

while the primal losses fit into the dual exact sequence

\[
 0\longrightarrow(L_0/L_1)^\vee
 \longrightarrow(L_0/L_2)^\vee
 \longrightarrow(L_1/L_2)^\vee
 \longrightarrow0.
\tag{FR.21}
\]

More precisely, inside

\[
 \mathfrak K_{02}=(L_0/L_2)^\vee\oplus(L_0/L_2),
\]

the natural injections define

\[
 \mathfrak M=(L_0/L_1)^\vee\oplus(L_1/L_2).
\tag{FR.21a}
\]

The two summands pair trivially because every functional from `(L_0/L_1)^vee` annihilates
`L_1/L_2`. Their total dimension is half that of `K_02`, so `M` is a canonical Lagrangian. The
ambient pairing identifies `K_02/M` with
`M^vee=(L_0/L_1) direct-sum (L_1/L_2)^vee`. This filtration need not have a canonical
direct-sum splitting. In particular,

\[
 \dim(L_0/L_2)
 =\dim(L_0/L_1)+\dim(L_1/L_2).
\tag{FR.22}
\]

This is an exact composition law for doctrine transitions. It replaces the unsupported claim that
separate losses add as one scalar curvature.

## 5. Literal prime-port instantiation

Let

\[
 X_0=c_{00}(\mathcal P),
 \qquad \varepsilon(x)=\sum_px_p,
 \qquad L=\mathbb C\varepsilon,
 \qquad I=\ker\varepsilon.
\tag{FR.23}
\]

For `X=ell^1(P)`, augmentation extends continuously, so

\[
 L_X=L,
 \qquad\operatorname{Red}_{\ell^1}\cong\mathbb H(\mathbb C),
 \qquad\mathfrak K_{\ell^1}=0.
\tag{FR.24}
\]

Moreover `closure_{ell^1}(I)=ker epsilon`. Indeed, for `x in ker epsilon`, truncate on a finite
set `F` and choose a fresh prime `q_F`; then
`x_F-(sum_{p in F}x_p)e_{q_F}` lies in `I`, and its distance to `x` is at most twice the omitted
`ell^1` tail.

For `X=ell^2(P)`, augmentation is not continuous and `I` is dense. Hence

\[
 L_X=0,
 \qquad\operatorname{Red}_{\ell^2}=0,
 \qquad\mathfrak K_{\ell^2}\cong\mathbb H(\mathbb C).
\tag{FR.25}
\]

For density, given finitely supported `x`, choose `N` fresh primes `q_1,...,q_N` and set

\[
 y_N=x-\frac{\varepsilon(x)}N\sum_{j=1}^Ne_{q_j}\in I.
\]

Then `norm(y_N-x)_2=|epsilon(x)|/sqrt(N)->0`; finitely supported vectors are dense in `ell^2`.

The comparison is not a failure of completion to commute with quotient. The quotient seminorm
induced from `ell^2` on `X_0/I` is already zero, and its separated completion is zero. The theorem
compares the discrete algebraic Chu object with the continuous Hausdorff Chu object.

## 6. Source-dagger prediction

Suppose a marked Cartier/Bockstein line has reporter leg represented by `lambda in L`, and suppose
its completed comparison is exactly the Chu reduction of this theorem. Then that reporter leg
survives as a continuous scalar reporter only if `lambda in L_X`. Therefore:

> Any completed source-dagger realization claiming to retain a specific algebraic reporter must
> exhibit its admission in `L_X`, or replace functional observation by an explicitly
> relation-valued doctrine.

For prime augmentation, `ell^1` admits the port and `ell^2` erases it before it can serve as a
continuous scalar Stokes reporter. Individual prime coordinate reporters remain continuous in
`ell^2`; the erased datum is specifically the cofinal codiagonal augmentation.

This is a topology/admission prediction, not source null-homology and not RH.

## 7. Categorical meaning

The pair `(rho_X,iota_X)` is a strict Chu map: law variables move forward, reporters move
contravariantly, and evaluation is preserved by `(FR.10)`. These results motivate a candidate
doctrine-indexed relational double-Chu virtual equipment for heterogeneous doctrines:

- objects carry a native law sort, reporter sort, and evaluation;
- horizontal proarrows carry constitutive relations;
- paired transitions carry forward law and backward reporter correspondences;
- multicells record evaluation compatibility;
- horizontal composition is used only when represented/admitted.

This card does not construct that indexed equipment. Shulman's Chu construction and Kawase's
profunctor equipment are separate established parents; combining them with the heterogeneous
fibres is a Stage-1 problem. Virtuality would matter because
closed linear relations are not closed under unqualified relational composition. One must use all
relations and make closure a separate noninvertible modality, declare a composition-stable class,
or retain an unrepresented multicell. No closed composite is fabricated.

## 8. Falsifiers and predictions

1. Retained Hausdorff reduction rank is exactly `dim L_X`; doctrine loss rank is
   `dim(L/L_X)`.
2. A claimed continuous realization retaining more reporters than `L_X` is impossible.
3. Serial loss has the exact filtration `(FR.20)--(FR.21)`; any claimed canonical direct-sum
   splitting requires extra source structure.
4. Path dependence among doctrine changes can only be called holonomy after two represented
   composites and a comparison multicell are constructed.
5. Reporter admission is port-specific: erasure of augmentation does not imply erasure of local
   prime coordinates.

## 9. No-go closure

- **Failed conjecture:** one global cotangent dual transports unchanged across algebraic and
  continuous doctrines.
- **Exact killing mechanism:** only `L_X` extends; the quotient `L/L_X` and its dual are erased as
  a perfect hyperbolic pair.
- **Strongest positive survivor:** the Chu mate `(rho_X,iota_X)` and serial exact loss filtration
  give a coordinate-free, composable doctrine-transition law.
- **Status:** dependency-closed paper proof; no Lean written or built.

## Log

- 2026-08-09 — proved finite-reporter admission and exact hyperbolic loss classification.
- 2026-08-09 — proved serial doctrine-loss composition law.
- 2026-08-09 — instantiated on prime augmentation and separated categorical infrastructure from
  source dynamics.
