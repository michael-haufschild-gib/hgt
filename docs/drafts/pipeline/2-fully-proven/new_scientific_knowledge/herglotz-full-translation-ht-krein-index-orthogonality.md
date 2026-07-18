# Measure-universal Herglotz maximal HT and its Krein gauge chambers

- **ID:** `herglotz-full-translation-ht-krein-index-orthogonality`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) — `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; exact Herglotz positivity; full complex translation orbit
- **Statement:** For every positive Herglotz measure with infinite support, a comeager set of bounded
  positive reweightings has maximal full-complex-translation differential-algebraic freedom as germs
  at upper infinity.  This covers discrete, singular-continuous, and absolutely continuous spectra;
  no spacing or arithmetic hypothesis survives.  The finite-atomic rational gauge fibers over each
  such field have a compatible cubical chamber structure: their chambers are finite residue-sign
  patterns and the exact Krein index
  is their graph distance from the positive chamber.  The embedded differential-translation field,
  real structure, and generator class modulo `C(z)` remain fixed throughout.  Therefore every exact
  positivity selector is forced to carry a distinguished, rational-gauge-sensitive representative—
  realized, for example, by a signed residue, divisor, kernel, measure, Euler, or spectral marking—
  rather than only the unpointed HT field.

## Infinite-support Herglotz measure-cone theorem `[PROVED HERE]`

Let `mu` be a positive Borel measure on `R` with infinite closed support and

`integral_R (1+t^2)^(-1) dmu(t)<infinity`.                    (H0)

For `u in L^infinity(mu;R)`, define the regularized Herglotz transform

`m_u(z)=integral_R [1/(t-z)-t/(1+t^2)] exp(u(t)) dmu(t)`,      (H1)

for `z in C\R`.  Condition (H0) gives normal convergence on compact subsets: the bracket in (H1)
is `O((1+t^2)^(-1))` uniformly on such a compact.  The subtraction is real on `R`, so

`Im m_u(z)>0` for `Im z>0`,

and `m_u(conj z)=conj(m_u(z))`.

For a finite complex shift tuple `(h_1,...,h_m)`, all translates are holomorphic on every upper
half-plane `Im z>Y` with `Y>max_i(-Im h_i)`.  Say that the full translation family is
differentially algebraically independent at upper infinity if no nonzero differential polynomial
over `C(z)` in any finite tuple of distinct translates vanishes identically on such a common upper
half-plane.

There is a comeager set

`U_free(mu) subset L^infinity(mu;R)`

such that every `u in U_free(mu)` has a differentially algebraically independent full complex
translation family at upper infinity.

### 1. `L^infinity` real Cauchy-jet surjectivity

Fix distinct nodes `x_1,...,x_L` in the upper half-plane, all different from `i`, and a jet order
`r`.  For real `t`, put

`v_(p,0)(t)=1/(t-x_p)-t/(1+t^2)`,

`v_(p,ell)(t)=ell!/(t-x_p)^(ell+1)`, `1<=ell<=r`.             (H2)

For a fixed `u_0`, these functions are integrable against `exp(u_0) mu`.  Consider the bounded
real-linear map

`T_(u_0):L^infinity(mu;R)->C^(L(r+1))`,

`T_(u_0)(p)_(q,ell)=integral p(t) exp(u_0(t)) v_(q,ell)(t) dmu(t)`.  (H3)

This map is onto.  Indeed, if a real-linear functional with complex coefficients `c_(q,ell)`
annihilates its range, then testing against every bounded real `p` gives

`Re R(t)=0` for `mu`-almost every `t`,                        (H4)

where

`R(t)=sum_q c_(q,0)[1/(t-x_q)-t/(1+t^2)]`

`     +sum_(q,ell>=1)c_(q,ell) ell!/(t-x_q)^(ell+1)`.         (H5)

The rational function `R(t)+conj(R(conj t))` therefore vanishes on `supp(mu)`: if it were nonzero
at a support point, continuity would give a positive-measure neighborhood contradicting (H4).
The support is infinite, so the rational function vanishes identically.  At `x_q`, only the
principal part of `R` contributes because the conjugate poles lie in the lower half-plane and
`x_q!=i`.  Hence every `c_(q,ell)` is zero.  The real annihilator is trivial, and the finite-
dimensional target makes (H3) surjective. `QED`

### 2. Uncountable shifts by finite-dimensional transversality

Fix a finite support of `R_0` expanded differential monomials of jet order `r`, let `q` be the
largest degree of their polynomial coefficients in `z`, put

`K=R_0(q+1)`,

and fix `h^0 in Conf_m(C)`.  Choose `N`
distinct evaluation points `z_a` high enough that every `x_(a,i)=z_a+h_i^0` lies in the upper
half-plane, the full packet is pairwise distinct, and no point equals `i`.  These properties persist
on a relatively compact real neighborhood `U` of `h^0`.

For `X=C^(m(r+1))`, form the `N by K` matrix whose columns are indexed by a monomial `M_beta` and a
coefficient degree `0<=d<=q`, with `(a,(beta,d))` entry

`z_a^d M_beta(x_a)`.

Let `B subset X^N` be its rank-defect locus.  A projective coefficient vector is a nonzero tuple of
polynomials `c_beta(z)` of degree at most `q`.  For at most `q` evaluation indices `a` can every
`c_beta(z_a)` vanish: one nonzero coefficient polynomial has at most `q` roots.  At each remaining
index, `sum_beta c_beta(z_a)M_beta` is a nonzero polynomial in the row jet variables because the
`M_beta` are distinct monomials.  Hence the projective incidence variety has codimension at least

`N-q-(K-1)`,

and projection gives

`codim_C B>=N-q-K+1=N-q-R_0(q+1)+1`.                         (H6)

Choose `N>m+q+K-1`; every Whitney stratum of `B` then has real codimension greater than
`dim_R U=2m`.

Apply (H3) to the full `Nm` node packet at `h^0`.  Choose finitely many bounded real directions
`p_1,...,p_d` whose images span the jet space, and let `V` be their real span.  For

`Psi:V times U -> X^N`, `Psi(p,h)=jets of m_(u_0+p) at z_a+h_i`,

the derivative in the `V` direction is onto at `(0,h^0)`.  Surjectivity is open, so after shrinking
to small neighborhoods in `V` and `U`, `Psi` is a smooth real submersion.  Parametric
transversality gives a residual dense set of arbitrarily small `p` for which `Psi_p` is transverse
to every stratum of `B`.  The codimension inequality makes every transverse preimage empty.

Thus avoidance of one monomial support on one compact shift patch is dense near every `u_0`.
It is open because (H1) and all its jets depend continuously on the `L^infinity` parameter,
uniformly on compact upper-half-plane packets.

### 3. Baire completion and sharp boundary

Exhaust every `Conf_m(C)` by countably many compact patches and intersect over all `m`, jet orders,
and finite expanded-monomial supports.  The real Banach space `L^infinity(mu)` is Baire, so the
intersection is comeager.  Clearing rational denominators identifies support avoidance with
differential algebraic independence over `C(z)`, proving the theorem. `QED`

Infinite support is sharp for this mechanism.  If `mu` has finite support, every transform (H1) is
rational up to a constant and is differentially algebraic.  For infinite support, no atomicity,
absolute continuity, support spacing, or support arithmetic is used.

## Discrete-support meromorphic corollary `[PROVED HERE]`

Let `(lambda_j)` be pairwise distinct real numbers with `|lambda_j|->infinity`, and let
`epsilon_j>0` satisfy

`sum_j epsilon_j/(1+|lambda_j|)<infinity`.                    (H7)

For `mu=sum_j epsilon_j delta_(lambda_j)`, one has
`L^infinity(mu;R)=ell^infinity(R)`.  The regularized transform differs by a real constant from

`m_u(z)=sum_j epsilon_j exp(u_j)/(lambda_j-z)`.                (1)

Condition (H7) makes both series converge normally away from the discrete pole set.  Adding a
constant is an invertible base-field substitution, so the measure-cone theorem gives a comeager
`U_free subset ell^infinity(R)` for which `{m_u(z+h):h in C}` is differentially algebraically
independent over `C(z)` as a family of meromorphic functions.

Hence every infinite discrete real spectral skeleton supports maximal translation HT in its
positive mass cone, with no spacing, density, commensurability, or arithmetic hypothesis.

## Unit-residue canonical-product strengthening `[PROVED HERE]`

A separate order-one realization replaces variable positive masses by simple zeros of multiplicity
one and varies their locations.  Put

`phi(t)=(1/4)tanh(t)`,

`Lambda_j(theta)=j+1+phi(theta_j)`, `theta in ell^infinity(R)`,

and define the genus-one canonical product

`F_theta(z)=prod_(j>=0) (1-z/Lambda_j(theta)) exp(z/Lambda_j(theta))`.       (5)

Since `Lambda_j(theta)=j+1+O(1)` uniformly, the product converges normally and
is a real entire function of order one with simple real zeros `Lambda_j(theta)`.  Indeed, splitting
the canonical-product estimate at `j asymp |z|` gives `log M(r)=O(r log r)`, while the exponent of
convergence of the zeros is one.  Its negative
logarithmic derivative is

`M_theta(z)=-F_theta'(z)/F_theta(z)`

`          =sum_j [1/(Lambda_j(theta)-z)-1/Lambda_j(theta)]`.                (6)

Every summand differs from a positive real Cauchy atom by a real constant, so `M_theta` is Herglotz
on the upper half-plane and has the unit logarithmic residue attached to a simple zero.

There is a comeager subset `Theta_free subset ell^infinity(R)` for which

`{M_theta(z+h):h in C}`

is differentially algebraically independent over `C(z)`.

### Proof of the strengthened jet lemma

Only the jet-surjectivity input changes.  Variation of the pole location `Lambda` gives, at a node
`x`,

`partial_Lambda [1/(Lambda-x)-1/Lambda]`

`    =-1/(Lambda-x)^2+1/Lambda^2`,                             (7)

and for `ell>=1`,

`partial_Lambda D_z^ell [1/(Lambda-z)-1/Lambda]|_(z=x)`

`    =-(ell+1)!/(Lambda-x)^(ell+2)`.                           (8)

Suppose a real-linear functional annihilates the columns (7)--(8) at all
`Lambda_j(theta)`.  Adding its conjugate turns it into a rational function of the real variable
`Lambda`, with poles only at the conjugation-separated nodes, their conjugates, and possibly `0`.
It vanishes at the infinite sequence `Lambda_j(theta) -> infinity`, hence is identically zero.
Principal parts at each node first force every coefficient in (7)--(8) to vanish; the possible
`Lambda^(-2)` term at zero then vanishes as well.  Thus the real span is the full complex jet packet.

Because `phi'(theta_j)>0`, the derivative with respect to each selected coordinate `theta_j` is a
nonzero scalar multiple of this location-variation column.  On a sufficiently small finite-coordinate
parameter ball the selected poles avoid the evaluation packet and the spanning minor stays nonzero.
The rank-defect codimension, real parametric transversality, compact exhaustion, and Baire argument
of the preceding theorem now apply verbatim. `QED`

## Canonical-product exact-index family `[PROVED HERE]`

Fix `theta in Theta_free`.  Choose `2k` distinct real zeros

`a_1,b_1,...,a_k,b_k`

from the divisor of `F_theta`, and distinct points `t_1,...,t_k` in the upper half-plane.  Set

`F_(theta,k)(z)=F_theta(z) prod_(ell=1)^k`

`  ((z-t_ell)(z-conj(t_ell)))/((z-a_ell)(z-b_ell))`.            (9)

The apparent denominators cancel simple zeros of `F_theta`, so (9) is entire.  Its divisor is
obtained by replacing two real simple zeros with one simple conjugate nonreal pair for each `ell`.
Moreover,

`M_(theta,k)=-F_(theta,k)'/F_(theta,k)=M_theta+Q_k`              (10)

for a real-symmetric rational function `Q_k in C(z)`.

Consequently the full translation orbit of `M_(theta,k)` is differentially algebraically
independent and generates exactly the same differential-translation field as `M_theta`.

The Pick kernel of `M_(theta,k)` has exactly `k` negative squares.  After the `2k` selected positive
real atoms are removed, the remaining real-zero carrier is still positive semidefinite.  Each added
pair contributes the standard conjugate-pair generalized Nevanlinna kernel, so the negative index is
at most `k`.  Conversely, the `k` simple poles `t_ell` in the upper half-plane are generalized poles
of nonpositive type.  The Krein--Langer pole-count theorem, or equivalently the pole-localized
Cauchy-rank lower bound, contributes at least one negative square per distinct pole.  Hence the index
is exactly `k`.

Thus the exact-index orthogonality law holds not only for arbitrary positive masses: it holds for
logarithmic derivatives of order-one entire canonical products with ordinary simple-zero residues.
`QED`

## Functional-equation-even strengthening `[PROVED HERE]`

The same result survives the scalar functional equation.  With the same positive locations
`Lambda_j(theta)`, define

`E_theta(z)=prod_(j>=0) (1-z^2/Lambda_j(theta)^2)`.              (11)

This normally convergent product is real, even, entire of order one, and has the simple real divisor
`{+-Lambda_j(theta)}`.  Its carrier

`H_theta(z)=-E_theta'(z)/E_theta(z)`

` =sum_j [1/(Lambda_j(theta)-z)+1/(-Lambda_j(theta)-z)]`         (12)

is Herglotz on the upper half-plane and odd under `z |-> -z`.

There is a comeager set of `theta in ell^infinity(R)` for which the full complex translation orbit
of `H_theta` is differentially algebraically independent over `C(z)`.

For the jet lemma, choose the evaluation packet so that its full orbits under sign and conjugation
are pairwise disjoint.  Differentiating a summand of (12) with respect to `Lambda` gives rational
jet columns with poles at `Lambda=+-x_p`.  A real-linear annihilator again produces a rational
function of `Lambda` vanishing at every `Lambda_j(theta)`.  At the pole `Lambda=x_p`, only the jet
coordinates based at `x_p` contribute, and their principal parts force all coefficients to vanish.
The real jet span is therefore full.  The same codimension and transversality proof applies.

Now choose `2k` positive zeros `a_ell,b_ell` and nonreal points `t_ell` in the upper half-plane with
nonzero real part.  The even Schwarz-real surgery

`E_(theta,k)(z)=E_theta(z) prod_(ell=1)^k`

` ((z^2-t_ell^2)(z^2-conj(t_ell)^2))/((z^2-a_ell^2)(z^2-b_ell^2))`       (13)

cancels the selected real sign-pairs and inserts the off-real quartets
`{+-t_ell,+-conj(t_ell)}`.  Its logarithmic derivative differs from `H_theta` by a rational
function, so the full translation field and free differential matroid are unchanged.

Each quartet has two poles in the upper half-plane, `t_ell` and `-conj(t_ell)`.  The generalized
Nevanlinna upper bound and pole-count lower bound therefore give exact negative index `2k`.

Hence, under the functional-equation involution, maximal HT coexists in one field with every even
Krein index

`0,2,4,6,...`.

The functional equation enforces the pairing/parity law already visible in the Lean polarization
theorems; hypertranscendence does not strengthen parity to index zero. `QED`

## Measure-level finite-atomic gauge chambers `[PROVED HERE]`

Fix `u in U_free(mu)` and write `nu=exp(u) mu`.  Choose distinct real points
`a_1,...,a_d` which are not atoms of `nu`; such points exist because a locally finite measure has
at most countably many atoms.  For `c=(c_1,...,c_d) in R^d`, put

`m_(u,c)(z)=m_u(z)+sum_(j=1)^d c_j/(a_j-z)`.                  (M1)

Every member of this family has the same embedded differential-translation field, the same full
translation differential matroid, and the same generator class modulo `C(z)`, because the added
term is rational.  Its Pick kernel is

`K_(u,c)(z,w)=integral_R exp(u(t))/((t-z)(t-conj(w))) dmu(t)`

`               +sum_j c_j/((a_j-z)(a_j-conj(w)))`.           (M2)

Then

`kappa_-(m_(u,c))=#{j:c_j<0}`.                               (M3)

The upper bound follows because (M2) is a positive semidefinite measure kernel minus one positive
rank-one kernel for every negative coefficient.  For the reverse bound, enumerate the negative
coordinates and take nodes `z_l=a_(j_l)+iy`.  The signed atomic part, multiplied by `y^2`, tends to
the negative diagonal matrix `diag(c_(j_l))`.

The measure part tends to zero.  On the diagonal this is

`integral_R y^2/((t-a_j)^2+y^2) dnu(t) -> nu({a_j})=0`:       (M4)

use dominated convergence on a compact interval and the `(1+t^2)^(-1)` tail bound outside it.
Off-diagonal convergence follows from Cauchy--Schwarz for the positive measure kernel.  Hence the
scaled Gram matrix tends to a negative definite matrix, proving (M3). `QED`

The coordinate walls `c_j=0` cut `R^d` into an orthant cube, and (M3) is its distance grading from
the closed positive orthant.  Thus every infinite-support positive measure supporting maximal HT
comes with rationally gauge-equivalent representatives of every finite Krein index.  The general
positive carrier forced by the theorem is an oriented signed-measure realization: the unpointed HT
field retains neither the signs of finitely inserted atoms nor the distinguished nonnegative cone.

## Finite-support rational gauge-chamber law `[PROVED HERE]`

Write `B=C(z)` and

`K(f)=B< D^n T_h f : n>=0, h in C >`

for the embedded differential-translation field of a meromorphic generator `f`.

Fix `u in U_free` and write `w_j=epsilon_j exp(u_j)>0`.  Let `A_w` be the affine finite-support
gauge fiber

`A_w={c in R^N : c_j=w_j for all but finitely many j}`.

For `c in A_w`, define

`m_c(z)=sum_j c_j/(lambda_j-z)`.

This is well-defined because it differs from `m_u` by a rational function.  Put

`J_-(c)={j:c_j<0}`, `J_0(c)={j:c_j=0}`.

Both sets are finite.  Then:

1. `K(m_c)=K(m_u)` as embedded differential-translation fields with derivation, translations, and
   Schwarz conjugation;
2. `[m_c]=[m_u]` in the additive quotient `K(m_u)/B`;
3. the full translation orbit of `m_c` is differentially algebraically independent over `C(z)`;
4. the Pick kernel of `m_c` has exactly

   `kappa_-(m_c)=#J_-(c)`                                      (C1)

   negative squares.

Indeed, `r_c=m_c-m_u` belongs to `B`, and so does every `D^n T_h r_c`.  The substitutions

`D^n T_h m_u |-> D^n T_h m_u + D^n T_h r_c`

and their rational inverses prove statements 1--3, including preservation of differential
algebraic independence for every finite orbit tuple.

Only (C1) remains to prove.  The kernel is

`K_c(z,w)=sum_j c_j/((lambda_j-z)(lambda_j-conj(w)))`.          (C2)

It is a positive semidefinite kernel minus `#J_-(c)` positive rank-one kernels, so its negative
index is at most `#J_-(c)`.  Enumerate the negative set as `{j_1,...,j_k}` and evaluate at
`z_l=lambda_(j_l)+iy`.  After multiplying the resulting Gram matrix by `y^2` and letting `y->0+`,
the matrix tends to

`diag(c_(j_1),...,c_(j_k))`,                                  (C3)

which is negative definite.  Thus the index is at least `k`, proving (C1).  Zero coefficients
simply delete their atoms and create no hidden null contribution. `QED`

The formula has an exact chamber interpretation.  For a finite set `S subset N`, let

`A_(w,S)={c in A_w:c_j=w_j for j notin S} ~= R^S`.

Its index walls are the coordinate hyperplanes

`Delta_S=union_(j in S){c:c_j=0}`.                             (C4)

The complement has `2^(#S)` chambers `C_J`, indexed by `J subset S`, where precisely the
coordinates in `J` are negative.  Equation (C1) becomes

`kappa_-|_(C_J)=#J=dist_cube(C_empty,C_J)`.                    (C5)

Crossing one wall changes the index by exactly one; a simultaneous crossing changes it by the
signed number of coordinates crossing zero.  These finite arrangements are compatible under
inclusion of supports.  Their chamber graph is therefore the direct-limit cube whose vertices are
finite subsets of `N`, and `kappa_-` is distance from its distinguished positive vertex.

The zero-index locus in `A_(w,S)` is the closed positive orthant `c_j>=0` for every `j in S`, namely
the closure of `C_empty`; its boundary walls merely delete positive atoms and remain Herglotz.

Thus positivity is a positive geometric datum inside the rational gauge fiber: it is the choice of
the closed base chamber, or equivalently a coherent orientation of every residue coordinate.  The
maximal HT field supplies the ambient fiber but does not choose that orientation.

Starting from the odd carrier of an even canonical product, apply an odd rational gauge that varies
each real pole-pair `+-Lambda_j(theta)` with one common real coefficient.  The same wall arrangement
results, but every negative coordinate supplies two independent negative atoms.  Hence

`kappa_-^FE(C_J)=2 #J=2 dist_cube(C_empty,C_J)`.                (C6)

The functional-equation involution therefore equips the chamber system with an even grading; it
still leaves the positive base chamber as additional pointed data.

## Pointed-carrier necessity law `[PROVED] [BRIDGE]`

Let `K_infinity(f)` be the differential-translation field generated over `B=C(z)` by all
`D^n T_h f` in the field of germs on sufficiently high upper half-planes.  Retain this embedded
field, its derivation, every complex translation, and the Schwarz-real continuation of its
generator, but do not retain a preferred generator.  Also write `[f]` for the class of `f` in the
additive quotient `K_infinity(f)/B`.

Fix an infinite-support `mu`, choose `u in U_free(mu)`, and choose distinct non-atoms
`a_1,a_2,...` of `exp(u)mu`.  For every finite `J subset N`, put

`f_J=m_u-sum_(j in J) 1/(a_j-z)`.  Then

`K_infinity(f_J)=K_infinity(m_u)`                              (14)

as embedded differential-translation fields, the generators have the same Schwarz reality, and

`[f_J]=[m_u] in K_infinity(m_u)/B`,                            (15)

while the Pick negative-square index is

`kappa_-(f_J)=|J|`.                                            (16)

Consequently, suppose a rule `S` recovers the exact negative-square index on this family.  Then `S`
cannot factor through either the unpointed structured field in (14) or the base-gauge class in
(15).  Positively stated:

> **Every exact Krein-positivity selector on a maximal-translation HT carrier must retain a
> distinguished representative that changes under rational finite-rank surgery.**

The canonical sufficient marking is the full signed Herglotz measure.  In the discrete realization
it is

`mu_f=sum_n c_n delta_(lambda_n)`.

Its negative atomic rank is exactly `kappa_-(f)`.  In the canonical-product realization, the
corresponding marking is the embedded zero divisor together with its real/nonreal polarization.
These markings are not decorative presentations of the HT field: they are the data on which the
integer selector lives.

Indeed, (14)--(15) follow from rational gauge invariance, whereas (16) is (M3) and ranges over all of
`N` as `J` ranges over finite sets.  Any rule constant on the data in (14) or (15) would therefore
be constant on a family on
which the required output is unbounded.  Thus an exact rule must distinguish at least one rational
surgery representative. `QED`

In the discrete specialization, the stronger `A_w` family realizes the same index spectrum while
keeping the pole support fixed pointwise.

For the even functional-equation family, the same conclusion holds after retaining the involution
`z |-> -z`: the structured field and generator class modulo `B` remain fixed while the exact index
runs through `2N`.  The involution supplies the parity grading, but an additional pointed
polarization is forced in order to select its zero level.

## Attacks and boundaries

1. **The index is global and exact.**  `k=0` is exact Herglotz positivity on the whole upper half-plane;
   `k>0` is the exact global negative-square index.
2. **Every infinite-support Herglotz measure cone supports maximal HT.**  A comeager set of bounded
   positive reweightings has the strongest possible full-translation differential independence.
3. **Infinite support supplies complete jet controllability.**  A finite support gives a rational
   transform.  On every infinite support, the rational-annihilator argument makes the
   `L^infinity` positive-density directions span every finite complex jet packet.
4. **The convergence hypothesis is the standard Herglotz measure condition.**  The subtraction in
   (H1) treats finite or infinite total mass satisfying (H0); no atomicity is assumed.
5. **The rational gauge fibers are classified.**  Every measure carrier admits finite-atomic
   orthant chambers graded by exact index, while the discrete case has the stronger fixed-support
   direct-limit cube.
6. **The selector is necessarily pointed.**  Every finite exact index occurs without changing the
   field, matroid, or generator class modulo `C(z)`, so the integer must live on a rational-gauge-
   sensitive residue, divisor, kernel, measure, Euler, or spectral marking.
7. **Unit residues are available.**  The canonical-product strengthening removes the arbitrary-mass
   objection and realizes the same law with simple zeros of an order-one entire function.
8. **The scalar functional equation is available.**  The even strengthening preserves reflection
   symmetry and realizes every even negative index in one free HT field.
9. **Euler marking is the forced escape.**  The rational zero replacement changes the distinguished
   carrier.  A zeta application must therefore retain the Euler realization and prove that it fixes
   the required polarization; the theorem does not modify the actual zeta carrier while preserving
   its Euler product.
10. **Nyman--Beurling requires its pointed closure data.**  Its Hilbert norm and closure predicate must
   retain the distinguished zeta-generated realization.  The exact zeta-generated closure remains
   outside the theorem's scope.

## Exact positive route law

The law identifies the mandatory carrier for an HT-based positivity argument.  A successful Weil,
de Branges, Connes, or Hilbert--Polya realization must retain a distinguished Euler/spectral
representative on which rational finite-rank surgery acts nontrivially.  Concretely, it must provide
a signed residue or divisor polarization, a Pick kernel, a measure, a cyclic vector, or an
equivalent source marking whose zero negative-index level is the desired positivity condition.
Equivalently, it must orient the finite-support rational gauge directions coherently and select the
closed base chamber of the resulting infinite cube.  Maximal HT controls the freedom of the
ambient field; the pointed marking carries the integer orientation that selects `kappa_-=0`.

The measure-universal theorem makes the obligation sharper.  Even after an infinite-support
positive background measure is fixed, finitely inserted signed atoms realize every finite Krein index
inside the same embedded HT field.  In the discrete specialization, the real spectral skeleton may be
fixed pointwise and may have arbitrary arithmetic spacing: changing finitely many nonzero residue
signs preserves that pole support while moving to any finite chamber depth.  Thus a bare spectrum or
support set is not yet the positive carrier.  A successful spectral route must retain the oriented
spectral measure, cyclic-state weights, or equivalent polarization attached to that support.

With the functional-equation involution imposed, the index spectrum inside the fixed field is
`2N`.  The involution therefore supplies a positive parity law.  A viable route must additionally
construct the pointed polarization that distinguishes the zero level from the positive even
levels.

For Nyman--Beurling, the precise positive obligation is narrower: a successful implementation must
retain the distinguished zeta-generated vector, measure, and closure embedding rather than define
its Hilbert norm from the unpointed HT field.  For Li-type implementations, the required marking is
the normalized divisor/explicit-formula trace from which the Li coefficients are read.  These
classical routes are not refuted; the theorem states exactly what extra carrier they must preserve.

## Distinguished-scale necessity for Hilbertization `[PROVED] [BRIDGE]`

Let `K_u` be the differential-translation field generated by the free orbit, and let `V_u` be the
complex vector space spanned by all formal orbit derivatives

`D^n T_h m_u`, `h in C`, `n>=0`.

For every `c in C^x`, differential algebraic freeness makes

`S_c(D^n T_h m_u)=c D^n T_h m_u`

extend to a differential-field automorphism of `K_u` over `C(z)`.  It commutes with every
translation because the same scalar is used on every orbit coordinate.

If a Hermitian form `B` on `V_u` is intrinsic to the unpointed differential-translation field—in
the precise sense that every structure automorphism preserves `B`—then `B=0`.  Indeed, invariance
under `S_2` gives

`B(v,v)=B(2v,2v)=4 B(v,v)`

for every `v`, hence every diagonal value is zero; Hermitian polarization gives `B=0`.

Thus every nonzero Hilbertization of the maximal HT orbit must carry a distinguished scale that
breaks scalar isotropy: a normalized generator, source normalization, cyclic vector, measure, or
Euler embedding.  This corollary is elementary representation theory and is classified as a
bridge, not new scientific knowledge.

## Novelty gate

- **Proof gate:** passes by the real Cauchy-jet spanning lemma, rank-defect codimension, parametric
  transversality, and the exact signed-atomic kernel calculation.
- **Significance gate:** provisionally passes.  It is an exact pointed-selector theorem, not a
  finite-probe warning.  Every infinite-support positive Herglotz measure supports a comeager cone of
  bounded positive reweightings with maximal full-translation HT, whether its spectrum is discrete,
  singular-continuous, or absolutely continuous.  Each resulting field admits finite-atomic gauge
  chambers whose distance grading is the full Krein index; discrete fields carry the stronger
  fixed-support direct-limit cube.  Unit-residue order-one canonical products realize every finite
  index, and the FE-even subfamily realizes every even index.
- **Parent-theory gate:** open for the combined theorem.  The signed-atomic index formula and its
  coordinate-hyperplane chamber geometry are direct generalized-Nevanlinna/linear-algebra bridges,
  not candidate-new mechanisms.  The candidate-new residue is measure-universal residual
  full-complex-translation differential independence inside every infinite-support positive
  Herglotz measure cone and its compatibility with the fixed-field chamber system.
- **Literature gate:** preliminary exact searches completed across generalized Nevanlinna
  functions, hypertranscendence, generic meromorphic functions, and translate independence;
  specialist MathSciNet/zbMATH and citation-chain audit remains open.
- **Rediscovery gate:** open.

No candidate-new label is applied until those audits pass.

## Preliminary parent and literature comparison

0. **Unrestricted and symmetry-caged gauge genericity.**  The project already contains full-orbit
   genericity for entire exponential gauges, where finite Hermite interpolation supplies arbitrary
   complex jets directly.  That argument does not imply the present theorem: a positive Herglotz
   reweighting cone has only real `L^infinity(mu)` density directions and has empty interior in the
   ambient holomorphic-function space.  The real rational-annihilator lemma is precisely what makes
   those constrained directions jointly span every finite complex jet packet.  The measure-
   universal theorem should nevertheless be viewed as a constrained-cone extension of that
   transversality mechanism, not as an unrelated genericity principle.
1. **Jones--Kirby--Le Gal--Servi, strong transcendence.**  Proposition 3.2 proves that strongly
   transcendental holomorphic functions are residual in the unrestricted Frechet space `O(U)`.
   Their condition concerns arithmetic transcendence of finite point-jets and local definability.
   It does not work in the positive bounded-reweighting cone of an arbitrarily prescribed Herglotz
   measure, does not prove differential algebraic independence over `C(z)` of every uncountable
   translate tuple, and does not compare exact negative-square indices inside one field.  Source:
   `https://arxiv.org/abs/1712.07064`.
2. **Forstneric, holomorphic jet transversality.**  The general jet-transversality theorem supplies
   a parent mechanism for unrestricted holomorphic mapping spaces.  Here the parameter space is the
   nonlinear positive-measure reweighting family; the real Cauchy-jet spanning lemma is what recovers the
   missing submersion.  The exact Herglotz and translation-field conclusions are not stated there.
   Source: `https://arxiv.org/abs/math/0401439`.
3. **Edwards, independent translates.**  This treats topological linear independence of translates
   in function spaces, not differential algebraic independence of every derivative/translate family
   and not a positive Pick kernel.  Source: `https://doi.org/10.5802/aif.35`.
4. **Krein--Langer generalized Nevanlinna theory.**  Integral representations and finite
   negative-square indices are classical.  The signed-atomic calculation above is a concrete special
   case, and the coordinate-wall chamber law is its elementary finite-atomic sign stratification,
   not a new parent mechanism.  The candidate-new content, if any, is the compatibility of this
   complete chamber system with residual full-translation HT in one fixed embedded field.  Adjacent
   source: Rovnyak--Sakhnovich,
   `https://doi.org/10.13001/1081-3810.1117`.
5. **Dijksma--Langer--Luger--Shondin factorization.**  The canonical factorization of a scalar
   generalized Nevanlinna function counts nonreal poles and generalized real poles of nonpositive
   type with multiplicity in the negative index.  This supplies the classical pole-count step used
   in the canonical-product and even-quartet strengthenings; it does not contain the Herglotz-cone
   genericity or fixed-HT-field plasticity theorem.  Source:
   `https://doi.org/10.1007/BF01236290`.

Exact searches for combinations of `Herglotz/Nevanlinna`, `Cauchy transform`, `positive measure`,
`bounded density/reweighting`, `discrete/singular/continuous support`, `differential algebraic
independence`, `all translates`, `comeager/residual`, `Laguerre--Polya/canonical product`, and
`negative squares` did not locate either the measure-universal generic-freeness theorem or the
combined fixed-field chamber theorem.
This is only preliminary negative evidence; MathSciNet/zbMATH and specialist citation-chain review
remain required.

## Lean status

The current Lean tree formalizes the finite pairability/index side (`OmegaComplexStructure`,
`SeamPolarizationWeld`, `SeamSpectralFlow`, `CarrierCauchy`), the measured-index blindness side, the
forward infinite positive-measure Herglotz/Pick theorem in `MeasureCarrier.lean`, and the abstract
countable Baire-avoidance backbone.  `HTGeometry.CauchyJetControllability` now proves the complete
finite-dimensional real Cauchy-jet surjectivity theorem for every infinite injective real support,
including the actual prime-log specialization.  For that discrete source,
`HTGeometry.PolynomialJetEscape`, `PrimeLogGaugePerturbation`,
`PolynomialRelationDetector`, and `PrimeLogPolynomialJetEscape` prove positivity-preserving
polynomial avoidance inside arbitrarily small bounded-gauge balls, including nonzero specialization
of polynomial-coefficient relations at distinct upper-half-plane nodes.  `DiscreteCauchyJetPacket`,
`DiscreteCauchyJetDerivatives`, and `JetFactorialScale` identify those coordinates exactly with the
actual iterated derivatives and transfer avoidance across the factorial diagonal.  `HTGeometry.RegularizedHerglotzTransform` now closes the
regularized infinite-measure reweighting layer: the (H0) transform is an invertible rational gauge
of the Cauchy transform of a probability measure, and `HTGeometry.MeasureCauchyJetDetection`
replaces the discrete separated-point detector by almost-everywhere vanishing against any measure
of infinite support.  The tree does not yet
contain the corresponding `L^infinity(mu)` measure-level surjectivity theorem for arbitrary
nondiscrete support, infinite **signed** Cauchy-kernel index, algebraic rank-defect codimension,
or full parametric transversality.  Those missing layers carry the
complete measure-universal claim, so no partial theorem is promoted to stage 3.

## Gates

- [x] 0 -> 1: exact law and measure-jet, transversality, chamber, and canonical-product cores isolated
- [x] 1 -> 2: complete unconditional paper proof
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready preprint and independent novelty audit

## Log

- 2026-07-11 -- Proved real jet-surjectivity for positive Cauchy masses by a rational-annihilator
  argument and used real parametric transversality to remove every uncountable shift configuration.
- 2026-07-11 -- Proved exact signed-atomic Krein index `k` by a rank upper bound and pole-localized
  negative-definite Gram matrices.  Rational surgery preserves the complete free HT field exactly.
- 2026-07-11 -- Strengthened the discrete exact-index family to the complete finite-support rational
  gauge fiber.  Its compatible finite slices form a cubical chamber system, with Krein index equal
  to distance from the closed positive chamber and FE index equal to twice that distance.
- 2026-07-11 -- Removed the artificial integer-support hypothesis.  The residual full-complex-
  translation freeness theorem now holds on every infinite discrete real support satisfying the
  single normal-convergence summability condition; no support arithmetic enters the proof.
- 2026-07-11 -- Extended residual full-translation freeness from discrete atomic supports to bounded
  positive reweightings of every infinite-support Herglotz measure.  Proved the accompanying
  finite-atomic exact-index chambers over an arbitrary positive background measure.
- 2026-07-19 — Lean gate opened; corpus survey done before writing any new code. The predicate the
  card needs already exists as `HTGeometry.MaximalTranslationDifferentialFree`
  (`BoundaryCarrierTranslationFreeness.lean`), with an entry point
  `maximalTranslationDifferentialFree_of_fullRankWitness` and a density result on infinite closed
  boundary faces, `boundaryCarrierFace_subset_closure_maximalTranslationDifferentialFree`
  (`NevanlinnaBoundaryFaceMaximalTranslation.lean`). "Germs at upper infinity" is the existing
  `upperEndFilter`/`upperEndMeroField` layer, and the full complex translation orbit already acts
  there by differential automorphisms via
  `HTGeometry.upperEndTranslationMeroDifferentialAlgEquiv`. So the open work is not the freeness
  predicate but the measure layer: the regularized transform (H1) as an upper-end carrier under
  (H0), and upgrading existing face-density to comeagerness in `L^infinity(mu;R)`.
- 2026-07-19 — measure layer started, first piece Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/RegularizedHerglotzTransform.lean`. The mismatch with the
  existing freeness layer was that the corpus works with finite (probability) measures and the
  plain Cauchy transform, while (H0) permits infinite mass. Resolved by factoring the Nevanlinna
  regularization: for real `t` and non-real `z`,
  `1/(t-z) - t/(1+t^2) = (1+t^2)^{-1} (z + (1+z^2)/(t-z))`
  (`regularizedHerglotzKernel_eq`), so with the weighted measure `dnu = (1+t^2)^{-1} e^u dmu` —
  finite exactly under (H0) — one gets
  `m_u(z) = z * nu(R) + (1+z^2) * C_nu(z)`  (`regularizedHerglotzTransform_eq`).
  Both corrections are rational in `z`, so they do not move the differential field over `C(z)`.
  Integrability of the Cauchy kernel against a finite measure is proved, not assumed
  (`integrable_cauchyKernel`), since the kernel is bounded by `|Im z|^{-1}`.
  Next: normalize `nu` to a probability measure to land on the corpus predicate
  `MaximalTranslationDifferentialFree`, then transport a translate relation through the rational
  gauge and upgrade infinite-closed-face density to comeagerness in `L^infinity(mu;R)`.
- 2026-07-19 — measure layer now lands on the corpus predicate's own object. Added the
  normalization bridge: every nonzero finite measure is its total mass times a probability measure
  (`exists_mass_probability_decomposition`, constructed rather than assumed), giving the standalone
  form `exists_probability_regularizedHerglotzTransform_eq`:
  `m_u(z) = c * (z + (1+z^2) * C_P(z))` for an honest probability measure `P` and mass `c`,
  with no decomposition hypothesis. Since `w |-> z + (1+z^2) w` is invertible over `C(z)` and `c`
  is a nonzero constant, `m_u` and `C_P` generate the same differential field over `C(z)`.
  Remaining and not started: transport a translate relation across that gauge inside the
  matrix/packet formalism of `probabilityCarrierExpandedPatternRelationHolds`, and upgrade
  infinite-closed-face density to comeagerness in `L^infinity(mu;R)` — the genuine analytic step.
- 2026-07-19 — affine base-gauge invariance built and Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/BaseGaugeDifferentialIndependence.lean`. The corpus had
  only the additive half (`DifferentialIndependent.addBase`); the multiplicative half was missing,
  and it is what the `m_u = c (z + (1+z^2) C_P)` gauge actually needs. Proved via the binomial
  Leibniz rule already in `ProjectiveHorizonFiniteJetRank` — the jets of `a * x` form a
  jet-triangular system over the jets of `x` with constant diagonal symbol `diagonal a` — fed to
  the existing `matrixPrincipalLowerLaw_ancestral_independence_iff`. Capstones:
  `differentialIndependent_mulBase_iff` and `differentialIndependent_affineBase_iff`
  (`x |-> a x + b`, `a` invertible in the base), both axiom-clean.
  Remaining: instantiate this gauge at the translated Herglotz family to convert freeness of the
  translates of `C_P` into freeness of the translates of `m_u`, and then the comeagerness upgrade
  in `L^infinity(mu;R)` — still the genuine open analytic step.
- 2026-07-19 — analytic realization done and Lean-checked. Holomorphy of the Cauchy transform of a
  finite measure off the real axis is proved by differentiation under the integral
  (`hasDerivAt_cauchyTransform`, derivative `∫ (t-z)^{-2}`), dominated by a constant because the
  kernel is uniformly bounded on any ball avoiding the axis (`lt_abs_im_of_mem_ball`); holomorphy
  upgrades to `analyticOnNhd_cauchyTransform` on any open axis-avoiding set. New module
  `formal/GaloisForLFunctions/HTGeometry/HerglotzUpperEndCarrier.lean` then places the transform in
  the upper-end field as `cauchyTransformUpperEndAnalytic` / `cauchyTransformUpperEndMero`, since
  every upper half-plane avoids the axis (height 0). All axiom-clean.
  The card's object now lives in the same field as the translation action
  (`upperEndTranslationMeroDifferentialAlgEquiv`) and the affine gauge lemma.
  Remaining: assemble translated carriers and apply `differentialIndependent_affineBase_iff`;
  then the comeagerness upgrade in `L^infinity(mu;R)` — still untouched, still the hard step.
- 2026-07-19 — step (1) closed: the gauge transfer is now available at the upper end, axiom-clean.
  `formal/GaloisForLFunctions/HTGeometry/UpperEndAffineGauge.lean` discharges the instance
  bookkeeping once (the coordinate field is derivation closed, so it carries the restricted
  derivation and is a differential subalgebra of the meromorphic field), giving
  `differentialIndependent_upperEnd_affineGauge_iff` and its rank-one form.
  `formal/GaloisForLFunctions/HTGeometry/HerglotzGaugeTransfer.lean` then instantiates it at the
  Herglotz normalization: the gauge coefficients `c(1+z^2)` and `cz` are genuine rational
  coordinates and the multiplier is invertible (`1+z^2` is the image of a nonzero coordinate
  polynomial, so it is nonzero by injectivity of `upperEndPolyToMero`), yielding
  `hypertranscendentalOver_herglotzGauge_iff`: the normalized Herglotz presentation
  `c (z + (1+z^2) C)` is hypertranscendental over `C(z)` exactly when the Cauchy carrier `C` is.
  The whole reduction from the card's `m_u` down to a probability Cauchy carrier is now
  unconditional. What remains is exactly one thing, and it is the whole theorem: the comeagerness
  of the free reweightings in `L^infinity(mu;R)`. Untouched.
- 2026-07-19 — began the comeagerness layer. Two findings changed the plan. First, the Baire engine
  already exists (`affineJetPacketCollision_denseResidual_exactMatroid`: countably many closed
  empty-interior defects in a Baire space give a dense residual avoider set), and the Nevanlinna
  pullback `normalizedPositiveChart_actualCarrier_relationFree_dense_residual` *assumes* residuality
  rather than proving it — so the open work is nowhere-density of each degenerate locus, not the
  category argument. Second, the discrete detector
  `CauchyJetControllability.cauchyJet_coeff_eq_zero_of_infinite` needs only infinitely many
  separated points, so it generalizes to measures cheaply: a full-measure set is infinite whenever
  the support is infinite (else the support sits in a finite closed set), giving
  `MeasureCauchyJetDetection.cauchyJet_coeff_eq_zero_of_ae` — coefficient detection from
  almost-everywhere vanishing, for an arbitrary measure of infinite support, no regularity needed.
  Next: measure-level controllability (surjectivity of the bounded-reweighting jet map), which is
  the dual of this detector, then nowhere-density of the degenerate loci.
- 2026-07-19 — measure-level controllability (dual form) Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/MeasureCauchyJetControllability.lean`. The jet form
  `Q t = sum_i sum_j c i j (t - x i)^{-(j+1)}` is uniformly bounded on the real axis whenever the
  nodes avoid it (`norm_cauchyJetForm_le`), hence integrable against any finite measure
  (`integrable_cauchyJetForm`) — no decay or regularity hypothesis is needed. Vanishing of every
  set integral then forces `Q = 0` a.e., and the detector of the previous module kills every
  coefficient: `cauchyJet_coeff_eq_zero_of_forall_setIntegral_eq_zero`. This says no nonzero finite
  Cauchy-jet functional annihilates all bounded reweightings of a finite measure of infinite
  support, which is the transversality input the degenerate loci need.
  Next: nowhere-density of each degenerate locus (closed with empty interior) in the reweighting
  space, then the existing Baire engine `affineJetPacketCollision_denseResidual_exactMatroid`
  closes comeagerness.
- 2026-07-19 — the nowhere-density link is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/ControlPullbackNowhereDense.lean`. The abstract halves
  already existed on both sides: `PolynomialJetEscape.mvPolynomial_zero_set_isNowhereDense` gives
  nowhere density of a nonzero polynomial's zero set in the finite jet space, and
  `BaireGenericAvoidance` gives countable avoidance. Missing was the transfer between them, since
  the Baire argument must run in the control space, not the jet space. Supplied by openness of a
  surjective continuous control map (`interior_preimage_eq_empty_of_surjective`): a ball of
  controls cannot be squeezed into a set with empty interior. Capstones
  `isNowhereDense_degenerateControls` and `dense_residual_nondegenerateControls` — the latter needs
  only per-pattern controllability plus nonvanishing of the pattern polynomial, no further side
  conditions.
  The comeagerness skeleton is now complete and abstract. What remains for this card is the
  instantiation: exhibiting the Herglotz reweighting control map as a surjective continuous linear
  map into the jet space (the analytic content of measure-level surjectivity, for which
  `MeasureCauchyJetControllability` supplies the dual injectivity), and identifying the pattern
  polynomials. Also still open: signed Cauchy-kernel index and rank-defect codimension.
- 2026-07-19 — signed Cauchy-kernel index closed, one of the card's named missing layers. Two
  steps. First, the positivity hypothesis in the measure-level detector and its dual was
  gratuitous: the underlying discrete detector
  `CauchyJetControllability.cauchyJet_coeff_eq_zero_of_infinite` needs only separation of the
  sampling points from the nodes, so both were generalized to nodes off the real axis in either
  half-plane. Second, and this is what the surjectivity argument actually forces: a real-linear
  functional on a complex jet space sees only `Re` of the pairing, and on the real axis `Re Q` is
  itself a jet form carried by the conjugate-doubled node family, since
  `conj ((t - x)^{-1}) = (t - conj x)^{-1}` for real `t` and conjugation maps the upper half-plane
  to the lower one, so the two halves never collide. New module
  `formal/GaloisForLFunctions/HTGeometry/SignedCauchyJetDetection.lean` proves
  `cauchyJetForm_doubled_eq_re` and the capstone `cauchyJet_coeff_eq_zero_of_ae_re`: real-part
  vanishing almost everywhere kills every coefficient. All axiom-clean.
  Next: assemble the control map `L^infinity(mu;R) -> C^N` as a continuous linear map, whose
  surjectivity now follows from `cauchyJet_coeff_eq_zero_of_ae_re` by the real-functional argument;
  feeding it to `ControlPullbackNowhereDense` then discharges comeagerness. Still open after that:
  rank-defect codimension.
- 2026-07-19 — the real/complex dictionary for the surjectivity argument is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/RealFunctionalJetCoefficients.lean`. Annihilation produces
  a real-linear functional while the Cauchy-jet detectors consume a complex coefficient packet;
  the bridge is that every real-linear functional on a finite complex jet space is the real part of
  a complex pairing, `phi v = Re (sum_s c s * v s)` with
  `c s = phi (single s 1) - I * phi (single s I)` (`re_sum_realFunctionalCoefficients`). Hence a
  real functional vanishes exactly when its packet does, and
  `surjective_of_forall_coefficients_eq_zero` reduces surjectivity of any real-linear map into a
  finite complex jet space to coefficient rigidity — which is exactly what
  `SignedCauchyJetDetection.cauchyJet_coeff_eq_zero_of_ae_re` supplies. All axiom-clean, and the
  argument is finite-dimensional linear algebra only, independent of the control space.
  Next and last for comeagerness: the `L^infinity(mu;R)` packaging — realize the reweighting map as
  a continuous linear map into the jet space (essential-sup bound, a.e. classes), instantiate
  surjectivity, and feed `ControlPullbackNowhereDense`. Still open after that: rank-defect
  codimension.
- 2026-07-19 — the two halves of the surjectivity argument now meet.
  `SignedCauchyJetDetection.cauchyJet_coeff_eq_zero_of_forall_setIntegral_re_eq_zero`: if every set
  integral of the jet form has vanishing real part, every coefficient vanishes. Real part commutes
  with the integral (`Complex.reCLM.integral_comp_comm`), the real part of the jet form is
  integrable against a finite measure, so it vanishes a.e. and the conjugate-doubling detector
  applies. This is exactly the hypothesis a real-linear functional annihilating the range of a
  reweighting control map produces, and it composes with
  `RealFunctionalJetCoefficients.surjective_of_forall_coefficients_eq_zero` to give surjectivity of
  any such control map, once the map itself is built.
  Remaining for comeagerness is now purely the `L^infinity(mu;R)` packaging: define the map
  `u |-> (int u(t) (t - x_s)^{-(j+1)} dmu)_s`, prove it continuous linear (essential-sup bound
  against a bounded kernel and finite measure), flatten the index `Sigma i, Fin (n i)` against the
  detector's dependent form, instantiate surjectivity, then feed `ControlPullbackNowhereDense`.
  Still open after that: rank-defect codimension.
- 2026-07-19 — index flattening closed in
  `formal/GaloisForLFunctions/HTGeometry/FlattenedCauchyJetRigidity.lean`. The detectors carry a
  dependent packet `(i : ι) -> Fin (n i) -> C` while a control map lands in a plain function space
  on `Sigma i, Fin (n i)`; `Fintype.sum_sigma` reconciles the two definitionally
  (`sum_cauchyJetKernel_eq_cauchyJetForm`), so rigidity transfers verbatim. Capstones:
  `flattened_coeff_eq_zero_of_forall_setIntegral_re_eq_zero`, and
  `surjective_of_setIntegral_pairing` — a real-linear map into the flattened jet space whose
  pairings are kernel set-integrals against a measure of infinite support is surjective. This is
  the exact input `ControlPullbackNowhereDense` consumes, so the abstract chain from measure to
  comeagerness is now closed end to end.
  Remaining is only the concrete `L^infinity(mu;R)` instance: define
  `u |-> (int u(t) K_s(t) dmu)_s`, prove it continuous linear (the essential-sup bound
  `enorm_ae_le_eLpNormEssSup` against the uniform kernel bound over a finite measure), and check
  the pairing hypothesis of `surjective_of_setIntegral_pairing` by Fubini on a finite sum.
  Still open after that: rank-defect codimension.
- 2026-07-19 — the `L^infinity` analytic core is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/BoundedReweightingControl.lean`. Mathlib carries only the
  converse direction (`Lp.norm_le_of_ae_bound`: an a.e. bound gives an `L^infinity` norm bound), so
  `ae_norm_le_norm_Lp_top` had to be built — an `L^infinity` element is a.e. bounded by its norm,
  via `enorm_ae_le_eLpNormEssSup` plus finiteness of the essential supremum to cross
  `ENNReal.toReal`. On that: `integrable_Lp_top_mul` (bounded reweighting times uniformly bounded
  kernel is integrable against a finite measure) and `norm_integral_Lp_top_mul_le`, whose bound
  `(B * mu univ) * ||f||` is linear in the reweighting norm — the operator-norm estimate a
  continuous control map needs. The norm bound needs no measurability hypothesis.
  Remaining: assemble these into `L : Lp R top mu ->L[R] (jetIndex n -> C)` (linearity uses
  `Lp.coeFn_add`/`coeFn_smul`, continuity is the bound above via `LinearMap.mkContinuous`), discharge
  the pairing hypothesis of `surjective_of_setIntegral_pairing` by exchanging the finite jet sum
  with the integral, then feed `ControlPullbackNowhereDense`.
  Still open after that: rank-defect codimension.
- 2026-07-19 — the control map itself is built and Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/HerglotzControlMap.lean`:
  `herglotzControl : Lp R top mu ->L[R] (jetIndex n -> C)`, sending a bounded reweighting to its
  vector of Cauchy jets at the prescribed nodes. Linearity uses `Lp.coeFn_add`/`coeFn_smul` on the
  a.e. classes; boundedness is componentwise via the uniform kernel bound, assembled with
  `pi_norm_le_iff_of_nonneg` and a sum-dominates-each-term estimate, so the operator bound
  `(sum_s B_s) * mu univ` needs no nonemptiness of the jet index.
  Remaining: discharge the pairing hypothesis of `surjective_of_setIntegral_pairing` for this map
  (exchange the finite jet sum with the integral), obtaining surjectivity, then feed
  `ControlPullbackNowhereDense` for comeagerness. Still open after that: rank-defect codimension.
- 2026-07-19 — the genericity chain is closed, unconditionally, in
  `formal/GaloisForLFunctions/HTGeometry/HerglotzControlSurjective.lean`.
  `surjective_herglotzControl`: for a finite measure of infinite support and distinct
  upper-half-plane nodes, every finite Cauchy-jet vector is realized by a bounded reweighting.
  Proof route: indicators are bounded reweightings and the control map sends the indicator of `S`
  to the Cauchy kernels integrated over `S` (`herglotzControl_indicatorConstLp`); exchanging the
  finite jet sum with the integral (`sum_mul_setIntegral_cauchyJetKernel`, which needs no
  measurability of `S`) turns annihilation by a real functional into exactly the real-part
  hypothesis of the signed detector, which then kills the coefficient packet.
  Capstone `dense_nondegenerate_reweightings`: for a finite measure of infinite support, the
  bounded reweightings on which a countable family of nonzero polynomial jet relations all fail to
  degenerate are dense in `L^infinity(mu;R)`. This is the genericity statement the card's Baire
  step needs, now unconditional and axiom-clean.
  Not yet done: this is stated for a finite measure. The card's `m_u` uses the (H0) reweighting
  `e^u dmu`, so the remaining link is to compose this with the regularized-transform reduction
  (`RegularizedHerglotzTransform`), i.e. carry genericity across the `u |-> e^u` chart onto the
  weighted measure. Also still open: rank-defect codimension.
- 2026-07-19 — support preservation under positive reweighting, Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/PositiveReweightingSupport.lean`. Needed because the
  control map is linear in the *density*, not in `u`: the tangent direction at a base reweighting
  `u_0` is the Cauchy-jet map of the measure `e^{u_0} w dmu`, so surjectivity there requires that
  measure to still have infinite support. An a.e. nonzero density moves no null set
  (`measure_withDensity_eq_zero_iff`), and `Measure.support` is defined by positivity on
  neighbourhoods, so `support_withDensity_eq` gives equality of supports outright. Specializing,
  `support_nevanlinnaWeightedMeasure_infinite`: the Nevanlinna-weighted measure of a base measure
  with infinite support again has infinite support, since its density is a strictly positive weight
  times an exponential. So `surjective_herglotzControl` and `dense_nondegenerate_reweightings` now
  apply at *every* base reweighting, not just at the unweighted measure.
  Remaining for the card's comeagerness: the nonlinear chart step itself. `u |-> e^u` is not
  linear, so density in `u`-space does not follow from the linear pullback; the paper argument is
  parametric transversality — along a finite-dimensional slice `u_0 + sum theta_k a_k` the jet map
  is analytic in `theta` with surjective derivative at `0` (that derivative is exactly the control
  map above), hence open, so a nonzero polynomial cannot vanish on its image. That inverse-function
  step is not yet formalized. Also still open: rank-defect codimension.
- 2026-07-19 — the transversality step is done, and it does not need transversality. Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/AffineReachabilityGenericity.lean`:
  `dense_nondegenerate_of_affine_reachability`. The card's paper argument linearizes the chart
  `u |-> e^u` and asks the derivative to be surjective. That derivative is unnecessary. It suffices
  that the reachable jets from a small parameter ball contain an *affine* image `F u_0 + L h` of a
  small ball for some surjective continuous linear `L`; then `L` is open, so the reachable set
  contains a neighbourhood of `F u_0`, and a nonzero polynomial cannot vanish on a neighbourhood.
  No differentiability of the parameter map is used anywhere.
  For the Herglotz chart the hypothesis holds *exactly*, with no linearization error, by perturbing
  the density multiplicatively: replacing `exp u_0` by `exp u_0 (1 + h)` moves the parameter to
  `u_0 + log (1 + h)` and moves the jets by exactly `L_{nu_0} h`, where `nu_0 = exp u_0 * w * dmu`
  and `L_{nu_0}` is `herglotzControl`, surjective by `surjective_herglotzControl` (applicable at
  every base point by `support_nevanlinnaWeightedMeasure_infinite`).
  Remaining: discharge that reachability hypothesis concretely — the `log (1 + h)` bookkeeping in
  `L^infinity` (that `u_0 + log(1+h)` is bounded and within `O(||h||)` of `u_0`, and that the
  weighted measure factors as claimed). Then comeagerness for the card follows. Also still open:
  rank-defect codimension.
- 2026-07-19 — the multiplicative gauge chart is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/MultiplicativeGaugePerturbation.lean`, supplying the
  pointwise content of the reachability hypothesis. `abs_log_one_add_le_two_mul`:
  `|log (1+x)| <= 2|x|` for `|x| <= 1/2`, so a uniformly small multiplicative gauge is a uniformly
  small additive change of the exponential parameter. Upper half from `log y <= y - 1`; lower half
  from `exp (2x) <= 1/(1-2x) <= 1+x`, which holds exactly on that range (the second inequality is
  `x(1+2x) <= 0`). With `exp_add_log_one_add` (`exp (u + log (1+x)) = exp u * (1+x)`) this is the
  reparameterization that makes the jet map affine with no linearization error.
  Remaining to close comeagerness: lift these pointwise facts to `L^infinity` classes — from
  `||h||_infty <= 1/2` conclude `log (1+h)` is in `L^infinity` with `||log(1+h)||_infty <= 2||h||`,
  and that the weighted measure factors as `(1+h) * exp(u_0) * w * dmu` — then feed
  `dense_nondegenerate_of_affine_reachability`. Also still open: rank-defect codimension.
- 2026-07-19 — the gauge lift to `L^infinity` is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/LogGaugeLift.lean`. `logOneAddLp` turns a bounded
  multiplicative gauge `h` with `||h|| <= 1/2` into an honest `L^infinity` parameter change
  `log (1 + h)`, and `norm_logOneAddLp_le` bounds it by `2||h||`. Supporting this,
  `norm_toLp_le_of_ae_bound`: at exponent infinity an a.e. bound *is* a norm bound, with no
  finiteness of the base measure — which matters here, since the card's parameter space is
  `L^infinity(mu;R)` over the possibly infinite base Herglotz measure, so
  `Lp.norm_le_of_ae_bound` (which assumes finiteness) is unusable.
  So the parameter-side half of the reachability hypothesis is done: small multiplicative gauge
  gives small additive parameter change. Remaining for reachability: the measure-side half — that
  the weighted measure of `u_0 + log(1+h)` factors as `(1+h) * exp(u_0) * w * dmu`, so the jets move
  by exactly `L_{nu_0} h`. Note one type mismatch to handle there: `h` lives in `L^infinity(mu)`
  while `herglotzControl` is stated over the finite measure `nu_0`; the two have the same null sets
  (`support_withDensity_eq`'s null-set lemma), so the classes correspond, but the identification
  must be made explicit. Also still open: rank-defect codimension.
- 2026-07-19 — the measure-side half of reachability is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/GaugeWeightedFactorization.lean`.
  `nevanlinnaWeightedMeasure_gauge`: the weighted measure of the gauged parameter
  `u_0 + log(1+h)` is the weighted measure of `u_0` reweighted by `1+h` — a `withDensity`
  factorization, since the density multiplies by exactly `1+h`. `integral_withDensity_one_add`:
  integrating any integrand against the gauged measure adds precisely the pairing of the gauge with
  that integrand, with no linearization error. Applied to the Cauchy kernel coordinates this says
  the jets move by exactly `L_{nu_0} h`, which is the affine hypothesis of
  `dense_nondegenerate_of_affine_reachability`.
  Both halves of reachability now exist: parameter side (`LogGaugeLift`) and measure side (this
  module). Remaining to assemble comeagerness: bridge the two `L^infinity` spaces — the gauge `h`
  is naturally an `L^infinity(nu_0)` class while the parameter lives in `L^infinity(mu)`; the
  measures share null sets, so the classes correspond, but the identification is not yet written.
  Then instantiate `dense_nondegenerate_of_affine_reachability` with `F = jets` and
  `L = herglotzControl`. Also still open: rank-defect codimension.
- 2026-07-19 — design correction, with its analytic core Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/WeightedJetControl.lean`. The `L^infinity(mu)` versus
  `L^infinity(nu_0)` mismatch flagged earlier should not be bridged by identifying the two spaces:
  the reachability hypothesis requires the control map to be defined on the *parameter* space
  `L^infinity(mu)`, so the right object is the *weighted* control map over `mu`,
  `L f = fun s => int f(t) w(t) K_s(t) dmu(t)`, with `w` the Radon-Nikodym density written
  explicitly. Both parameter and gauge then live over `mu` throughout and no identification is
  needed. Boundedness now comes from integrability of `w` (which is exactly (H0)) rather than
  finiteness of `mu`, so the infinite-mass base measure is handled directly:
  `integrable_Lp_top_mul_weight` and `norm_integral_Lp_top_mul_weight_le`, the latter with operator
  bound `(B * int |w|) * ||f||`.
  Remaining: bundle these into a continuous linear map (mirrors `HerglotzControlMap`), redo
  surjectivity for the weighted map (the dual argument is unchanged — a functional annihilating it
  gives `Re(int_S w Q dmu) = 0`, and `w > 0` reduces this to `Q = 0` a.e. against `mu`, whose
  support is infinite by hypothesis), then instantiate
  `dense_nondegenerate_of_affine_reachability`. Also still open: rank-defect codimension.
