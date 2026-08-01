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
- 2026-07-19 — the weighted control map is built:
  `WeightedJetControl.weightedJetControl : Lp R top mu ->L[R] (jetIndex n -> C)`, defined over the
  base measure with the density written explicitly, so parameter and gauge share one space.
  Linearity via `Lp.coeFn_add`/`coeFn_smul`; operator bound `(sum_s B_s * int |w|) * ||f||` from
  `norm_weightedJetControlLinear_le`. Hypotheses are `Integrable w mu` only — no finiteness of
  `mu`, which is what the (H0) setting requires. Axiom-clean.
  Remaining: weighted surjectivity (dual argument as before: annihilation gives
  `Re(int_S w Q dmu) = 0`, and `w > 0` reduces to `Q = 0` a.e. against `mu`, whose support is
  infinite by hypothesis, so the signed detector applies), then instantiate
  `dense_nondegenerate_of_affine_reachability` with `F = jets`, `L = weightedJetControl`, using
  `LogGaugeLift` for the parameter bound and `GaugeWeightedFactorization` for the exact affine
  displacement. Also still open: rank-defect codimension.
- 2026-07-19 — weighted surjectivity is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/WeightedJetControlSurjective.lean`:
  `surjective_weightedJetControl`. For a base measure of infinite support carrying a strictly
  positive integrable density, every finite Cauchy-jet vector is realized by a bounded reweighting —
  and no finiteness of the base measure is used anywhere, which is what the (H0) setting needs.
  Two points. `indicatorConstLp` was unusable because it demands a set of finite measure, false for
  an infinite base measure; at exponent infinity boundedness alone suffices, so `indicatorLpTop`
  builds the indicator directly from its uniform bound. And the density cancels at the end rather
  than the start: annihilation gives `Re(w * Q) = 0` a.e., `w > 0` pointwise then yields
  `Re(Q) = 0` a.e., and the signed detector applies since `mu` has infinite support.
  Remaining for comeagerness: instantiate `dense_nondegenerate_of_affine_reachability` with
  `F = jets`, `L = weightedJetControl`, discharging its reachability hypothesis from
  `LogGaugeLift` (parameter bound) and `GaugeWeightedFactorization` (exact affine displacement).
  Also still open: rank-defect codimension.
- 2026-07-19 — the jet map on bounded parameters is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/HerglotzJetMap.lean`. `integrable_exp_Lp_top_mul`:
  boundedness of the parameter is exactly what keeps the exponential density integrable for *every*
  parameter, since `exp u <= exp ||u||`, so integrability of `w` is inherited with no extra
  hypothesis. `herglotzJetMap` sends a parameter to the Cauchy jets of its measure, and
  `surjective_weightedJetControl_expDensity` gives surjectivity of the tangent control at every
  base parameter (not just at the unweighted one) — the linear part the reachability argument needs,
  available uniformly.
  Remaining for comeagerness: assemble the reachability hypothesis of
  `dense_nondegenerate_of_affine_reachability` — given `u_0` and `eps`, take `delta = min(1/2, eps/2)`
  and for `||h|| < delta` set `u = u_0 + logOneAddLp h`; then `dist u u_0 <= 2||h|| < eps` by
  `norm_logOneAddLp_le`, and `F u = F u_0 + L h` by `GaugeWeightedFactorization` (the identity is
  exact, so this is an equality, not an estimate). Also still open: rank-defect codimension.
- 2026-07-19 — **genericity for the Herglotz chart is closed**, unconditionally, in
  `formal/GaloisForLFunctions/HTGeometry/HerglotzGenericity.lean`:
  `dense_nondegenerate_herglotzJetMap`. For a base measure of infinite support with a strictly
  positive integrable Nevanlinna density, the bounded parameters on which a fixed nonzero
  polynomial jet relation fails to degenerate are dense in `L^infinity(mu;R)`.
  The chart is handled without any derivative. `herglotzJetMap_gauged` is an exact identity:
  gauging the density by `1 + h` sends the jets to `F u_0 + L h` with `L` the weighted control map,
  and `norm_logOneAddLp_le` bounds the induced parameter change by `2||h||`. Both are equalities or
  clean estimates, never linearizations, so the paper's parametric-transversality step is replaced
  by `dense_nondegenerate_of_affine_reachability` whose linear part is surjective at every base
  parameter (`surjective_weightedJetControl_expDensity`).
  Scope note: this is density for *one* nonzero polynomial relation. The card's comeagerness is the
  countable intersection over all finite differential patterns; the Baire step for that is
  `dense_residual_nondegenerateControls` / `affineJetPacketCollision_denseResidual_exactMatroid`,
  but the countable-family version of the *chart* statement is not yet assembled — the present
  theorem must be iterated over a countable pattern family and intersected. Also still open:
  rank-defect codimension, and the connection of these jets back to the card's translation-orbit
  freeness predicate.
- 2026-07-19 — quantitative continuity of the jet map, Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/HerglotzJetMapContinuity.lean`. Needed because the
  countable Baire step requires each degeneracy locus to be *closed*, which density alone does not
  give. `abs_exp_sub_exp_le`: `|exp a - exp b| <= 2 exp b |a-b|` for unit-length increments, from
  `Real.abs_exp_sub_one_le` after factoring `exp a - exp b = exp b (exp(a-b) - 1)`.
  `norm_herglotzJetMap_sub_le`: on the unit ball around any base parameter each jet coordinate is
  Lipschitz in the parameter, with explicit constant `2 B_s int exp(u_0)|w|`. No dominated
  convergence or compactness argument is used — the estimate is uniform and explicit.
  Remaining for the countable statement: package this as topological continuity of
  `herglotzJetMap`, conclude each degeneracy locus is closed with empty interior (interior empty is
  exactly `dense_nondegenerate_herglotzJetMap`), hence nowhere dense, then intersect over a
  countable pattern family with `dense_setOf_forall_notMem_of_isNowhereDense`. Also still open:
  rank-defect codimension, and the bridge from jet nondegeneracy to the card's
  `MaximalTranslationDifferentialFree` predicate.
- 2026-07-19 — **countable genericity for the Herglotz chart is closed**, unconditionally, in
  `formal/GaloisForLFunctions/HTGeometry/HerglotzCountableGenericity.lean`.
  `continuous_herglotzJetMap` packages the Lipschitz estimate as topological continuity, so each
  degeneracy locus is closed; its interior is empty by the single-relation density theorem; hence
  each is nowhere dense, and `dense_setOf_forall_notMem_of_isNowhereDense` intersects them.
  `dense_countable_nondegenerate_herglotzJetMap`: for a base measure of infinite support with a
  strictly positive integrable Nevanlinna density, the bounded parameters on which *every* member of
  a countable family of nonzero polynomial jet relations fails to degenerate are dense in
  `L^infinity(mu;R)`. This is the analytic engine the card's comeagerness claim rests on, now
  unconditional and axiom-clean.
  What this is NOT yet: the card's own statement. Two gaps remain.
  (1) The bridge from jet nondegeneracy to `MaximalTranslationDifferentialFree` — the card asserts
  differential-algebraic independence of the full complex translation orbit, and the finite
  differential patterns of that predicate must be shown to be exactly a countable family of nonzero
  polynomial jet relations in the sense above. That identification is not written.
  (2) Rank-defect codimension, untouched.
- 2026-07-19 — started the bridge to the card's own predicate. Analysis first: reaching
  `MaximalTranslationDifferentialFree` goes through `maximalTranslationDifferentialFree_of_fullRankWitness`,
  whose witness is nonsingularity of a matrix built from `probabilityCarrierExpandedPacketValue` —
  which is *iterated derivatives* of the Cauchy transform at shifted nodes, while all the
  controllability work is in *kernel powers*. The two differ by a factorial.
  First piece Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/CauchyTransformIteratedDeriv.lean`:
  `hasDerivAt_cauchyKernelMoment` — differentiating the `k`-th kernel moment gives `k+1` times the
  `(k+1)`-st, by the same dominated-derivative argument as the first derivative, with kernel powers
  uniformly bounded off the axis. Iterating this gives the factorial identification.
  Two obstacles now identified for the rest of the bridge, neither yet addressed:
  (a) the freeness predicate quantifies over *all* shift configurations, an uncountable family, so
  Baire does not apply directly — the card's paper proof uses a compact exhaustion of shift space
  plus continuity in the shift to reduce to countably many conditions, and that reduction is not
  formalized;
  (b) each pattern determinant must be shown to be a *nonzero* polynomial in the jet coordinates,
  which is the finite-dimensional nondegeneracy input.
  Also still open: rank-defect codimension.
- 2026-07-19 — the factorial dictionary is closed:
  `CauchyTransformIteratedDeriv.iteratedDeriv_cauchyTransform` —
  `iteratedDeriv k (cauchyTransform nu) z = k! * cauchyKernelMoment nu k z` off the real axis, by
  induction on `k` using `hasDerivAt_cauchyKernelMoment` and the fact that the off-axis set is open,
  so the inductive hypothesis holds on a neighbourhood and `EventuallyEq.deriv_eq` applies.
  This is the exact translation between the freeness predicate (iterated derivatives) and the
  controllability theory (kernel powers), so `probabilityCarrierExpandedPacketValue` is now
  expressible in the coordinates all the genericity work uses.
  Still open, unchanged from the previous entry:
  (a) the uncountable quantification over shift configurations in
  `MaximalTranslationDifferentialFree` — needs the compact-exhaustion-plus-continuity reduction from
  the paper proof before the countable Baire result can apply;
  (b) nonvanishing of each pattern determinant as a polynomial in the jet coordinates;
  (c) rank-defect codimension.
- 2026-07-19 — obstacle (a) resolved structurally, Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/CompactPatchGenericity.lean`. Re-reading the paper proof
  (section 3, "Baire completion") shows the reduction is not "the uncountable family is countably
  determined" but rather: over a *compact patch* of shift space the good set is not merely dense but
  **open**, and countably many compact patches exhausting the space give countably many open dense
  sets, which Baire intersects.
  `isOpen_setOf_forall_mem_compact_ne_zero`: for a jointly continuous test function, the parameters
  at which it avoids zero on all of a compact patch form an open set — this is the tube lemma, via
  `IsCompact.eventually_forall_of_forall_eventually`.
  `dense_setOf_forall_mem_iUnion_compact_ne_zero` and
  `dense_setOf_forall_ne_zero_of_compactExhaustion` then give density over the union, and over the
  whole parameter space when the patches cover it. Stated abstractly — the only inputs are joint
  continuity and compactness of each patch — so it is reusable well beyond this card.
  Remaining for the card: instantiate this with the shift configuration space (exhibit a compact
  exhaustion of `Conf_m(C)` and joint continuity of the pattern determinant in
  parameter-and-shift), plus (b) nonvanishing of each pattern determinant as a polynomial in the jet
  coordinates, and (c) rank-defect codimension.
- 2026-07-19 — node-variable regularity added to `CauchyTransformIteratedDeriv`:
  `differentiableOn_cauchyKernelMoment`, `analyticOnNhd_cauchyKernelMoment`,
  `continuousOn_cauchyKernelMoment` — each kernel moment is analytic, hence continuous, in the node
  off the real axis, straight from `hasDerivAt_cauchyKernelMoment`. This is the shift-variable half
  of the joint continuity that `CompactPatchGenericity` consumes.
  Remaining for the compact-patch instantiation: combine this with the parameter-side Lipschitz
  estimate (`norm_herglotzJetMap_sub_le`) into *joint* continuity in (parameter, shift). Separate
  continuity does not imply joint, but the Lipschitz constant `2 B_s int exp(u_0)|w|` is uniform in
  the node once the node stays in a compact set away from the axis, which is exactly the
  local-uniformity needed; that combination is not yet written. Then: a compact exhaustion of the
  shift configuration space, plus (b) nonvanishing of each pattern determinant as a polynomial in
  the jet coordinates, and (c) rank-defect codimension.
- 2026-07-19 — the joint-continuity principle is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/JointContinuityFromLipschitz.lean`:
  `continuousAt_uncurry_of_lipschitz_of_continuousAt`. Separate continuity in each variable does not
  give joint continuity; what does is continuity in one variable plus a Lipschitz estimate in the
  other that is *uniform* over a neighbourhood of the first. The triangle inequality then splits the
  increment into a Lipschitz part and a one-variable continuity part. Stated abstractly over a
  metric first factor and an arbitrary topological second factor, so it is reusable.
  This is exactly the shape the Cauchy-jet family has: the parameter estimate
  `norm_herglotzJetMap_sub_le` is Lipschitz with constant `2 B_s int exp(u_0)|w|`, and `B_s` is
  uniform once the node stays in a compact set off the real axis, while
  `continuousOn_cauchyKernelMoment` gives the node-variable continuity.
  Remaining: instantiate this principle at the jet family to obtain joint continuity in
  (parameter, shift) with an explicit uniform `L` on a compact node patch — the estimate exists but
  the uniform-`L` bookkeeping over the patch is not written; then a compact exhaustion of the shift
  configuration space feeds `CompactPatchGenericity`. Also still open: (b) nonvanishing of each
  pattern determinant as a polynomial in the jet coordinates, (c) rank-defect codimension.
- 2026-07-19 — consolidation and a reuse finding for (b). Audit: all modules added for this card
  build clean and every umbrella import took — the project lint gate reports no unreachable module
  among them (its four unreachable-module errors are other agents' RHTower files, and the
  generated-index staleness is a race with concurrent edits, not a defect in this work).
  Reuse finding: obstacle (b) is largely already served by
  `HTGeometry.PolynomialRelationDetector.exists_upper_noncolliding_polynomial_detector` — given a
  nonzero polynomial-coefficient relation and an injective shift family, it produces a base node `z`
  with the specialization nonzero, all shifted nodes `z + shift i` distinct, and all in the open
  upper half-plane. That is exactly the node-placement nondegeneracy the pattern determinant needs;
  what remains for (b) is to identify the pattern determinant with such a polynomial-coefficient
  relation, not to prove a new nondegeneracy result.
  Remaining overall: instantiate `JointContinuityFromLipschitz` at the jet family with a uniform
  Lipschitz constant over a compact node patch; a compact exhaustion of the shift configuration
  space feeding `CompactPatchGenericity`; the (b) identification above; and (c) rank-defect
  codimension.
- 2026-07-19 — the uniformity hypothesis for joint continuity is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/CompactNodePatchBounds.lean`. The Lipschitz constant of the
  jet map depends on the node through the kernel bound, so it is not uniform on its face; restricting
  the node to a compact set off the real axis repairs it. `exists_pos_le_abs_im_of_compact`: distance
  to the axis attains a positive minimum on such a patch (via `IsCompact.exists_isMinOn`, with the
  empty patch handled separately). `exists_uniform_kernelPow_bound`: hence every kernel power is
  bounded by one constant `(c^{-1})^{k+1}` across the whole patch.
  This supplies exactly the uniform `L` that
  `JointContinuityFromLipschitz.continuousAt_uncurry_of_lipschitz_of_continuousAt` requires, so the
  three ingredients for joint continuity in (parameter, shift) are now all present: parameter-side
  Lipschitz (`norm_herglotzJetMap_sub_le`), node-side continuity
  (`continuousOn_cauchyKernelMoment`), and patch uniformity (this module). Assembling them into a
  single joint-continuity statement for the jet family is the next step and is not yet written.
  Then: compact exhaustion of shift configuration space into `CompactPatchGenericity`; the (b)
  identification against `exists_upper_noncolliding_polynomial_detector`; and (c) rank-defect
  codimension.
- 2026-07-19 — the parameter-side input for joint continuity is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/NodeJetUniformLipschitz.lean`. `nodeJet` reads the jet of
  order `k` at a single node, `integrable_nodeJet_integrand` gives integrability off the axis, and
  `norm_nodeJet_sub_le_uniform` is the Lipschitz estimate in the parameter with constant
  `2 B int exp(u_0)|w|` — *independent of the node*, valid for every node in the patch. The proof
  uses only the uniform kernel bound, so compactness of the patch is not a hypothesis; it enters
  solely through `exists_uniform_kernelPow_bound`, which produces the bound. Dropping the
  compactness and positivity hypotheses the first draft carried makes the lemma apply to any node
  set admitting a uniform bound.
  All three inputs of `continuousAt_uncurry_of_lipschitz_of_continuousAt` are now available in
  matching form for `nodeJet`: uniform Lipschitz in the parameter (this module), continuity in the
  node (`continuousOn_cauchyKernelMoment`, after identifying `nodeJet` with a kernel moment of the
  reweighted measure), and the neighbourhood supplied by a compact patch. The one remaining glue
  step is that identification of `nodeJet` with `cauchyKernelMoment` of `mu.withDensity (exp u * w)`,
  which is a `withDensity` integral transfer of the kind already done in
  `RegularizedHerglotzTransform`. Then: compact exhaustion of shift configuration space into
  `CompactPatchGenericity`; the (b) identification; and (c) rank-defect codimension.
- 2026-07-19 — the glue step is done: `nodeJet_eq_cauchyKernelMoment` identifies the node jet with
  the kernel moment of `expWeightedMeasure mu w u = mu.withDensity (exp u * w)`, by the
  `withDensity` integral transfer (`integral_withDensity_eq_integral_smul0`, the AEMeasurable form,
  since an `L^infinity` class gives only a.e. measurability). Consequently every node-variable
  regularity statement proved for kernel moments — differentiability, analyticity, continuity —
  transfers to the node jet.
  With this, all inputs of `continuousAt_uncurry_of_lipschitz_of_continuousAt` are present for
  `nodeJet` in matching form: uniform Lipschitz in the parameter, continuity in the node, and the
  neighbourhood from a compact patch. Writing the resulting joint-continuity statement is
  bookkeeping over three named lemmas; it is the immediate next step.
  Then: compact exhaustion of shift configuration space into `CompactPatchGenericity`; the (b)
  identification of the pattern determinant with a polynomial-coefficient relation, against
  `exists_upper_noncolliding_polynomial_detector`; and (c) rank-defect codimension.
- 2026-07-19 — two blockers to the joint-continuity assembly removed, both Lean-checked.
  First, `JointContinuityFromLipschitz.continuousAt_uncurry_of_lipschitz_of_continuousAt` demanded a
  Lipschitz bound for *all* parameters, but `norm_nodeJet_sub_le_uniform` gives one only for
  `||u - u_0|| <= 1`. The lemma was revised to take the bound on a ball of radius `r > 0` around the
  base point, intersecting that ball with the epsilon-ball in the proof. This is the correct form —
  continuity at a point is local, so a global hypothesis was never appropriate.
  Second, `isFiniteMeasure_expWeightedMeasure`: the parameter's measure is finite, since
  boundedness of the parameter makes `exp u * w` integrable and
  `ofReal_integral_eq_lintegral_ofReal` converts that to finiteness of the density's lintegral.
  This is what lets the kernel-moment regularity results (which assume `IsFiniteMeasure`) apply to
  `expWeightedMeasure`, hence via `nodeJet_eq_cauchyKernelMoment` to the node jet.
  Every hypothesis of the joint-continuity principle is now available for `nodeJet` in the exact
  form required. Remaining: state the joint-continuity corollary; compact exhaustion of shift
  configuration space into `CompactPatchGenericity`; the (b) identification; and (c) rank-defect
  codimension.
- 2026-07-19 — **joint continuity of the node jet is proved**:
  `NodeJetUniformLipschitz.continuousAt_nodeJet_uncurry` — in the interior of a compact node patch
  off the real axis, the node jet is continuous in parameter and node *jointly*. It combines the
  three pieces built over the last turns: uniform Lipschitz in the parameter over the patch,
  continuity in the node (via `nodeJet_eq_cauchyKernelMoment` and finiteness of
  `expWeightedMeasure`), and the joint-continuity criterion.
  This is the hypothesis `CompactPatchGenericity.isOpen_setOf_forall_mem_compact_ne_zero` needs, so
  the compact-patch reduction can now be instantiated at the Herglotz jet family.
  Remaining: compact exhaustion of the shift configuration space feeding
  `CompactPatchGenericity`; the (b) identification of the pattern determinant with a
  polynomial-coefficient relation, against `exists_upper_noncolliding_polynomial_detector`; and
  (c) rank-defect codimension.
- 2026-07-19 — the compact exhaustion is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/UpperHalfPlaneExhaustion.lean`: the patches
  `upperPatch m = {z : 1/(m+1) <= Im z and ||z|| <= m+1}` are compact
  (`isCompact_upperPatch`, closed and bounded in the proper space `C`), each is bounded away from
  the real axis (`upperPatch_im_ne_zero` — the second hypothesis every kernel bound needs), and they
  exhaust the open upper half-plane (`iUnion_upperPatch`).
  Together with `continuousAt_nodeJet_uncurry` this supplies both hypotheses of
  `CompactPatchGenericity.dense_setOf_forall_ne_zero_of_compactExhaustion` for the node variable:
  countably many compact patches covering the region, and joint continuity on each. The remaining
  hypothesis there is per-patch density, which is what the single-relation genericity theorem
  provides.
  Remaining: assemble those into node-uniform genericity; then (b) the identification of the
  pattern determinant with a polynomial-coefficient relation, against
  `exists_upper_noncolliding_polynomial_detector`; and (c) rank-defect codimension.
- 2026-07-19 — the node-variable reduction is complete.
  `CompactPatchGenericity`'s continuity hypothesis was too strong to instantiate: it demanded global
  joint continuity, while the jet family is only jointly continuous near the upper half-plane. It
  now takes the pointwise form actually used in the proof — joint `ContinuousAt` at each point of
  the patch — which is both weaker and sufficient.
  `UpperHalfPlaneExhaustion.dense_setOf_forall_upperHalfPlane_ne_zero`: if nonvanishing is dense
  over each compact patch and jointly continuous along it, it is dense over the *entire* open upper
  half-plane. Also `upperPatch_subset_interior_succ`, since each patch sits inside the interior of
  the next — needed because the joint-continuity result requires the node in the interior of the
  patch supplying the uniform bound, so consecutive patches are used for the two roles.
  So the uncountable node quantifier is now fully reduced to countably many dense conditions, with
  every hypothesis available for the Herglotz jet family.
  Remaining: (b) identification of the pattern determinant with a polynomial-coefficient relation,
  against `exists_upper_noncolliding_polynomial_detector`; and (c) rank-defect codimension.
- 2026-07-19 — item (c) opened. Reading the card's section around (H6): the codimension estimate for
  the rank-defect locus rests on two elementary facts about a projective coefficient vector — a
  nonzero tuple of polynomials `c_beta` of degree at most `q`. Both are now Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/RankDefectAlgebraicCore.lean`:
  `finite_common_roots_of_exists_ne_zero` — the indices where *every* `c_beta` vanishes are finite,
  since one member is a nonzero polynomial and so has finitely many roots (with
  `common_roots_subset_roots` giving the containment that bounds the count by the degree); and
  `sum_monomial_ne_zero` / `sum_eval_monomial_ne_zero` — at any index where some `c_beta` survives,
  the combination `sum_beta c_beta(z) M_beta` is a nonzero polynomial, because distinct monomial
  exponents make the coefficient at `M_beta0` equal `c_beta0(z)`.
  Together these are the nondegeneracy driving the codimension count: the projective incidence
  condition fails at only boundedly many indices.
  Explicitly NOT formalized: the layers built on this count — Whitney stratification of the
  rank-defect locus, real codimension of the strata, and the parametric-transversality step that
  uses `codim > dim_R U` to empty the transverse preimages. Those need differential-topology
  machinery (stratified sets, Sard/transversality) that mathlib does not currently carry, so (c)
  remains substantially open even though its algebraic core is now done.
  Also still open: (b) the identification of the pattern determinant with a polynomial-coefficient
  relation.
- 2026-07-19 — (b) bridged, and a correction to the previous entry's pessimism about (c).
  `sum_coeff_mul_expandedDifferentialEvaluationMatrix`: reading one row of the expanded evaluation
  matrix against a coefficient vector is *exactly* the evaluation of `sum_beta c_beta(z_b) M_beta`,
  where `c_beta(z) = sum_d coeff(beta,d) z^d` has degree at most `q` — i.e. the matrix relation is
  literally the projective coefficient vector of the card's (H6). With
  `expandedRelation_nonzero_polynomial`, a row whose coefficient polynomial survives forces the jets
  into the zero set of a *nonzero* polynomial.
  Correction: the previous entry judged (c) substantially open pending Whitney stratification and
  parametric transversality. On this formalization route that machinery appears unnecessary. The
  paper needs codimension-plus-transversality because it linearizes the chart; the route here
  replaced linearization by exact affine reachability, so "the bad set is small" is delivered
  instead by `mvPolynomial_zero_set_isNowhereDense` plus Baire. What is actually required is only
  that the relation polynomial be nonzero — which is what the two lemmas above supply. Stated as an
  assessment, not a proved reduction: the remaining work is to run the chain
  coeff != 0 => some c_beta != 0 => c_beta has at most q roots => all but boundedly many rows
  survive => generic jets violate the relation, and confirm no stratification enters.
- 2026-07-19 — the first half of the (b)/(c) chain is Lean-checked, without stratification.
  `rowCoefficientPoly` realizes the coefficient polynomial as an honest `Polynomial C` of degree at
  most `q`, with `eval_rowCoefficientPoly` matching it to the evaluation form used by the matrix
  identity. `rowCoefficientPoly_ne_zero`: a single nonzero entry of the coefficient vector makes
  that polynomial nonzero (its `d0`-th coefficient is that entry). `finite_degenerate_rowNodes`:
  hence the row nodes at which *every* coefficient polynomial vanishes form a finite set.
  Combined with `expandedRelation_nonzero_polynomial` this is the card's (H6) mechanism in full:
  a nonzero coefficient vector degenerates at only finitely many row nodes, and at every other node
  the relation is the vanishing of a nonzero polynomial in the jet variables — which the genericity
  machinery already handles via nowhere-density plus Baire, with no codimension count and no
  Whitney strata. The assessment recorded last entry now has its algebraic half proved; what
  remains is to thread it through the pattern predicate rather than to build new theory.
- 2026-07-19 — the row-level bridge is Lean-checked.
  `expandedRelation_forces_jet_in_zeroSet`: at a row whose coefficient polynomial survives, an
  expanded pattern relation says *exactly* that the row's jet vector lies in the zero set of a
  nonzero multivariate polynomial — the conjunction is stated so both halves are available, the
  nonzero-ness and the vanishing. `finite_rows_without_surviving_coefficient`: for a nonzero
  coefficient vector the rows where this does not apply are finite.
  So the (H6) mechanism is now complete as Lean theorems, in the exact vocabulary of the corpus's
  `expandedDifferentialEvaluationMatrix`, and with no codimension or stratification anywhere.
  What remains to reach `MaximalTranslationDifferentialFree`: choose an admissible row packet whose
  nodes avoid the finite bad set (the packet type carries an upper-half-plane admissibility
  condition, so this is a placement argument, and `exists_upper_noncolliding_polynomial_detector`
  is the corpus tool for exactly that placement), then feed the resulting nonzero polynomial to the
  genericity theorems. That is the last structural step for the freeness predicate; after it, the
  card's statement follows by the chain already built.
- 2026-07-19 — the packet placement engine is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/PacketPlacementAvoidance.lean`. A row packet is just an
  injective family of complex numbers, so placement is free; the constraint is to dodge the finite
  bad set of the rank-defect mechanism while sitting high enough for upper-half-plane
  admissibility. Vertical translation does both at once:
  `finite_translations_into_finite` (a vertical line meets a finite set finitely often),
  `exists_translation_avoiding_finite` (finitely many rows give a finite union of bad heights, and
  heights above any bound are infinite), `injective_translate` (translation preserves injectivity),
  and `exists_translation_upper_and_avoiding`, which produces a single height putting every
  row-plus-shift node strictly in the upper half-plane while keeping all rows off the bad set — the
  height threshold being the total absolute imaginary mass of rows and shifts.
  This supplies the placement step flagged last entry. What remains to reach
  `MaximalTranslationDifferentialFree` is assembly: instantiate the placement at the bad set from
  `finite_degenerate_rowNodes`, apply `expandedRelation_forces_jet_in_zeroSet` at a surviving row,
  and contradict it with the genericity theorems. No further structural ingredient is outstanding
  for the freeness predicate.
- 2026-07-19 — placement and rank-defect are now joined:
  `exists_placed_packet_all_rows_nondegenerate`. Given a nonzero coefficient vector, a single
  vertical translation simultaneously lifts an arbitrary injective row family into admissible
  position (all row-plus-shift nodes strictly in the upper half-plane) and carries it off the finite
  degenerate set, so at *every* row the relation polynomial is nonzero — not merely at all but
  finitely many. That stronger form is what makes the downstream contradiction uniform in the row.
  With this the ingredient list for the freeness predicate is closed. The remaining work is the
  final derivation: given a pattern relation with nonzero coefficient vector, place the packet,
  read off a row via `expandedRelation_forces_jet_in_zeroSet`, and contradict with the countable
  genericity theorem. The one piece of genuine care left is matching the corpus's
  `probabilityCarrierExpandedPacketValue` (iterated derivatives at shifted nodes) to the jet
  coordinates of the genericity theorem, for which `iteratedDeriv_cauchyTransform` supplies the
  factorial dictionary and `nodeJet_eq_cauchyKernelMoment` the measure identification.
- 2026-07-19 — the packet-value bridge is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/PacketValueFactorialBridge.lean`.
  `probabilityCarrierExpandedPacketValue_eq_factorial_moment`: off the real axis, the corpus's
  carrier packet value — an iterated derivative of the Cauchy transform at a row-plus-shift node —
  is the factorial of its jet order times the corresponding kernel moment. With `packetNode` and
  `packetOrder` naming the two projections of a packet coordinate, the statement is in the corpus's
  own vocabulary, so a pattern relation can now be read directly as a condition on kernel-moment
  coordinates, which is the form the genericity theorems refute.
  This was the step flagged as needing care; it went through by definitional unfolding onto
  `iteratedDeriv_cauchyTransform`, the factorial dictionary proved earlier.
  Remaining for the freeness predicate: the final derivation — take a pattern relation with nonzero
  coefficient vector, place the packet with
  `exists_placed_packet_all_rows_nondegenerate`, convert the packet values by this bridge, read a
  row via `expandedRelation_forces_jet_in_zeroSet`, and contradict with countable genericity. All
  named ingredients now exist and are axiom-clean.
- 2026-07-19 — the rank-defect mechanism is now a statement about the actual carrier:
  `formal/GaloisForLFunctions/HTGeometry/PatternRelationConfinement.lean`,
  `exists_placed_relation_forcing_zeroSet`. Given a pattern relation with a nonzero coefficient
  vector, the row packet can be placed so that every row node is admissible (so the relation's own
  quantifier applies to it) and misses the finite degenerate set; the relation then says, at *every*
  row, that the carrier's jet vector lies in the zero set of a nonzero multivariate polynomial.
  This is the exact shape the genericity theorems refute, stated against the corpus's
  `probabilityCarrierExpandedPacketValue`, so the two halves of the development finally meet on one
  object.
  What is left for `MaximalTranslationDifferentialFree` is to run the refutation: for a carrier in
  the generic set, no nonzero polynomial vanishes on its jets, so the coefficient vector cannot have
  a nonzero entry. The remaining care is indexing — the genericity theorems speak of jets in the
  `jetIndex`/kernel-moment coordinates while this theorem speaks of packet coordinates, and
  `probabilityCarrierExpandedPacketValue_eq_factorial_moment` is the dictionary between them (a
  nonzero factorial rescaling, so it does not affect vanishing).
  Beyond the freeness predicate the card also needs the Krein-index chamber half, untouched.
- 2026-07-19 — the refutation step is Lean-checked.
  `CarrierJetNondegenerateAt` names the property the genericity theorems establish: at every
  admissible packet, no nonzero polynomial vanishes on the carrier's jet vector.
  `coeff_eq_zero_of_relation_of_jetNondegenerate`: a carrier with that property admits no pattern
  relation with a nonzero coefficient — the placement theorem would otherwise manufacture exactly
  such a vanishing polynomial. So the rank-defect side is now fully reduced to the genericity side.
  Scope, stated precisely. This theorem takes three inputs that are *not* discharged here:
  (i) `CarrierJetNondegenerateAt` for the carrier — supplied in substance by
  `dense_countable_nondegenerate_herglotzJetMap` together with the factorial dictionary, but the
  indexing translation between packet coordinates and `jetIndex` coordinates is not yet written;
  (ii) injectivity of the pattern's exponent map, a property of `carrierPatternExponent` not yet
  checked; (iii) an initial injective row family, which exists since `row` is finite and `C`
  infinite but is passed in rather than constructed.
  Discharging (i)-(iii) turns this into `MaximalTranslationDifferentialFree` via
  `maximalTranslationDifferentialFree_of_fullRankWitness`'s sibling route. Beyond that the card
  still needs the Krein-index chamber half, untouched.
- 2026-07-19 — two of the three inputs flagged last entry are discharged, and the statement is
  consolidated. Input (ii) was already in the corpus:
  `AnalyticNevanlinnaCarrierRelationFree.carrierPatternExponent_injective`. Input (iii) is now
  constructed (`exists_injective_complexFamily`: a finite index type admits an injective family of
  complex numbers, via `Fintype.equivFin` and the injectivity of the natural cast into `C`).
  Result: `maximalTranslationDifferentialFree_of_jetNondegenerate` derives
  `MaximalTranslationDifferentialFree nu` from a *single* hypothesis — that the carrier's jets are
  nondegenerate against every nonzero polynomial, at every pattern and shift configuration. The
  whole rank-defect, placement, and confinement apparatus is now behind that one interface.
  The single remaining input for the freeness predicate is therefore input (i): establish
  `CarrierJetNondegenerateAt` for a generic carrier, by translating
  `dense_countable_nondegenerate_herglotzJetMap` from `jetIndex`/kernel-moment coordinates into
  packet coordinates via `probabilityCarrierExpandedPacketValue_eq_factorial_moment` (the factorial
  is nonzero, so it does not affect vanishing).
  Beyond the freeness predicate the card still needs the Krein-index chamber half, untouched.
- 2026-07-19 — the coordinate translation is Lean-checked in
  `formal/GaloisForLFunctions/HTGeometry/PolynomialVariableRescale.lean`. Packet values differ from
  kernel moments by a factorial in each coordinate, so the two coordinate systems differ by a
  diagonal rescaling of the polynomial variables. `scaleSubst` is that rescaling;
  `scaleSubst_scaleSubst` shows rescaling by reciprocals inverts it (hence it is an automorphism),
  `scaleSubst_ne_zero` that it preserves being nonzero, `eval_scaleSubst` that evaluating a rescaled
  polynomial is evaluating the original at the rescaled point, and `eval_ne_zero_of_scaled` packages
  the transport: nondegeneracy at one coordinate system gives nondegeneracy at the other.
  This is the mathematical content of the last outstanding input for the freeness predicate. What
  remains is bookkeeping: instantiate the rescaling with the factorial of the packet order (nonzero
  by `Nat.factorial_ne_zero`), apply `probabilityCarrierExpandedPacketValue_eq_factorial_moment`
  coordinatewise, and read `CarrierJetNondegenerateAt` off
  `dense_countable_nondegenerate_herglotzJetMap`.
  Beyond the freeness predicate the card still needs the Krein-index chamber half, untouched.
- 2026-07-19 — the freeness side is closed down to a single analytic interface.
  `carrierJetNondegenerateAt_of_momentNondegenerate` transfers nondegeneracy from kernel-moment
  coordinates to packet coordinates (packet values are factorial multiples of moments, factorials
  are nonzero, so the systems differ by an invertible diagonal rescaling), and
  `maximalTranslationDifferentialFree_of_momentNondegenerate` composes it with the refutation:
  a carrier whose *kernel moments* are nondegenerate against every nonzero polynomial, at every
  pattern and admissible packet, is maximally translation-differentially free.
  That hypothesis is stated in exactly the vocabulary the analytic genericity development uses, so
  the algebraic and analytic halves of this session's work now meet at one interface. Everything
  from the rank-defect mechanism through placement, confinement, refutation and coordinate transfer
  is behind it, unconditional and axiom-clean.
  Remaining for the predicate: supply that hypothesis for a generic carrier from
  `dense_countable_nondegenerate_herglotzJetMap`. This is not yet a formality — the genericity
  theorem produces a dense set of *parameters* with a fixed countable polynomial family, while the
  interface quantifies over all patterns, shifts and packets, so the countable family must be chosen
  to cover the pattern enumeration. Beyond the predicate the card still needs the Krein-index
  chamber half, untouched.
- 2026-07-19 — the pattern quantifier is discharged. `Countable (FiniteDifferentialPattern Gamma)`
  for countable `Gamma` was already in the corpus (`CountableDifferentialPattern`), and `Unit` is
  countable, so the freeness predicate's outermost quantifier is countable after all.
  `formal/GaloisForLFunctions/HTGeometry/PatternIndexedBaire.lean` uses this:
  `dense_setOf_forall_pattern` (a property open and dense for each pattern holds densely for all
  patterns at once) and `dense_setOf_forall_pattern_and_index`, the form produced by pairing the
  pattern quantifier with a compact exhaustion — the two countable quantifiers are intersected
  together rather than in sequence.
  This resolves the concern recorded last entry, that the genericity theorem fixes one countable
  polynomial family while the interface ranges over all patterns: the pattern index can simply be
  carried into the Baire intersection. What remains is to produce, for each fixed pattern and patch,
  the open dense set — openness from `isOpen_setOf_forall_mem_compact_ne_zero` with the joint
  continuity already proved, density from `dense_nondegenerate_herglotzJetMap` — and then feed
  `maximalTranslationDifferentialFree_of_momentNondegenerate`.
  Beyond the freeness predicate the card still needs the Krein-index chamber half, untouched.
- 2026-07-19 — **CORRECTION: the interface built over the previous three entries is vacuous.**
  `CarrierJetNondegenerateAt` asks that *no* nonzero polynomial vanish on the carrier's jet vector.
  That is unsatisfiable: for any point `y` of a nonempty jet index, `X s - C (y s)` is a nonzero
  polynomial vanishing at `y`. Verified in Lean by explicit construction before recording this.
  Consequently `carrierJetNondegenerateAt_of_momentNondegenerate`,
  `maximalTranslationDifferentialFree_of_jetNondegenerate` and
  `maximalTranslationDifferentialFree_of_momentNondegenerate` are true implications with
  unsatisfiable hypotheses — they do not advance the card, and the genericity development cannot
  supply what they ask. The definition now carries a warning docstring recording the dead end.
  Where the reasoning went wrong: `coeff_eq_zero_of_relation_of_jetNondegenerate` needs
  nonvanishing only for the specific polynomials arising from coefficient vectors, and I
  generalized that to all nonzero polynomials when naming the interface — which is strictly
  stronger and false. The genuinely correct nondegeneracy is rank-theoretic: the expanded
  evaluation matrix should have a nonvanishing minor, one polynomial condition per pattern and
  packet rather than one per coefficient vector. That is exactly the corpus's
  `probabilityCarrierExpandedFullRankWitness` / `MaximalTranslationFullRankWitness`, reached by
  `maximalTranslationDifferentialFree_of_fullRankWitness`, and it is the shape
  `dense_nondegenerate_herglotzJetMap` can actually feed.
  Still valid and unaffected: everything below the interface — the rank-defect mechanism, placement,
  confinement, the factorial dictionary, the rescaling transport, and the whole analytic genericity
  chain. The next step is to restate the interface through the full-rank witness.
- 2026-07-19 — **SECOND CORRECTION, and it retracts an earlier one.** Verified in Lean: with two or
  more monomial slots, a *single* row admits a nonzero annihilating coefficient vector for any
  evaluated monomial data (one linear form on a space of dimension >= 2 has nontrivial kernel). So
  `expandedRelation_forces_jet_in_zeroSet`, which extracts one row, is true but can never conclude
  `coeff = 0`. The multi-row system is essential, not a convenience.
  This retracts the 2026-07-19 entry claiming "(c) dissolves — no codimension count needed". That
  claim was based on replacing the multi-row rank condition by a per-row polynomial condition, which
  the above shows is impossible. The multi-row rank-defect analysis the codimension count performs
  is doing real work and cannot be bypassed that way.
  Status of the two corrections, stated so the record is unambiguous.
  VERIFIED: the `forall Q != 0` interface is vacuous; single-row nondegeneracy is unsatisfiable.
  OPEN: the correct condition is that some maximal *minor* of the multi-row expanded evaluation
  matrix is a nonzero polynomial in the jet variables — a generalized-Vandermonde statement from
  distinct nodes plus distinct monomials. Whether the Baire route then needs only that (weaker than
  the full codimension count, and plausibly free of Whitney strata) or genuinely needs the paper's
  stratified transversality is NOT settled, and I have twice guessed wrong about it. It should be
  decided by attempting the minor-nonvanishing lemma, not by argument.
  Unaffected and still valid: the analytic genericity chain end to end, the rank-defect algebraic
  core, placement, the factorial dictionary, the rescaling transport, and the pattern-indexed Baire
  step. What is broken is only the bridge from those to the freeness predicate.
- 2026-07-19 — attempted the multi-row lemma rather than arguing about it, per the previous entry,
  and the key tool turned out to be one generalization away in the corpus.
  `PrimeValuationProfileRankLaw.exists_injective_evaluation_minor_of_linearIndependent_profiles`
  gives: a finite linearly independent family of scalar *sequences* has a nonsingular evaluation
  minor at pairwise distinct natural coordinates. Its proof never uses anything about the index
  type, so
  `formal/GaloisForLFunctions/HTGeometry/EvaluationMinorGeneralDomain.lean` restates it verbatim for
  an arbitrary domain: `exists_injective_evaluation_minor_of_linearIndependent`. It compiled
  unchanged.
  This is the tool the multi-row rank condition needs: the sample points there are complex nodes,
  not natural coordinates. The route is now concrete — distinct monomials are linearly independent
  as functions on the jet space (`sum_monomial_ne_zero` is the coefficient-detection half of this),
  so this theorem produces nodes at which the evaluation matrix is nonsingular, which is exactly
  `probabilityCarrierExpandedFullRankWitness`.
  Not yet done, and not to be assumed: the linear independence input must be established for the
  *specific* family indexed by (monomial, coefficient degree) — entries `z^d M_beta(y)` — whose
  independence mixes the `z`-powers with the monomials. That is the remaining mathematical content,
  and it is where the paper's codimension count does its work.
- 2026-07-19 — the linear independence flagged above as "the remaining mathematical content" is
  proved. `formal/GaloisForLFunctions/HTGeometry/MonomialPowerIndependence.lean`:
  `linearIndependent_pow_mul_monomial` — the family `(beta,d) |-> ((z,y) |-> z^d * M_beta(y))` is
  linearly independent over C. The argument separates the two variables and needs no codimension
  count: fixing `y`, a vanishing combination is a polynomial in `z` vanishing identically on C, so
  each coefficient in `z` vanishes (`powerCoeffs_eq_zero_of_eval_eq_zero`, via the corpus's
  `rowCoefficientPoly_ne_zero` plus `Polynomial.funext`); each such coefficient is a combination of
  distinct monomials in `y` vanishing identically, so its coefficients vanish
  (`monomial_coeffs_eq_zero_of_eval_eq_zero`, via `MvPolynomial.funext` plus the corpus's
  `sum_monomial_ne_zero`). Compiled first try.
  Worth recording against the previous entry's expectation: the mixing of z-powers with monomials,
  which I flagged as the hard part and as the place "where the paper's codimension count does its
  work", is not hard and needs no codimension count. The two variables simply separate. The paper's
  stratified count is doing something the Lean route does not need here.
- 2026-07-19 — bridged that to the matrix interface the freeness predicate speaks in.
  `formal/GaloisForLFunctions/HTGeometry/ExpandedMatrixFullRankNodes.lean`:
  `exists_nodes_jets_expandedMatrix_mulVec_injective` — with one row per column there exist node/jet
  sample points at which `expandedDifferentialEvaluationMatrix` has injective `mulVec`, i.e. full
  column rank. Proof: feed the independence into `exists_injective_evaluation_minor_of_linearIndependent`
  over the domain `C x (Fin n -> C)`, then transport the resulting square minor along
  `Fintype.equivFin` on the column index (`Matrix.det_submatrix_equiv_self`,
  `Matrix.mulVec_injective_iff_isUnit`). Compiled first try; axiom-clean; audit 8545/8545.
  This is the abstract core of `probabilityCarrierExpandedFullRankWitness`, and it replaces the two
  wrong nondegeneracy formulations of the earlier entries.
  TWO GAPS remain between this and the witness, both real, neither assumed:
  (a) NODE DISTINCTNESS. The minor lemma gives an injective row chart `r |-> (z r, y r)`, not
  injective nodes `z` alone, while `InjectiveProjectiveRowPacket` requires distinct nodes. Route to
  try: the determinant is a polynomial in the variables `(z_r, y_{r,k})`, nonzero since it is
  nonzero at the found point; `MvPolynomial` over C is a domain, so `det * prod_{r<s}(z_r - z_s)` is
  a nonzero polynomial and hence has a nonvanishing point, which has distinct nodes. Needs the
  determinant expressed as an `MvPolynomial` in those variables.
  (b) REACHABILITY. The witness's sample pairs are not free: row `r` has node `z r` and jet `y r`
  tied together by the carrier. The pairs must land in the image of the carrier's chart. The
  candidate tool is already in the tree — `surjective_weightedJetControl` says every finite
  Cauchy-jet vector is realized by a bounded reweighting, over a base measure of infinite support
  with a strictly positive integrable density. If that applies here then the nodes may be fixed
  first and the density chosen to realize the jets the minor lemma demands. Whether its hypotheses
  are available for this carrier family is the next thing to attempt, not to assert.
  Next move: (a) first, since it is self-contained algebra and independent of the carrier.
- 2026-07-19 — gap (a), node distinctness, is closed.
  `formal/GaloisForLFunctions/HTGeometry/ExpandedMatrixDistinctNodes.lean`:
  `exists_injective_nodes_expandedMatrix_mulVec_injective` — there are node/jet sample points with
  PAIRWISE DISTINCT nodes at which the expanded evaluation matrix has injective `mulVec`.
  Mechanism, as conjectured in the previous entry and now carried out: `expandedPolyMatrix` is the
  matrix with indeterminate node and jet coordinates over
  `MvPolynomial (row ⊕ row × Fin n) ℂ`; `eval_det_expandedPolyMatrix` (via `RingHom.map_det`) says
  its determinant evaluates to the numeric determinant. That determinant is a nonzero polynomial,
  since the previous entry's theorem supplies a point where it does not vanish. The node-difference
  product over `Finset.univ.offDiag` is nonzero as a product of nonzero factors in a domain
  (`X_sub_X_ne_zero`, by evaluating at an indicator point). `MvPolynomial` over C is a domain, so
  the product of the two is nonzero, and `exists_eval_ne_zero` (contrapositive of
  `MvPolynomial.funext`) gives a point where BOTH factors are nonzero: distinct nodes and a
  nonsingular matrix at once. Axiom-clean; audit 8546/8546; zero warnings.
  The polynomial-domain trick is worth keeping in view: it converts "two independent generic
  conditions" into one nonvanishing statement about a single product, with no measure theory,
  no Baire argument and no topology. Where else in this card is a conjunction of generic conditions
  currently being handled by a Baire intersection that this would handle algebraically instead? The
  pattern-indexed Baire step is countable and genuinely needs Baire, but the shift/packet
  quantifiers inside a single pattern may be finite conjunctions of polynomial conditions.
  Remaining: gap (b), REACHABILITY — the sample pairs must lie in the image of the carrier's chart,
  since row `r`'s node and jet are tied together by the carrier rather than free. Candidate tool
  `surjective_weightedJetControl`; whether its hypotheses (base measure of infinite support,
  strictly positive integrable density) are available for this carrier family is the next thing to
  attempt. Also still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — the density half of gap (b) is closed, modulo one named analytic input.
  `formal/GaloisForLFunctions/HTGeometry/ExpandedJetDeterminantGenericity.lean`.
  The observation that made this short: `dense_nondegenerate_of_affine_reachability` (built earlier
  in this card) consumes exactly ONE thing, a nonzero polynomial in the jets — and the distinct-node
  theorem of the previous entry is precisely a supply of that. Holding the nodes fixed at the values
  it produces, the determinant becomes a polynomial in the jet coordinates alone
  (`expandedJetPolyMatrix`, `eval_det_expandedJetPolyMatrix`), and it is nonzero as a polynomial
  because there is a jet vector where it does not vanish
  (`exists_injective_nodes_expandedJetDet_ne_zero`).
  Result: `exists_nodes_dense_expandedMatrix_mulVec_injective` — under affine jet reachability there
  are pairwise distinct nodes at which the parameters carrying FULL EXPANDED COLUMN RANK are DENSE.
  No differentiability of the jet map is used anywhere. Compiled first try; axiom-clean; audit
  8550/8550.
  This is the density half of the `hfull` hypothesis that
  `countablePatterns_relationFree_dense_residual_of_fullRankWitness` has been waiting on since it
  was written. That theorem takes dense+residual full rank and returns dense+residual
  relation-freeness, so the chain to the freeness predicate is now assembled except for two things.
  STILL OPEN, both named, neither assumed:
  (b1) THE REACHABILITY INSTANCE. `exists_nodes_dense_expandedMatrix_mulVec_injective` takes affine
  reachability as a hypothesis. It must be discharged for the actual carrier family: construct the
  multiplicative gauge `u0 + log(1+h)` on this family and verify `F(u) = F(u0) + L h` EXACTLY, with
  `L` surjective. The corpus has the pieces — `herglotzControlLinear` is the candidate `L`,
  `surjective_weightedJetControl` its surjectivity — but the exact affine identity for this chart is
  not yet proved. This is the next thing to attempt.
  (b2) THE RESIDUAL HALF. Density is proved; `hfull` also wants membership in `residual`. The
  nonsingularity set is open (the determinant is continuous in the jets — `continuous_expandedDifferentialEvaluationMatrix`
  is already in the tree), and open+dense gives residual directly, so this should be short once
  (b1) lands. Do not assume it: the openness must be transported through `F`, which needs `F`
  continuous, a hypothesis not currently carried.
  Also still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — gap (b2) is closed and gap (b1) is reduced to four checkable facts about the carrier.
  `formal/GaloisForLFunctions/HTGeometry/MultiplicativeGaugeFullRankResidual.lean`. Compiled first
  try; axiom-clean; audit 8551/8551.
  (b2) `exists_nodes_residual_expandedMatrix_mulVec_injective` — for a CONTINUOUS jet map, full
  expanded column rank is an OPEN condition (it is nonvanishing of a determinant depending
  continuously on the jets, via the tree's `continuous_expandedDifferentialEvaluationMatrix` and
  `Continuous.matrix_det`), hence with the previous entry's density it is RESIDUAL
  (`residual_of_dense_open`). The continuity of `F` that the previous entry flagged as missing is
  now carried as an explicit hypothesis, and it is discharged in the composite below.
  (b1) `affine_reachability_of_multiplicative_chart` — the reachability hypothesis is supplied by
  ANY chart that perturbs multiplicatively. If the jets are a continuous linear image `J` of a
  density and the chart moves the density from `G u0` to `G u0 + M u0 h`, then the jets move by
  exactly `J . M u0`, and surjectivity of the composite is surjectivity of the two factors. The
  proof is four lines because the identity is EXACT — this is the card's founding observation
  (the multiplicative gauge removes the linearization error) finally cashed in as a lemma rather
  than as prose.
  Composite: `exists_nodes_residual_expandedMatrix_of_multiplicative_chart` — open + dense +
  residual full expanded rank, from a continuous multiplicatively-perturbed chart. Its hypotheses
  are now four concrete facts about the carrier, none of them about genericity, topology or Baire:
    (i)   `G : X -> D` continuous — the chart into densities;
    (ii)  `J : D ->L[R] jets` surjective — the jet map. Candidate: `herglotzControlLinear` for the
          map, `surjective_weightedJetControl` for the surjectivity;
    (iii) `M u0 : X ->L[R] D` surjective — multiplication by `G u0`. For `G u0 = exp u0` this is
          multiplication by a strictly positive bounded function, invertible when the function and
          its reciprocal are both bounded;
    (iv)  the exact chart identity `G u = G u0 + M u0 h` for small `h`, with `u` near `u0`. For the
          exponential chart this is `exp(u0 + log(1+h)) = exp(u0) * (1+h) = exp(u0) + exp(u0)*h`,
          so `u := u0 + log(1+h)`; the work is the estimate that `u` is near `u0` for small `h`,
          and that `log(1+h)` is defined in the space.
  NEXT: instantiate (i)-(iv). (iv) is the one with actual analytic content — it needs `log(1+h)` in
  the density space and a norm estimate; (ii) and (iii) look like bookkeeping over existing corpus
  lemmas but should not be assumed to be, given that every previous "bookkeeping" guess on this card
  was wrong in one direction or the other.
  Also still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — gap (b1) does not need the multiplicative gauge for THIS family, and that changes the
  remaining work. `formal/GaloisForLFunctions/HTGeometry/AffineChartFullRankGenericity.lean`;
  axiom-clean; audit 8552/8552.
  Two checks before building anything, both of which redirected the route:
  (1) `Lp R (top) mu` has NO `Ring` instance in mathlib. A Banach-algebra exp/log route for
  hypothesis (iv) would therefore require first constructing the algebra structure on L-infinity —
  a large detour, and one I was about to walk into.
  (2) The corpus's own family perturbs ADDITIVELY: `actualNevanlinnaExpandedPacketValue` uses
  `baseDensity + w.1` with `w` in a submodule. It is a linear slice, not an exponential chart.
  For an additive chart the exact displacement identity is just linearity, so:
  `affine_reachability_of_affine_chart` — for `u |-> base + i u` the reachability hypothesis holds
  with `L = J . i`, EXACTLY, with no smallness condition and no analytic input; the perturbed
  parameter is `u0 + h` itself, at distance exactly `norm h`.
  `exists_nodes_residual_expandedMatrix_of_affine_chart` — full expanded column rank is open, dense
  and residual along such a chart. NO reachability, transversality, differentiability or Baire
  hypothesis remains in the statement.
  Where this leaves the genericity side: the entire chain from the algebra up to
  dense+residual full rank now rests on exactly ONE input, `Function.Surjective (J . i)` — the jet
  map surjective on the chart directions. Everything else is discharged.
  Sharpening for the next iteration: for the FULL-SPACE chart (`i = id`, no submodule restriction)
  that input is already a theorem in this tree — `surjective_weightedJetControl`, for a base measure
  of infinite support with a strictly positive integrable density. What stands between it and
  `exists_nodes_residual_expandedMatrix_of_affine_chart` is only an index-type match:
  `weightedJetControl` lands in `jetIndex n -> C` while the expanded matrix wants
  `(kappa x Fin (q+1)) x Fin n -> C`. Composing with a coordinate-permuting linear equivalence
  should close it and make the genericity conclusion UNCONDITIONAL for that chart. Attempt next;
  do not record as done until it compiles, and note that a submodule-restricted `S` is a genuinely
  different question (surjectivity of `J . i` can fail on a proper subspace).
  Note on the card's founding metaphor: the multiplicative gauge is what one needs when POSITIVITY
  of the density must be preserved. Where the family is already a linear slice, reachability is
  free. The gauge lemma proved last iteration is retained — it is the right tool for the
  probability-carrier family, where positivity is a constraint — but it is not on the critical path
  for the Nevanlinna family.
  Also still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — the genericity chain is CLOSED for the reweighting family. Two modules; both
  axiom-clean; audit 8564/8564.
  `formal/GaloisForLFunctions/HTGeometry/JetIndexReindexGenericity.lean` — the index mismatch
  flagged last entry was exactly a reindexing and nothing more. `funLeftCLM` is precomposition by a
  reindexing map as a continuous linear map; `surjective_funLeftCLM_comp` transports surjectivity
  across a bijection of index types; `jetIndexProdEquiv` splits the repeated-over-rows jet index as
  rows times the single-row jet index. Then
  `exists_nodes_residual_expandedMatrix_of_surjective_jetMap`: along the IDENTITY chart on the
  density space, with jet coordinates matched to matrix coordinates by any bijection, the densities
  carrying full expanded column rank are open, dense and residual — with surjectivity of the jet map
  as the ONLY hypothesis.
  `formal/GaloisForLFunctions/HTGeometry/WeightedJetControlFullRankGenericity.lean` —
  `exists_nodes_residual_expandedMatrix_weightedJetControl`: instantiating that with
  `weightedJetControl` and `surjective_weightedJetControl`. Over a base measure of infinite support
  carrying a strictly positive integrable density, the bounded reweightings whose jets give the
  expanded evaluation matrix FULL COLUMN RANK are OPEN, DENSE and RESIDUAL. No transversality, no
  differentiability, no reachability, no Baire hypothesis appears anywhere in the statement; the
  measure hypotheses are the honest analytic input and nothing else is assumed.
  What this closes, tracing back: the algebraic core (monomial/power independence, evaluation minor,
  distinct nodes via the polynomial-domain product trick), the genericity core (nonzero jet
  determinant, affine reachability, open+dense = residual), and the analytic input (jet
  controllability) are now one connected chain ending in a residual full-rank statement. This is
  precisely the `hfull` shape that
  `countablePatterns_relationFree_dense_residual_of_fullRankWitness` consumes.
  REMAINING, and none of it assumed:
  (1) The index equivalence `e : (kappa x Fin (q+1)) x Fin n ~ jetIndex orders` is carried as a
  hypothesis. In the real application the row type and jet count are both determined by the pattern,
  so it should be CONSTRUCTIBLE rather than assumed — `jetIndexProdEquiv` plus `Fintype.equivFin`
  are the pieces. Build it; do not leave it as a hypothesis in the final statement.
  (2) The carrier-side bridge. The chain above is about a jet map of a reweighting; the witness
  interfaces (`probabilityCarrierExpandedFullRankWitness`,
  `actualNevanlinnaExpandedFullRankWitness`) are phrased through the packet-value machinery, which
  carries the row/shift packet structure and the `m0` centering term. Connecting the two is the next
  real step, and its shape is a match of packet values to reindexed jets — the factorial dictionary
  (`probabilityCarrierExpandedPacketValue_eq_factorial_moment`) and the rescaling transport
  (`eval_ne_zero_of_scaled`) already exist for exactly this purpose.
  (3) The Krein-index chamber half of the card: still untouched.
- 2026-07-19 — item (1) of the previous entry is closed: the index equivalence is CONSTRUCTED, not
  assumed. `formal/GaloisForLFunctions/HTGeometry/PacketJetIndexGenericity.lean`; compiled first
  try; axiom-clean; audit 8565/8565.
  `packetJetIndexEquiv` — the combined jet index of a row packet over a shift family,
  `jetIndex (fun p : row x iota => orders p.2)`, splits by `jetIndexProdEquiv` as rows times the
  single-row jet index, and the latter matches `Fin (card (Sigma i, Fin (orders i)))` by the
  canonical enumeration. Composing gives the bijection outright.
  `exists_nodes_residual_expandedMatrix_packetJets` — over a base measure of infinite support with a
  strictly positive integrable density, the bounded reweightings whose PACKET JETS give the expanded
  evaluation matrix full column rank are OPEN, DENSE and RESIDUAL. No index hypothesis remains; the
  surviving hypotheses are the measure ones plus injectivity of the exponent enumeration and of the
  combined nodes, all of which are genuine content rather than bookkeeping.
  I flagged this last entry as a place where an administrative-looking hypothesis could be hiding a
  cardinality obstruction. It was not — the two sides are the same finite type by construction. The
  check was still the right move; the cost of checking was one module and the cost of being wrong
  would have been a chain resting on an unsatisfiable hypothesis, which is exactly the failure mode
  that the vacuous `CarrierJetNondegenerateAt` predicate already produced once on this card.
  REMAINING:
  (2) The carrier-side bridge, now the only thing between this chain and
  `MaximalTranslationFullRankWitness`. Shape of the join: the genericity chain speaks of
  `weightedJetControl` applied to a reweighting; the witness interfaces speak of
  `probabilityCarrierExpandedPacketValue` / `actualNevanlinnaExpandedPacketValue`, which add the row
  and shift packet structure and an `m0` centering term. The dictionary between them is already
  built — `probabilityCarrierExpandedPacketValue_eq_factorial_moment` converts packet values to
  Cauchy kernel moments up to factorials, and `eval_ne_zero_of_scaled` transports nondegeneracy
  across that diagonal rescaling. What is NOT yet checked: whether `weightedJetControl` computes the
  same moments that `packetNode`/`packetOrder` name, and what the `m0` centering does to the rank
  condition (it is an additive shift of the jets, so it should be absorbable, but an additive shift
  of an affine chart is exactly the `base` argument of
  `exists_nodes_residual_expandedMatrix_of_affine_chart` and should be routed through there rather
  than waved at).
  (3) The Krein-index chamber half of the card: still untouched.
- 2026-07-19 — the `m0` centering is handled, and the shape of the last gap has changed.
  `formal/GaloisForLFunctions/HTGeometry/CenteredJetOffsetGenericity.lean`; compiled first try;
  axiom-clean; audit 8566/8566.
  `exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset` — a CONSTANT additive term in
  the jets leaves the whole genericity conclusion untouched. The chart is still the identity on the
  density space and the displacement identity is still exact, because a constant cancels in the
  difference. The previous no-offset theorem is the `c = 0` case.
  `exists_nodes_residual_expandedMatrix_centeredPacketJets` — the packet-level version: centering
  term plus reweighting jets, index bijection constructed, open + dense + residual. Neither the
  index bijection nor the centering is assumed away, which is what the previous entry demanded.
  The `m0` term of `actualNevanlinnaExpandedPacketValue` is exactly of this form
  (`iteratedDeriv s.2 m0 (packet.1 p.1 + shift.1 s.1)`, constant in the density), so it is now
  covered rather than waved at.
  REFRAMING OF THE LAST GAP — this is the useful part of the iteration. I had recorded the remaining
  question as "does `weightedJetControl` compute the same moments that `packetNode`/`packetOrder`
  name". That question does not need an answer. The offset theorem is stated for an ARBITRARY
  continuous linear jet map `J` with `Function.Surjective J`; it never inspects what `J` computes.
  And `projectiveNevanlinnaJetExpansionSmoothControl` has precisely the same type shape —
  `Lp R (top) mu ->L[R] ((Sigma i, Fin (n i)) -> C)`, built via `linftyLpKernelControl` over
  `Measure (OnePoint R)`. So the genericity machinery applies to the Nevanlinna control map
  DIRECTLY, with no identification between the two control maps required.
  What that leaves is ONE named theorem, and it is a clean analytic statement rather than a
  structural match:
    SURJECTIVITY OF `projectiveNevanlinnaJetExpansionSmoothControl`.
  This is the exact analogue of `surjective_weightedJetControl`, which is already proved in this
  tree by an annihilator argument: annihilation on indicators forces vanishing set integrals, which
  forces the coefficient vector to vanish. The route to copy is
  `surjective_of_forall_coefficients_eq_zero` plus the integrability and kernel-bound lemmas, now
  over the one-point compactification and with the Nevanlinna kernel
  (`projectiveNevanlinnaJetExpansionBanachMap`) in place of `cauchyJetKernel`. Whether the
  annihilator argument survives the compactified base and that kernel is the thing to attempt next;
  it is not to be assumed, since the kernel is a different object and the one-point base adds a
  point at infinity whose mass could in principle carry an annihilator.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — the surjectivity question is split at its natural seam.
  `formal/GaloisForLFunctions/HTGeometry/KernelControlSurjectivityCriterion.lean`; axiom-clean;
  audit 2712/2712 (module-local; the umbrella carries it).
  Reading the existing `surjective_weightedJetControl` proof line by line shows it is two arguments
  welded together, and only one of them is about the Cauchy kernel:
    HALF 1 (generic, measure-theoretic): a coefficient packet annihilating the range, TESTED ON
    INDICATORS, forces every set integral of the paired kernel to vanish, hence the pairing vanishes
    almost everywhere. This uses nothing about the kernel or the base space.
    HALF 2 (kernel-specific): an almost-everywhere vanishing pairing forces the coefficients to
    vanish. For the Cauchy kernel this is `cauchyJet_coeff_eq_zero_of_ae_re`, and it is where the
    node injectivity and infinite support are actually consumed.
  `surjective_of_kernel_ae_re_rigidity` isolates HALF 1 over an ARBITRARY measure space: a control
  map represented on indicators by set integrals of integrable kernels is surjective as soon as no
  nonzero coefficient packet makes the paired kernel have vanishing real part a.e. Supporting this,
  `indicatorLpTopGen` generalises `indicatorLpTop` off `Measure R` to any measure space — the
  original proof never used the real line, only measurability and boundedness at exponent infinity.
  Consequence for the last gap: surjectivity of `projectiveNevanlinnaJetExpansionSmoothControl` no
  longer requires redoing the measure theory over the one-point compactification. It requires
  exactly two things, both narrow:
    (i) a REPRESENTATION lemma — that the map applied to `indicatorLpTopGen` is the set integral of
    the Nevanlinna kernel. Since the map is `linftyLpKernelControl mu K` and that is an L-infinity /
    L-1 pairing, this should be an unfolding of `linftyLpPairingRight`, but the pairing is stated
    through `Lp` coercions and the unfolding is not free.
    (ii) a RIGIDITY lemma for `projectiveNevanlinnaJetExpansionBanachMap` — the analogue of
    `cauchyJet_coeff_eq_zero_of_ae_re`. This is the real mathematical content and the place where
    my earlier worry belongs: the one-point base adds a point at infinity, and rigidity is exactly
    the statement that could fail there if that point carries mass. Note the worry is now LOCALISED
    to (ii) rather than contaminating the whole surjectivity argument, which is what splitting the
    proof bought.
  Next: attempt (i), which is bounded work, then (ii). If (ii) fails at the point at infinity, the
  fix is likely a hypothesis that `mu` gives it no mass, which would be an honest analytic
  hypothesis rather than a defeat — but do not pre-suppose that shape; find out what the annihilator
  argument actually needs.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — item (i) of the previous entry is closed, and the card's remaining content is now a
  single named analytic lemma.
  `formal/GaloisForLFunctions/HTGeometry/KernelControlIndicatorRepresentation.lean`; axiom-clean;
  audit 2744/2744 module-local.
  `linftyLpPairingRight_indicatorLpTopGen` — pairing an L-1 kernel against the indicator of a
  measurable set is the set integral. `linftyLpKernelControl_indicatorLpTopGen_apply` — the same
  read in one coordinate of a finite tuple, by commuting the coordinate projection (a continuous
  linear map) with the Bochner integral.
  `surjective_linftyLpKernelControl_of_rigidity` — ANY bounded-density control map given by pairing
  against an L-1 kernel is SURJECTIVE as soon as no nonzero coefficient packet makes the paired
  kernel have vanishing real part almost everywhere. All measure theory discharged; rigidity is the
  only input.
  This applies to `projectiveNevanlinnaJetExpansionSmoothControl` DIRECTLY, since that map is by
  definition `linftyLpKernelControl mu (ContinuousMap.toLp 1 mu R (projectiveNevanlinnaJetExpansionBanachMap a q n z))`.
  So the state of the card's genericity programme is:
    - algebraic core: DONE (independence, minor, distinct nodes, jet determinant nonzero)
    - genericity core: DONE (affine reachability, open + dense = residual, centering offset)
    - index matching: DONE (constructed, not assumed)
    - surjectivity, measure-theoretic half: DONE (indicator representation + annihilator chain,
      over an arbitrary measure space)
    - surjectivity, kernel half: THE ONE REMAINING ITEM.
  THE REMAINING ITEM, stated exactly: for the Nevanlinna jet kernel
  `projectiveNevanlinnaJetExpansionBanachMap a q n z` over `Measure (OnePoint R)`, show that
  `(forall-ae x, Re (sum_s c_s K(x)_s) = 0)` implies `c = 0`.
  For the Cauchy kernel the corresponding statement is `cauchyJet_coeff_eq_zero_of_ae_re`, proved
  from node injectivity and infinite support. The Nevanlinna kernel is a different object and the
  base is compactified, so this is not a transcription; it is the place where the analysis actually
  lives, and it is the right place for the card's remaining effort. My standing worry — that the
  point at infinity could carry an annihilator — is a statement about THIS lemma and nothing else
  now.
  Two routes to try, in order: (A) reduce to the Cauchy case by showing the Nevanlinna kernel agrees
  with a Cauchy jet kernel off the point at infinity, so that `cauchyJet_coeff_eq_zero_of_ae_re`
  applies to the restriction of `mu` to `R`; (B) if that fails, run the annihilator argument
  directly on the compactified space. Route (A) would also make the point-at-infinity question
  explicit rather than incidental, which is a reason to prefer it even if (B) looks shorter.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — the remaining rigidity lemma is factored, and the factoring exposes a condition that
  was hidden. `formal/GaloisForLFunctions/HTGeometry/KernelRigidityTransfer.lean`; compiled first
  try; axiom-clean; audit 2745/2745 module-local.
  Reading the Nevanlinna kernel: `projectiveNevanlinnaJetExpansionColumn` is
  `K(t)_s = sum_k nevanlinnaJetCoeff a q s.2 k (z s.1) * projectiveCauchyPower (q (z s.1)) k t`,
  i.e. a fixed triangular combination of CAUCHY POWERS whose coefficients depend on the nodes only,
  not on the integration variable. So the composite kernel is `M` applied to a base kernel `B`.
  `kernel_ae_re_rigidity_of_transpose_injective` — if `K` expands in `B` with coefficient matrix
  `M`, the base kernel `B` is rigid, and no nonzero packet is annihilated by the TRANSPOSE of `M`,
  then `K` is rigid. Proof: a packet `c` annihilating `K` annihilates `B` through
  `d k = sum_s c s * M s k`, by exchanging two finite sums; base rigidity kills `d`, transpose
  injectivity kills `c`.
  WHAT THIS EXPOSES, and it is the point of the iteration. Rigidity of the Nevanlinna kernel is NOT
  unconditional, and I would have mis-stated the remaining goal without factoring it. The docstring
  of `nevanlinnaJetPacketForwardLinearMap` says it plainly: "Unlike the triangular equivalence, this
  map needs no nonvanishing diagonal hypothesis: CRITICALITY CAN DESTROY INVERTIBILITY but never the
  forward jet expansion." The forward jet expansion always exists; its injectivity fails on the
  critical locus. Transpose injectivity of `M` IS that injectivity. So:
    at a critical node configuration the Nevanlinna control map need not be surjective,
    and the genericity conclusion cannot hold there.
  This is not a defeat and not a gap in the argument — it is why the corpus module is named
  `NevanlinnaNoncriticalProjectiveCompactPatch`. Noncriticality was always part of the setting; what
  was missing was a proof-side statement of WHERE it is consumed, and it is consumed here and only
  here. My earlier worry about the point at infinity was aimed at the wrong object: the obstruction
  is the critical locus in the NODE variables, not the compactification of the base.
  REMAINING, now two lemmas instead of one, both sharply stated:
  (R1) BASE RIGIDITY: for the Cauchy powers `projectiveCauchyPower (q (z i)) k` over
  `Measure (OnePoint R)`, an a.e. vanishing real part of a packet combination forces the packet to
  vanish. This is the true analogue of `cauchyJet_coeff_eq_zero_of_ae_re` and is where the base
  measure's support hypotheses will be consumed. The point-at-infinity question belongs to THIS
  lemma.
  (R2) TRANSPOSE INJECTIVITY of the `nevanlinnaJetCoeff` matrix under noncriticality. The corpus
  already has triangular-equivalence machinery for the invertible case; find it and check whether it
  yields the transpose statement directly, rather than re-deriving the triangular inverse.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — (R2) is proved, and noncriticality is now a named, consumed hypothesis rather than an
  ambient assumption. `formal/GaloisForLFunctions/HTGeometry/TriangularCoefficientInjectivity.lean`;
  axiom-clean; audit 2747/2747 module-local.
  `transpose_annihilator_eq_zero_of_lowerTriangular` — a lower triangular matrix with nonvanishing
  diagonal admits no nonzero packet annihilated by its transpose (det = product of the diagonal by
  `Matrix.det_of_lowerTriangular`, hence nonzero, hence `mulVec` of the transpose injective).
  `nevanlinnaJetCoeffMatrix_lowerTriangular` and `nevanlinnaJetCoeffMatrix_diagonal_ne_zero` — the
  jet coefficient array IS lower triangular (`nevanlinnaJetCoeff_eq_zero_of_lt`) with diagonal
  `r! * a z * (deriv q z)^r` (`nevanlinnaJetCoeff_diagonal`), both already in the corpus; the
  diagonal is nonzero exactly when `a z /= 0` and `deriv q z /= 0`.
  `nevanlinnaJetCoeff_transpose_annihilator_eq_zero` — the hypothesis the rigidity transfer wants,
  under those two nonvanishing conditions.
  So NONCRITICALITY has a precise proof-side meaning on this card: `a z /= 0 and deriv q z /= 0` at
  each node. Nothing weaker will do — the diagonal is literally `r! * a z * (deriv q z)^r`, so if
  either factor vanishes at a node, the corresponding block is singular and the transfer genuinely
  fails there. That matches the corpus naming (`NevanlinnaNoncriticalProjectiveCompactPatch`) and
  confirms it was never an idle qualifier.
  REMAINING for the surjectivity half, now ONE lemma:
  (R1) BASE RIGIDITY for the Cauchy powers `projectiveCauchyPower (q (z i)) k` over
  `Measure (OnePoint R)`: an a.e. vanishing real part of a packet combination forces the packet to
  vanish. This is where the base measure hypotheses (support, mass at the point at infinity) get
  consumed, and it is the last piece of analysis on the genericity side.
  Plus one piece of GLUE, which is bookkeeping but should not be skipped: the coefficient matrix for
  the full packet is BLOCK DIAGONAL over the node index — the jet at node `i` expands only in the
  Cauchy powers at node `i`. `kernel_ae_re_rigidity_of_transpose_injective` wants transpose
  injectivity of the assembled sigma-indexed matrix, and the per-node theorem above gives it
  blockwise. Assembling blocks over a sigma index with dependent `Fin (n i)` fibres needs a
  transport and is the kind of step that looks free and is not.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — the block-diagonal glue flagged last entry is done, and it did NOT need the dependent
  transport I expected. `formal/GaloisForLFunctions/HTGeometry/BlockDiagonalAnnihilator.lean`;
  axiom-clean; audit 2748/2748 module-local.
  `sigma_annihilator_eq_zero_of_blockwise` — for a matrix that vanishes off the diagonal blocks of a
  sigma index, a packet annihilated by the transpose is annihilated blockwise, so blockwise
  injectivity gives injectivity outright.
  The transport worry was avoidable by FORMULATION rather than by work: state the blockwise
  hypothesis as a statement about `M` evaluated at `<i,j> <i,k>` — both indices at the SAME node —
  and no fibre-to-fibre transport ever arises, because testing at a target node only ever involves
  source indices at that node. The proof is then a sigma-sum split (`Fintype.sum_sigma`) plus
  `Finset.sum_eq_single`, with the off-diagonal terms killed by hypothesis. Worth remembering as a
  general move: a dependent-index obstruction that appears when you write the assembled object down
  can often be dissolved by never forming the cross-fibre comparison in the first place.
  This composes with the previous entry: `nevanlinnaJetCoeff_transpose_annihilator_eq_zero` supplies
  the per-node hypothesis (`F i = Fin (n i)`), so transpose injectivity of the assembled packet
  coefficient matrix holds whenever every node is noncritical.
  STATE OF THE SURJECTIVITY HALF — one lemma, no glue:
  (R1) BASE RIGIDITY for the Cauchy powers `projectiveCauchyPower (q (z i)) k` over
  `Measure (OnePoint R)`: an a.e. vanishing real part of a packet combination forces the packet to
  vanish. Everything else on this half is proved: the measure-theoretic annihilator chain, the
  indicator representation, the rigidity transfer along the coefficient matrix, the triangular
  injectivity of that matrix under noncriticality, and now the blockwise assembly.
  For (R1) the corpus analogue is `cauchyJet_coeff_eq_zero_of_ae_re` (Cauchy jet kernel over
  `Measure R`, from node injectivity and infinite support). The two differences to confront are the
  compactified base and the projective form of the Cauchy power. Route (A) from two entries ago
  still stands and is now the ONLY thing between this card's genericity programme and a closed
  chain: show the projective Cauchy power agrees with the affine Cauchy jet kernel off the point at
  infinity, so the existing lemma applies to the restriction of `mu` to `R`, and see explicitly what
  the point at infinity contributes.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — (R1) IS PROVED. The last analytic piece of the genericity programme is in.
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveCauchyBaseRigidity.lean`; compiled first try;
  axiom-clean; audit 8504/8504.
  `projectiveCauchyPower_coeff_eq_zero_of_ae_re` (node-indexed) and
  `projectiveCauchyPower_sigma_coeff_eq_zero_of_ae_re` (packet/sigma-indexed, the shape
  `kernel_ae_re_rigidity_of_transpose_injective` consumes): at distinct upper-half-plane nodes,
  against a measure of infinite support, an a.e. vanishing real part of a packet combination of
  projective Cauchy powers forces every coefficient to vanish.
  THE POINT AT INFINITY QUESTION IS SETTLED, and the answer is that there was never anything there.
  `projectiveCauchyPower x k = fun t => t.elim 0 (fun r => ((r - x)^{-1})^{k+1})` — the kernel is
  DEFINED to be ZERO at infinity (`projectiveCauchyPower_infty` is a simp lemma in the corpus). So
  the compactification adds a point on which every kernel coordinate vanishes; no annihilator can be
  supported there, and no hypothesis about the mass of `mu` at infinity is needed. On the real
  points `projectiveCauchyPower_coe` makes the kernel literally the affine Cauchy jet kernel, so the
  reduction to `cauchyJet_coeff_eq_zero_of_ae_re` is a rewrite.
  I carried the point-at-infinity worry for four entries, twice aimed it at the wrong object (first
  at the whole surjectivity argument, then at the base measure), and it dissolved on reading the
  definition. Recording that as a process fact: the cost of NOT reading the definition earlier was
  four entries of hedging; the cost of reading it was one grep. The worry was still correct to
  carry — an unexamined compactification IS where an annihilator could hide — but "go read the
  definition" should have outranked "reason about what could go wrong" much sooner.
  STATE OF THE GENERICITY PROGRAMME — every component now proved:
    algebraic core; genericity core; index matching; centering offset; surjectivity measure-theoretic
    half; indicator representation; rigidity transfer; triangular injectivity under noncriticality;
    blockwise assembly; base rigidity.
  WHAT REMAINS IS ASSEMBLY, not new mathematics: chain
  `projectiveCauchyPower_sigma_coeff_eq_zero_of_ae_re` (as `hB`) and
  `sigma_annihilator_eq_zero_of_blockwise` + `nevanlinnaJetCoeff_transpose_annihilator_eq_zero`
  (as `hM`) through `kernel_ae_re_rigidity_of_transpose_injective` to get rigidity of the Nevanlinna
  kernel, then through `surjective_linftyLpKernelControl_of_rigidity` to get surjectivity of
  `projectiveNevanlinnaJetExpansionSmoothControl`, then into
  `exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset`.
  Two things to check while assembling, neither of which I have verified and neither of which should
  be assumed: (a) the `hK` expansion hypothesis of the transfer needs the Nevanlinna column written
  as `sum_k M s k * B t k` with B sigma-indexed — the corpus column sums over `Fin (n s.1)`, so the
  index shapes must be reconciled, and that is exactly the sort of step that has produced real work
  twice on this card; (b) the a.e. hypothesis in the base rigidity is stated over a measure on R
  while the control map integrates over `Measure (OnePoint R)` — the caller must supply the pullback
  along the embedding, which is honest but is a real hypothesis, not a coercion.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — RIGIDITY OF THE NEVANLINNA JET KERNEL IS PROVED.
  `formal/GaloisForLFunctions/HTGeometry/NevanlinnaKernelRigidity.lean`; axiom-clean; audit
  8509/8509.
  `nevanlinnaPacketCoeffMatrix` — the block diagonal coefficient array
  `if s.1 = k.1 then nevanlinnaJetCoeff a q s.2 k.2 (z s.1) else 0`. Note it takes NATURAL number
  arguments, so assembling it over the sigma index needs no dependent transport at all — the same
  formulation trick that dissolved the blockwise glue two entries ago applies here for free.
  `projectiveNevanlinnaJetExpansionColumn_eq_sum` — the jet column IS that array applied to the
  projective Cauchy powers (a sigma-sum split plus `Finset.sum_eq_single`, off-diagonal blocks
  killed by the `if`). This discharges concern (a) of the previous entry: the index shapes
  reconciled without new mathematics, though the `if`-orientation differs between the two uses and
  had to be handled with `Ne.symm` in one of them.
  `nevanlinnaJetColumn_coeff_eq_zero_of_ae_re` — at distinct noncritical upper-half-plane nodes,
  against a measure of infinite support, an a.e. vanishing real part of a packet combination of
  Nevanlinna jet columns forces every coefficient to vanish. Hypotheses, all named and none hidden:
  `q . z` injective, `0 < im (q (z i))`, `a (z i) /= 0`, `deriv q (z i) /= 0`, `nu.support.Infinite`.
  The last two ARE the noncriticality, and they enter through exactly one place — the diagonal
  `r! * a z * (deriv q z)^r` of the triangular array.
  One practical note for future assembly on this card: the first attempt at this theorem hit a
  `deterministic timeout at isDefEq` when the four kernel arguments were passed inline to
  `kernel_ae_re_rigidity_of_transpose_injective`. Binding B, M and K with `set ... with` and proving
  the three hypotheses as separate `have`s elaborated instantly. Sigma-indexed families with
  dependent `Fin (n i)` fibres are where this bites; prefer named bindings over inline lambdas there.
  REMAINING TO CLOSE THE GENERICITY SIDE — assembly only, two steps:
  (S1) Feed this rigidity into `surjective_linftyLpKernelControl_of_rigidity` to obtain surjectivity
  of `projectiveNevanlinnaJetExpansionSmoothControl`. Concern (b) of the previous entry is the live
  one here and is NOT yet resolved: this rigidity is stated a.e. over a measure on R, while the
  control map integrates over `Measure (OnePoint R)`. The caller must supply the pullback along the
  embedding `OnePoint.some`. Since the kernel vanishes at infinity that pullback should lose
  nothing, but "should lose nothing" is precisely the kind of claim this card has punished before —
  it needs a lemma relating `forall-ae over mu on OnePoint R` to `forall-ae over the pullback on R`,
  and that lemma has a measurability side condition.
  (S2) Feed the resulting surjectivity into
  `exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset`.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — concern (b) resolved: the projective pullback is a lemma, not a coercion, and it now
  exists. `formal/GaloisForLFunctions/HTGeometry/OnePointPullbackRigidity.lean`; compiled first try;
  axiom-clean; audit 8510/8510.
  `measurable_onePoint_some` — the projective embedding is measurable for the Borel structure. The
  corpus supplies `instMeasurableSpaceOnePointReal := borel (OnePoint R)` in
  `NevanlinnaBoundaryAlgebra`, and with `BorelSpace (OnePoint R)` obtained as `<rfl>` the embedding's
  continuity (`OnePoint.continuous_coe`) upgrades to measurability. Worth noting that mathlib does
  NOT give `MeasurableSpace (OnePoint R)` by default — the instance is the corpus's own, which is
  the kind of thing that would have silently blocked this step had it not been there.
  `ae_onePoint_pullback` — an a.e. statement for a pushforward along the embedding pulls back, via
  `ae_of_ae_map`. This is the one-directional form and needs only `AEMeasurable`, so no
  measurable-set side condition on the predicate is required. I had flagged that side condition as a
  risk; the one-directional lemma sidesteps it entirely.
  `nevanlinnaJetColumn_coeff_eq_zero_of_ae_re_map` — kernel rigidity stated over
  `nu.map OnePoint.some`, i.e. exactly the measures on the compactified line that carry no mass at
  infinity. Nothing is lost there, and now for a stated reason rather than an expectation: the
  pushforward gives the point at infinity zero mass, so the a.e. hypothesis upstairs is precisely
  the a.e. hypothesis downstairs.
  REMAINING TO CLOSE THE GENERICITY SIDE — one representation step, then plumbing:
  (S1a) TRANSFER TO THE Lp REPRESENTATIVE. `surjective_linftyLpKernelControl_of_rigidity` states its
  rigidity hypothesis for `K : Lp (sigma -> C) 1 mu`, i.e. for the a.e. equivalence class, whereas
  the rigidity just proved is about the honest function `projectiveNevanlinnaJetExpansionColumn`.
  The control map is built from `ContinuousMap.toLp 1 mu R (projectiveNevanlinnaJetExpansionBanachMap ...)`,
  so the bridge is `ContinuousMap.coeFn_toLp` (an a.e. equality) followed by
  `projectiveNevanlinnaJetExpansionBanachMap_apply`, which identifies the Banach map with the column
  ON THE UPPER PACKET LOCUS — note that identification carries the hypothesis
  `z in nevanlinnaUpperPacketSet q`, so it is a genuine condition to thread through, not a rewrite.
  (S1b) Then `surjective_linftyLpKernelControl_of_rigidity` gives surjectivity of
  `projectiveNevanlinnaJetExpansionSmoothControl`.
  (S2) Then `exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset` closes the chain.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — (S1a) is done: rigidity now holds for the L-1 CLASS the control map actually pairs
  against, not merely for the honest jet column.
  `formal/GaloisForLFunctions/HTGeometry/NevanlinnaControlKernelRigidity.lean`; axiom-clean; audit
  8513/8513.
  `nevanlinnaControlKernel_coeff_eq_zero_of_ae_re` — at distinct noncritical upper packet nodes,
  over a projective pushforward of a finite measure of infinite support, no nonzero coefficient
  packet annihilates the real part of `ContinuousMap.toLp 1 mu R (projectiveNevanlinnaJetExpansionBanachMap a q n z)`
  almost everywhere. Two a.e. rewrites: `ContinuousMap.coeFn_toLp` (class to representative) and
  `projectiveNevanlinnaJetExpansionBanachMap_apply` (Banach map to jet column, ON the upper packet
  locus).
  The upper-packet condition I flagged last entry as "a genuine condition, not a rewrite" turned out
  to be exactly that, and it is now carried explicitly as `hz : z in nevanlinnaUpperPacketSet q`.
  Since that set is definitionally `{z | forall i, 0 < im (q (z i))}`, it also SUPPLIES the
  upper-half-plane hypothesis the rigidity chain needs — the same fact serves both roles, so
  threading it cost nothing extra. Naming it in advance was still right: had it been an independent
  condition it would have been an unremarked hypothesis leaking into the final statement.
  A tooling note worth keeping: `ContinuousMap.coeFn_toLp` has a different explicit/implicit split
  from `ContinuousMap.toLp`, so writing the arguments positionally in the pattern of the toLp call
  fails. Stating the a.e. equality as a `have` with the full expected type and closing it with
  `ContinuousMap.coeFn_toLp _ _` is robust and does not depend on guessing the split. Same lesson as
  the `isDefEq` timeout two entries ago: state the intermediate object, let unification fill it.
  REMAINING ON THE GENERICITY SIDE — two plumbing steps, no mathematics:
  (S1b) `surjective_linftyLpKernelControl_of_rigidity` applied to the above gives surjectivity of
  `projectiveNevanlinnaJetExpansionSmoothControl`. The one thing to check is that the criterion's
  `K` and the control map's kernel are the SAME `Lp` term — the control map is
  `linftyLpKernelControl mu (ContinuousMap.toLp ...)`, so this should be a definitional match, but
  the sigma index of the criterion must line up with `(Sigma i, Fin (n i))` and that is where the
  previous two index reconciliations on this card each cost a module.
  (S2) `exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset` then closes the chain to
  open + dense + residual full expanded rank for the Nevanlinna family.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — (S1b) DONE. THE NEVANLINNA JET CONTROL MAP IS SURJECTIVE.
  `formal/GaloisForLFunctions/HTGeometry/NevanlinnaControlSurjective.lean`; axiom-clean; audit
  8514/8514.
  `surjective_projectiveNevanlinnaJetExpansionSmoothControl` — at distinct noncritical upper packet
  nodes, over a projective pushforward of a finite measure of infinite support, EVERY finite
  Nevanlinna jet packet is attained by a bounded density. Hypotheses, complete and all named:
  `nu` finite with `nu.support.Infinite`; `z in nevanlinnaUpperPacketSet q`; `q . z` injective;
  `a (z i) /= 0`; `deriv q (z i) /= 0`.
  The index reconciliation I flagged as likely to cost a module did NOT materialize: the criterion's
  sigma index and the Banach kernel's `(Sigma i, Fin (n i))` matched definitionally, and the proof
  is `rw` of the control map's definition followed by the criterion. The only fix needed was a name
  (`Measure.isFiniteMeasure_map`, not `isFiniteMeasure_map`), found with `exact?`. Recording the
  miss: I have now over-predicted index friction once and under-predicted it twice on this card, so
  the prediction itself carries no information — the right policy is simply to attempt and see,
  which costs one build either way.
  THIS COMPLETES THE ANALYTIC INPUT OF THE GENERICITY PROGRAMME. Chain now standing, end to end,
  every link proved and axiom-clean:
    monomial/power independence -> evaluation minor -> distinct nodes (polynomial-domain product)
    -> nonzero jet determinant -> affine reachability (exact, no linearization error)
    -> open + dense -> residual -> centering offset absorbed -> index bijection constructed
    -> surjectivity criterion (measure-theoretic half, arbitrary base) -> indicator representation
    -> rigidity transfer along the coefficient matrix -> triangular injectivity under noncriticality
    -> blockwise assembly -> projective Cauchy base rigidity -> Nevanlinna kernel rigidity
    -> projective pullback -> L-1 class rigidity -> CONTROL MAP SURJECTIVE.
  REMAINING: (S2) only. Instantiate
  `exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset` with this surjectivity to get
  open + dense + residual full expanded rank for the Nevanlinna family. The shapes to line up: the
  offset theorem's node/shift index is the packet index `(kappa x Fin (q+1)) x iota'`, so the `ι` of
  the surjectivity theorem must be instantiated at that product, and `packetJetIndexEquiv` supplies
  the bijection to the matrix coordinates. Per the note above, attempt rather than predict.
  Then the card's remaining half is the Krein-index chamber, still untouched.
- 2026-07-19 — (S2) DONE. THE GENERICITY CHAIN IS CLOSED FOR THE NEVANLINNA PACKET FAMILY.
  `formal/GaloisForLFunctions/HTGeometry/NevanlinnaPacketFullRankGenericity.lean`; compiled first
  try; axiom-clean; audit 8595/8595.
  `exists_nodes_residual_expandedMatrix_nevanlinnaPacket` — for the Nevanlinna packet family there
  are pairwise distinct nodes at which the bounded densities giving the expanded evaluation matrix
  FULL COLUMN RANK are OPEN, DENSE and RESIDUAL.
  The statement contains NO transversality, differentiability, reachability, Baire, index or
  nondegeneracy hypothesis. What it does contain, all named and all genuine:
    `nu` finite with `nu.support.Infinite`; `zz in nevanlinnaUpperPacketSet qf`; `qf . zz` injective;
    `am (zz p) /= 0`; `deriv qf (zz p) /= 0`; `exponent` injective.
  The last two are the noncriticality, and they are consumed at exactly one place in the whole
  development — the diagonal `r! * am z * (deriv qf z)^r` of the triangular jet coefficient array.
  WHERE THIS LEAVES THE CARD. The genericity half is complete as a chain of proved, axiom-clean
  theorems. What it delivers is residual full expanded rank for the Nevanlinna packet family, which
  is the `hfull` shape that
  `countablePatterns_relationFree_dense_residual_of_fullRankWitness` consumes to produce dense +
  residual RELATION FREENESS. Connecting those two is the next step and is not yet done: that
  theorem quantifies over a countable family of patterns with per-pattern row/shift/exponent data,
  whereas the theorem just proved fixes one pattern's data; the per-pattern statement must be
  produced uniformly and then intersected. `dense_setOf_forall_pattern_and_index` is the tool for
  the intersection, and the pattern quantifier is already known countable
  (`Countable (FiniteDifferentialPattern Gamma)`).
  Also NOT yet connected, and worth stating so it is not mistaken for done: the chain above is about
  `actualNevanlinnaExpandedFullRankWitness`-shaped data. The card's carrier-side predicate
  `MaximalTranslationFullRankWitness` is phrased through
  `probabilityCarrierExpandedFullRankWitness`, a different (probability-carrier) family. The
  factorial dictionary and rescaling transport were built for that join and remain unused; whether
  the probability-carrier family admits the same surjectivity is a separate question, since its
  densities are constrained to be positive and normalised — which is exactly the setting where the
  MULTIPLICATIVE GAUGE lemma proved earlier on this card is the right tool and the affine chart is
  not.
  Next: (1) uniformise over patterns and intersect, to land dense+residual relation freeness for the
  Nevanlinna family; (2) then attack the probability-carrier family via the multiplicative gauge.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — the countable-intersection step now delivers RESIDUALITY, not only density.
  `formal/GaloisForLFunctions/HTGeometry/CountableResidualIntersection.lean`; compiled first try;
  axiom-clean; audit 8498/8498.
  `dense_and_residual_setOf_forall` and `dense_and_residual_setOf_forall_pattern_and_index` — a
  property open and dense for each member of a countable family holds densely AND residually for all
  members at once. Density is Baire; residuality is the countable-intersection property of the
  residual filter (`countable_iInter_mem`, since `residual` is a `CountableInterFilter`).
  This strictly strengthens the card's own earlier `dense_setOf_forall_pattern` /
  `dense_setOf_forall_pattern_and_index`, which produced density only. That was a real gap rather
  than a stylistic one: `countablePatterns_relationFree_dense_residual_of_fullRankWitness` takes
  `hfull` as a CONJUNCTION of dense and residual, so the density-only versions could never have
  discharged it. Worth noting the gap existed for many entries without being visible, because the
  density half is the one that looks like the hard half — the residual half is one filter lemma, and
  precisely because it is easy it was never written down.
  REMAINING to reach dense+residual relation freeness for the Nevanlinna family:
  (U1) UNIFORMISE OVER PATTERNS. `exists_nodes_residual_expandedMatrix_nevanlinnaPacket` fixes one
  pattern's row/shift/exponent data and produces `exists z, ... open, dense, residual`. To feed the
  intersection above, the per-pattern sets must be produced as a FAMILY indexed by the pattern, which
  means choosing the nodes `z` per pattern — an application of choice over the countable pattern
  index. Mechanical, but it changes the statement shape from `exists` inside to a chosen family.
  (U2) THE SHIFT QUANTIFIER. `actualNevanlinnaExpandedFullRankWitness` quantifies over
  `InjectiveShiftConfiguration (iota n)`, which is NOT countable. This is what the compact-patch
  machinery on this card exists for (`upperPatch`, `iUnion_upperPatch`,
  `dense_setOf_forall_upperHalfPlane_ne_zero`, `NevanlinnaNoncriticalProjectiveCompactPatch`). The
  intersection lemma above handles the pattern quantifier and any countable auxiliary index; the
  shift quantifier must first be reduced to a countable exhaustion by those tools. This is the
  substantive remaining step on the genericity side, and it should not be described as plumbing.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — (U1) done. `formal/GaloisForLFunctions/HTGeometry/UniformNodeChoiceGenericity.lean`;
  compiled first try; axiom-clean; audit 8499/8499.
  `exists_choice_dense_and_residual` — if each member of a COUNTABLE family admits a datum
  satisfying a side condition and carrying an open dense set of parameters, there is a SINGLE
  assignment of data whose conditions hold simultaneously on a dense residual set. Proof is `choose`
  followed by the countable intersection of the previous entry.
  `exists_choice_dense_and_residual_pair` — the same with a pair index, so a countable auxiliary
  index (a compact exhaustion) rides alongside the primary one.
  This is exactly the shape `exists_nodes_residual_expandedMatrix_nevanlinnaPacket` produces:
  `exists z, Injective z and IsOpen ... and Dense ...`, one existential per pattern, with the nodes
  as the chosen datum and injectivity as the side condition `P`. The change of shape from
  "existential inside" to "chosen family" that I flagged as needing choice is now a lemma rather
  than an obligation.
  REMAINING on the genericity side — (U2) ALONE, and it is the substantive one.
  `actualNevanlinnaExpandedFullRankWitness` quantifies over `InjectiveShiftConfiguration (iota n)`,
  which is uncountable. Both intersection lemmas above require countability, so the shift quantifier
  cannot be fed to them directly; it must first be reduced to a countable exhaustion. The tools
  built earlier on this card for precisely this are `upperPatch`, `iUnion_upperPatch`,
  `dense_setOf_forall_upperHalfPlane_ne_zero` and the compact-patch reduction of
  `NevanlinnaNoncriticalProjectiveCompactPatch`; the shape of the argument is that the rank
  condition is OPEN in the shift, so its failure set is closed, and a compact patch of shifts meets
  the failure set in a compact set which a countable exhaustion detects. That the rank condition is
  continuous in the shift is available — `continuous_expandedDifferentialEvaluationMatrix` gives
  continuity in the jets, but the dependence of the jets ON THE SHIFT is through the control map's
  nodes and has NOT been established continuous here. That is the first thing to check when
  attacking (U2), and it should not be assumed: it is a different continuity from the one already
  proved and used for the residual half.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the continuity flagged as unverified last entry EXISTS, and the shape of (U2) is now
  understood precisely — including an obstruction I had not seen.
  `formal/GaloisForLFunctions/HTGeometry/NevanlinnaControlNodeContinuity.lean`; compiled first try;
  axiom-clean; audit 8596/8596.
  `continuousOn_projectiveNevanlinnaJetExpansionSmoothControl` and
  `continuousOn_nevanlinnaJets_nodes` — at a fixed bounded density the jet packet depends
  CONTINUOUSLY ON THE NODE CONFIGURATION throughout the upper packet locus. This is the second
  continuity, distinct from continuity in the density. It comes from the corpus's
  `contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl` (operator-norm smoothness in the nodes,
  requiring `ContDiff C top a` and `ContDiff C top q`), composed with evaluation at a density, which
  is continuous linear. So my flagged worry resolved positively — but it needed the two
  differentiability hypotheses on `a` and `q`, which the affine/genericity chain did NOT previously
  carry. Any compact-patch argument therefore inherits them.
  THE ACTUAL OBSTRUCTION IN (U2), which I had not previously stated correctly. Reading
  `actualNevanlinnaExpandedFullRankWitness`, its quantifier structure is
    for all shift, EXISTS packet, full rank,
  and the `hfull` hypothesis wraps that in `Dense {w | for all n, for all shift, ...}`. So the
  target set is an intersection over an UNCOUNTABLE shift family of sets each of which is dense —
  and an uncountable intersection of dense sets is not dense in general. Countability of the pattern
  quantifier does not help here; the shift quantifier is the uncountable one.
  Crucially, the packet is chosen AFTER the shift, so the nodes supplied by
  `exists_nodes_residual_expandedMatrix_nevanlinnaPacket` depend on the shift, and with them the
  dense residual set of densities. That dependence is exactly what blocks a naive intersection: the
  sets being intersected are not a fixed countable family.
  What the compact-patch reduction must therefore do is NOT "cover the shifts by countably many
  patches and intersect" — that only works if the condition on a whole compact patch is itself open
  and dense, which is a statement about a UNIFORM choice of packet over the patch, not a
  consequence of the pointwise statements. The continuity proved above is the input that makes a
  uniform choice plausible (a packet good at one shift stays good nearby), and
  `isOpen_setOf_forall_mem_compact_ne_zero` — built earlier on this card, with a pointwise
  `ContinuousAt` hypothesis — is the tool for turning that into openness on a patch. The density of
  the patchwise condition is the genuinely open sub-problem.
  Next: attempt patchwise density — fix a compact shift patch, use continuity to get a packet valid
  on a neighbourhood of each shift, extract a finite subcover, and intersect FINITELY many dense open
  conditions (finite intersections of dense open sets are dense, so the uncountability dissolves if
  and only if the finite subcover step goes through). Do not record as done before it compiles; the
  step that could fail is that the packet valid near one shift may fail to be valid on the whole
  patch, and finitely many packets give finitely many rank conditions that must hold SIMULTANEOUSLY
  for one density.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the OPENNESS half of the patchwise step is proved, and it does NOT need a finite
  subcover or a uniform choice of packet.
  `formal/GaloisForLFunctions/HTGeometry/CompactShiftPatchOpenness.lean`; axiom-clean; audit
  8500/8500.
  `isOpen_setOf_forall_mem_compact_notMem` — if the failure locus is closed JOINTLY in parameter and
  shift, the parameters succeeding at every shift of a COMPACT patch form an OPEN set. Proof is the
  generalized tube lemma applied to `{x} x K` inside the open complement.
  `isClosed_setOf_forall_zero` — the locus where a whole family of continuous functions vanishes is
  closed (an intersection of preimages of a point).
  `isOpen_setOf_forall_compact_exists_ne_zero` — combining them: if for each choice of DATUM the
  value is jointly continuous in (parameter, shift), then the parameters admitting, at EVERY shift of
  a compact patch, SOME datum with nonvanishing value form an open set.
  That last statement is exactly the shape of the witness condition — `for all shift, EXISTS packet`
  — restricted to a compact patch. Note what the tube lemma bought: I had planned to extract a
  finite subcover of shifts and intersect finitely many conditions, worrying that finitely many
  packets would have to work simultaneously for one density. That worry is void. The tube lemma
  handles the whole patch at once, and the existential over packets is absorbed into the closedness
  of the failure locus (an intersection over ALL packets of closed conditions is closed, however
  many packets there are). No subcover, no uniform packet.
  Recording the pattern, since it is the third time on this card that a quantifier obstruction
  dissolved by choosing the right formulation instead of by work: the uncountable existential is
  harmless inside a CLOSED condition, because arbitrary intersections of closed sets are closed. The
  obstruction is only ever with uncountable intersections of DENSE sets.
  REMAINING for (U2): the DENSITY half on a compact patch, i.e. that
  `{u | for all shift in K, exists packet, full rank}` is dense. Openness is now free; density is
  the open sub-problem and is NOT implied by the pointwise density statements. What is available to
  attack it: the set is open (just proved), the failure locus is closed, the jets depend
  analytically on the packet nodes, and for a FIXED shift the pointwise statement gives a packet
  working on a dense residual set of densities. What is NOT available and must not be assumed: that
  a density generic for one shift is generic for nearby shifts with the SAME packet — that is the
  content still missing, and the continuity proved last entry is the natural input to it.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the patchwise-to-global connector is proved, so the uncountable shift quantifier is
  now reduced to EXACTLY ONE unproved statement.
  `formal/GaloisForLFunctions/HTGeometry/PatchwiseToGlobalGenericity.lean`; compiled first try;
  axiom-clean; audit 8501/8501.
  `dense_and_residual_of_patchwise` — if the shift space is covered by countably many patches and
  for each patch the parameters satisfying the condition THROUGHOUT that patch form an open dense
  set, then the parameters satisfying it at EVERY shift are dense and residual. The global
  statement follows formally: the countable intersection of the patch sets is dense and residual,
  and it is contained in the global set because the patches cover.
  `dense_and_residual_of_patchwise_exists_ne_zero` — the same specialised to the witness shape, with
  openness supplied automatically by the previous entry's tube-lemma lemma, so its only remaining
  hypothesis is PATCHWISE DENSITY.
  STATE OF (U2). The uncountable shift quantifier costs exactly one thing now:
    for each compact patch K, `{u | for all shift in K, exists packet, full rank}` is DENSE.
  Everything else — openness on a patch, the countable exhaustion, the passage to the global
  quantifier, residuality — is proved. If patchwise density lands, the Nevanlinna family's
  dense+residual relation freeness follows by feeding this into
  `countablePatterns_relationFree_dense_residual_of_fullRankWitness` together with (U1)'s uniform
  choice over the countable pattern index.
  I am NOT going to record a route for patchwise density that I have not tested. What I know: the
  pointwise statements (a packet good for one shift on a dense residual set of densities) do not
  imply it, since that is the uncountable-intersection-of-dense-sets failure the whole reduction
  exists to avoid. The plausible input is that a density generic for one shift stays generic for
  NEARBY shifts with the SAME packet, which would let a single packet cover a neighbourhood and
  compactness finish; `continuousOn_nevanlinnaJets_nodes` is the continuity that would drive it. But
  whether the resulting neighbourhoods can be chosen uniformly enough for a dense set of densities
  is precisely the untested step, and on this card three of my untested structural predictions have
  been wrong in one direction or the other. Attempt it next; report what happens.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the remaining obligation is now stated in checkable form.
  `formal/GaloisForLFunctions/HTGeometry/PatchwiseDensityCriterion.lean`; axiom-clean; audit
  8502/8502.
  `patchwiseFailure` — the failure locus, `{x | exists s in K, for all c, f c (x,s) = 0}`.
  `dense_setOf_forall_compact_exists_ne_zero_iff` — patchwise density is EXACTLY emptiness of the
  interior of that locus (the condition is the complement of the locus, and
  `interior_eq_empty_iff_dense_compl`).
  `dense_and_residual_of_patchwiseFailure_interior_eq_empty` — the whole shift quantifier now
  reduces to: for each compact patch, the failure locus has EMPTY INTERIOR. Everything else is
  proved.
  WHAT I TRIED AND DID NOT GET, recorded so it is not retried blindly. I attempted to reduce
  patchwise density to a single packet working across a patch — i.e. `exists packet z such that
  {u | for all shift in K, det(u, shift, z) /= 0} is dense`. That sufficient condition is almost
  certainly FALSE and should not be pursued: for fixed `u` and `z` the determinant is analytic in
  the shift, so requiring it to be nonvanishing on an entire compact patch is a strong constraint,
  not a generic one. The existential over packets is therefore ESSENTIAL — different shifts need
  different packets — which is precisely why the tube-lemma formulation (existential absorbed into a
  closed condition) was the right move and why a finite-subcover argument was not needed.
  So the failure locus is genuinely a statement about ALL packets degenerating at once at some shift
  of the patch. That is a strong degeneracy, which is the reason to expect empty interior; but
  expecting is not proving, and I have no argument yet. The natural attack is that for fixed `u` and
  shift, `packet |-> det` is analytic, so "all packets degenerate" means an analytic function
  vanishes identically, and the set of densities forcing that should be thin — but turning "should
  be thin" into "has empty interior" is the open work.
  STATUS SUMMARY for the genericity side: every component proved except one, and that one is now a
  single sentence about a single explicitly-named set.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the packet existential is reduced to a COUNTABLE family.
  `formal/GaloisForLFunctions/HTGeometry/CountablePacketReduction.lean`; axiom-clean; audit
  8503/8503.
  `exists_ne_zero_iff_exists_mem_dense` — a continuous nonvanishing witness can always be taken in a
  DENSE set of witnesses: nonvanishing somewhere is nonvanishing on a neighbourhood, which meets any
  dense set.
  `setOf_forall_compact_exists_ne_zero_eq_dense_family` and `patchwiseFailure_eq_dense_family` —
  restricting the packet existential to a dense family leaves both the patchwise condition and its
  failure locus UNCHANGED. Since the packet space is a finite product of copies of C, it is
  separable, so a COUNTABLE dense family suffices.
  Why this matters for the remaining obligation: the failure locus is now
  `{u | exists shift in K, for all z in Q, det(u, shift, z) = 0}` with `Q` COUNTABLE. So the inner
  degeneracy is a countable intersection of closed conditions rather than an arbitrary one. The
  shift existential is still uncountable, but it is confined by compactness of `K` (which the tube
  lemma already exploited for openness).
  Recording the running pattern once more, since it has now paid four times on this card: every
  quantifier obstruction here has yielded to a change of formulation, not to added machinery —
  monomial independence by separating variables, node distinctness by a polynomial product, the
  blockwise assembly by never forming the cross-fibre comparison, the packet existential absorbed
  into a closed condition by the tube lemma, and now the packet existential made countable by
  density of witnesses. When a quantifier looks too large here, the first move should be to ask what
  it is quantifying INSIDE — closed conditions and continuous witnesses both shrink it for free.
  STILL OPEN, unchanged and not conjectured away: that the failure locus has EMPTY INTERIOR. The
  countable reduction does not by itself supply this; it only makes the object a countable
  intersection, which is the form a Baire argument could act on if one is found. I have no such
  argument yet and am not asserting one.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the SINGLE-SHIFT half of the remaining obligation is proved; the union over shifts is
  what stays open. `formal/GaloisForLFunctions/HTGeometry/SingleShiftFailureThin.lean`; axiom-clean;
  audit 8504/8504.
  `interior_setOf_forall_eq_zero_eq_empty` and `interior_setOf_forall_mem_eq_zero_eq_empty` — at ONE
  fixed shift, the parameters degenerating against every packet have EMPTY INTERIOR. The proof is
  containment: they degenerate in particular against the one packet the genericity theorem supplies,
  whose nondegeneracy set is dense, so the failure set sits inside a closed set with empty interior.
  The `mem Q` variant is the form left by the countable packet reduction.
  `dense_setOf_exists_ne_zero_of_dense` — consequently the parameters witnessing a FIXED shift are
  dense.
  So each `A_sigma` is closed and NOWHERE DENSE, and `patchwiseFailure` is their union over
  `sigma in K`. Both facts about the union are now precisely stated: it IS closed (tube lemma,
  proved earlier) and it is a union of nowhere dense closed sets — but the union is UNCOUNTABLE, so
  Baire does not apply and emptiness of interior does not follow. That is the entire remaining gap,
  and it is now a statement about one union of one explicitly described family.
  Attempts made and rejected this round, recorded so they are not retried:
  (i) reduce the SHIFT existential to a countable dense subset of `K`, as was done for the packet
  existential. This FAILS, and for a structural reason worth keeping: the packet reduction worked
  because the witness condition is OPEN in the packet (nonvanishing), so a witness survives into any
  dense set. The bad-shift condition is CLOSED in the shift, and a closed set can be a single point
  that misses every countable dense subset. Openness of the inner condition is exactly what made the
  packet case work and its absence is exactly what breaks the shift case.
  (ii) conclude from "each `A_sigma` nowhere dense" plus "`patchwiseFailure` closed". A closed set
  with nonempty interior is non-meager, so this would suffice IF the union were meager — but an
  uncountable union of nowhere dense sets need not be meager, and nothing here supplies that.
  What remains untried and is the natural next attack: for FIXED `u`, the set
  `{sigma | for all z, det(u,sigma,z) = 0}` is the common zero set of a countable family of
  functions ANALYTIC in `sigma`. If for a dense set of `u` at least one of those is not identically
  zero in `sigma`, that set is a proper analytic subset, hence has empty interior in shift space —
  but the requirement is that it be EMPTY on `K`, not merely thin, so analyticity alone is not
  enough and something must rule out isolated bad shifts. Do not assume it does.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the shift quantifier is reduced to a FINITE packet family, per parameter.
  `formal/GaloisForLFunctions/HTGeometry/FiniteSubcoverPacket.lean`; compiled first try;
  axiom-clean; audit 8505/8505.
  `forall_mem_compact_exists_ne_zero_iff_finset` — at a fixed parameter, witnessing every shift of a
  COMPACT patch is EQUIVALENT to witnessing it with FINITELY many packets. The witness condition is
  open in the shift (nonvanishing of a continuous function, and the packet existential is a union of
  such open sets), so `IsCompact.elim_finite_subcover` applies.
  `setOf_forall_compact_exists_ne_zero_eq_iUnion_finset` — hence the patchwise condition is a UNION
  over finite packet families `F` of the conditions "this one finite family covers the whole patch".
  With a countable dense packet family (previous entry) the index `Finset Z` is countable, so this
  is a COUNTABLE union.
  This is the finite-subcover idea I dismissed several entries ago as unnecessary, and I had it
  placed wrongly then: I was trying to make the finite family UNIFORM in the parameter, which is
  false and is not what compactness gives. The finite family depends on the parameter, and the
  equivalence above is per-parameter. Both statements are true; only the second is useful. Recording
  the correction because "I already ruled that out" was wrong and nearly cost the route.
  WHERE THIS PUTS THE REMAINING GAP. The patchwise condition is now a countable union of sets
  `V_F = {u | the finite packet family F covers K}`. Density of a countable UNION does not follow
  from density of one member unless that member is dense — but conversely it SUFFICES that a single
  `V_F` be dense. So the obligation has weakened from
    "for a dense set of parameters, every shift of K is witnessed"
  to the strictly easier
    "for SOME finite family of packets F, the parameters for which F covers K are dense".
  That is a real weakening and it is the first form of this obligation that looks attackable by the
  tools already on the card: `V_F` is a finite intersection of conditions of the shape already
  handled, and finite intersections of dense open sets are dense.
  NOT yet done and not assumed: exhibiting such an `F`, or proving `V_F` dense for one. Finite
  intersections of dense open sets are dense, but `V_F` is not literally such an intersection —
  it says the union of the F-many nonvanishing sets covers K, which is weaker than any single one
  covering K and is not a finite intersection of the per-packet dense conditions. That mismatch is
  the next thing to work out.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the mismatch of the previous entry is resolved, and the whole shift quantifier now
  reduces to ONE positive statement about packets.
  `formal/GaloisForLFunctions/HTGeometry/NoCommonDegeneracyCriterion.lean`; compiled first try;
  axiom-clean; audit 8506/8506.
  THE ANALOGUE THAT SETTLED IT. Model case `f(u,sigma) = u - sigma` with `u` and `sigma` complex.
  With ONE packet, `{u | for all sigma in K, f /= 0}` is the complement of `K`, which is NOT dense
  when `K` has interior — so my earlier judgement that a single packet cannot work was correct, and
  now for a concrete reason rather than a heuristic about analytic zeros. With TWO packets
  `f_1 = u - sigma` and `f_2 = u - sigma - 1`, no `u` can degenerate against both at the same
  `sigma`, so the condition holds for EVERY `u`. The finite family works precisely because distinct
  packets degenerate at distinct shifts; nothing about density is needed once degeneracies are
  disjoint.
  `forall_mem_compact_exists_ne_zero_of_no_common_zero` — a finite family that never degenerates
  simultaneously on the patch gives the patchwise condition for EVERY parameter.
  `dense_setOf_forall_compact_exists_ne_zero_of_dense_no_common_zero` — it suffices that this hold
  on a DENSE set of parameters.
  `dense_and_residual_of_dense_no_common_zero` — combining with the compact exhaustion: if every
  patch admits such a family on a dense set of parameters, the parameters witnessing EVERY shift are
  dense and residual. This is the complete reduction of the shift quantifier.
  THE ENTIRE REMAINING OBLIGATION on the genericity side is now this, and nothing else:
    for each compact patch K of shifts, exhibit a FINITE family of packets that, for a dense set of
    densities, never all degenerate at the same shift of K.
  This is a positive construction rather than a negative genericity claim, which is a better kind of
  target: it asks to build finitely many packets with disjoint degeneracy loci, not to prove some
  set is thin. The two-packet analogue above suggests the mechanism — translating a packet moves its
  degeneracy locus in the shift variable — and the card already has the tool for producing packets
  with prescribed nondegeneracy at a chosen shift
  (`exists_nodes_residual_expandedMatrix_nevanlinnaPacket`).
  NOT done and NOT assumed: that translated packets have disjoint degeneracy loci, or that finitely
  many suffice for a whole patch. The analogue is an analogue, not a proof about the Nevanlinna
  determinant.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the positive construction WORKS, abstractly and in Lean.
  `formal/GaloisForLFunctions/HTGeometry/TranslateFamilyEscapesPatch.lean`; compiled first try;
  axiom-clean; audit 8507/8507.
  `exists_finset_translates_notMem` — if `D` is CLOSED with EMPTY INTERIOR, then every point of a
  COMPACT set escapes one of FINITELY MANY translates of `D`. The argument is short and is the one
  the previous entry's analogue predicted:
    - empty interior means the complement is dense, so pick any escape point `p` not in `D`;
    - every shift `s` escapes the translate by `s - p`, since `s - (s - p) = p`. So the pointwise
      statement is free — no genericity needed, just one point outside `D`;
    - escaping a FIXED translate is an OPEN condition on the shift (preimage of an open complement),
      so the translates cover `K` by open sets and compactness extracts a finite subfamily.
  `exists_finset_no_common_zero_of_translation_covariant` — packaging it: if the value is covariant
  under simultaneous translation of datum and shift, `f (tr z t) (x,s) = f z (x, s - t)`, then
  finitely many translates of a single datum NEVER degenerate simultaneously on the patch. That is
  exactly the hypothesis `dense_and_residual_of_dense_no_common_zero` consumes.
  So the shift quantifier is now closed ABSTRACTLY, end to end, from two inputs about the actual
  Nevanlinna determinant and nothing else:
  (T1) TRANSLATION COVARIANCE: `det(u, sigma, packet translated by -t) = det(u, sigma - t, packet)`.
  This should hold structurally, since the combined nodes are `packet r + shift i` and translating
  the packet by `-t` while translating the shift by `+t` leaves every combined node unchanged. It is
  a statement about the packet/shift addition in `combinedProjectiveRowShiftPacket` and needs to be
  proved, not asserted — the row and shift index types differ and the translation must act
  uniformly.
  (T2) THIN DEGENERACY: for the relevant densities, `{sigma | det(u, sigma, z) = 0}` is closed with
  EMPTY INTERIOR. Closedness is continuity, already available. Empty interior needs that
  `det(u, . , z)` is not identically zero on any ball, which is where ANALYTICITY in the shift and
  the identity theorem enter — and the card already has `contDiffOn` smoothness in the nodes, though
  smooth is weaker than analytic and the identity theorem needs the latter. Do not conflate the two:
  this is the one place where the existing smoothness result may be insufficient and a genuinely
  analytic statement is required.
  Note what changed in character: the remaining work is now two CONCRETE properties of a specific
  determinant, both local statements, with no genericity, Baire, or quantifier structure left in
  them. Every uncountable quantifier on the genericity side has been discharged.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — (T1) TRANSLATION COVARIANCE IS PROVED.
  `formal/GaloisForLFunctions/HTGeometry/PacketShiftTranslationCovariance.lean`; axiom-clean; audit
  8517/8517.
  `combinedProjectiveRowShiftPacket` is literally `packet.1 x.1 + shift.1 x.2`, so:
  `translatePacket` and `translateShift` — translation preserves injectivity, so it acts on both
  `InjectiveProjectiveRowPacket` and `InjectiveShiftConfiguration` (both are subtypes of injective
  families; injectivity survives because `sub_left_inj`).
  `combinedProjectiveRowShiftPacket_translatePacket` — translating the PACKET by `t` gives the same
  combined node family as translating the SHIFT by `t`. One `funext` and a `ring`.
  `eq_of_combined_translate` — hence ANY quantity determined by the combined node family is
  covariant. This is the form that matters: the jets, the evaluation matrix and its determinant all
  factor through the combined family, so none of them needs a separate covariance proof. Stating it
  for an arbitrary `Phi` avoids re-deriving covariance at each layer of the chain.
  `translatePacket_translatePacket` — translations compose additively, so the translate family is a
  genuine group action and finitely many translates can be indexed by their offsets.
  This was the hypothesis I flagged as "should hold structurally, but the row and shift index types
  differ and it must be proved, not asserted". It did hold structurally, and the index-type worry
  was unfounded: the two translations act on different factors of `row x iota` and never interact.
  REMAINING for the shift quantifier: (T2) ALONE.
    for the relevant densities, `{sigma | det(u, sigma, z) = 0}` is CLOSED with EMPTY INTERIOR.
  Closedness is continuity and is available. Empty interior is the open item, and the concern
  recorded last entry stands unchanged and unresolved: the corpus supplies `ContDiffOn` smoothness
  of the control map in the nodes, but SMOOTH IS NOT ANALYTIC, and the identity theorem — which is
  what turns "not identically zero" into "zero set has empty interior" — needs analyticity. A smooth
  function can vanish on a ball without vanishing identically. So either an analyticity statement
  must be established for the determinant in the shift, or empty interior must be obtained some
  other way. Do not paper over this with the smoothness result already in hand.
  Note the determinant IS a polynomial in the jets and the jets ARE built from Cauchy powers
  `((r - x)^{-1})^{k+1}` in the nodes, which are holomorphic off the real axis — so analyticity is
  very plausible and the ingredients are present; but plausible is not proved, and this card has
  twice punished exactly that step.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — (T2) DOES NOT EXIST. The analyticity requirement was an artefact of an unnecessarily
  strong hypothesis in my own lemma, found by re-reading the proof rather than by new mathematics.
  `formal/GaloisForLFunctions/HTGeometry/TranslateFamilyEscapesPatch.lean` updated; dependents
  rebuild clean; axiom-clean; audit 8517/8517.
  `exists_finset_translates_notMem` previously assumed `interior D = empty`. Re-reading its proof,
  the empty-interior hypothesis was used ONLY to obtain `Dense D^c` and then ONLY via
  `.nonempty` — that is, to produce a single point outside `D`. Nothing else in the argument touched
  density. The hypothesis is therefore weakened to `exists p, p not in D`, and `Nonempty S` is
  dropped as well (it followed from the escape point). The lemma compiles unchanged otherwise.
  Consequences, which are large:
    - The requirement that the degeneracy locus be THIN is gone. Only CLOSED (continuity, already
      available) plus ONE non-degenerate shift is needed.
    - Therefore no analyticity of the determinant in the shift is required, and the concern recorded
      for two entries — that the corpus supplies `ContDiffOn` smoothness while the identity theorem
      needs analyticity — is VOID. It was a real gap in the route I had written down, but the route
      did not need to be that way.
    - The single non-degenerate shift is exactly what
      `exists_nodes_residual_expandedMatrix_nevanlinnaPacket` already produces.
  Why the escape works with so little: translating the escape point `p` onto a given shift `s` (take
  offset `s - p`) escapes at `s` by construction, so the POINTWISE statement is free for every shift
  whatever `D` looks like. Escaping a fixed translate is open, so compactness finishes. Thinness of
  `D` was never doing any work; it only looked necessary because the analogue that motivated the
  construction (`f = u - sigma`) has a thin degeneracy locus incidentally.
  PROCESS NOTE, recorded because it is the second time this session that re-reading my own proof
  beat proving something new: the previous instance was the `CarrierJetNondegenerateAt` predicate,
  where re-reading showed a hypothesis was unsatisfiable. Here it showed a hypothesis was
  unnecessary. Both were found by reading, not by thinking harder about the mathematics.
  STATUS: the shift quantifier is closed except for assembling the abstract lemmas against the
  concrete Nevanlinna determinant — translation covariance (proved), closedness of the degeneracy
  locus (continuity), and one non-degenerate shift (the packet theorem). No open mathematical
  content remains on the genericity side that I am aware of.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — THE SHIFT QUANTIFIER IS CLOSED, abstractly and completely.
  `formal/GaloisForLFunctions/HTGeometry/ShiftQuantifierClosure.lean`; compiled first try;
  axiom-clean; audit 8518/8518.
  `dense_and_residual_forall_shift_of_translate` — given
    (a) continuity of each datum's value,
    (b) covariance under simultaneous translation of datum and shift,
    (c) a compact exhaustion of the shift space,
    (d) a DENSE set of parameters on which ONE fixed datum is nondegenerate at SOME ONE shift,
  the parameters witnessing EVERY shift are DENSE and RESIDUAL.
  That is the entire uncountable shift quantifier, discharged from four hypotheses none of which
  mentions thinness, analyticity, transversality or Baire. Hypothesis (d) is strikingly weak — one
  datum, one shift — and it is exactly what
  `exists_nodes_residual_expandedMatrix_nevanlinnaPacket` delivers.
  A detail that made the assembly work: the criterion
  `dense_and_residual_of_dense_no_common_zero` wants a finite family `F` independent of the
  parameter, but the translate construction produces a family depending on the parameter (through
  the escape point). That is not an obstruction, because the witness condition
  `for all s, exists z, f z (x,s) /= 0` already lets `z` depend on both `x` and `s`. So the
  fixed-`F` criterion is bypassed and `dense_and_residual_of_patchwise_exists_ne_zero` is applied
  directly. Worth noting: the intermediate criterion I built two entries ago was over-specified for
  the job, and recognising that was faster than trying to make the finite family uniform — which is
  the same mistake, made and corrected, that the finite-subcover entry records.
  WHAT REMAINS ON THE GENERICITY SIDE: instantiating this against the concrete Nevanlinna
  determinant. The four inputs map to:
    (a) continuity of the determinant in (density, shift) — the two continuity results are proved
        (`continuous_expandedDifferentialEvaluationMatrix` in the jets,
         `continuousOn_nevanlinnaJets_nodes` in the nodes); combining them into JOINT continuity in
        the pair is the one thing not yet done and should not be assumed — joint continuity does not
        follow from separate continuity in general, though here linearity in the density plus local
        uniformity should give it, and `continuousAt_uncurry_of_lipschitz_of_continuousAt` was built
        earlier on this card for exactly this shape;
    (b) `eq_of_combined_translate`, proved;
    (c) the upper-half-plane exhaustion `upperPatch` / `iUnion_upperPatch`, in the tree;
    (d) the packet theorem, proved.
  So the genericity side has exactly one open item and it is a joint-continuity statement, not
  research content.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — JOINT CONTINUITY IS PROVED. This was the last item I had flagged as open on the
  genericity side. `formal/GaloisForLFunctions/HTGeometry/NevanlinnaJetJointContinuity.lean`;
  compiled first try; axiom-clean; audit 8625/8625.
  `continuous_clm_apply_pair` — evaluation of a continuous linear map at a vector is JOINTLY
  continuous, since it is a bounded bilinear operation (`isBoundedBilinearMap_apply`, in the ROOT
  namespace, not under `ContinuousLinearMap` as I first guessed).
  `continuousOn_nevanlinnaJets_pair` — on the upper packet locus the jet packet depends continuously
  on the node configuration AND the bounded density TOGETHER.
  The proof is the composition the structure suggests: the control map is continuous in the nodes in
  OPERATOR NORM (`contDiffOn_...`, from the corpus), so pairing it with the identity on densities and
  composing with the bilinear evaluation gives joint continuity. Operator-norm continuity is what
  makes this work — continuity of each `control z` and of `z |-> control z u` separately would NOT
  have sufficed, which is exactly why I flagged this rather than assuming it.
  GENERICITY SIDE — all four inputs of `dense_and_residual_forall_shift_of_translate` are now
  proved for the Nevanlinna family:
    (a) joint continuity — this entry;
    (b) translation covariance — `eq_of_combined_translate`;
    (c) compact exhaustion — `upperPatch` / `iUnion_upperPatch`;
    (d) one nondegenerate shift on a dense set — `exists_nodes_residual_expandedMatrix_nevanlinnaPacket`.
  No item on the genericity side is open that I am aware of. What is left is INSTANTIATION: feeding
  these four into the closure theorem with the concrete determinant in place of the abstract `f`,
  and threading the pattern quantifier through (U1)'s uniform choice. That is assembly, and on this
  card assembly has twice turned out to hide an index or shape mismatch, so it is not to be called
  done in advance.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — RETRACTION AND CORRECTION. Attempting the instantiation found a real shape mismatch,
  and my previous entry's claim that "no item on the genericity side is open" was WRONG.
  `formal/GaloisForLFunctions/HTGeometry/OrbitEscapeCompactPatch.lean`; compiled first try;
  axiom-clean; audit 8626/8626.
  THE MISMATCH. `exists_finset_translates_notMem` has the shift space acting ON ITSELF: translation
  is `s - t` with `t` ranging over the shift space, and the escape point argument
  (`s - (s - p) = p`) uses that freedom essentially. In the Nevanlinna setting the available
  translation group is only C, acting DIAGONALLY: the packet is indexed by `row` and the shift by
  `iota`, so `combinedProjectiveRowShiftPacket` is covariant ONLY under a uniform scalar translation
  of both. A row-dependent change of packet moves the nodes `(r,i)` by a row-dependent amount, which
  is not a change of shift at all. So the orbit of a shift configuration under the covariance group
  is a one-dimensional DIAGONAL LINE inside a high-dimensional shift space, and the action is NOT
  transitive. The escape-point argument therefore does not apply as written.
  WHAT IS SALVAGED, and it is most of the structure. Separating the two steps shows they are
  independent:
  `exists_finset_escape_of_pointwise` — COMPACTNESS upgrades POINTWISE escape (every shift of the
  patch is carried off the locus by SOME group element) to a FINITE family serving the whole patch.
  This step is free and holds for any action, transitive or not.
  `exists_escape_of_transitive` — pointwise escape follows from transitivity plus one point off the
  locus. This is the step that fails for the Nevanlinna action.
  `exists_finset_escape_of_transitive` — their composition, which is the earlier lemma in corrected
  generality.
  SO THE ACTUAL OPEN ITEM, stated correctly this time:
    for each shift configuration `sigma` in a compact patch, some DIAGONAL translate
    `sigma + t*(1,...,1)` must be nondegenerate for the given density.
  That is a statement about the determinant restricted to a line through `sigma`, and it is exactly
  where analyticity would earn its keep: a nonzero analytic function of one variable `t` has
  isolated zeros, so if the restriction to the diagonal line is not identically zero, escape is
  immediate. This RESURRECTS the analyticity question that the previous weakening had retired — but
  now in a much smaller form, one complex variable rather than the full shift space.
  Recording the error honestly: I weakened `interior D = empty` to `exists p, p not in D` and
  concluded the analyticity concern was void. The weakening was correct AND the conclusion was wrong,
  because the weakened hypothesis is only sufficient when the action is transitive, which I had not
  checked. The lesson is the one this card keeps teaching: check the instantiation before declaring
  the abstraction adequate.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — the diagonal-line escape tools are in, and writing them clarified where analyticity
  does and does not help. `formal/GaloisForLFunctions/HTGeometry/AnalyticLineEscape.lean`;
  axiom-clean; audit 8627/8627.
  `exists_ne_zero_near_of_analytic` — an analytic function on a preconnected open set that is
  nonzero SOMEWHERE is nonzero at points ARBITRARILY CLOSE to ANY given point. Proof by the identity
  theorem (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`): if it vanished on a whole
  neighbourhood of the given point it would vanish identically.
  `exists_ne_zero_on_line` — the same on the whole plane, which is the form a translation line takes.
  A CORRECTION MADE WHILE WRITING. My first version of the escape lemma carried an analyticity
  hypothesis `hline` and Lean reported it UNUSED. That is informative rather than cosmetic: escaping
  the degeneracy locus along a shift's translation line IS, definitionally, the existence of one
  translate where the value is nonzero. Analyticity contributes nothing to that step. Its only role
  is DERIVING that existence from weaker information — specifically from "the restriction to the line
  does not vanish identically", which is what `exists_ne_zero_near_of_analytic` converts. The lemma
  is renamed `escape_of_line_ne_zero` and the false hypothesis removed.
  So the remaining obligation is unchanged in substance but now correctly located:
    for a dense set of densities `u`, and every shift configuration `sigma` in a compact patch, the
    map `t |-> det(u, sigma + t*(1,...,1), z)` must not vanish identically in `t`.
  Two things would each suffice and neither is proved:
    (i) that this restriction is analytic in `t` AND nonzero at some `t` depending on `sigma`;
    (ii) any direct argument producing one good translate per shift.
  Note (i) still needs a per-sigma nonvanishing point, so analyticity alone does not close it — it
  converts "nonzero somewhere on the line" into "nonzero near every point of the line", which is
  strictly more than needed. The genuinely missing ingredient is a source of one nonvanishing point
  on EACH line, uniform in a dense set of densities. The packet theorem supplies nonvanishing at a
  given shift for a dense set of densities that DEPENDS on the shift, and that dependence is exactly
  what has to be removed.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — a new reduction gets DENSELY many good shifts on a residual set of densities, which
  is strictly short of the witness predicate by a closed nowhere dense set.
  `formal/GaloisForLFunctions/HTGeometry/DenseGoodShiftSet.lean`; compiled first try; axiom-clean;
  audit 8628/8628.
  The reduction, which is new and does not repeat earlier attempts: the packet theorem gives for
  EACH shift a RESIDUAL set of densities witnessing it. Residual sets are stable under COUNTABLE
  intersection (`residual_iInter_of_countable`). So intersect over a COUNTABLE DENSE family `Q` of
  shifts: the result is a residual — hence dense — set `R` of densities each of which witnesses
  every shift in `Q`.
  `dense_goodShift_of_countable_dense_witnessed` — for a density in `R`, the good-shift set is OPEN
  (proved earlier) and contains the dense family `Q`, hence is DENSE; equivalently the bad-shift set
  is CLOSED with EMPTY INTERIOR.
  Why this does not finish, stated exactly: the witness predicate needs the good-shift set to be
  ALL of the shift space (`forall_mem_goodShift_iff_compl_eq_empty`), and an open dense set can have
  nonempty closed nowhere-dense complement. A single bad shift is enough to fail the predicate, and
  density of the good set does not exclude one.
  Why the earlier objection does not apply to this argument: several entries ago I rejected reducing
  the shift quantifier to a countable dense subset, on the ground that the bad-shift condition is
  CLOSED in the shift so knowing goodness on a dense subset does not extend. That objection remains
  correct and is exactly why this reduction stops where it does — it delivers density of the good
  set, not its totality. What is new here is that the reduction is nonetheless VALID and gives a
  residual set of densities, which the earlier framing did not extract; the countable intersection
  is over shifts and lands in the DENSITY space, where residuality is available, rather than trying
  to extend a property across the shift space.
  So the gap is now quantified: the shortfall between what is proved and what the predicate demands
  is a closed nowhere dense set of shifts, for each density in a residual set. Closing it requires
  ruling out isolated bad shifts, which is precisely the diagonal-line escape question of the
  previous entry — for a bad shift `sigma`, some translate `sigma + t*(1,...,1)` is good, and
  goodness is open, so the bad set cannot contain a whole translation line segment. Whether that
  suffices to empty it is the open question; it does not follow from nowhere density alone.
  Then: the probability-carrier family via the multiplicative gauge; and the Krein-index chamber
  half, still untouched.
- 2026-07-19 — analytic thinness packaged; and a status checkpoint, because the shift sub-problem has
  now resisted several distinct attacks and the card's other open half has not been started.
  `formal/GaloisForLFunctions/HTGeometry/AnalyticZeroSetThin.lean`; axiom-clean; audit 8629/8629.
  `interior_zeroSet_eq_empty_of_analytic`, `dense_compl_zeroSet_of_analytic`,
  `interior_lineDegeneracy_eq_empty` — the zero set of an analytic function that is nonzero
  somewhere has empty interior; along a translation line, degeneracy is therefore confined to
  isolated points.
  ATTACKS TRIED ON THE REMAINING SHIFT GAP, all recorded so none is repeated:
  1. single packet covering a patch — FALSE (model case `f = u - sigma`, bad set is `K`, has
     interior).
  2. reduce the shift existential to a countable dense subset — FAILS, bad-shift condition is closed
     in the shift.
  3. finite subcover with a UNIFORM finite packet family — FALSE; compactness gives a per-density
     family, which is what the witness condition actually permits.
  4. escape-point translation argument — VALID abstractly, but the covariance group is only C acting
     diagonally and is NOT transitive, so pointwise escape is not free. (This is where I wrongly
     declared the side closed; retracted.)
  5. countable intersection of residual sets over a dense family of shifts — VALID and new, gives a
     residual set of densities whose good-shift set is open and DENSE, i.e. bad set closed and
     nowhere dense. Falls short by exactly that nowhere dense set.
  6. analyticity along the diagonal line — gives that degeneracy on a line is isolated, but still
     requires one good point per line, which is the thing not available uniformly.
  WHAT IS ACTUALLY MISSING, in one sentence: a source of ONE nondegenerate packet at EVERY shift,
  valid for a single density — the packet theorem gives this per shift with a density set that
  depends on the shift, and no attack so far removes that dependence.
  ASSESSMENT. The genericity side is complete except this, and it is a genuine research step rather
  than assembly. It may be that the witness predicate as stated (`for all shift, exists packet`) is
  simply stronger than the Baire method delivers, and that the corpus's own
  `NevanlinnaNoncriticalProjectiveCompactPatch` development handles the shift quantifier by a route
  I have not read. THAT IS THE NEXT THING TO DO: read that module's treatment of the shift
  quantifier before attacking a seventh time. Repeatedly re-deriving is worse than reading what is
  already in the tree, and on this card reading has twice beaten proving.
  Also still untouched after all of this: the probability-carrier family via the multiplicative
  gauge, and the Krein-index chamber half of the card.
- 2026-07-19 — MAJOR CORRECTION. The shift quantifier was ALREADY SOLVED IN THIS TREE, and I spent
  many iterations re-deriving a sub-problem that has a complete, axiom-clean proof in
  `GaloisForLFunctions/HTGeometry/NevanlinnaNoncriticalProjectiveCompactPatch.lean`. Reading that
  module, as I committed to last entry instead of attacking a seventh time, found it immediately.
  The chain that exists, all verified `[propext, Classical.choice, Quot.sound]`:
    `compact_injectiveShiftPatch_has_dense_completeAtlas_actualNevanlinna` (line 556) — a COMPACT
    shift patch admits a finite compact refinement by complete combined row charts, and the rank
    condition on every member is open dense; hence EVERY shift in the patch has a row packet
    witnessing full rank.
    `global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual` (line 684) — sigma
    compactness of the shift configuration space upgrades that to ALL shifts, one dense residual set.
    `countablePatterns_global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual`
    (line 750) — all patterns and all shifts at once.
    `countablePatterns_actualNevanlinna_relationFree_dense_residual` (line 830) — the capstone:
    relation-freeness, dense and residual.
  THE MECHANISM I WAS MISSING, and it is the thing I dismissed earliest on this card. The compact
  patch theorem carries
    `hrows : card (kappa x Fin (degree+1)) + degree < card row`
    `hdim  : finrank R (iota -> C) < 2 * (card row - card (kappa x Fin (degree+1)) - degree + 1)`
  — a DIMENSION COUNT. With ENOUGH ROWS the rank-defect locus has codimension exceeding the
  dimension of the shift space, and then a SINGLE packet can cover a whole compact patch of shifts.
  My attack (1), "a single packet covering a patch is FALSE", was refuted by the model case
  `f = u - sigma`, which is codimension 1 against dimension 1 — exactly the borderline. In the real
  setting the ROW COUNT is a free parameter that pushes codimension up, and the statement becomes
  TRUE. The model case was not a counterexample to the real claim; it was a counterexample to the
  claim WITHOUT the dimension hypothesis, and I never asked whether such a hypothesis was available.
  This retroactively corrects my very first assessment on this card, that the paper's codimension
  count "is doing something the Lean route does not need here". That was true for the monomial
  independence step and I over-generalised it to the whole development. The codimension count is
  exactly what the shift quantifier needs, and the corpus already implements it.
  COST OF THE ERROR: roughly a dozen iterations of genuine but redundant work. The modules produced
  are correct and axiom-clean and several are reusable in their own right (the tube-lemma patch
  openness, the countable packet reduction, the translate escape, the analytic thinness lemmas), but
  none of them was necessary for this card.
  RULE FOR THIS CARD GOING FORWARD, and the reason the last entry's decision was right: before
  attacking any sub-problem here, grep the corpus for a theorem whose STATEMENT matches the goal,
  not merely for the objects involved. I searched repeatedly for the objects (packets, shifts,
  witnesses) and found the definitions, but never searched for the CONCLUSION shape
  ("dense residual" + "all shift"), which would have surfaced this module immediately.
  NEXT, with the shift quantifier removed from the open list: connect the existing capstone to the
  card's carrier-side predicate `MaximalTranslationFullRankWitness`, which is phrased through the
  PROBABILITY-CARRIER family rather than the Nevanlinna one; then the Krein-index chamber half.
- 2026-07-19 — AUDIT FINDING: this card's own "Lean status" section is STALE, and reading it (and
  section 2) earlier would have prevented the redundant work of the last dozen entries. Two
  corrections, both verified against the tree today.
  (1) The status says the tree "does not yet contain the corresponding `L^infinity(mu)` measure-level
  surjectivity theorem for arbitrary nondiscrete support". IT DOES:
  `HTGeometry.WeightedJetControlSurjective.surjective_weightedJetControl` — for a base measure of
  infinite support with a strictly positive integrable weight, every finite Cauchy-jet vector is
  realized by a bounded reweighting. That is exactly section 1 of this card (`v_(p,ell)(t) =
  ell!/(t-x_p)^(ell+1)` weighted by `exp(u_0)`), with no discreteness assumption. Axiom-clean.
  (2) The status lists "algebraic rank-defect codimension" and "full parametric transversality" as
  missing. The compact-patch chain in `NevanlinnaNoncriticalProjectiveCompactPatch` carries both, as
  the explicit hypotheses
  `hrows : card (kappa x Fin (degree+1)) + degree < card row` and
  `hdim : finrank R (iota -> C) < 2 * (card row - card (kappa x Fin (degree+1)) - degree + 1)`,
  and uses them to prove the all-shift, all-pattern, dense-residual rank law and the
  relation-freeness capstone. Axiom-clean.
  ALSO: SECTION 2 OF THIS CARD IS TITLED "Uncountable shifts by finite-dimensional transversality"
  and describes precisely the matrix with `(a,(beta,d))` entry `z_a^d M_beta(x_a)` and its
  rank-defect locus `B`. That is `expandedDifferentialEvaluationMatrix` and
  `expandedDifferentialEvaluationRankDefect`, both in the tree. The card stated the mechanism for the
  shift quantifier — finite-dimensional transversality, i.e. the codimension count — in its own
  SECTION HEADING, and I attacked that quantifier six ways without reading the section that names its
  solution.
  CONSOLIDATED LESSON for this card, now demonstrated three times (vacuous predicate, unnecessary
  hypothesis, and the whole shift quantifier): READ FIRST — the card's own sections and status, and
  the corpus by CONCLUSION SHAPE — before deriving anything. Grepping for the objects involved finds
  definitions; grepping for the conclusion finds the theorem.
  WHAT IS GENUINELY OPEN, after these corrections and to the best of what I have verified:
  the card's family is `exp(u) dmu` — POSITIVE reweightings via the MULTIPLICATIVE gauge — while the
  formalized capstone chain is for the Nevanlinna family `baseDensity + w`, an additive linear
  slice. Bridging them is where `affine_reachability_of_multiplicative_chart` (proved earlier this
  session) and `differentialIndependent_mulBase_iff` are the intended tools, and that bridge is NOT
  yet built. The Krein-index chamber half of the card is likewise untouched.
  The `Lean status` section above should be rewritten by whoever next audits this card; I am
  appending rather than editing it so the original wording and this correction both remain visible.
- 2026-07-19 — the multiplicative-gauge bridge is started, with the hypothesis shape corrected to
  match what the corpus actually supplies.
  `formal/GaloisForLFunctions/HTGeometry/MultiplicativeGaugeCompositeReachability.lean`; compiled
  first try; axiom-clean; audit 8562/8562.
  `affine_reachability_of_multiplicative_chart_composite` — the reachability argument needs only
  surjectivity of the COMPOSITE `J . (M u0)`, not of the jet map and the multiplication separately.
  The earlier version of this lemma asked for both factors, which is strictly stronger and is NOT
  what is available: for the Herglotz family the object in hand is the jet map of a reweighting
  AGAINST THE BASE WEIGHT, which is already the composite. Checking what the corpus supplies before
  fixing the hypothesis shape is the rule this card has been teaching; applying it here saved
  inventing a surjectivity statement for `M u0` alone, which would have needed the L-infinity
  algebra structure that mathlib lacks.
  `surjective_herglotz_composite` — that composite is `weightedJetControl mu w hw x ... n` with
  `w = exp(u_0)`, and its surjectivity is `surjective_weightedJetControl`, for a base measure of
  infinite support with a strictly positive integrable weight. So hypothesis (i) of the bridge is
  discharged for the card's actual family `exp(u) dmu`.
  WHAT THE BRIDGE STILL NEEDS, and neither is assumed:
  (M1) THE CHART IDENTITY `G u = G u0 + M u0 h` for the exponential chart, i.e.
  `exp(u0 + log(1+h)) = exp(u0) + exp(u0)*h` with `u := u0 + log(1+h)` near `u0` for small `h`.
  This is the item that needs `log(1+h)` to exist in the density space with a norm estimate. Recall
  the earlier finding that `Lp R (top) mu` has NO `Ring` instance in mathlib, so the pointwise
  exponential and logarithm on L-infinity must be built directly as measurable-function operations
  rather than through a Banach-algebra functional calculus. That is real work and is the honest
  remaining core of the multiplicative side.
  (M2) The composition of the bridge with the genericity conclusion, once (M1) lands.
  Note what is NOT needed, which the composite form makes visible: no surjectivity of multiplication
  by `exp(u0)` as a map on the density space, hence no invertibility of that multiplication, hence
  no requirement that `exp(u0)` and its reciprocal both be bounded. The composite formulation
  removed a hypothesis I had listed as required three separate times.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — the numerical core of (M1) is proved.
  `formal/GaloisForLFunctions/HTGeometry/LogOnePlusBound.lean`; axiom-clean; audit 8563/8563.
  `log_one_add_le` — `log (1+x) <= x` for `x > -1`, from `Real.log_le_sub_one_of_pos`.
  `le_log_one_add` — `x/(1+x) <= log (1+x)`, the same inequality applied to `1/(1+x)`.
  `abs_log_one_add_le_two_mul` — for `|x| <= 1/2`, `|log (1+x)| <= 2|x|`. This is the uniform
  constant the multiplicative gauge needs: since the bound is POINTWISE it passes to the essential
  supremum without any further argument, so `norm (log (1+h)) <= 2 * norm h` in L-infinity once the
  measurability side is handled.
  Checked first, per the rule this card has been teaching: `PrimeLogGaugePerturbation` in the tree is
  the DISCRETE prime-indexed gauge, not a general L-infinity construction, so this layer genuinely
  had to be built rather than found.
  WHAT REMAINS OF (M1), and it is measure-theoretic plumbing rather than analysis:
    - `log (1+h)` is measurable and essentially bounded when `h` is, given `norm h < 1/2` — the
      bound above supplies boundedness; measurability is composition with a continuous function on
      the relevant range.
    - the pointwise identity `exp (u_0 + log (1+h)) = exp u_0 * (1+h)` a.e., which needs `1+h > 0`
      a.e., again from `norm h < 1/2`.
    - assembling these into the chart hypothesis `G u = G u_0 + M u_0 h` with `u := u_0 + log (1+h)`
      and `dist u u_0 <= 2 * norm h < epsilon`, which is where the choice `delta := min (1/2) (eps/2)`
      enters.
  None of that is assumed; all of it is stated so the next iteration can execute it directly. With
  (M1) done, `affine_reachability_of_multiplicative_chart_composite` plus
  `surjective_herglotz_composite` discharge the reachability for the card's actual family
  `exp(u) dmu`, which is the last structural piece of the multiplicative side.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — SECOND DUPLICATION FOUND AND REVERTED. My previous entry's `LogOnePlusBound.lean` was
  redundant: `abs_log_one_add_le_two_mul` ALREADY EXISTS in
  `HTGeometry/MultiplicativeGaugePerturbation.lean` with the SAME NAME and statement, alongside
  `one_add_pos_of_abs_le_half`, `exp_two_mul_le_one_add`, and `exp_add_log_one_add` — the latter
  being exactly the chart identity `exp (u + log (1+x)) = exp u * (1+x)`. All axiom-clean.
  The module is DELETED and its umbrella import removed; the tree rebuilds clean at 8562 jobs. Left
  in place it would have been a duplicate declaration in the same namespace, reachable from the
  umbrella — a latent build break, not merely dead code.
  Worse, (M1) as a whole is already built. `HTGeometry/LogGaugeLift.lean` provides
  `memLp_top_log_one_add`, `logOneAddLp` (the additive parameter change as an honest `L^infinity`
  element) and `norm_logOneAddLp_le` (`norm (log (1+h)) <= 2 * norm h`), with the explicit remark
  that no finiteness of the base measure is needed. And `HTGeometry/HerglotzJetMap.lean` already
  builds the jet map of the family `exp(u) * w` — the card's actual family.
  WHY I MISSED IT, precisely, because the failure mode is now repeatable: I searched for
  `PrimeLogGaugePerturbation` (named in the card's stale Lean-status paragraph), found it to be the
  DISCRETE prime-indexed gauge, and concluded the general layer "genuinely had to be built". I
  searched by the name the card gave me instead of by the CONCLUSION SHAPE — `Real.log (1 +` over
  `Lp`, or `norm ... <= 2 *` — which would have surfaced `MultiplicativeGaugePerturbation` and
  `LogGaugeLift` at once. I stated the correct rule two entries ago and then failed to apply it,
  because the card's own prose supplied a plausible-looking name and I followed that instead.
  This is the SECOND redundant construction on this card (the first being the entire shift
  quantifier). Both were caught by reading the tree; neither was caught by reasoning.
  REVISED STATE OF THE MULTIPLICATIVE SIDE: (M1) is DONE in the tree, not by me. What genuinely
  remains is (M2): assembling `logOneAddLp` + `norm_logOneAddLp_le` + `exp_add_log_one_add` into the
  chart hypothesis of `affine_reachability_of_multiplicative_chart_composite`, and feeding
  `surjective_herglotz_composite` as the composite surjectivity. That assembly is the next concrete
  step and is small — but per this card's record I will check for an existing assembly before
  writing it.
  Still untouched: the Krein-index chamber half of the card.
- 2026-07-19 — THIRD DUPLICATION. (M2) is also already in the tree, and checking BEFORE writing —
  which I committed to last entry — is what caught it this time rather than after the fact.
  `HTGeometry/HerglotzGenericity.lean` contains, all axiom-clean:
    `exp_gauged_parameter_ae` — the a.e. identity for the multiplicatively gauged parameter;
    `herglotzJetMap_gauged` — REACHABILITY for the Herglotz chart, i.e. the jets of
      `exp (u_0 + logOneAddLp h)` split as base plus linear term;
    `dense_nondegenerate_herglotzJetMap` — for a base measure of infinite support with a strictly
      positive integrable Nevanlinna density, the bounded parameters on which a fixed nonzero
      polynomial jet relation does not degenerate are DENSE. It applies
      `dense_nondegenerate_of_affine_reachability` with `delta := min (1/2) (eps/2)` and
      `surjective_weightedJetControl_expDensity`.
  `HTGeometry/HerglotzCountableGenericity.dense_countable_nondegenerate_herglotzJetMap` gives the
  countable version.
  So the ENTIRE multiplicative side — (M1) and (M2) — was already formalized for the card's actual
  family `exp(u) dmu`. My `MultiplicativeGaugeCompositeReachability.lean` is therefore redundant as
  well and is DELETED with its umbrella import; the corpus's `surjective_weightedJetControl_expDensity`
  is the exp-density surjectivity directly, which is strictly more useful than my
  `surjective_herglotz_composite` alias. Tree rebuilds clean.
  TALLY OF REDUNDANT WORK ON THIS CARD: the shift quantifier, the log-gauge bound, and now the whole
  multiplicative reachability layer. Three constructions, all already present, all found by reading
  the tree. The single change that would have prevented all three: search by CONCLUSION SHAPE
  (`Dense {u | ... /= 0}`, `Real.log (1 +`, `for all shift`) rather than by object names or by names
  quoted in the card's own prose.
  REVISED ASSESSMENT OF WHAT THIS CARD STILL NEEDS. Given that the Nevanlinna capstone, the shift
  and pattern quantifiers, the L-infinity surjectivity, and the full multiplicative gauge layer all
  exist, the remaining gap is NOT any of the pieces I have been building. It is whatever separates
  `dense_countable_nondegenerate_herglotzJetMap` (dense nondegeneracy for countably many fixed
  polynomial relations at fixed nodes) from the card's stated theorem (a COMEAGER set of bounded
  positive reweightings whose FULL COMPLEX TRANSLATION family is differentially algebraically
  independent at upper infinity). That is a quantifier-and-germ question: countably many relations
  is fine, but the translation family is indexed by arbitrary finite tuples of complex shifts, and
  the conclusion is about germs at upper infinity rather than at fixed nodes.
  NEXT: locate, by conclusion shape, whether the tree already connects jet-level nondegeneracy to
  germ-level differential independence at upper infinity — `differentialIndependent`,
  `upperEndMeroField`, `HypertranscendentalOver` are the target vocabulary — before building
  anything further. The Krein-index chamber half remains untouched.
- 2026-07-19 — THE WHOLE CHAIN EXISTS IN THE TREE. Searching by conclusion shape, as committed,
  found every link of the card's main theorem already formalized and axiom-clean. Recording the
  chain explicitly, since the card's Lean-status paragraph badly understates it and my own log has
  been chasing pieces of it for two dozen entries.
    (1) `NevanlinnaNoncriticalProjectiveCompactPatch.countablePatterns_global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual`
        — dense residual full-rank witnesses, ALL patterns and ALL shifts, via the finite-dimensional
        transversality/codimension hypotheses `hrows` and `hdim`.
    (2) `ClassicalAnalyticNevanlinnaCarrierFamily.probabilityCarrierExpandedFullRankWitness_weightedBoundaryProbabilityCarrier`
        — THE CONNECTOR between the two witness families I had listed as the open carrier-side
        bridge: an abstract compact-patch full-rank witness IS the same certificate for the
        intrinsic Cauchy jets of the normalized PROBABILITY carrier.
    (3) `maximalTranslationDifferentialFree_of_fullRankWitness` — witness to freeness.
    (4) `ClassicalAnalyticNevanlinnaCarrierFamily.hypertranscendental_weightedBoundaryProbabilityCarrierCauchy`
        — freeness to literal HYPERTRANSCENDENCE of the Cauchy transform of the carrier.
    (5) `HerglotzGaugeTransfer.hypertranscendentalOver_herglotzGauge_cauchyTransform_iff` — the (H0)
        regularized Herglotz transform is an invertible RATIONAL GAUGE of that Cauchy transform, so
        hypertranscendence transfers to the card's actual transform.
  And on the parameter side, `HerglotzGenericity` / `HerglotzCountableGenericity` give dense and
  countable-dense nondegeneracy for the multiplicative family `exp(u) dmu`.
  ASSESSMENT. The card's central claim — a comeager set of bounded positive reweightings with
  maximal full-complex-translation differential freedom, transferred to the (H0) transform — is
  present in the tree as a chain of proved, axiom-clean links. What I have NOT done, and what an
  audit still requires, is exhibiting a SINGLE Lean theorem that composes (1)-(5) with matching
  index types and hypotheses, and checking that the hypotheses of (1) (`hrows`, `hdim`,
  `HasMinimalExponentialType`, the projective geometry argument) are simultaneously satisfiable for
  the card's setting rather than merely individually stated. Composition of five theorems with
  distinct index conventions is exactly where this card has repeatedly hidden real work, so I am not
  calling the card done.
  WHAT I ACTUALLY CONTRIBUTED THIS SESSION, stated plainly: the three redundant constructions are
  deleted or superseded; the genuinely new and retained modules are the algebraic core
  (`MonomialPowerIndependence`, `ExpandedMatrixFullRankNodes`, `ExpandedMatrixDistinctNodes`,
  `ExpandedJetDeterminantGenericity`) and a set of reusable abstract genericity tools
  (`CompactShiftPatchOpenness`, `PatchwiseToGlobalGenericity`, `CountableResidualIntersection`,
  `UniformNodeChoiceGenericity`, `OrbitEscapeCompactPatch`, `AnalyticZeroSetThin`,
  `KernelControlSurjectivityCriterion`, `KernelRigidityTransfer`, `TriangularCoefficientInjectivity`,
  `BlockDiagonalAnnihilator`, `NevanlinnaKernelRigidity`, `NevanlinnaControlSurjective`). Those are
  correct and independently useful; they were not on this card's critical path.
  NEXT: attempt the single composed theorem (1)->(5). If the index conventions do not line up, that
  mismatch IS the card's remaining formal content and should be recorded as such. The Krein-index
  chamber half remains untouched throughout.
- 2026-07-19 — THE COMPOSED CAPSTONE ALSO EXISTS. Checking for it before writing one, as committed,
  found it immediately.
  `ClassicalAnalyticNevanlinnaCarrierFamily.positiveSingularContinuousCarrier_hypertranscendental_dense_residual`
  in `HTGeometry/AnalyticNevanlinnaCarrierRelationFree.lean` (line 769); axiom-clean
  `[propext, Classical.choice, Quot.sound]`.
  Its conclusion is the card's theorem for the singular-continuous case, composed end to end: for the
  positive chart `Metric.ball 0 1` inside the frozen tangent `S`, the set
    `{w | Hypertranscendental (fun z => integral ((x:C) - z)^{-1} d(weightedBoundaryCarrier ... (linftyOne mu + w)))}`
  is DENSE and RESIDUAL, while every point of the chart is an atomless singular probability solution
  of the same Hamburger moment problem. So (1)-(5) of the previous entry are already composed, with
  the index conventions reconciled, by the corpus itself.
  THIS SETTLES THE SESSION'S QUESTION. The card's central claim is formalized in this tree. My
  contribution to that claim was zero; everything I built for it was either redundant with existing
  work or infrastructure off its critical path.
  WHAT AN AUDIT SHOULD STILL CHECK, and what I have NOT verified:
    - the capstone is stated for SINGULAR CONTINUOUS projective parameter laws with a null-set
      pullback hypothesis; the card claims coverage of "discrete, singular-continuous, and
      absolutely continuous spectra". Whether the discrete and a.c. cases have their own capstones,
      or follow from this one, I did not check.
    - the capstone concludes hypertranscendence of the CAUCHY transform of the carrier. The card's
      object is the (H0) REGULARIZED Herglotz transform. `hypertranscendentalOver_herglotzGauge_cauchyTransform_iff`
      supplies the rational-gauge equivalence, but I did not verify it is applied inside this
      capstone rather than merely available beside it.
    - the hypotheses `HasMinimalExponentialType`, `hnoCommon`, `hupperMap`, `hnull` and the
      projective-geometry argument must be simultaneously satisfiable for the card's setting. They
      are stated; I did not check they are jointly instantiable.
    - the KREIN-INDEX CHAMBER HALF of the card is untouched by all of the above and by me.
  RECOMMENDATION for the next agent on this card: do not build. Start by enumerating the capstones
  in `AnalyticNevanlinnaCarrierRelationFree` and `NevanlinnaNoncriticalProjectiveCompactPatch`,
  check the four items above, and if they hold, the card's Lean-status paragraph should be rewritten
  and the card promoted to stage 3 for the HT half. The remaining genuine formalisation target on
  this card is the Krein-index chamber structure, which no module in the tree appears to address.
- 2026-07-19 — first work on the KREIN-INDEX CHAMBER half, which is the card's genuinely
  unformalized side. `formal/GaloisForLFunctions/HTGeometry/SignChamberHammingGrading.lean`;
  axiom-clean; audit 2958/2958.
  Checked first, per the rule: `HTGeometry/UniversalPrimeKreinHamming.lean` DOES formalize a
  Krein-Hamming chamber law — "relative Pick defects are rectangular factored Krein forms whose
  exact inertia recovers the directed Hamming geometry" — but for the PRIME-LOG source
  specifically, not for a general infinite-support measure with arbitrary non-atom insertion points
  `a_1,...,a_d`. `RectangularKreinInertia.rectangular_exact_neg_inertia` is the inertia tool it uses.
  So the general measure-level statement (M3) is not covered by it.
  New here, and measure-independent:
  `negCount` — the number of negative coordinates of a real coefficient vector;
  `signPattern`, `positiveChamber` — the chamber and the all-positive chamber;
  `negCount_eq_hammingDist` — THE CHAMBER GRADING IS THE HAMMING DISTANCE from the positive
  chamber, which is exactly the card's claim that the coordinate walls `c_j = 0` cut `R^d` into an
  orthant cube whose grading is graph distance from the closed positive orthant;
  `negCount_eq_zero_iff` and `signPattern_eq_positiveChamber_iff` — the positive chamber is exactly
  the zero of the grading;
  `negCount_le` — the grading is bounded by the ambient dimension.
  This is the COMBINATORIAL half of (M3). It is deliberately stated with no measure in sight, so it
  can serve both the prime-log specialization already in the tree and the general measure-level
  version.
  WHAT (M3) STILL NEEDS — the ANALYTIC half, and it is the real content:
    `kappa_-(m_(u,c)) = negCount c`, i.e. the negative Krein index of the Pick kernel (M2) equals the
    number of negative inserted atoms. The card's proof is two-sided:
    UPPER BOUND: (M2) is a positive semidefinite measure kernel minus one positive rank-one kernel
    per negative coefficient, so `kappa_- <= negCount`. `rectangular_exact_neg_inertia` and
    `neg_inertia_le_of_posSemidef` in `RectangularKreinInertia` look like the right tools.
    LOWER BOUND: take nodes `z_l = a_(j_l) + i y`, scale by `y^2`, and show the Gram matrix tends to
    `diag(c_(j_l))`, negative definite. This needs (M4), `integral y^2/((t-a_j)^2+y^2) dnu -> nu({a_j}) = 0`
    by dominated convergence plus the `(1+t^2)^{-1}` tail bound, and Cauchy-Schwarz for the
    off-diagonal terms. That limit computation is the substantive remaining formalisation on this
    card.
  Next: attempt the UPPER bound first, since the corpus's rectangular inertia machinery appears to
  target exactly that shape; then (M4).
- 2026-07-19 — the UPPER BOUND half of (M3) is connected to the chamber grading.
  `formal/GaloisForLFunctions/HTGeometry/ChamberNegInertiaBound.lean`; axiom-clean; audit 2959/2959.
  `negIndices`, `card_negIndices`, `mem_negIndices`, `negIndicesEquiv` — the negative coordinates as
  a finite index set, enumerated by the chamber grading (`Finset.equivFin` composed with
  `finCongr`). This enumeration is the fiddly part and is reusable.
  `neg_inertia_le_negCount` — if correcting a Hermitian kernel by one positive rank-one term per
  negative coordinate makes it positive semidefinite, every subspace on which the kernel is negative
  definite has dimension at most the chamber grading. This is the corpus's
  `KreinLangerInertia.neg_inertia_le_of_posSemidef` specialised at `k := negCount c`.
  `neg_inertia_le_hammingDist` — the same bound read through `negCount_eq_hammingDist`, i.e.
  `kappa_- <= HammingDist(chamber, positive chamber)`, which is the card's (M3) upper bound in its
  chamber form.
  `no_neg_direction_of_mem_positiveChamber` — in the positive chamber the kernel admits no negative
  directions at all, the degenerate case of the grading.
  A note on scope: `Matrix.PosSemidef` over `C` needs `open scoped ComplexOrder`, which is not in
  scope by default; the corpus module opens it explicitly. Copying the opens from the module whose
  lemma one is consuming is a cheaper fix than debugging the instance failure.
  WHAT REMAINS FOR (M3) — the LOWER bound, and it is the genuine analytic content of this half of
  the card:
    `kappa_-(m_(u,c)) >= negCount c`, proved by taking nodes `z_l = a_(j_l) + i y`, scaling the Gram
    matrix by `y^2`, and showing the limit is `diag(c_(j_l))`, negative definite.
    Its core is (M4): `integral y^2/((t-a_j)^2 + y^2) dnu(t) -> nu({a_j}) = 0` as `y -> 0`, by
    dominated convergence on a compact interval plus the `(1+t^2)^{-1}` tail bound outside it — this
    is exactly where the card's hypothesis that the `a_j` are NOT ATOMS of `nu` is consumed, and it
    is the only place in the chamber half where the measure enters analytically. Off-diagonal
    convergence is Cauchy-Schwarz for the positive measure kernel.
  Also still needed for the card's full chamber claim: that the family `m_(u,c)` has the SAME
  embedded differential-translation field and generator class modulo `C(z)` for all `c`, which the
  card justifies by the added term being RATIONAL. `HerglotzGaugeTransfer` and
  `UpperEndAffineGauge.differentialIndependent_upperEnd_affineGauge_iff` look like the right tools
  and should be checked before that is built.
- 2026-07-19 — the kernel core of (M4) is proved.
  `formal/GaloisForLFunctions/HTGeometry/AtomMassKernel.lean`; axiom-clean; audit 2960/2960.
  Checked first: `HTGeometry/PoissonFatou.lean` is Fatou's theorem on the DISC (a.e. boundary limits
  of Poisson integrals of `L^1` functions on the circle, built for the Szego side). That is a
  different setting from (M4), which is a half-plane atom-selection limit against a possibly INFINITE
  measure on `R`. So this layer genuinely had to be built.
  `atomKernel a y t = y^2 / ((t-a)^2 + y^2)` with:
    `atomKernel_nonneg`, `atomKernel_le_one` — bounded by one, so the constant `1` dominates on any
    finite piece;
    `atomKernel_self` — equal to ONE at the node, for every positive height. This is why the limit
    picks up exactly `nu({a})` and nothing else;
    `atomKernel_le_sq_div` — off the node it is dominated by `y^2/(t-a)^2`, which is the bound that
    controls the TAIL against the Herglotz condition `integral (1+t^2)^{-1} dmu < infinity` when the
    measure is infinite;
    `tendsto_atomKernel_of_ne`, `eventually_atomKernel_lt` — it tends to zero at every point other
    than the node.
  These are exactly the three ingredients the card's (M4) argument names: bounded by one for
  dominated convergence on a compact interval, the square-ratio bound for the tail, and pointwise
  vanishing off the node. Note the card's hypothesis that `a_j` is NOT AN ATOM of `nu` is what turns
  the resulting limit `nu({a_j})` into ZERO; the kernel lemmas above are agnostic to that and hold
  for any node.
  REMAINING for (M4) and the lower bound of (M3):
    - assemble the split: dominated convergence on a compact interval containing `a` (dominant `1`,
      integrable since `nu` restricted there is finite) plus the tail estimate via
      `atomKernel_le_sq_div` and the `(1+t^2)^{-1}` bound, giving
      `integral atomKernel a y t dnu -> nu({a})`;
    - the OFF-DIAGONAL terms, by Cauchy-Schwarz for the positive measure kernel;
    - the conclusion that the `y^2`-scaled Gram matrix tends to `diag(c_(j_l))`, hence is eventually
      negative definite, giving `kappa_- >= negCount c` and, with the upper bound of the previous
      entry, the card's (M3) `kappa_- = negCount c`.
  The scaled-limit assembly is the last substantive analytic step of the chamber half.
- 2026-07-19 — (M4) IS PROVED for finite measures.
  `formal/GaloisForLFunctions/HTGeometry/AtomMassLimit.lean`; axiom-clean; audit 3196/3196.
  `continuous_atomKernel` — for nonzero height the kernel is continuous in the base point.
  `tendsto_atomKernel_indicator` — the kernel converges POINTWISE to the INDICATOR of the node, as
  `y -> 0` within `y /= 0`. The restriction to `y /= 0` is essential and not cosmetic: at `y = 0`
  the kernel is `0/0 = 0` at the node, so the limit along the full neighbourhood filter would be
  wrong exactly at the one point that carries the mass.
  `tendsto_integral_atomKernel` — against a FINITE measure, `integral atomKernel a y t dnu` tends to
  `(nu {a}).toReal`. Dominated convergence with the constant dominant `1`, which is integrable
  precisely because the measure is finite.
  `tendsto_integral_atomKernel_of_notAtom` — at a node carrying NO mass the limit is ZERO. This is
  the card's (M4) in the form its Krein-index argument consumes, and it is where the hypothesis that
  the inserted points `a_j` are not atoms of `nu` is used.
  SCOPE, stated so it is not overread: this is the FINITE-measure case. The card's `nu = exp(u) mu`
  need not be finite — it satisfies only the Herglotz condition
  `integral (1+t^2)^{-1} dmu < infinity`. For that case the card's proof splits into a compact
  interval (where the argument above applies verbatim, since the restriction is finite) and a tail
  controlled by `atomKernel_le_sq_div` against the `(1+t^2)^{-1}` bound. The finite case is the
  substance; the split is the remaining bookkeeping and I have NOT done it.
  REMAINING for the chamber half:
    - the infinite-measure split just described;
    - the OFF-DIAGONAL Gram entries by Cauchy-Schwarz for the positive measure kernel;
    - the conclusion that the `y^2`-scaled Gram matrix tends to `diag(c_(j_l))`, hence is eventually
      negative definite, giving `kappa_- >= negCount c`;
    - combined with `neg_inertia_le_hammingDist` from two entries ago, that is the card's (M3)
      `kappa_-(m_(u,c)) = negCount c = HammingDist(chamber, positive chamber)`.
    - and separately, that the family `m_(u,c)` shares one embedded differential-translation field
      and generator class modulo `C(z)` — the rational-gauge invariance, for which
      `HerglotzGaugeTransfer` and `UpperEndAffineGauge` should be checked before building.
- 2026-07-19 — the TAIL estimate for the infinite-measure case of (M4) is proved.
  `formal/GaloisForLFunctions/HTGeometry/AtomKernelTailBound.lean`; axiom-clean; audit 3197/3197.
  `tailComparison a R = 1/R^2 + (1 + |a|/R)^2` — the explicit comparison constant.
  `one_add_sq_le_tailComparison_mul` — OUTSIDE the interval of radius `R` about the node,
  `1 + t^2 <= tailComparison a R * (t-a)^2`. The proof is the two-term split the estimate suggests:
  `1 <= (t-a)^2/R^2` because the distance exceeds the radius, and `t^2 <= (|t-a| + |a|)^2 <=
  (1 + |a|/R)^2 (t-a)^2` because the point is within the node distance plus the node.
  `atomKernel_le_tail_weight` — hence on the tail the scaled kernel is bounded by
  `y^2 * tailComparison a R / (1 + t^2)`: the HEIGHT SQUARED times the HERGLOTZ WEIGHT. Since the
  Herglotz condition `integral (1+t^2)^{-1} dmu < infinity` makes that weight integrable, the tail
  contribution is `O(y^2)` and vanishes with the height, with no finiteness of the measure used.
  This supplies the second of the two pieces the card's (M4) argument names. Together with
  `tendsto_integral_atomKernel` (the finite/compact-interval piece, proved last entry) the
  infinite-measure statement now needs only the SPLIT itself: restrict to the interval, apply the
  finite case there (the restriction is finite because `(1+t^2)^{-1}` is bounded below on a compact
  set), bound the complement by the above, and let `R -> infinity` after `y -> 0`.
  I have NOT done the split, and it is the kind of two-parameter limit interchange that deserves
  care rather than an estimate that it is routine.
  STATE OF THE CHAMBER HALF after this entry:
    (M3) upper bound — DONE (`neg_inertia_le_hammingDist`).
    (M3) chamber grading — DONE (`negCount_eq_hammingDist`).
    (M4) finite case — DONE (`tendsto_integral_atomKernel_of_notAtom`).
    (M4) tail estimate — DONE (this entry).
    (M4) infinite-measure split — OPEN, bookkeeping with a two-parameter limit.
    (M3) lower bound — OPEN: off-diagonal Cauchy-Schwarz, then the scaled Gram matrix tends to
      `diag(c_(j_l))` and is eventually negative definite.
    rational-gauge invariance of the differential field across the family — OPEN, and to be checked
      against `HerglotzGaugeTransfer` / `UpperEndAffineGauge` before building.
- 2026-07-19 — the infinite-measure split needs NO limit interchange: a single height-independent
  dominant does it. `formal/GaloisForLFunctions/HTGeometry/AtomKernelDominant.lean`; axiom-clean;
  audit 3198/3198.
  I flagged the split last entry as "a two-parameter limit interchange that deserves care". It is
  not one. The card's own proof phrases it as compact interval plus tail with `R` chosen and then
  sent to infinity, which does suggest an interchange; but the two bounds can instead be GLUED into
  one function of `t` alone, at a single fixed `R`, valid for every height at most one:
  `atomDominant a R t = if |t - a| < R then 1 else tailComparison a R / (1 + t^2)`.
  `atomKernel_le_one'` — the scaled kernel never exceeds one, at ANY height including zero (the
  earlier version needed `y /= 0`; the unconditional form is what the dominant argument wants,
  since the dominating bound must hold on a whole neighbourhood of zero).
  `atomKernel_le_atomDominant` — for `y^2 <= 1` the kernel is bounded by the dominant everywhere:
  the constant bound near the node, the tail bound away from it.
  `atomDominant_eq_indicator` — the dominant is the indicator of a bounded set plus the indicator of
  its complement times a multiple of the Herglotz weight, which is the form in which integrability
  is checked: the first piece is integrable because a bounded set has finite measure under the
  Herglotz condition, the second because the Herglotz weight is integrable by hypothesis.
  With this, the infinite-measure case of (M4) follows from `tendsto_integral_filter_of_dominated_convergence`
  exactly as the finite case did, with `atomDominant a R` in place of the constant `1` — no `R`
  limit, no interchange.
  Recording the correction: my caution last entry was directed at a difficulty that the card's
  phrasing suggests but the mathematics does not require. That is the opposite failure from the
  earlier ones on this card — there I was too confident, here too cautious — and both came from
  taking a prose description as a specification of the proof rather than of the result.
  REMAINING for the chamber half:
    - assemble the infinite-measure (M4) from the dominant (mechanical, given the integrability of
      `atomDominant`, which needs the two hypotheses named above);
    - the (M3) lower bound: off-diagonal Cauchy-Schwarz, then the `y^2`-scaled Gram matrix tends to
      `diag(c_(j_l))` and is eventually negative definite;
    - rational-gauge invariance of the differential field across the family `m_(u,c)`, to be checked
      against `HerglotzGaugeTransfer` / `UpperEndAffineGauge` before building.
- 2026-07-19 — (M4) IS PROVED IN FULL, infinite Herglotz measures included.
  `formal/GaloisForLFunctions/HTGeometry/AtomMassLimitHerglotz.lean`; compiled first try;
  axiom-clean; audit 3199/3199.
  `eventually_sq_le_one` — heights near zero are eventually small enough for the dominating bound.
  `tendsto_integral_atomKernel_of_integrable_dominant` — whenever the height-independent dominant is
  integrable, `integral atomKernel a y t dnu -> (nu {a}).toReal`. Dominated convergence with
  `atomDominant a R`, no finiteness of `nu` anywhere.
  `tendsto_integral_atomKernel_of_notAtom_herglotz` — THE CARD'S (M4): at a node carrying no mass
  the scaled kernel integral tends to ZERO, for an infinite measure, assuming only integrability of
  the Herglotz dominant.
  As predicted last entry, the assembly was mechanical once the dominant existed — the difficulty
  was entirely in choosing the right dominating function, not in the limit argument.
  CHAMBER HALF STATUS:
    (M3) chamber grading is Hamming distance — DONE.
    (M3) upper bound `kappa_- <= negCount` — DONE.
    (M4) atom limit, finite and infinite — DONE.
    (M3) LOWER bound — OPEN. Needs: off-diagonal Gram entries by Cauchy-Schwarz for the positive
      measure kernel; then the `y^2`-scaled Gram matrix at nodes `z_l = a_(j_l) + i y` tends to
      `diag(c_(j_l))`, which is negative definite when every `c_(j_l) < 0`, so eventually the Gram
      matrix has a negative definite subspace of dimension `negCount c`, giving
      `kappa_- >= negCount c`. The diagonal convergence is exactly (M4) applied at each `a_(j_l)`
      plus the signed atomic part, so the remaining genuinely new content is the OFF-DIAGONAL
      estimate and the passage from "limit is negative definite" to "eventually negative definite".
    rational-gauge invariance across the family — OPEN, check `HerglotzGaugeTransfer` /
      `UpperEndAffineGauge` first.
  With the lower bound, (M3) closes as `kappa_-(m_(u,c)) = negCount c = HammingDist(chamber,
  positive chamber)`, which is the card's chamber law and the last unformalised piece of this card
  that I have identified.
- 2026-07-19 — the structural half of the (M3) lower bound is proved.
  `formal/GaloisForLFunctions/HTGeometry/PerturbedNegativeDefinite.lean`; compiled first try;
  axiom-clean; audit 3200/3200.
  `neg_of_perturbed_negDef` — a quadratic form bounded above by `-delta * norm(x)^2` stays strictly
  negative on nonzero vectors after any perturbation bounded by `epsilon * norm(x)^2` with
  `epsilon < delta`. Three lines, and it replaces the compactness-of-the-unit-sphere argument the
  card's proof sketch implies.
  `eventually_neg_of_tendsto_negDef` — hence if the forms converge with a UNIFORM QUADRATIC MODULUS
  and the limit is negative definite with margin `delta`, every form past the threshold is negative
  definite. This is the "limit negative definite implies eventually negative definite" step, and it
  is stated on an arbitrary normed group, so it applies to the Gram forms directly.
  `negDiagonal_le` — a diagonal form with all entries at most `-delta` has that margin, which is the
  hypothesis the limit `diag(c_(j_l))` supplies when every `c_(j_l) < 0`.
  Worth noting why the quadratic-modulus formulation is the right one: convergence of matrices in
  ANY norm gives the uniform modulus for free, whereas a pointwise-in-`x` convergence statement
  would not, and compactness would then be needed to upgrade it. Choosing the modulus formulation
  makes the step trivial and removes the only place compactness would have entered the chamber half.
  REMAINING for (M3) lower bound, and it is now a single analytic estimate:
    the OFF-DIAGONAL Gram entries. At nodes `z_l = a_(j_l) + i y` the `y^2`-scaled Gram matrix has
    diagonal entries converging to `c_(j_l)` — that is (M4) plus the signed atomic part, both proved
    — and off-diagonal entries that must converge to ZERO. The card obtains this by Cauchy-Schwarz
    for the positive measure kernel. With those two convergences the matrix tends to
    `diag(c_(j_l))` in norm, `eventually_neg_of_tendsto_negDef` applies, and
    `kappa_- >= negCount c` follows; combined with `neg_inertia_le_hammingDist` that is the card's
    (M3).
  Also still open: rational-gauge invariance of the differential field across the family, to be
  checked against `HerglotzGaugeTransfer` / `UpperEndAffineGauge` before building.
- 2026-07-19 — the bridge from the atom limit to the Gram matrix is proved.
  `formal/GaloisForLFunctions/HTGeometry/GramDiagonalAtomKernel.lean`; compiled first try;
  axiom-clean; audit 3201/3201.
  `upperNode a y = a + i y`; `normSq_sub_upperNode` — the squared distance from a REAL point to an
  upper node is exactly `(t-a)^2 + y^2`, the kernel denominator.
  `sq_mul_normSq_inv_eq_atomKernel` — hence `y^2 * normSq((t - upperNode a y)^{-1}) = atomKernel a y t`
  POINTWISE. So the height-squared scaling of the diagonal Pick entry IS the atom kernel, and
  integrating gives: the diagonal of the scaled Gram matrix equals `integral atomKernel a y t dnu`,
  whose limit is `nu({a})` and hence ZERO at a non-atom, by the (M4) proved two entries ago.
  This is the identification that makes (M4) usable for the Krein index rather than a standalone
  limit. It also gives the OFF-DIAGONAL bound its target: by Cauchy-Schwarz for the positive measure
  form, `|G_lm| <= sqrt(G_ll * G_mm)`, and both diagonal factors now tend to zero, so the
  off-diagonal entries do too.
  REMAINING for (M3) lower bound: the Cauchy-Schwarz step itself, i.e. that for the positive measure
  form `<f,g> = integral f * conj(g) dnu` one has `|<f,g>|^2 <= <f,f> <g,g>` applied to the Cauchy
  kernels at the two nodes. This is a standard inner-product inequality and mathlib has it for `L^2`;
  the work is exhibiting the Cauchy kernels as `L^2(nu)` elements, which needs their square
  integrability — and that is exactly `integral atomKernel dnu < infinity`, already available from
  the dominant. So the remaining step is bounded and its inputs are in place.
  After that: the scaled Gram matrix tends to `diag(c_(j_l))` in norm, `eventually_neg_of_tendsto_negDef`
  gives eventual negative definiteness on the span of the negative coordinates, hence
  `kappa_- >= negCount c`, and with `neg_inertia_le_hammingDist` the card's (M3) closes as
  `kappa_- = negCount c = HammingDist(chamber, positive chamber)`.
  Still open beyond (M3): rational-gauge invariance of the differential field across the family
  `m_(u,c)`, to be checked against `HerglotzGaugeTransfer` / `UpperEndAffineGauge` before building.
- 2026-07-19 — the energy identification for the Gram diagonal is proved; the Cauchy-Schwarz step
  itself is scoped and NOT done.
  `formal/GaloisForLFunctions/HTGeometry/GramOffDiagonalBound.lean`; axiom-clean; audit 3202/3202.
  `normSq_scaled_cauchy_eq_atomKernel` — the scaled Cauchy kernel `y * (t - upperNode a y)^{-1}` has
  POINTWISE squared modulus equal to `atomKernel a y t`.
  `integral_normSq_scaled_cauchy` — hence its energy is the atom kernel integral, i.e. the scaled
  Gram DIAGONAL is exactly the quantity whose limit (M4) computes.
  `integrable_normSq_scaled_cauchy_iff` — square integrability of the scaled Cauchy kernel is
  equivalent to integrability of the atom kernel, which the Herglotz dominant supplies. This is the
  hypothesis a Cauchy-Schwarz step would need, so it is now available.
  WHAT I ATTEMPTED AND BACKED OUT OF, recorded honestly: I first wrote a general Cauchy-Schwarz
  lemma bounding `norm (integral f * conj g)` by the geometric mean of the energies. It failed on
  three separate points — the integrability of `norm f * norm g` needs a product lemma I did not
  have, `Complex.norm_real` produces a real norm rather than an absolute value so the squaring
  rewrite misfired, and the corpus's integral Cauchy-Schwarz
  (`sq_integral_mul_le_integral_sq_mul_integral_sq` in `HalfLineSteinRobertson`) lives in namespace
  `HTGeometry`, NOT `GaloisForLFunctions.HTGeometry`, so it does not resolve unqualified from this
  file. Rather than accumulate fixes I cut the lemma and kept the part that was certain. The
  namespace discrepancy is worth remembering: this tree has modules in BOTH namespaces and the
  unqualified name silently fails to resolve.
  REMAINING for the (M3) lower bound:
    - the Cauchy-Schwarz bound `|G_lm|^2 <= G_ll * G_mm`, using
      `_root_.HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq` with the square
      integrability now available;
    - hence off-diagonal entries vanish with the diagonal, the scaled Gram matrix tends to
      `diag(c_(j_l))`, and `eventually_neg_of_tendsto_negDef` gives `kappa_- >= negCount c`.
  Still open beyond (M3): rational-gauge invariance of the differential field across the family.
- 2026-07-19 — THE OFF-DIAGONAL ESTIMATE IS PROVED. The Cauchy-Schwarz step that failed last entry
  succeeds once stated correctly.
  `formal/GaloisForLFunctions/HTGeometry/GramPairingCauchySchwarz.lean`; compiled first try;
  axiom-clean; audit 8488/8488.
  `norm_integral_mul_conj_sq_le` — for a complex measure pairing,
  `norm(integral f * conj g)^2 <= (integral norm(f)^2) * (integral norm(g)^2)`, assuming only
  measurability of the moduli and SQUARE integrability of each factor.
  `norm_scaledPairing_sq_le_atomKernel_mul` — specialised to the scaled Cauchy kernels at two upper
  nodes: the squared modulus of the off-diagonal Gram entry is at most the PRODUCT OF THE TWO ATOM
  KERNEL INTEGRALS.
  WHY IT WORKS NOW, and it is a correction to my analysis last entry: I had recorded that the proof
  "needs a product lemma I did not have" for the integrability of `norm(f) * norm(g)`. That was
  wrong. `norm_integral_le_integral_norm` is UNCONDITIONAL — it holds whether or not the integrand is
  integrable, since a non-integrable integral is junk-valued zero and the inequality survives. So no
  product integrability is required anywhere, and the corpus lemma
  `sq_integral_mul_le_integral_sq_mul_integral_sq` takes only the two square-integrability
  hypotheses. The other two obstacles were real but shallow: `Complex.norm_conj` is the right
  rewrite, and the corpus lemma needs the `_root_.HTGeometry.` prefix because that module is in a
  DIFFERENT namespace from this one.
  Two of the three "obstacles" I recorded were therefore artifacts of a hurried first draft, not
  facts about the mathematics. Cutting the lemma was still right — but the postmortem I wrote
  overstated the difficulty, and it would have sent a later reader down a needless path.
  CONSEQUENCE — the (M3) lower bound is now assembled from proved parts:
    diagonal entries = atom kernel integrals (`integral_normSq_scaled_cauchy`), tending to
    `nu({a_j}) = 0` at non-atoms (`tendsto_integral_atomKernel_of_notAtom_herglotz`);
    off-diagonal entries bounded by the geometric mean of those (this entry), hence tending to zero;
    so the scaled Gram matrix tends to the signed atomic part `diag(c_(j_l))`;
    which is negative definite when every `c_(j_l) < 0` (`negDiagonal_le`), so
    `eventually_neg_of_tendsto_negDef` gives a negative definite subspace of dimension
    `negCount c` for small heights, i.e. `kappa_- >= negCount c`.
  With `neg_inertia_le_hammingDist` this closes the card's (M3):
  `kappa_-(m_(u,c)) = negCount c = HammingDist(chamber, positive chamber)`.
  What remains is to WRITE that composition as a single theorem against the card's concrete
  `m_(u,c)`, which requires the signed atomic part's contribution to the Gram matrix to be computed
  explicitly; every analytic input it needs is now proved. Also still open: rational-gauge
  invariance of the differential field across the family.
- 2026-07-19 — the scaled ATOMIC part of the Gram matrix is computed exactly.
  `formal/GaloisForLFunctions/HTGeometry/ScaledAtomicGram.lean`; axiom-clean; audit 8489/8489.
  `sub_upperNode_self` and `sub_conj_upperNode_self` — at the node directly above an atom the two
  Cauchy factors are `-i y` and `+i y`.
  `sub_mul_sub_conj_upperNode` — their product is EXACTLY `y^2`.
  `scaled_atomic_diagonal` — hence scaling by `y^2`, an atom's own rank-one contribution at the node
  above it equals its coefficient `c` EXACTLY, with NO limit and no error term.
  This is the sharp point of the card's lower-bound argument and it is worth stating plainly: the
  diagonal of the scaled Gram matrix is not merely asymptotic to `c_(j_l)`, its atomic part IS
  `c_(j_l)` identically for every positive height. All the limiting behaviour sits in the MEASURE
  part (which tends to zero at a non-atom, by (M4)) and in the OTHER atoms' contributions and the
  off-diagonal entries (which tend to zero, by the Cauchy-Schwarz bound of the previous entry).
  So the three convergences the lower bound needs are now: exact for the own-atom diagonal, (M4) for
  the measure diagonal, Cauchy-Schwarz for everything off-diagonal.
  REMAINING to close (M3): the decay of the CROSS terms — an atom's contribution at a node above a
  DIFFERENT atom, and at distinct nodes. Both are of the form `y^2 / (bounded away from zero)` or
  `y^2 / (y * nonzero)`, hence `O(y^2)` and `O(y)` respectively; the estimates are elementary but
  are not yet written. With them the scaled Gram matrix tends to `diag(c_(j_l))` and the chain
  through `negDiagonal_le` and `eventually_neg_of_tendsto_negDef` gives `kappa_- >= negCount c`,
  closing the card's (M3) against `neg_inertia_le_hammingDist`.
  Still open beyond (M3): rational-gauge invariance of the differential field across the family.
- 2026-07-19 — the SAME-NODE cross term is proved to decay.
  `formal/GaloisForLFunctions/HTGeometry/ScaledAtomicCrossTerms.lean`; axiom-clean; audit 8490/8490.
  `sub_conj_upperNode_eq_conj` — for a REAL evaluation point the conjugate factor is the conjugate of
  the factor, so the two Cauchy factors multiply to a squared modulus.
  `sub_mul_sub_conj_upperNode_other` — that product is exactly `(b-a)^2 + y^2`, real and positive.
  `norm_scaled_atomic_cross_le` — hence an atom at `b` seen from the node above `a /= b`, scaled by
  the height squared, is bounded by `y^2 * norm(c) / (b-a)^2`: it is `O(y^2)` and vanishes with the
  height, the denominator being bounded below by the atom separation.
  Note this is the SAME-NODE cross term (different atom, one node). The DISTINCT-NODE cross term is
  not yet done and is genuinely different: there the two factors are `-i y` and `(a-b) + i y`, whose
  product `y^2 - i y (a-b)` has modulus at least `y |a-b|` — only ONE power of `y`, so that term is
  `O(y)` rather than `O(y^2)`. It still vanishes, but the estimate is not the one above and must be
  written separately. I record this because the two cases look symmetric and are not: the card's
  phrase "off-diagonal convergence follows from Cauchy-Schwarz" covers the MEASURE part, while these
  atomic cross terms need their own elementary estimates, and one of the two loses a power of `y`.
  STATE OF (M3):
    upper bound `kappa_- <= negCount` — DONE.
    chamber grading = Hamming distance — DONE.
    own-atom diagonal exactly `c_j` — DONE.
    measure diagonal -> 0 at a non-atom — DONE ((M4), infinite measures included).
    measure off-diagonal -> 0 — DONE (Cauchy-Schwarz).
    same-node atomic cross term -> 0 — DONE (this entry).
    distinct-node atomic cross term -> 0 — OPEN, `O(y)` estimate as described.
    assembly into `kappa_- >= negCount` — OPEN, mechanical once the last estimate lands.
  Still open beyond (M3): rational-gauge invariance of the differential field across the family.
- 2026-07-19 — the DISTINCT-NODE cross term is proved to decay. Every analytic input of the (M3)
  lower bound is now in place.
  `formal/GaloisForLFunctions/HTGeometry/ScaledAtomicDistinctNodes.lean`; axiom-clean; audit
  8491/8491.
  `sub_mul_sub_conj_upperNode_distinct` — at distinct nodes the two Cauchy factors multiply to
  `y^2 - i y (a - b)`.
  `im_sub_mul_sub_conj_distinct` — that product has imaginary part `-y(a-b)`.
  `norm_sub_mul_sub_conj_distinct_ge` — hence its modulus is at least `|y| * |a-b|`, by
  `Complex.abs_im_le_norm`. Bounding a modulus below by an imaginary part is the whole trick; no
  case analysis on the real part is needed.
  `norm_scaled_atomic_distinct_le` — so the scaled contribution is at most `|y| * norm(c) / |a-b|`:
  `O(y)`, as predicted, one power weaker than the same-node cross term and still vanishing.
  THE (M3) LOWER BOUND NOW HAS ALL ITS PIECES:
    own-atom diagonal = `c_j` EXACTLY (no limit);
    measure diagonal -> 0 at a non-atom, infinite measures included;
    measure off-diagonal -> 0 by Cauchy-Schwarz against the diagonal;
    same-node atomic cross term `O(y^2)` -> 0;
    distinct-node atomic cross term `O(y)` -> 0.
  So the `y^2`-scaled Gram matrix tends entrywise to `diag(c_(j_l))`; `negDiagonal_le` gives the
  margin when every `c_(j_l) < 0`; `eventually_neg_of_tendsto_negDef` converts that into a negative
  definite subspace of dimension `negCount c` for small heights; hence `kappa_- >= negCount c`.
  With `neg_inertia_le_hammingDist` this is the card's (M3):
  `kappa_-(m_(u,c)) = negCount c = HammingDist(chamber, positive chamber)`.
  WHAT IS LEFT ON THE CHAMBER HALF is the ASSEMBLY of these into one theorem against the card's
  concrete `m_(u,c)`: defining the Gram matrix of the family at a chosen node tuple, showing its
  entries decompose as measure part plus atomic part, and applying the five bounds above. That is
  bookkeeping over proved facts, but it is not nothing — the entrywise convergence has to be
  upgraded to matrix-norm convergence to feed `eventually_neg_of_tendsto_negDef`, and the index
  bookkeeping between the negative coordinates and the chosen nodes must match `negIndicesEquiv`.
  Also still open: rational-gauge invariance of the differential field across the family, unchecked
  against `HerglotzGaugeTransfer` / `UpperEndAffineGauge`.
- 2026-07-19 — assembly obstacle (1) is removed: entrywise bounds now feed the quadratic-form
  criterion directly.
  `formal/GaloisForLFunctions/HTGeometry/EntrywiseQuadraticBound.lean`; compiled first try;
  axiom-clean; audit 8492/8492.
  `norm_quadForm_le_of_entries` — on a finite index, if every entry of `E` has modulus at most `M`
  then `norm(star x . E.mulVec x) <= M * n^2 * norm(x)^2`, with the supremum norm on the coordinate
  space.
  This is exactly the shape `eventually_neg_of_tendsto_negDef` consumes: it wants a QUADRATIC
  MODULUS `epsilon * norm(x)^2`, and the five decay estimates of the previous entries are all
  ENTRYWISE. So the upgrade from entrywise to matrix-norm convergence — which I flagged as a real
  step in the assembly — is this one lemma, and the constant `n^2` is harmless since the criterion
  only needs the modulus eventually below `delta/2`.
  Worth noting the norm choice: `Fin n -> C` carries the SUPREMUM norm in mathlib, which is what
  makes `norm_le_pi_norm` available and the estimate a plain double sum. Had the argument been
  phrased on `EuclideanSpace` the same bound would need Cauchy-Schwarz instead. Choosing the
  coordinate norm keeps the step elementary.
  ASSEMBLY STATE for the (M3) lower bound: obstacle (1) done; obstacle (2), the index bookkeeping
  between the negative coordinates and the chosen node tuple via `negIndicesEquiv`, remains. With
  those, the composition is: entrywise decay -> quadratic modulus (this entry) -> eventual negative
  definiteness (`eventually_neg_of_tendsto_negDef`) on the span of the negative coordinates ->
  `kappa_- >= negCount c`, closing (M3) against `neg_inertia_le_hammingDist`.
  Also still open: rational-gauge invariance of the differential field across the family, still
  unchecked against `HerglotzGaugeTransfer` / `UpperEndAffineGauge`.
- 2026-07-19 — the limiting diagonal form is computed and shown negative definite.
  `formal/GaloisForLFunctions/HTGeometry/DiagonalQuadraticForm.lean`; axiom-clean; audit 8493/8493.
  `quadForm_diagonal_eq` — the Hermitian quadratic form of a REAL diagonal matrix is the
  coefficient-weighted sum of squared coordinate moduli, `sum_j c_j * norm(x_j)^2`, as a real number.
  `re_quadForm_diagonal` — its real part is that sum.
  `re_quadForm_diagonal_neg` — hence if every coefficient is NEGATIVE the form is strictly negative
  on nonzero vectors. Proof by splitting off one coordinate where `x` does not vanish
  (`Finset.add_sum_erase`): that term is strictly negative, the rest are nonpositive.
  PROCESS NOTE, recorded because it is a rule violation I caught myself: my first draft of the last
  theorem contained a `sorry` in the `x j = 0` branch, written while sketching the case split. I
  caught it on re-reading before any build and replaced the argument with the split-off-one-coordinate
  form, which handles both branches uniformly. Nothing with a `sorry` reached a build or the tree,
  but the draft should not have contained one — the correct habit is to write the case analysis
  completely or not at all, not to stub a branch intending to return to it.
  This supplies the limiting form for the (M3) lower bound in explicit shape. Combined with
  `norm_quadForm_le_of_entries` (entrywise to quadratic modulus) and
  `eventually_neg_of_tendsto_negDef` (perturbation), the chain from entrywise decay to eventual
  negative definiteness is complete at the level of abstract matrices.
  REMAINING on the chamber half:
    - the margin form: `re_quadForm_diagonal_neg` gives strict negativity, while
      `eventually_neg_of_tendsto_negDef` wants the uniform margin `-delta * norm(x)^2`. On the
      supremum norm that needs `norm(x)^2 <= sum_j norm(x_j)^2`, one inequality not yet written;
    - the index bookkeeping via `negIndicesEquiv` between negative coordinates and chosen nodes;
    - then the composition against the card's concrete `m_(u,c)`.
  Also still open: rational-gauge invariance of the differential field across the family.
- 2026-07-19 — the uniform MARGIN is proved, so the abstract lower-bound chain is complete.
  `formal/GaloisForLFunctions/HTGeometry/DiagonalNegativeMargin.lean`; axiom-clean; audit 8494/8494.
  `sq_pi_norm_le_sum_sq` — the squared SUPREMUM norm is at most the sum of squared coordinate
  moduli. No attainment of the supremum is needed: each coordinate is at most the square root of the
  sum, hence so is the supremum, by `pi_norm_le_iff_of_nonneg`.
  `re_quadForm_diagonal_le_margin` — hence a diagonal with all coefficients at most `-delta`
  satisfies `re(quadratic form) <= -delta * norm(x)^2`, which is exactly the margin hypothesis of
  `eventually_neg_of_tendsto_negDef`.
  THE ABSTRACT (M3) LOWER-BOUND CHAIN IS NOW COMPLETE, every link proved and axiom-clean:
    entrywise decay of the scaled Gram matrix (five estimates: exact own-atom diagonal, measure
    diagonal by (M4), measure off-diagonal by Cauchy-Schwarz, same-node atomic cross term `O(y^2)`,
    distinct-node atomic cross term `O(y)`)
    -> quadratic modulus (`norm_quadForm_le_of_entries`)
    -> limiting diagonal form with uniform margin (this entry)
    -> eventual negative definiteness (`eventually_neg_of_tendsto_negDef`)
    -> a negative definite subspace of dimension `negCount c`, i.e. `kappa_- >= negCount c`
    -> with `neg_inertia_le_hammingDist`, the card's (M3)
       `kappa_- = negCount c = HammingDist(chamber, positive chamber)`.
  WHAT IS LEFT is instantiation against the card's concrete `m_(u,c)`: constructing the Gram matrix
  of that family at a node tuple, decomposing its entries into measure part plus atomic part, and
  matching the negative-coordinate indexing to `negIndicesEquiv`. Every ingredient it consumes is
  proved; none of the remaining work is analysis.
  Also still open, and untouched throughout: rational-gauge invariance of the differential field
  across the family `m_(u,c)`, which the card justifies by the inserted term being rational and
  which should be checked against `HerglotzGaugeTransfer` / `UpperEndAffineGauge` before anything is
  built for it.
- 2026-07-19 — the abstract lower bound is now ONE theorem.
  `formal/GaloisForLFunctions/HTGeometry/EventualNegDefFromEntrywise.lean`; compiled first try;
  axiom-clean; audit 8495/8495.
  `eventually_negDef_of_entrywise_tendsto_diagonal` — a family of matrices converging ENTRYWISE to a
  real diagonal with all entries at most `-delta` is EVENTUALLY NEGATIVE DEFINITE. The proof
  composes the three previous entries: `norm_quadForm_le_of_entries` turns the entrywise bound into
  a quadratic modulus, `re_quadForm_diagonal_le_margin` supplies the diagonal's margin, and
  `eventually_neg_of_tendsto_negDef` concludes. The threshold is explicit,
  `epsilon = delta / (2 (n^2 + 1))`, chosen so that `epsilon * n^2 <= delta/2`; the `+1` avoids a
  case split at `n = 0`.
  One structural detail worth keeping: the difference of the two quadratic forms is the form of the
  difference of the matrices (`Matrix.sub_mulVec` and `dotProduct_sub`), so the perturbation
  hypothesis is checked on `G i - D` directly rather than by comparing two forms term by term.
  STATUS OF THE CHAMBER HALF. Both bounds of the card's (M3) are now available as abstract theorems
  over proved analytic inputs:
    UPPER: `neg_inertia_le_hammingDist` — `kappa_- <= negCount c = HammingDist(chamber, positive)`.
    LOWER: this entry, fed by the five entrywise estimates, gives eventual negative definiteness on
    the coordinate span, hence `kappa_- >= negCount c`.
  What remains for (M3) is ONLY instantiation against the card's concrete `m_(u,c)`: build its Gram
  matrix at a node tuple, decompose entries into measure plus atomic parts, verify the five decay
  estimates apply, and match the indexing to `negIndicesEquiv`. No analysis and no new abstract
  machinery is left in it.
  Still open beyond (M3), and untouched all session: rational-gauge invariance of the differential
  field across the family `m_(u,c)`. It should be checked against `HerglotzGaugeTransfer` /
  `UpperEndAffineGauge` first — on this card, three separate constructions turned out to exist
  already, and that check has never once been wasted.
- 2026-07-19 — the RATIONAL-GAUGE INVARIANCE of the chamber family is proved, in the exact form the
  card states it. `formal/GaloisForLFunctions/HTGeometry/ChamberFamilyGaugeInvariance.lean`;
  axiom-clean; audit 8681/8681.
  Checked first, per the rule, and the general statement WAS already there:
  `UpperEndAffineGauge.hypertranscendentalOver_upperEnd_affineGauge_iff` — hypertranscendence over
  the embedded coordinate field is invariant under an invertible affine rational gauge `a x + b`.
  The card's family `m_(u,c) = m_u + sum_j c_j/(a_j - z)` is exactly the UNIT-MULTIPLIER case, since
  the inserted term is rational in the coordinate.
  New here, and specialised to that case:
  `hypertranscendentalOver_upperEnd_addRational_iff` — adding a rational function preserves
  hypertranscendence;
  `differentialIndependent_upperEnd_addRational_iff` — the family form, a whole tuple may be shifted
  by rational functions without changing differential independence.
  Together these are the card's claim that "every member of this family has the same embedded
  differential-translation field, the same full translation differential matroid, and the same
  generator class modulo C(z), because the added term is rational".
  A TREE CONVENTION worth recording, since it cost three build cycles: the `Differential
  upperEndMeroField` instance and its companions are declared `local instance` in EVERY module that
  uses them, deliberately, so they do NOT propagate through imports. Importing the module that
  proves the theorem is not enough; the five local instances (domain, complex algebra, differential,
  coordinate-field differential, differential algebra) must be re-declared verbatim. That is why the
  first attempts failed with `failed to synthesize Differential upperEndMeroField` despite the
  import being present.
  CHAMBER HALF STATUS:
    (M3) upper bound — DONE. (M3) chamber grading — DONE. (M3) lower bound, abstract — DONE.
    (M4) atom limit, finite and infinite — DONE. All five entrywise decay estimates — DONE.
    Rational-gauge invariance of the family — DONE (this entry).
    REMAINING: instantiate the abstract lower bound against the concrete `m_(u,c)` — build its Gram
    matrix at a node tuple, decompose entries into measure plus atomic parts, match the indexing to
    `negIndicesEquiv`. No analysis and no abstract machinery left; it is construction and
    bookkeeping over proved facts.
- 2026-07-19 — the concrete atomic Gram matrix is defined and its diagonal estimated.
  `formal/GaloisForLFunctions/HTGeometry/AtomicGramMatrix.lean`; compiled first try; axiom-clean;
  audit 8496/8496.
  `atomicGram a c y` — the scaled atomic part of the Pick Gram at the nodes directly above the
  atoms, `y^2 * sum_j c_j / ((a_j - z_l)(a_j - conj z_m))` with `z_l = upperNode (a l) y`. This is
  the card's (M2) atomic term, evaluated at the card's (M3) node choice.
  `atomicGram_diagonal_split` — the diagonal splits as `c_l` EXACTLY plus the cross terms from the
  other atoms, using `scaled_atomic_diagonal` for the `j = l` term and `Finset.add_sum_erase` to
  peel it off.
  `norm_atomicGram_diagonal_sub_le` — hence the deviation of the diagonal from `c_l` is at most
  `sum_(j /= l) y^2 * norm(c_j) / (a_j - a_l)^2`, an explicit `O(y^2)` rate with the atom
  separations in the denominators. Injectivity of the atom placement is exactly what makes those
  denominators nonzero.
  This is the first module of the instantiation phase: it moves from abstract matrices to the card's
  actual object. The remaining instantiation work is the same treatment for the OFF-DIAGONAL atomic
  entries (which use `norm_scaled_atomic_distinct_le`, the `O(y)` estimate) and for the MEASURE
  part (whose diagonal is `integral atomKernel` by `integral_normSq_scaled_cauchy` and whose
  off-diagonal is controlled by `norm_scaledPairing_sq_le_atomKernel_mul`), after which the total
  Gram matrix satisfies the entrywise hypothesis of
  `eventually_negDef_of_entrywise_tendsto_diagonal` and (M3) closes.
  Every analytic ingredient of that remaining work is proved; what is left is assembling the two
  parts into one matrix and checking the entrywise bound uniformly in the pair of indices.
- 2026-07-19 — the MIRRORED distinct-node estimate is proved, completing the primitives for the
  off-diagonal atomic entries.
  `formal/GaloisForLFunctions/HTGeometry/ScaledAtomicMirrored.lean`; compiled first try;
  axiom-clean; audit 8497/8497.
  Why a second lemma was needed, which is a genuine asymmetry and not duplication: an off-diagonal
  entry `atomicGram a c y l m` contains a term for EVERY atom `j`, and two of them have the atom
  sitting at one of the two nodes — `j = l` puts it at the LEFT node, `j = m` at the RIGHT. The
  existing `norm_scaled_atomic_distinct_le` covers the left case, where the product is
  `y^2 - i y (a - b)`. The right case has product `y^2 + i y (b - a)` — the mirror image — and needs
  its own computation, though the modulus bound `|y| * |b - a|` is the same.
  `sub_mul_sub_conj_upperNode_mirrored`, `im_sub_mul_sub_conj_mirrored`,
  `norm_sub_mul_sub_conj_mirrored_ge`, `norm_scaled_atomic_mirrored_le` — the mirrored chain, ending
  in the same `O(y)` bound.
  THE PRIMITIVES FOR THE ATOMIC OFF-DIAGONAL ARE NOW COMPLETE. An entry `l /= m` decomposes into:
    `j = l` — left-node case, `O(y)` by `norm_scaled_atomic_distinct_le`;
    `j = m` — right-node case, `O(y)` by this entry;
    `j /= l, m` — both factors bounded away from zero, `O(y^2)`; this case still needs its own
    elementary bound, analogous to `norm_scaled_atomic_cross_le` but with the two nodes distinct,
    and is the last atomic primitive missing.
  After that: assemble `atomicGram` off-diagonal bound, add the measure part (diagonal by
  `integral_normSq_scaled_cauchy`, off-diagonal by `norm_scaledPairing_sq_le_atomKernel_mul`), and
  feed the total into `eventually_negDef_of_entrywise_tendsto_diagonal` to close (M3).
- 2026-07-19 — the FAR-term estimate is proved. All atomic primitives for the (M3) lower bound now
  exist. `formal/GaloisForLFunctions/HTGeometry/ScaledAtomicFarTerms.lean`; compiled first try;
  axiom-clean; audit 8498/8498.
  `norm_sub_upperNode_ge` and `norm_sub_conj_upperNode_ge` — the distance from a real point to an
  upper node, or to its conjugate, is at least the REAL separation. Both follow from
  `Complex.abs_re_le_norm` since the real part of each factor is exactly `b - a`; the conjugate case
  is identical because conjugation preserves the real part.
  `norm_scaled_atomic_far_le` — hence an atom differing from BOTH nodes contributes at most
  `y^2 * norm(c) / (|b-a| |b-a'|)`: `O(y^2)`, the fastest-decaying of the three off-diagonal kinds.
  THE ATOMIC PRIMITIVE SET IS COMPLETE. Every term of `atomicGram a c y l m` is now covered:
    `l = m`, `j = l` — EXACTLY `c_l`, no error (`scaled_atomic_diagonal`);
    `l = m`, `j /= l` — `O(y^2)` (`norm_scaled_atomic_cross_le`);
    `l /= m`, `j = l` — `O(y)` left-node (`norm_scaled_atomic_distinct_le`);
    `l /= m`, `j = m` — `O(y)` right-node (`norm_scaled_atomic_mirrored_le`);
    `l /= m`, `j /= l, m` — `O(y^2)` far (this entry).
  Note the pattern: only the two terms where the atom sits AT one of the evaluation nodes lose a
  power of `y`, and only the one where it sits at BOTH survives the limit. That is precisely why the
  limit is the diagonal of coefficients, and it is now visible in the estimates rather than only in
  the card's prose.
  REMAINING for (M3): assemble the five estimates into an off-diagonal bound for `atomicGram`,
  combine with the measure part, and feed the total into
  `eventually_negDef_of_entrywise_tendsto_diagonal`. All inputs proved; the work is summation
  bookkeeping over the three-way case split on `j`.
- 2026-07-19 — the summation scaffolding for the atomic Gram entries is in.
  `formal/GaloisForLFunctions/HTGeometry/AtomicGramEntrySum.lean`; compiled first try; axiom-clean;
  audit 8499/8499.
  `atomicGram_eq_sum` — each entry is the sum over atoms of individually scaled terms, so the five
  case estimates apply TERMWISE.
  `sq_le_abs_of_abs_le_one` — for heights at most one, `y^2 <= |y|`. This is the small observation
  that removes a case split from the assembly: the `O(y^2)` terms (same-node cross, far) are in
  particular `O(|y|)`, so ONE linear rate covers every off-diagonal term and the summation does not
  need to track two rates.
  `norm_atomicGram_le_of_termwise` — a termwise bound gives an entrywise bound, by
  `norm_sum_le` and `Finset.sum_le_sum`.
  With these, the off-diagonal assembly is: apply the three-way case split on `j` to choose which of
  `norm_scaled_atomic_distinct_le`, `norm_scaled_atomic_mirrored_le`, `norm_scaled_atomic_far_le`
  bounds the term, weaken every bound to the common linear rate via `sq_le_abs_of_abs_le_one`, and
  sum. The diagonal assembly is already done (`norm_atomicGram_diagonal_sub_le`).
  STATE OF THE CHAMBER HALF. Everything analytic and everything abstract is proved:
    (M3) upper bound and chamber grading; (M4) finite and infinite; all five atomic estimates; the
    measure diagonal and off-diagonal; the perturbation criterion, the margin, the entrywise-to-
    quadratic bridge and their composition; the rational-gauge invariance of the family.
  What remains is one summation lemma for the off-diagonal atomic entries, then combining atomic and
  measure parts into the total Gram matrix and invoking
  `eventually_negDef_of_entrywise_tendsto_diagonal`. No ingredient of that is unproved.
- 2026-07-19 — the OFF-DIAGONAL atomic Gram bound is assembled. The atomic part of the (M3) lower
  bound is complete. `formal/GaloisForLFunctions/HTGeometry/AtomicGramOffDiagonal.lean`;
  axiom-clean; audit 8500/8500.
  `offDiagWeight a l m j` — the separation weight of an atom against a pair of distinct nodes,
  defined by the three cases: `1/|a_l - a_m|` when the atom is the left node, `1/|a_m - a_l|` when it
  is the right, `1/(|a_j-a_l| |a_j-a_m|)` when it is neither.
  `norm_atomicGram_offdiag_le` — for `l /= m` and height at most one,
  `norm(atomicGram a c y l m) <= sum_j |y| * norm(c_j) * offDiagWeight a l m j`. The proof is the
  three-way case split, each branch discharged by its own estimate
  (`norm_scaled_atomic_distinct_le`, `norm_scaled_atomic_mirrored_le`, `norm_scaled_atomic_far_le`),
  with the far branch weakened from `y^2` to `|y|` by `sq_le_abs_of_abs_le_one` so that a single
  linear rate covers all three.
  So the ATOMIC part of the scaled Gram is fully controlled:
    diagonal — `c_l` exactly, with `O(y^2)` deviation (`norm_atomicGram_diagonal_sub_le`);
    off-diagonal — `O(|y|)` (this entry).
  Both vanish as the height does, leaving exactly the diagonal of coefficients.
  REMAINING for (M3): the same assembly for the MEASURE part — its diagonal is
  `integral atomKernel` (tending to zero at a non-atom by (M4)) and its off-diagonal is bounded by
  the geometric mean of two diagonals (`norm_scaledPairing_sq_le_atomKernel_mul`) — and then the sum
  of the two parts fed into `eventually_negDef_of_entrywise_tendsto_diagonal`. Every ingredient is
  proved; what is left is defining the measure Gram matrix and combining.
- 2026-07-19 — the MEASURE Gram part is defined and both its diagonal and off-diagonal identified.
  `formal/GaloisForLFunctions/HTGeometry/MeasureGramMatrix.lean`; compiled first try; axiom-clean;
  audit 8501/8501.
  `measureGram nu a y` — the scaled measure part of the Pick Gram at the nodes above the atoms, i.e.
  the pairing matrix of the scaled Cauchy kernels.
  `measureGram_diagonal` — its diagonal is EXACTLY the atom kernel integral, as a real number
  coerced to C. The pointwise step is `Complex.mul_conj` plus `normSq_scaled_cauchy_eq_atomKernel`;
  the passage from a pointwise real value to a real integral is `Complex.ofRealCLM.integral_comp_comm`,
  which is where the integrability hypothesis enters.
  `norm_measureGram_sq_le` — its off-diagonal has squared modulus at most the product of the two
  diagonal integrals, restating the Cauchy-Schwarz bound for this matrix.
  BOTH PARTS OF THE SCALED GRAM ARE NOW CONTROLLED:
    ATOMIC: diagonal `c_l` exactly with `O(y^2)` deviation; off-diagonal `O(|y|)`.
    MEASURE: diagonal `integral atomKernel`, tending to zero at a non-atom by (M4), infinite measures
      included; off-diagonal bounded by the geometric mean of two diagonals, hence tending to zero
      with them.
  So the total scaled Gram `atomicGram + measureGram` converges entrywise to `diag(c)`, which is
  exactly the hypothesis of `eventually_negDef_of_entrywise_tendsto_diagonal`.
  REMAINING for (M3): state the total Gram as the sum of the two matrices, convert the four bounds
  above into the single entrywise convergence hypothesis, and invoke the eventual-negative-
  definiteness theorem to conclude `kappa_- >= negCount c`. This is the final composition; every one
  of its inputs is a proved theorem in this tree, and no analysis remains in it.
- 2026-07-19 — the TOTAL scaled Gram is defined and its deviation from the coefficient diagonal
  split. `formal/GaloisForLFunctions/HTGeometry/TotalGramMatrix.lean`; compiled first try;
  axiom-clean; audit 8502/8502.
  `totalGram nu a c y = atomicGram a c y + measureGram nu a y` — the card's (M2) Pick kernel, scaled
  by the height squared and evaluated at the nodes above the atoms.
  `totalGram_sub_diagonal` — the deviation from `diag(c)` splits as (atomic deviation) + (measure
  entry), since the reference diagonal sits entirely in the atomic part.
  `norm_totalGram_sub_diagonal_le` — hence the entrywise deviation is bounded by the sum of the two,
  by the triangle inequality. Together with the simp lemmas for the diagonal reference on and off
  the diagonal, this reduces the entrywise convergence hypothesis to the four bounds already proved.
  THE (M3) INGREDIENT LIST IS NOW CLOSED. Every quantity appearing in the lower bound has an
  explicit proved estimate:
    `norm_atomicGram_diagonal_sub_le` — atomic diagonal deviation, `O(y^2)`;
    `norm_atomicGram_offdiag_le` — atomic off-diagonal, `O(|y|)`;
    `measureGram_diagonal` with `tendsto_integral_atomKernel_of_notAtom_herglotz` — measure diagonal,
      tending to zero at a non-atom;
    `norm_measureGram_sq_le` — measure off-diagonal, squared modulus at most the product of two
      diagonals, hence tending to zero with them;
    `norm_totalGram_sub_diagonal_le` — the combination.
  WHAT REMAINS is to turn those four estimates into the `Tendsto`/`eventually` form that
  `eventually_negDef_of_entrywise_tendsto_diagonal` consumes, i.e. to show that for each `epsilon`
  the entrywise deviation is eventually below it. Each bound tends to zero for elementary reasons
  (a fixed finite sum times `|y|` or `y^2`, or an integral limit already proved), so this is limit
  bookkeeping rather than estimation. After it, `kappa_- >= negCount c` and, with
  `neg_inertia_le_hammingDist`, the card's (M3) closes.
- 2026-07-19 — the ATOMIC limits are proved: both atomic Gram entries converge.
  `formal/GaloisForLFunctions/HTGeometry/AtomicGramLimits.lean`; axiom-clean; audit 8503/8503.
  `atomicDiagConst` and `atomicOffDiagConst` — the fixed constants of the two estimates, sums of
  coefficient moduli over atom separations. Naming them is what turns the bounds into "constant
  times a power of the height" and makes the limits immediate.
  `tendsto_atomicGram_diagonal_sub` — the atomic diagonal converges to the atom's COEFFICIENT, the
  deviation being squeezed by `y^2 * atomicDiagConst`.
  `tendsto_atomicGram_offdiag` — the atomic off-diagonal converges to ZERO, squeezed by
  `|y| * atomicOffDiagConst`.
  Both use `squeeze_zero_norm'`, the EVENTUAL form of the squeeze, which is required because the
  underlying estimates need `y /= 0` (and, off-diagonal, `|y| <= 1`) — conditions that hold only
  eventually on `nhdsWithin 0 (/= 0)`, not identically. A tooling note: in this mathlib the bounding
  function of `squeeze_zero_norm'` is the named argument `a`, not `g`, and it must be supplied
  explicitly since it is not determined by unification.
  TWO OF THE FOUR LIMITS ARE DONE. Remaining:
    measure diagonal -> 0 — from `measureGram_diagonal` and
      `tendsto_integral_atomKernel_of_notAtom_herglotz`, both proved; the composition is a rewrite
      plus a coercion limit;
    measure off-diagonal -> 0 — from `norm_measureGram_sq_le` and the diagonal limit, going through
      a square root, which is the one of the four that is not purely mechanical.
  Then `norm_totalGram_sub_diagonal_le` combines all four into the entrywise hypothesis of
  `eventually_negDef_of_entrywise_tendsto_diagonal`, giving `kappa_- >= negCount c` and closing the
  card's (M3).
- 2026-07-19 — ALL FOUR ENTRYWISE LIMITS ARE PROVED.
  `formal/GaloisForLFunctions/HTGeometry/MeasureGramLimits.lean`; axiom-clean; audit 8504/8504.
  `tendsto_norm_of_tendsto_sq` — a vanishing SQUARED norm gives a vanishing norm, by continuity of
  the square root at zero and `Real.sqrt_sq`. This isolates the step I flagged as the one of the
  four that is not mechanical; isolating it makes the off-diagonal argument a squeeze like the
  others rather than a special case.
  `tendsto_zero_of_tendsto_norm` — and a vanishing norm gives a vanishing family.
  `tendsto_measureGram_diagonal` — the measure diagonal converges to the atom mass, hence to ZERO at
  a non-atom, by rewriting through `measureGram_diagonal` and pushing the real limit through the
  coercion.
  `tendsto_measureGram_offdiag` — the measure off-diagonal converges to zero: its squared modulus is
  squeezed by the product of the two diagonal integrals, both of which vanish, and the square-root
  step finishes.
  THE FOUR LIMITS THE (M3) LOWER BOUND NEEDS ARE NOW ALL PROVED:
    atomic diagonal -> coefficient; atomic off-diagonal -> 0;
    measure diagonal -> 0; measure off-diagonal -> 0.
  With `norm_totalGram_sub_diagonal_le` these give the entrywise convergence of `totalGram` to
  `diag(c)`, which is exactly the hypothesis of
  `eventually_negDef_of_entrywise_tendsto_diagonal`. That theorem then yields eventual negative
  definiteness, hence `kappa_- >= negCount c`, and with `neg_inertia_le_hammingDist` the card's (M3)
  `kappa_- = negCount c = HammingDist(chamber, positive chamber)`.
  WHAT REMAINS is the single final composition assembling those four limits into the `∀ epsilon`
  entrywise form and invoking the criterion. Every input is proved; nothing analytic or structural
  is left in the chamber half of this card.
- 2026-07-19 — THE (M3) LOWER BOUND IS ASSEMBLED. The chamber half's analytic and structural work is
  complete. `formal/GaloisForLFunctions/HTGeometry/TotalGramNegativeDefinite.lean`; axiom-clean;
  audit 8505/8505.
  `eventually_negDef_totalGram` — given that the diagonal entries of the total scaled Gram converge
  to the atom coefficients and the off-diagonal entries to zero, and that every coefficient is at
  most `-delta < 0`, the Gram is NEGATIVE DEFINITE for all small heights.
  The assembly turns the four separate limits into the single `for all epsilon` entrywise hypothesis
  using `Filter.eventually_all` twice — once per matrix index — which is available because the index
  is finite, so finitely many `eventually`s intersect. On the diagonal the reference matrix is the
  coefficient (`Matrix.diagonal_apply_eq`); off it the reference vanishes
  (`Matrix.diagonal_apply_ne`) and the deviation is the entry itself.
  So the chamber law's lower bound now reads, in this tree: negative coefficients force a negative
  definite scaled Gram at small heights, hence a negative definite subspace of dimension equal to
  the number of atoms, hence `kappa_- >= negCount c`. Together with `neg_inertia_le_hammingDist`
  that is the card's (M3), `kappa_- = negCount c = HammingDist(chamber, positive chamber)`.
  STATE OF THE CHAMBER HALF: every mathematical component is proved and axiom-clean — the chamber
  grading, the upper bound, the atom limit for finite and infinite measures, the five atomic
  estimates, the measure diagonal and off-diagonal, all four entrywise limits, the perturbation
  criterion with its margin and entrywise bridge, this assembly, and the rational-gauge invariance
  of the family.
  WHAT IS NOT DONE, and should not be read as done: the four limit hypotheses of this theorem are
  supplied as HYPOTHESES here, and discharging them for the card's concrete `m_(u,c)` requires
  feeding `tendsto_atomicGram_diagonal_sub`, `tendsto_atomicGram_offdiag`,
  `tendsto_measureGram_diagonal` and `tendsto_measureGram_offdiag` through
  `norm_totalGram_sub_diagonal_le` — a squeeze on the sum of two vanishing bounds. That is the last
  step, and it is mechanical, but it has not been written.
- 2026-07-19 — THE CHAMBER LOWER BOUND IS UNCONDITIONAL IN THE ATOMIC PART.
  `formal/GaloisForLFunctions/HTGeometry/TotalGramLimits.lean`; compiled first try; axiom-clean;
  audit 8506/8506.
  `tendsto_totalGram_diagonal_sub` and `tendsto_totalGram_offdiag` — the total Gram's deviation from
  the coefficient diagonal converges, because it is the SUM of the atomic deviation and the measure
  entry and both converge. No squeeze is involved: I had recorded the remaining step as "a squeeze
  on the sum of two vanishing bounds", but a squeeze is unnecessary when both summands have proved
  limits — `Tendsto.add` suffices. The estimates were needed to PROVE those limits, not to combine
  them.
  `eventually_negDef_totalGram_of_measure_vanishing` — the chamber lower bound with the atomic side
  fully discharged: given only that the MEASURE part vanishes at every node pair, and that every
  coefficient is at most `-delta < 0`, the total scaled Gram is negative definite at all small
  heights. The atomic limits are supplied internally from
  `tendsto_atomicGram_diagonal_sub` and `tendsto_atomicGram_offdiag`, which need nothing but
  injectivity of the atom placement.
  So the card's (M3) lower bound now depends on exactly one external input: that the measure part of
  the Pick kernel vanishes in the scaled limit — which is (M4), proved for finite AND infinite
  Herglotz measures, together with the Cauchy-Schwarz control of the off-diagonal, also proved. The
  remaining connection is instantiating `tendsto_measureGram_diagonal` and
  `tendsto_measureGram_offdiag` at the card's nodes, whose hypotheses are integrability of the atom
  kernel and the non-atom condition on the insertion points — both card hypotheses.
  With that the chamber law reads: `kappa_-(m_(u,c)) = negCount c = HammingDist(chamber, positive
  chamber)`, upper bound by `neg_inertia_le_hammingDist`, lower bound by this chain.
- 2026-07-19 — the MEASURE DIAGONAL is discharged from the Herglotz dominant alone.
  `formal/GaloisForLFunctions/HTGeometry/MeasureGramVanishing.lean`; compiled first try;
  axiom-clean; audit 8507/8507.
  `integrable_atomKernel_of_dominant` — the dominant makes the atom kernel integrable at every SMALL
  height, by `Integrable.mono'` against `atomKernel_le_atomDominant`.
  `eventually_integrable_atomKernel` — hence integrability holds EVENTUALLY as the height tends to
  zero. The eventual form is forced and not a convenience: for an infinite measure the constant
  bound `atomKernel <= 1` is useless at large heights, so integrability genuinely fails there and
  only the small-height statement is true.
  `tendsto_measureGram_diagonal_of_dominant` — the measure diagonal vanishes at a NON-ATOM, from the
  dominant and the atom law, with no integrability hypothesis left to supply: it is derived.
  So the chamber lower bound's remaining input has shrunk to the measure OFF-diagonal, and that is
  already available as `tendsto_measureGram_offdiag`, whose hypotheses are the Cauchy-Schwarz bound
  (proved, `norm_measureGram_sq_le`) and the two diagonal limits (now proved, this entry). The only
  gap between those is that `norm_measureGram_sq_le` is stated pointwise in `y` with measurability
  and integrability hypotheses, while `tendsto_measureGram_offdiag` wants it EVENTUALLY — the same
  eventual-form adjustment made here for the diagonal.
  STATE: the card's (M3) is proved end to end except for that one eventual-form restatement of the
  Cauchy-Schwarz bound. Every mathematical ingredient of the chamber half is complete and
  axiom-clean; what remains is a hypothesis-shape adjustment of exactly the kind this entry performed
  for the diagonal.
- 2026-07-19 — THE CHAMBER LOWER BOUND IS COMPLETE, from card hypotheses only.
  `formal/GaloisForLFunctions/HTGeometry/ChamberLowerBound.lean`; compiled first try; axiom-clean;
  audit 8508/8508.
  `sub_upperNode_ne_zero` — at a nonzero height the Cauchy factor never vanishes on the real line,
  since its squared modulus is `(t-a)^2 + y^2 > 0`.
  `continuous_scaledCauchyNorm` — hence the modulus of the scaled Cauchy kernel is continuous, which
  supplies the measurability the Cauchy-Schwarz bound needs.
  `tendsto_measureGram_offdiag_of_dominant` — the measure off-diagonal vanishes, the Cauchy-Schwarz
  bound now being available eventually rather than only pointwise.
  `eventually_negDef_totalGram_chamber` — THE LOWER BOUND: at pairwise distinct NON-ATOMIC insertion
  points with a Herglotz dominant, and with every inserted coefficient at most `-delta < 0`, the
  total scaled Pick Gram is NEGATIVE DEFINITE at all small heights.
  Its hypotheses are exactly the card's: `a` injective (distinct insertion points), `nu {a j} = 0`
  (not atoms of the measure), a Herglotz dominant integrable (the (H0) condition), and the
  coefficients negative. Nothing auxiliary survives.
  THE CARD'S (M3) IS NOW PROVED IN BOTH DIRECTIONS:
    UPPER — `neg_inertia_le_hammingDist`: `kappa_- <= negCount c = HammingDist(chamber, positive)`.
    LOWER — this entry: negative coefficients force a negative definite scaled Gram at small
      heights, hence a negative definite subspace of full dimension, hence `kappa_- >= negCount c`.
  Together: `kappa_-(m_(u,c)) = negCount c = HammingDist(chamber, positive chamber)`, which is the
  card's measure-level finite-atomic gauge chamber law, with the chamber grading identified as the
  graph distance in the sign hypercube.
  With the rational-gauge invariance proved earlier, the chamber half of this card is complete:
  every member of the family shares one differential field and one generator class modulo C(z), and
  the exact Krein index is the Hamming distance of its sign chamber from the positive chamber.
  REMAINING ON THE CARD AS A WHOLE: the HT half is already formalised in this tree (the capstone
  `positiveSingularContinuousCarrier_hypertranscendental_dense_residual` and its chain), subject to
  the four audit items recorded earlier — the discrete and absolutely continuous spectra, whether
  the capstone applies the (H0) rational gauge internally, and joint instantiability of its
  hypotheses.
- 2026-07-19 — the chamber law is stated at both EXTREME chambers.
  `formal/GaloisForLFunctions/HTGeometry/ChamberLawExtremes.lean`; axiom-clean; audit 8509/8509.
  `negCount_eq_card_of_all_neg` and `hammingDist_eq_card_of_all_neg` — the all-negative chamber has
  grading `d`, i.e. sits at MAXIMAL Hamming distance from the positive chamber.
  `chamberLaw_all_negative` — with every inserted coefficient at most `-delta < 0` and the card's
  hypotheses (distinct non-atomic insertion points, Herglotz dominant), the scaled Pick Gram is
  negative definite on the WHOLE space at small heights, and the chamber's distance from the
  positive chamber is `d`. So the negative index is the full dimension, matching the grading.
  `chamberLaw_all_positive` — the opposite endpoint: in the positive chamber the grading is zero and
  the kernel admits no negative directions at all.
  These are the two endpoints of the distance grading, and together with the general upper bound
  (`neg_inertia_le_hammingDist`) they pin the card's (M3) at the extremes with the intermediate
  chambers covered by the two bounds separately.
  A checking note: my `grep -c "sorry\|admit"` guard reported 2 hits on this file, which turned out
  to be the word "admits" inside two docstrings. The guard needs `-w` (word boundaries); an
  unanchored grep for `admit` false-positives on ordinary English and would eventually train me to
  ignore it, which is worse than not having it.
  WHAT REMAINS for the general (mixed-sign) chamber: the lower bound proved here applies to the
  whole space when ALL coefficients are negative. For a mixed chamber the negative definite subspace
  is the span of the negative coordinates, of dimension `negCount c`, and extracting it needs the
  `negIndicesEquiv` bookkeeping recorded earlier — restricting the Gram to those coordinates and
  applying the same argument there. That is the one remaining step of the chamber half, and it is
  index bookkeeping over an already-proved estimate rather than new mathematics.
- 2026-07-19 — the MIXED chamber margin is proved; the lower bound now covers every chamber, not
  only the all-negative one.
  `formal/GaloisForLFunctions/HTGeometry/MixedChamberMargin.lean`; compiled first try; axiom-clean;
  audit 8510/8510.
  `negSupported c` — the submodule of vectors supported in the NEGATIVE coordinates of the
  coefficient vector.
  `re_quadForm_diagonal_le_margin_on_negSupported` — on that subspace the coefficient diagonal
  carries the margin: each term either sits at a negative coefficient (where the margin applies) or
  at a nonnegative one (where the vector vanishes, so the term is zero). The two cases are handled
  uniformly by proving the termwise inequality `c_j norm(x_j)^2 <= -delta norm(x_j)^2` for EVERY j,
  which is what makes the sum estimate a single `Finset.sum_le_sum` rather than a split sum.
  `negDef_on_negSupported_of_perturbed` — hence a Gram deviating from the diagonal by less than the
  margin is negative definite ON that subspace, which is the mixed-chamber form of the lower bound.
  So the chamber lower bound is no longer restricted to the all-negative case: in ANY chamber the
  negative coordinate subspace is negative definite for the scaled Gram at small heights, giving a
  negative definite subspace of dimension `negCount c` once that subspace's dimension is computed.
  REMAINING for the general chamber law: `Module.finrank C (negSupported c) = negCount c`. The
  subspace is a coordinate subspace cut out by vanishing conditions on the complement of
  `negIndices c`, so its dimension is the cardinality of `negIndices c`, which is `negCount c` by
  `card_negIndices`. This is a standard coordinate-subspace dimension computation and is the last
  step of the chamber half; with it, `kappa_- >= negCount c` in every chamber and the card's (M3)
  holds in full generality rather than at the extremes.
- 2026-07-19 — THE CHAMBER HALF IS COMPLETE IN FULL GENERALITY.
  `formal/GaloisForLFunctions/HTGeometry/NegSupportedDimension.lean`; compiled first try;
  axiom-clean; audit 8511/8511.
  `negSupportedEquiv` — the negative coordinate subspace is linearly isomorphic to the coordinate
  space indexed by the negative coefficients, by restriction and extension-by-zero.
  `finrank_negSupported` — hence `finrank C (negSupported c) = negCount c`, via
  `Module.finrank_fintype_fun_eq_card` and `Fintype.card_subtype`, the latter identifying the
  subtype cardinality with the filtered cardinality that DEFINES `negCount`.
  WITH THIS THE CARD'S (M3) HOLDS IN EVERY CHAMBER:
    UPPER — `neg_inertia_le_hammingDist`: any negative definite subspace has dimension at most
      `negCount c = HammingDist(chamber, positive chamber)`.
    LOWER — `negDef_on_negSupported_of_perturbed` gives a negative definite subspace, namely
      `negSupported c`, and `finrank_negSupported` gives its dimension as exactly `negCount c`.
  So `kappa_-(m_(u,c)) = negCount c = HammingDist(signPattern c, positiveChamber d)` — the card's
  measure-level finite-atomic gauge chamber law, for an ARBITRARY sign pattern, not only the two
  extremes.
  THE CHAMBER HALF OF THIS CARD IS NOW COMPLETE: the chamber grading is the Hamming distance
  (`negCount_eq_hammingDist`); the exact Krein index equals it in both directions; the family shares
  one differential field and one generator class modulo C(z)
  (`hypertranscendentalOver_upperEnd_addRational_iff`); and the analytic inputs — the atom law for
  finite and infinite Herglotz measures, the five atomic estimates, the Cauchy-Schwarz control of
  the measure part — are all proved and axiom-clean.
  WHAT REMAINS ON THE CARD is the HT half, which is already formalised in this tree (the capstone
  `positiveSingularContinuousCarrier_hypertranscendental_dense_residual` and its chain), subject to
  the four audit items recorded earlier: whether the discrete and absolutely continuous spectra are
  covered, whether the capstone applies the (H0) rational gauge internally, and whether its
  hypotheses are jointly instantiable. Those are audit questions about existing code, not
  construction.
- 2026-07-19 — AUDIT FINDING on the HT half, plus the infrastructure it needs.
  `formal/GaloisForLFunctions/HTGeometry/PolynomialVariableShift.lean`; axiom-clean; warning-free;
  audit 8512/8512.
  THE FINDING. The HT chain uses TWO DIFFERENT hypertranscendence predicates and the bridge between
  them is not in the tree. The capstone
  `positiveSingularContinuousCarrier_hypertranscendental_dense_residual` concludes
  `Hypertranscendental (fun z => integral ((x:C) - z)^{-1} d(carrier))` — the PLAIN predicate on a
  concrete function. The (H0) gauge transfer
  `hypertranscendentalOver_herglotzGauge_cauchyTransform_iff` is stated for
  `HypertranscendentalOver upperEndRationalCoordinateField (cauchyTransformUpperEndMero nu)` — the
  RELATIVE predicate on an element of the upper-end meromorphic field. `cauchyTransformUpperEndMero`
  has no theorem connecting it to the plain predicate. So the card's step from "the Cauchy transform
  is hypertranscendental" to "the (H0) regularized transform is hypertranscendental" is NOT closed in
  the tree, contrary to what I recorded when I first found the chain.
  WHAT THE BRIDGE ACTUALLY NEEDS, and it is smaller than the general gauge statement: the (H0)
  regularization subtracts `integral t/(1+t^2) exp(u) dmu`, which is a CONSTANT in `z`. So the two
  transforms differ by an additive constant, not by a general rational function, and the required
  invariance is `Hypertranscendental (f + const) <-> Hypertranscendental f`.
  `DifferentiallyAlgebraicInvariance` has the three neighbouring invariances — `f (z + a)`,
  `f (c z)`, `c * f` — but NOT the additive value shift. It is genuinely missing.
  BUILT HERE, as the algebraic core of that missing invariance: `shiftSubst i c` shifts one
  polynomial variable by a constant; `shiftSubst_shiftSubst` inverts it; `shiftSubst_ne_zero` shows
  it preserves nonvanishing (it is an algebra automorphism); `eval_shiftSubst` evaluates it at the
  shifted point. These mirror the existing `scaleSubst` of `PolynomialVariableRescale`.
  NEXT: use these to prove `differentiallyAlgebraic_add_const_iff` and hence
  `hypertranscendental_add_const_iff`, applying `shiftSubst` at the VALUE slot (index 1 of
  `Fin (n+2)`, slot 0 being `z`), since adding a constant changes the value and no derivative. That
  closes the bridge and with it the last identified gap in the HT half.
- 2026-07-19 — THE ADDITIVE-CONSTANT INVARIANCE IS PROVED, closing the gap found last entry.
  `formal/GaloisForLFunctions/HTGeometry/HypertranscendentalAddConst.lean`; axiom-clean;
  warning-free; audit 8515/8515.
  `deriv_add_const_fun`, `iteratedDeriv_add_const_succ` — adding a constant changes NO derivative of
  positive order.
  `differentiallyAlgebraic_add_const` — hence a differential polynomial annihilating `f + c`
  yields one annihilating `f`, by applying `shiftSubst` at the VALUE slot (index 1 of `Fin (n+2)`,
  slot 0 holding `z`). The jet vector of `f + c` is exactly the jet vector of `f` with slot 1
  updated by `+ c`, which is precisely what `eval_shiftSubst` computes.
  `differentiallyAlgebraic_add_const_iff` and `hypertranscendental_add_const_iff` — the invariance in
  both directions, the reverse obtained by shifting the shifted function back by `-c`.
  This fills the hole in `DifferentiallyAlgebraicInvariance`, which had `f (z + a)`, `f (c z)` and
  `c * f` but not `f + c`. The missing case was the one the (H0) regularization needs, since the
  regularized Herglotz transform differs from the plain Cauchy transform by the constant
  `integral t/(1+t^2) exp(u) dmu`.
  So the audit item recorded last entry — that the card's step from Cauchy-transform
  hypertranscendence to (H0)-transform hypertranscendence was not closed — is now closed AT THE LEVEL
  OF THE PLAIN PREDICATE, which is the predicate the capstone actually concludes in. Applying it
  requires only identifying the (H0) transform as (plain Cauchy transform) + (a constant), which is
  the definition of the regularization.
  STATE OF THE CARD after this session: the chamber half is complete in full generality; the HT half
  is formalised in the tree with its capstone, and the one gap I identified in it is now filled. The
  three remaining audit questions are unchanged and are about EXISTING code rather than missing
  work: whether the discrete and absolutely continuous spectra are covered by the capstone or need
  their own, and whether the capstone's hypotheses (`HasMinimalExponentialType`, the no-common-zero
  condition, the upper-half-plane map condition, the null-set pullback, and the projective geometry
  argument) are jointly instantiable for this card's setting.
- 2026-07-19 — the (H0) BRIDGE is applied: the regularized transform inherits hypertranscendence.
  `formal/GaloisForLFunctions/HTGeometry/RegularizedTransformBridge.lean`; compiled first try;
  axiom-clean; audit 8516/8516.
  `hypertranscendental_of_eq_add_const` — a transform differing from another by a constant has the
  same hypertranscendence status.
  `hypertranscendental_regularized_iff` and `hypertranscendental_regularizedHerglotz_iff` — the
  (H0) form: `m z = cauchy z - reg` is hypertranscendental exactly when the plain Cauchy transform
  is, the regularization constant playing no role.
  So the card's step from the capstone's conclusion — hypertranscendence of the CAUCHY transform of
  the carrier — to its stated object, the (H0) REGULARIZED Herglotz transform, is now a theorem in
  this tree rather than an unexamined assumption. The hypothesis it consumes is exactly the
  regularization identity `m z = cauchy z - reg`, which is the DEFINITION of the (H0) transform once
  the two integrals are separated; separating them requires integrability of each piece, which the
  (H0) condition `integral (1+t^2)^{-1} dmu < infinity` supplies and which I have NOT written out.
  SESSION SUMMARY FOR THIS CARD.
  CHAMBER HALF — complete in full generality: chamber grading is Hamming distance; exact Krein index
  equals it in both directions and in every chamber; family shares one differential field modulo
  C(z); atom law proved for finite and infinite Herglotz measures; all five atomic estimates, the
  measure diagonal and off-diagonal, all four entrywise limits, and the perturbation machinery.
  HT HALF — the chain exists in the tree (capstone
  `positiveSingularContinuousCarrier_hypertranscendental_dense_residual`), and the one gap I found in
  it, the passage to the (H0) transform, is now closed by this entry and the additive-constant
  invariance it rests on.
  REMAINING AUDIT ITEMS, all about existing code: coverage of the discrete and absolutely continuous
  spectra; joint instantiability of the capstone's hypotheses; and writing out the integral
  separation that supplies the regularization identity above.
- 2026-07-19 — RETRACTION. My previous two entries mis-identified the (H0) bridge. The
  regularization is NOT a constant shift.
  Reading `RegularizedHerglotzTransform.lean`, which I had cited without opening:
  `regularizedHerglotzKernel_eq` — the kernel is `nevanlinnaWeight t * (z + (1 + z^2)/(t - z))`;
  `regularizedHerglotzTransform_eq` — the transform is
  `z * (total mass of the weighted measure) + (1 + z^2) * (Cauchy transform of that measure)`.
  That is a genuine RATIONAL gauge in the spectral variable, with an `(1 + z^2)` multiplier and a
  `z`-linear shift. It is not "Cauchy transform minus a constant".
  WHY I GOT IT WRONG. I reasoned that the subtracted kernel term `t/(1+t^2)` does not involve `z`,
  so integrating it gives a constant. The step is true only if the integral SPLITS, and under (H0)
  the two pieces need not converge separately — which is the whole reason the regularization exists.
  The corpus avoids the split entirely by reweighting the measure, which is why its identity has a
  weighted Cauchy transform rather than a plain one.
  CONSEQUENCE. The correct bridge is `hypertranscendentalOver_herglotzGauge_iff`, which is exactly
  the affine rational gauge `a * C + b` with `a = 1 + z^2` and `b = z * mass` — and it was already in
  the tree. My additive-constant work does not supply it.
  WHAT REMAINS VALID from those entries, and it is not nothing: `shiftSubst` and
  `differentiallyAlgebraic_add_const_iff` / `hypertranscendental_add_const_iff` are correct theorems
  filling a real hole in `DifferentiallyAlgebraicInvariance`, which had `f (z + a)`, `f (c z)` and
  `c * f` but no additive value shift. They are simply not the (H0) bridge. The module
  `RegularizedTransformBridge` has been renamed in substance — its theorems are now
  `hypertranscendental_sub_const_iff` and `hypertranscendental_sub_const_presentation_iff` — and
  carries a WARNING docstring recording that the regularization is a rational gauge and pointing to
  the correct lemma, so a later reader is not misled the way I was.
  LESSON, the same one this card has taught repeatedly: I cited `RegularizedHerglotzTransform` as
  supporting the constant-shift story without opening it. The file states the correct identity in
  its first theorem. Reading beats reasoning here, and this is the fourth time on this card.
- 2026-07-19 — THE HT HALF HAS A STRUCTURAL GAP, and it is not the one I have been chasing.
  Searched the tree for any theorem relating the plain predicate `Hypertranscendental : (C -> C) ->
  Prop` to the relative predicate `HypertranscendentalOver upperEndRationalCoordinateField` on
  `upperEndMeroField`. THERE IS NONE. Also none embedding a concrete function into
  `upperEndMeroField` for this purpose.
  WHY THIS MATTERS. The two halves of the card's HT argument live in different predicates:
    the capstone `positiveSingularContinuousCarrier_hypertranscendental_dense_residual` concludes
    `Hypertranscendental (fun z => integral ((x:C) - z)^{-1} d(carrier))` — PLAIN, on a function;
    the (H0) step needs `hypertranscendentalOver_herglotzGauge_iff`, which is RELATIVE, on a field
    element, because the gauge `(1 + z^2) * C + z * mass` has RATIONAL coefficients and rational-gauge
    invariance is a differential-field statement.
  The plain predicate's invariance file `DifferentiallyAlgebraicInvariance` carries only
  `f (z + a)`, `f (c z)`, `c * f` and now (this session) `f + c` — all with CONSTANT parameters. None
  covers multiplication by a nonzero polynomial in `z`, which is what the (H0) gauge requires.
  SO THE CARD'S HT HALF IS NOT CLOSED IN THIS TREE, contrary to what I recorded when I first found
  the capstone chain and called it "complete except for audit items". The capstone is real and
  axiom-clean; the (H0) gauge invariance is real and axiom-clean; but they are stated about
  different objects and nothing connects them.
  WHAT WOULD CLOSE IT, in order of increasing generality:
    (a) plain-predicate invariance under an affine gauge with POLYNOMIAL coefficients,
        `Hypertranscendental (fun z => a z * f z + b z) <-> Hypertranscendental f` for `a, b`
        polynomials with `a` not identically zero. This is the minimal statement the (H0) step needs
        and it is provable in the plain jet formulation, though the jets of `a f + b` involve
        derivatives of `a` and `b` so the substitution is not the simple variable shift used for
        constants;
    (b) or an embedding of concrete functions into `upperEndMeroField` with a theorem that the plain
        and relative predicates agree under it, which would connect the capstone to the whole
        upper-end gauge library at once and is the more valuable target.
  I am recording this rather than starting either, because both are substantial and a half-built
  bridge is worse than a precise handoff. The chamber half of this card is complete; this is the one
  identified structural gap remaining, and it is in the HT half.
- 2026-07-19 — first real progress on the HT-half gap: the POLYNOMIAL axis shift is built.
  `formal/GaloisForLFunctions/HTGeometry/AxisShiftSubstitution.lean`; axiom-clean; warning-free;
  audit 8517/8517.
  `axisShiftSubst i h` — shifts every variable OTHER than a distinguished one by a polynomial in
  that distinguished variable, leaving it fixed. This is the substitution that realizes "add a
  polynomial to a function": the jet slot of order `j` shifts by the `j`-th derivative of that
  polynomial, and every such derivative is a polynomial in the spectral variable, which is exactly
  the distinguished variable of the jet coordinates.
  `axisShiftSubst_axisShiftSubst` — shifting by the negated family inverts it, so the substitution is
  an algebra automorphism. The inner induction is over the shifting polynomial itself, since the
  shift must be shown invariant under the substitution — it involves only the distinguished
  variable, which the substitution fixes.
  `axisShiftSubst_ne_zero` — hence it preserves nonvanishing, which is what transferring a
  differential relation requires.
  This strictly generalises `shiftSubst` (constant shift of ONE variable) built earlier this
  session, and it is the additive half of the polynomial gauge the (H0) step needs. The remaining
  half is multiplicative — invariance under `f |-> a * f` for a nonzero polynomial `a` — which does
  NOT reduce to a substitution of this kind: the inverse substitution would divide by `a`, leaving
  the polynomial ring. That half needs either clearing denominators after a rational substitution,
  or the differential-field route (option (b) of the previous entry).
  Recording the asymmetry explicitly because it is the crux: additive polynomial gauges are
  substitutions and are easy; multiplicative ones are not, and that is why the corpus's gauge
  library lives in a FIELD (`upperEndMeroField`) rather than in the plain jet formulation. My
  instinct that the plain-predicate route would be "the minimal statement" underestimated this —
  option (b), the embedding into the field, may well be the shorter path after all.
- 2026-07-19 — the ADDITIVE POLYNOMIAL gauge invariance is proved for the plain predicate.
  `formal/GaloisForLFunctions/HTGeometry/AddPolynomialInvariance.lean`; axiom-clean; audit
  8518/8518.
  `eval_aeval_X` — evaluating a univariate polynomial substituted at one variable.
  `eval_axisShiftSubst` — the evaluation law of the axis shift.
  `iteratedDeriv_polynomial_eval` — the iterated derivatives of a polynomial function are the
  polynomial's own iterated derivatives.
  `iteratedDeriv_add_polynomial` — the jets of `f + p` are the jets of `f` shifted by the successive
  derivatives of `p`.
  `differentiallyAlgebraic_add_polynomial` — hence adding a polynomial preserves differential
  algebraicity, by `axisShiftSubst` at the spectral variable.
  A HYPOTHESIS THAT IS GENUINELY NEEDED, and was not needed for the constant case: differentiability
  of every iterated derivative of `f`. For a CONSTANT shift the corresponding step is
  `deriv_add_const`, which mathlib states UNCONDITIONALLY, so no smoothness is required. For a
  POLYNOMIAL shift the step is `deriv (f + p) = deriv f + deriv p`, which needs `f` differentiable.
  The difference is real and not an artefact of my proof: without differentiability `iteratedDeriv`
  is junk-valued and the jets of `f + p` need not be the shifted jets of `f`. The card's transforms
  are analytic, so the hypothesis is harmless there, but it must be carried.
  STATE OF THE HT-HALF GAP: the additive half of the rational gauge is now proved for the PLAIN
  predicate. What remains is the MULTIPLICATIVE half, `Hypertranscendental (a * f) <->
  Hypertranscendental f` for a nonzero polynomial `a`, which as recorded is not a substitution of
  this kind — the inverse would divide by `a` and leave the polynomial ring. The two candidate
  routes are unchanged: clear denominators after a rational substitution, or embed into
  `upperEndMeroField` and use the existing field-level gauge library.
- 2026-07-19 — THE HERGLOTZ GAUGE IS REDUCED TO ITS MULTIPLICATIVE PART.
  `formal/GaloisForLFunctions/HTGeometry/GaugeReductionToMultiplicative.lean`; compiled first try;
  axiom-clean; audit 8519/8519.
  `differentiallyAlgebraic_add_polynomial_iff` — the additive polynomial invariance in BOTH
  directions, the reverse by shifting back by the negated polynomial.
  `hypertranscendental_gauge_iff_mul` — presenting the regularized transform as
  `polynomial + (1 + z^2) * C`, exactly the shape `regularizedHerglotzTransform_eq` gives with the
  polynomial being `z * mass`, the SHIFT DROPS OUT ENTIRELY:
    `Hypertranscendental m <-> Hypertranscendental (fun z => (1 + z^2) * C z)`.
  So the (H0) gauge question is now reduced to one statement and no other:
    does multiplying by the nonzero polynomial `1 + z^2` change hypertranscendence?
  WHAT THE REMAINING STEP LOOKS LIKE, from the analysis: in the direction `DA(a f) -> DA(f)` the
  substitution is POLYNOMIAL and needs no division — by Leibniz, `(a f)^(k)` is a linear combination
  of the jets of `f` with coefficients the derivatives of `a`, so the substitution
  `X_(k+1) |-> sum_j binom(k,j) a^(j)(X_0) X_(k-j+1)` is a genuine polynomial substitution. It is
  TRIANGULAR with diagonal `a(X_0)`, hence injective over the fraction field `C(X_0)`, which is what
  nonvanishing of the transformed relation needs. So the remaining work is (i) the Leibniz identity
  for iterated derivatives of a product, and (ii) injectivity of a triangular substitution with
  nonzero diagonal. Neither is research; both are standard algebra not yet in this tree.
  Note this is strictly better than the position two entries ago, when the multiplicative half looked
  like it might need the differential-field embedding: the polynomial direction of the substitution
  exists, and only its injectivity requires the fraction field, not the construction itself.
  CARD STATUS: chamber half complete in full generality; HT half complete except for this single
  multiplicative gauge step, with every other link — capstone, additive gauge, predicate bookkeeping
  — proved and axiom-clean.
- 2026-07-19 — the Leibniz half of the remaining step is ALREADY IN MATHLIB.
  Probed for `iteratedDeriv_mul` and it exists:
    `ContDiffAt K n f x -> ContDiffAt K n g x ->
       iteratedDeriv n (f * g) x = sum over range (n+1) of binomial times the paired jets`.
  So of the two pieces I identified for the multiplicative gauge —
    (i) the Leibniz identity for iterated derivatives of a product, and
    (ii) injectivity of a triangular substitution with nonzero diagonal —
  piece (i) needs no construction at all. It carries a `ContDiffAt` hypothesis, which the card's
  analytic transforms satisfy and which is anyway already implied by the differentiability
  hypotheses the additive invariance carries.
  For the specific gauge the identity is very short: with `a = 1 + z^2` one has `a' = 2z`,
  `a'' = 2`, `a''' = 0`, so the Leibniz sum has only THREE nonzero terms and
    `(a f)^(k) = a f^(k) + 2 k z f^(k-1) + k (k-1) f^(k-2)`.
  The substitution `X_(k+1) |-> (1 + X_0^2) X_(k+1) + 2 k X_0 X_k + k (k-1) X_(k-1)` is therefore
  explicit, triangular, with diagonal `1 + X_0^2` — a nonzero polynomial. Only its injectivity
  remains, and that is the fraction-field argument recorded last entry.
  HANDOFF STATE OF THIS CARD.
  CHAMBER HALF — complete in full generality and axiom-clean: chamber grading is Hamming distance;
  exact Krein index equals it in both directions in every chamber; the family shares one
  differential field modulo C(z); atom law for finite and infinite Herglotz measures; all five
  atomic estimates; measure diagonal and off-diagonal; all four entrywise limits; the perturbation
  machinery and its assembly.
  HT HALF — the capstone chain exists in the tree; the predicate mismatch I found is reduced, via
  the additive polynomial gauge proved this session, to the SINGLE question whether multiplying by
  `1 + z^2` changes hypertranscendence; the substitution realizing it is explicit and the Leibniz
  input is in mathlib; only triangular-substitution injectivity is unbuilt.
  Everything above is axiom-clean `[propext, Classical.choice, Quot.sound]` and the umbrella builds.
- 2026-07-19 — the INJECTIVITY tool for the multiplicative gauge is proved, and it needs no fraction
  field. `formal/GaloisForLFunctions/HTGeometry/SubstitutionNonvanishing.lean`; compiled first try;
  axiom-clean; audit 8590/8590.
  `subst_ne_zero_of_pointMap_surjective` — if a substitution acts on points by a map `T`, and `T`
  hits every point where some fixed nonzero polynomial `g` does not vanish, then the substitution
  cannot kill a nonzero polynomial. Proof: `P * g` is nonzero in a domain, so it has a nonvanishing
  point `w`; there `P` and `g` are both nonzero; surjectivity pulls `w` back through `T` to a point
  where the substituted polynomial is nonzero.
  `subst_injective_of_pointMap_surjective` — the injective form, by applying it to a difference.
  THIS REPLACES THE FRACTION-FIELD ARGUMENT I had planned for the triangular substitution. Rather
  than constructing the inverse substitution over `C(X_0)` and proving it inverts, one only has to
  observe that the triangular system `T v = w` is SOLVABLE wherever its diagonal does not vanish —
  a finite recursion — and take `g` to be that diagonal. The tool it reuses,
  `exists_eval_ne_zero`, is the same one built for the distinct-node argument on the chamber half
  many entries ago; the polynomial-domain trick pays a second time.
  STATE OF THE MULTIPLICATIVE GAUGE, the last open step of this card:
    the substitution is explicit — `X_(k+1) |-> (1 + X_0^2) X_(k+1) + 2k X_0 X_k + k(k-1) X_(k-1)`;
    its Leibniz justification is `iteratedDeriv_mul`, in mathlib;
    its nonvanishing now follows from this entry once the point map is exhibited and its triangular
    solvability off the zero set of `1 + X_0^2` is checked.
  What remains is assembling those three: defining the substitution, proving the jet identity from
  `iteratedDeriv_mul`, and checking the triangular solvability. No further tools are missing, and no
  step of it is research.
- 2026-07-19 — TRIANGULAR SOLVABILITY is proved. The last named tool for the multiplicative gauge
  exists. `formal/GaloisForLFunctions/HTGeometry/TriangularSolvability.lean`; axiom-clean; audit
  8591/8591.
  `triangularSolve` — the solution of a triangular system, built by STRONG RECURSION: each unknown
  is read off from the strictly earlier ones by dividing by the diagonal.
  `exists_triangular_solution` — if each equation's lower part depends only on strictly earlier
  unknowns and the diagonal is nonzero, the system is solvable. The proof needs
  `Nat.strongRecOn_eq` to unfold the recursion, then the dependence hypothesis to replace the
  truncated argument by the full solution.
  A tooling note: the unfolding lemma is `Nat.strongRecOn_eq`, not the `_beta` or `_beta'` names I
  guessed; and after unfolding, the two sides differ only by the definition of `triangularSolve`
  itself, so a bare `rfl` closes the step. Guessing simp-lemma names cost two cycles here, and
  `exact?` on the exact goal found it immediately — the same lesson as elsewhere in this session,
  applied to lemma names rather than to whole theorems.
  ALL TOOLS FOR THE MULTIPLICATIVE GAUGE NOW EXIST:
    the jet identity — `iteratedDeriv_mul`, in mathlib;
    the nonvanishing criterion — `subst_ne_zero_of_pointMap_surjective`, proved two entries ago;
    the surjectivity of the point map — this entry, off the diagonal's zero set.
  What remains is only to write the specific substitution for `a = 1 + z^2`, instantiate these three
  against it, and conclude `DifferentiallyAlgebraic (a * f) -> DifferentiallyAlgebraic f`. With that
  and `hypertranscendental_gauge_iff_mul` the (H0) gauge closes, and with it the HT half of this
  card.
- 2026-07-19 — the two nonvanishing tools are bridged: the criterion now applies directly to a
  substitution given by its coordinate images.
  `formal/GaloisForLFunctions/HTGeometry/BindSubstitutionNonvanishing.lean`; axiom-clean; audit
  8592/8592.
  `bindPointMap J` — the point map induced by a coordinatewise substitution, evaluating each
  coordinate image.
  `eval_bind₁_eq` — evaluating a substituted polynomial is evaluating the original at that induced
  point. (`MvPolynomial.eval_bind₁` does not exist under that name in this toolchain; a three-case
  induction proves it directly and is shorter than hunting for the right composition lemma.)
  `bind₁_ne_zero_of_pointMap_surjective` and `bind₁_injective_of_pointMap_surjective` — the
  criterion of two entries ago, instantiated at `bind₁`. So for ANY coordinatewise substitution, it
  now suffices to exhibit a nonzero polynomial whose nonvanishing locus the induced point map
  covers.
  THE MULTIPLICATIVE GAUGE IS NOW ONE INSTANTIATION AWAY. Its three inputs are in place and connect
  without further construction:
    the jet identity for `a * f` — `iteratedDeriv_mul` (mathlib);
    nonvanishing of the induced substitution — this entry, given a covering point map;
    the covering — `exists_triangular_solution`, since the jet substitution is triangular with
      diagonal `a(X_0)` and the system is solvable wherever `a` does not vanish.
  All that is left is to WRITE the coordinate images
  `J (k+1) = sum_j binom(k,j) * a^(j)(X_0) * X_(k-j+1)` for `a = 1 + z^2`, where the sum has three
  terms, and feed them through. I am at the end of what this session can hold; the next iteration
  should start there, and every lemma it needs is named above.
  CARD STATUS AT SESSION END. Chamber half: COMPLETE in full generality, axiom-clean. HT half: the
  capstone chain exists in the tree; the predicate gap I discovered is reduced to the single
  multiplicative gauge step; every tool for that step is built and verified; only the instantiation
  remains.
- 2026-07-19 — full `GaloisForLFunctions.HTGeometry` umbrella build launched as a coherence check on
  everything added this session (~40 modules). Running in the background; per the one-build-at-a-time
  rule no further build was started alongside it. Each module was already individually built and
  audited axiom-clean as it landed; the umbrella build additionally checks for duplicate declaration
  names across modules and for import coherence, which per-module builds do not — that is exactly the
  failure mode the deleted `LogOnePlusBound` duplicate would have caused had it not been caught.
  Result to be recorded next iteration.
- 2026-07-19 — exact statement of the Leibniz input recorded, with a form detail that would
  otherwise cost a cycle. From `Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:418`:
    `iteratedDeriv_mul (hf : ContDiffAt K n f x) (hg : ContDiffAt K n g x) :
       iteratedDeriv n (f * g) x
         = sum over i in range (n+1) of (n.choose i) * iteratedDeriv i f x * iteratedDeriv (n-i) g x`
  With `f := a` the polynomial and `g` the function, the `i`-th term is
  `binom(n,i) * a^(i) * g^(n-i)`, which is the substitution's coordinate image as expected.
  THE FORM DETAIL: this lemma is stated for `f * g` (the Pi multiplication), and it carries
  `@[to_fun iteratedDeriv_fun_mul]`, so a LAMBDA-form variant `iteratedDeriv_fun_mul` exists for
  `fun x => f x * g x`. The lambda form is the one to use. I lost two cycles earlier this session to
  exactly this distinction with `deriv_add`, which is stated for `f + g` and would not rewrite
  against `fun w => f w + Polynomial.eval w b`; the fix there was `HasDerivAt`. Here the `to_fun`
  variant already exists and no workaround is needed — provided one reaches for it directly.
  Also note the hypotheses are `ContDiffAt` at the point, not global smoothness, which is weaker
  than the `∀ j, Differentiable (iteratedDeriv j f)` the additive invariance carries and so is
  already implied by it.
  Umbrella coherence build still running at the time of writing; result to be recorded when it
  completes.
- 2026-07-19 — multiplicative gauge module DRAFTED in the scratchpad, deliberately NOT placed in the
  tree while the umbrella coherence build holds the single build slot. Unverified code must not
  enter a tree other agents build against; the draft lives at
  `scratchpad/MulPolynomialInvariance_draft.lean` and records the substitution together with its
  five remaining obligations in order.
  The substitution: `mulJetImage a s` sends the jet slot of order `k` to the Leibniz combination
  `sum_(i <= k) binom(k,i) * a^(i)(X_0) * X_(k-i+1)`, fixing the spectral coordinate. Its diagonal
  term is `a(X_0) * X_(k+1)`, which is why `Polynomial.aeval (X 0) a` is the polynomial whose
  nonvanishing locus the point map must cover.
  THE ONE PLACE NEEDING CARE, identified in advance: `exists_triangular_solution` is stated over `N`
  while the jets are indexed by `Fin (n+2)`. Extending the finite system to `N` by zero, solving,
  and restricting is the intended route; the lower-part dependence hypothesis survives because the
  Leibniz sum for slot `k+1` involves only slots of index at most `k`. Recording this now because
  index transport between `Fin` and `N` is precisely the kind of step that has twice cost a module
  on this card when discovered late rather than planned for.
- 2026-07-19 — PROCESS ERROR, recorded because the diagnosis was wrong and the reasoning is worth
  not repeating. I judged the umbrella coherence build "stalled" and killed it. It was not stalled:
  it reached 9785/9796 jobs and exited 0. Two bad inferences:
  (i) I ran `pgrep -c lean` and read 0 as "no work happening". Wrong pattern — `lake` spawns lean
  workers that are short-lived and not matched by that name, so a zero count says nothing about
  progress.
  (ii) I read the task output file with `tail` and saw only the initial `pwd` line, concluding no
  output. The file was buffered; the progress lines appeared only at completion. Buffered output is
  not absence of output.
  The correct check would have been the output file's SIZE over time, or simply waiting for the
  completion notification, which is what the harness provides. Killing a working build in a shared
  repo also wasted several minutes of other agents' contention budget for nothing.
  The captured log shows 0 errors, and the only warning is an unused variable in
  `FiniteRangePrimeDirichletRelationIdeal.lean`, another agent's module. No error is attributable to
  anything added this session. A clean re-run has been launched to confirm properly rather than rely
  on a truncated log.
- 2026-07-19 — NAME-HYGIENE AUDIT of this session's modules, done by static scan rather than by
  build. 82 modules, 264 declarations. Results:
  NO internal duplicates among them.
  THREE names collide with declarations elsewhere in `HTGeometry`, all in DIFFERENT namespaces, so
  none is a genuine duplicate and the umbrella build is unaffected:
    `differentiallyAlgebraic_add_polynomial_iff` — mine in `GaloisForLFunctions.HTGeometry`,
      also in `LogSuperlacunaryMagnitudeHypertranscendence` under `GaloisForLFunctions`;
    `exists_eval_ne_zero` — mine in `GaloisForLFunctions.HTGeometry`, also in
      `PolynomialEvaluationLemma` under `AffineJet`;
    `iteratedDeriv_polynomial_eval` — mine in `GaloisForLFunctions.HTGeometry`, also in
      `DigammaPolynomialCarrier` under `GaloisForLFunctions`.
  WHY THIS STILL MATTERS, and why a build would not have found it: two of the three shadow names in
  the PARENT namespace `GaloisForLFunctions`, and several of my modules `open GaloisForLFunctions`.
  Inside those modules a bare reference to either name is ambiguous between the parent and the child
  declaration. Nothing in my code triggers it — every use resolves — so it is latent, not an error,
  and no build will report it. But a later edit that uses the bare name inside one of these modules
  will get an ambiguity error whose cause is nonlocal and hard to see.
  Recording rather than renaming: the names are apt in their own modules and renaming now would
  churn a working chain. The right fix, if it ever bites, is to qualify at the use site.
  This check cost one static scan and no build. It is the kind of thing that per-module builds and
  even the umbrella cannot surface, since the ambiguity is only realised at a use site that does not
  yet exist.
- 2026-07-19 — REACHABILITY AND DANGLING-REFERENCE AUDIT, static, no build:
    all 82 modules added this session exist on disk;
    all 82 are imported by the `GaloisForLFunctions.HTGeometry` umbrella — none is orphaned;
    the two modules DELETED this session as redundant (`LogOnePlusBound`,
    `MultiplicativeGaugeCompositeReachability`) have no dangling references anywhere in
    `HTGeometry` and are absent from the umbrella.
  Orphaned modules are worth checking for specifically because an unimported module is never built
  by the umbrella and so silently stops being verified — it can rot for a long time while every
  local check still passes. Deletions are worth checking for the mirror reason: a stale import
  breaks the umbrella for everyone, not just the author.
  Together with the earlier name-hygiene scan (264 declarations, no internal duplicates, three
  cross-namespace shadowings recorded as latent), the static audit of this session's contribution is
  complete: everything is present, reachable, uniquely named within its namespace, and free of
  references to deleted code.
- 2026-07-19 — CORRECTION to a claim I have repeated for several entries. I have been writing
  "the chamber half is COMPLETE in full generality". Checked it by enumerating the theorems, and it
  is an OVERSTATEMENT. What actually exists:
    UPPER BOUND — `neg_inertia_le_hammingDist` : any negative definite subspace has dimension at most
      `negCount c = HammingDist(chamber, positive chamber)`. Proved.
    LOWER INGREDIENTS — `negDef_on_negSupported_of_perturbed` (the negative coordinate subspace is
      negative definite for a Gram close enough to the diagonal) and `finrank_negSupported`
      (its dimension is `negCount c`). Both proved.
    EXTREMES — `chamberLaw_all_negative`, `chamberLaw_all_positive`. Proved.
    ANALYTIC INPUT — `eventually_negDef_totalGram_chamber`, from card hypotheses. Proved.
  WHAT DOES NOT EXIST: a single theorem asserting `kappa_-(m_(u,c)) = negCount c` for a GENERAL sign
  pattern. Every ingredient of it is proved and the combination is short, but the statement has not
  been written, so the card's (M3) is not discharged as one citable result.
  The distinction matters for an auditor: "all the pieces are proved" and "the theorem is proved"
  are different claims, and I conflated them. The correct summary of the chamber half is that its
  analysis is complete and its final assembly is one unwritten theorem.
  Not writing it this turn: the umbrella coherence build holds the single build slot, and I will not
  put an unverified theorem into a tree other agents build against — that is the same discipline
  that kept the drafted multiplicative-gauge module in the scratchpad. It is the first thing to
  write when the slot frees.
- 2026-07-19 — the missing chamber equality is DRAFTED (scratchpad, pending build slot):
  `scratchpad/ChamberLawEquality_draft.lean`.
  FORM CHOICE, decided by reading the corpus rather than by preference: there is no single
  `kappa_-` definition for a Hermitian matrix in this tree — `KreinLangerInertia` expresses the index
  as a subspace-dimension bound, and mathlib's `sigNeg` is used elsewhere only for quadratic forms.
  So "the negative index equals the chamber grading" is stated TWO-SIDED, which is what makes it
  citable without inventing a `kappa_-`:
    every negative definite subspace has dimension at most `negCount c`, AND
    `negSupported c` is negative definite with dimension exactly `negCount c`.
  Those two together ARE the assertion that the maximum is `negCount c`; the pair is the honest
  formulation, not a weakening.
  `chamberLaw_negIndex_eq_grading` combines `neg_inertia_le_negCount` with `finrank_negSupported`;
  `chamberLaw_negIndex_eq_hammingDist` reads it through `negCount_eq_hammingDist`, giving the card's
  own phrasing — the exact Krein index is the graph distance of the sign chamber from the positive
  chamber.
  Both are assembled entirely from theorems already proved and audited this session; nothing new is
  assumed. They stay in the scratchpad until the umbrella build releases the single build slot,
  after which they are the first thing to verify and install.
- 2026-07-19 — DESK-CHECK of the chamber-equality draft, done statically while the build slot is
  held. Three things verified without compiling:
  (1) SIGNATURE MATCH. `neg_inertia_le_negCount` is
      `(H : Matrix (Fin n) (Fin n) C) (c : Fin d → R) (v : Fin (negCount c) → (Fin n → C)) ...`
      with `n` and `d` INDEPENDENT. The draft instantiates `n := d`, which is exactly the card's
      situation (one evaluation node per inserted atom), and the types then line up: `v` lands in
      `Fin d → C` and `W` is a submodule of `Fin d → C`.
  (2) REACHABILITY. Traced the transitive `HTGeometry` imports of `NegSupportedDimension`: 37
      modules, and `ChamberNegInertiaBound`, `SignChamberHammingGrading`, `MixedChamberMargin` are
      all reachable. So the draft's single import suffices for every name it uses — `negCount`,
      `negSupported`, `signPattern`, `positiveChamber`, `finrank_negSupported`,
      `neg_inertia_le_negCount`, `negCount_eq_hammingDist`.
  (3) REWRITE DIRECTION. `negCount_eq_hammingDist : negCount c = hammingDist (signPattern c)
      (positiveChamber d)`, so `rw [← negCount_eq_hammingDist]` turns the goal's `hammingDist`
      occurrences into `negCount`, matching the hypotheses in hand. The direction is the one the
      draft uses.
  Desk-checking costs nothing while the slot is unavailable and removes the three failure modes that
  have actually bitten this session — wrong argument shape, a missing transitive import, and a
  rewrite pointing the wrong way. It does not replace compiling, and the draft stays in the
  scratchpad until it does compile.
- 2026-07-19 — DESK-CHECK of the `mulJetImage` index arithmetic in the multiplicative-gauge draft.
  Slot convention: slot 0 holds `z`, slot `k+1` holds the jet of ORDER `k`. So a slot `s` carries
  order `s.1 - 1`.
  Leibniz for order `k` reads `(a f)^(k) = sum_(i=0)^(k) binom(k,i) a^(i) f^(k-i)`, and `f^(k-i)`
  lives in slot `(k-i)+1`. With `s.1 = k+1` that slot is `s.1 - i`, which is what the draft writes.
  The summation range `range (s.1 - 1 + 1)` is `range (k+1)`, i.e. `i` from `0` to `k`. The binomial
  `binom(s.1 - 1, i)` is `binom(k,i)`. All three line up.
  TWO LIKELY SMALL FAILURES flagged in advance rather than discovered at compile time:
  (a) the `Fin` bound `⟨s.1 - i, by omega⟩` needs `s.1 < n + 2` in scope for `omega`; that fact is
      `s.isLt` and may have to be supplied explicitly rather than found automatically, since `s` is
      only bound as a `Fin` argument. Natural subtraction makes the inequality `s.1 - i <= s.1` true
      without side conditions, so the only gap is having `s.isLt` available.
  (b) the coefficient is written `(Nat.choose ... : C) • ...`; on `MvPolynomial ... C` this smul is
      defeq to multiplication by `C (...)`, but the simp set may not see through it. Writing it as
      `MvPolynomial.C (...) * ...` is the safer form if the `•` version resists rewriting.
  Neither is mathematical content; both are the kind of detail that costs a compile cycle when met
  cold. Recording them now means the first verification attempt can include the fixes rather than
  discover them.
- 2026-07-19 — read the card's "Attacks and boundaries" section, previously unopened. It confirms the
  formalisation targets and, more usefully, marks where the card deliberately STOPS — which is
  information an auditor needs and which I could not have inferred from the theorem statements.
  Confirmations relevant to what was built this session:
    item 1 — the index is the EXACT global negative-square index, with `k = 0` exactly Herglotz
      positivity. That matches the two-sided formulation chosen for the chamber equality draft:
      an exact index is precisely "no larger subspace, and one of that size exists".
    item 3 — infinite support is what supplies complete jet controllability, and a FINITE support
      would give a merely rational transform. This is the hypothesis `nu.support.Infinite` carried
      throughout the chamber work, and the card explains why it cannot be dropped rather than
      weakened.
    item 4 — (H0) covers finite OR infinite total mass and assumes no atomicity, which is exactly
      the generality the atom law was proved in (finite case, then the dominant for the infinite
      case).
    item 5 — the general measure carrier gets finite-atomic ORTHANT chambers graded by exact index,
      while the DISCRETE case has a stronger fixed-support direct-limit cube. The chamber work this
      session is the former; the latter is a separate, stronger statement and is NOT what was
      formalised.
  DELIBERATE BOUNDARIES, recorded so no later reader mistakes them for gaps:
    item 9 — a zeta application must retain the Euler realization; the theorem does NOT modify the
      zeta carrier, and rational zero replacement would change the distinguished carrier.
    item 10 — the exact zeta-generated Nyman-Beurling closure is explicitly OUTSIDE the theorem's
      scope.
  So the card is not claiming a zeta consequence, and the absence of one is by design. Reading this
  section earlier would not have changed any proof, but it would have kept me from wondering whether
  the RHTower side was meant to connect.

### (M3) discharged: the chamber law at a general chamber

`GaloisForLFunctions.HTGeometry.ChamberLawEquality`
- `chamberLaw_negIndex_eq_grading` — the two-sided abstract statement: for a Hermitian form that a
  rank-one correction per negative coefficient makes PSD, and that is negative definite on the
  negative coordinate subspace, no negative definite subspace exceeds `negCount c` and the negative
  coordinate subspace attains it.
- `chamberLaw_negIndex_eq_hammingDist` — the same read as the Hamming distance from the positive
  chamber, which is the card's phrasing of the grading.

`GaloisForLFunctions.HTGeometry.GeneralChamberLaw`
- `eventually_negDef_on_negSupported_of_entrywise` — entrywise convergence to the coefficient
  diagonal gives eventual negative definiteness on the negative coordinates, needing the margin only
  at the negative coefficients.
- `eventually_negDef_totalGram_negSupported` — the same for the scaled Pick Gram of a measure, at all
  small heights.
- `chamberLaw_totalGram_general` — the chamber law at an *arbitrary* chamber, at measure level.

This closes the gap between `ChamberLawExtremes` (which pinned only the all-positive and all-negative
chambers) and the general mixed chamber. Both new modules build; all declarations depend only on
`propext`, `Classical.choice`, `Quot.sound`.

Two proof steps that were inline are now separate reusable lemmas, so the general chamber shares one
proof with the extremes rather than duplicating it:
`eventually_quadForm_sub_diagonal_le` (in `EventualNegDefFromEntrywise`, the entrywise-to-quadratic
perturbation bound — it does not use the sign of the coefficients) and
`entrywise_totalGram_sub_diagonal` (in `TotalGramNegativeDefinite`, the limits-to-threshold
repackaging). `eventually_negDef_totalGram` was rewritten on top of them and still depends on only
the three standard axioms.

Correction to an earlier entry: the umbrella build recorded as "exit 0" had in fact failed. lake
printed `error: build failed` and the shell's exit status came from a pipe. The three failing modules
are `DerivationTerminalLinearJacobian`, `GaussianTorsionLanguageTailLock`, and
`PrimeValuationCoordinateFusionCompletion` — none belong to this card and none import anything from
it; their import chains are disjoint.

Correction to a plan: the negative block of `totalGram` is *not* the Gram of the negative subfamily.
`atomicGram a c y l m` sums over all atoms, so a positive atom contributes `y² c_j |S_j|² ≥ 0` to the
form even on vectors supported in the negative coordinates. Restricting the index set is therefore
invalid; the route that works is entrywise convergence plus the subspace margin, as above.

Next: the PSD witness in `chamberLaw_totalGram_general` is carried as an explicit hypothesis
(`hPSD`), matching how `chamberLaw_all_positive` states it. Supplying it from the Pick kernel's own
structure at measure level is the remaining connector on the chamber half.

### The chamber law now carries its own PSD witness

The previous entry left `hPSD` as an explicit hypothesis. It is now discharged from the Pick
kernel's own structure, so no matrix structure is assumed.

`GaloisForLFunctions.HTGeometry.ComplexIntegralGram` — new infrastructure. The corpus had only the
*real* `integralFeatureGram`; the measure Gram is a complex conjugate Gram, so the complex analogue
was missing.
- `complexFeatureGram`, `complexFeatureCombination`, `complexFeatureCombination_mul_conj`
- `complexFeatureGram_isHermitian`, `complexFeatureGram_quadratic` — the quadratic form is the
  integral of the squared modulus of the feature combination.
- `complexFeatureGram_posSemidef`
- `measureGram_posSemidef` — the measure part of the scaled Pick kernel, as an instance.

`GaloisForLFunctions.HTGeometry.AtomicGramPosSemidef`
- `atomFeature`, `atomicGram_eq_sum_atomFeature` — the atomic Gram is the coefficient-weighted sum
  of the atom rank-one terms, `atomicGram a c y l m = Σ_j c_j · u_j(l) · conj(u_j(m))` with
  `u_j(l) = y/(a_j − w_l)`.
- `negIndex`, `c_negIndex_neg`, `negAtomWitness`, `negAtomWitness_mul_star` — the correction
  attached to the `i`-th negative coefficient, of modulus `|c_j|`.
- `atomicGram_add_negAtomWitness` — correcting exactly the negative coefficients replaces every
  coefficient by its positive part.
- `posPartAtomFactor`, `posPartAtomicGram_posSemidef` — the positive-part Gram is `B Bᴴ`.
- `totalGram_add_negAtomWitness_posSemidef` — the two halves combine.

`GaloisForLFunctions.HTGeometry.ChamberLawPickWitness`
- `chamberLaw_totalGram_pick` — the chamber law at an arbitrary chamber whose only inputs are node
  injectivity, the margin at the negative coefficients, and integrability of the scaled Cauchy
  kernels. The rank-one correction is no longer assumed; it is the one built from the negative
  atoms, and its count is the chamber grading by construction.

All modules build; every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

A note on why the correction count comes out exactly right: the weight `max (c j) 0` lets the
corrected matrix be a single full-index weighted Gram, since `c_j + (if c_j < 0 then −c_j else 0)`
is `max (c j) 0` pointwise. That avoids splitting the index set on the positive-semidefinite side,
where the split would have been the whole difficulty.

### The chamber law now rests on the Herglotz dominant alone

`GaloisForLFunctions.HTGeometry.ScaledCauchyProductIntegrable`
- `continuous_scaledCauchy` — at a nonzero height the node is off the real line, so the kernel is
  continuous and no measurability hypothesis is needed.
- `integrable_scaledCauchy_product` — the modulus of a product of two scaled Cauchy kernels is
  bounded by the average of the two atom kernels (arithmetic-geometric mean), so the product is
  integrable as soon as both atom kernels are. Reuses `integrable_normSq_scaled_cauchy_iff` and
  `sub_upperNode_ne_zero`, both already in the tree.

`GaloisForLFunctions.HTGeometry.ChamberLawPickWitness`
- `eventually_totalGram_add_negAtomWitness_posSemidef` — the dominant makes every atom kernel
  integrable at small heights, hence every kernel product integrable, hence the measure Gram
  positive semidefinite.
- `chamberLaw_totalGram_pick` — restated with no `hprod` and no `hPSD`. Its hypotheses are now
  exactly those of `chamberLaw_all_negative`: injective nodes, a margin, the dominant, and no mass
  at any node — with `hc` weakened from `∀ j, c j ≤ -δ` to `∀ j, c j < 0 → c j ≤ -δ`. So the
  general chamber is reached on the same inputs that previously bought only the all-negative
  extreme.

`hPSD` in `chamberLaw_totalGram_general` was weakened from `∀ y` to `∀ᶠ y in 𝓝[≠] 0`, matching its
eventual conclusion; that is what makes `y ≠ 0` available to discharge continuity.

All modules build; every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

Scope of what (M3) now means here. The chain is stated throughout for `totalGram`, which the tree
defines directly as the scaled Pick Gram of a chamber member. There is no formal link anywhere in
the corpus between `totalGram` and `regularizedHerglotzTransform` — grep confirms `totalGram` is
referenced only within this chamber chain. So (M3) is discharged at the level of the scaled Pick
Gram, not yet transported to the Pick kernel of the actual transform `m_{u,c}`. That gap is not new
work introduced here: `ChamberLawExtremes` already had it.

Next: close that gap by proving `totalGram ν a c y l m = y² · (m(w_l) − conj(m(w_m)))/(w_l −
conj(w_m))` for the atoms-plus-measure Herglotz function, with nodes `w_l = a_l + i y`. The finite
real-spectrum case of exactly this identity is already proved as
`GaloisForLFunctions.pick_gram_eq_kernel` in `CarrierPickKernel`, which is the model to follow.

### (M3) transported to the actual transform

The gap flagged in the previous entry is closed. The chamber law is no longer a statement about an
ad hoc matrix; it is a statement about the Pick kernel of a Herglotz function.

`GaloisForLFunctions.HTGeometry.PickKernelChamberIdentity`
- `integrable_conj` — conjugation preserves integrability (absent from mathlib under any name tried:
  `Integrable.conj`, `Integrable.star`, and `exact?` all fail; proved via `Integrable.mono'` against
  `hf.norm`).
- `regularizedHerglotzKernel_sub_conj` — **the identity the regularization exists for.** Since
  `t / (1 + t ^ 2)` is real it cancels in `m z - conj (m w)`, leaving
  `regK t z - conj (regK t w) = (z - conj w) · (t - z)⁻¹ (t - conj w)⁻¹`.
- `atomPart`, `chamberHerglotz` — the chamber member's regularized transform.
- `atomPart_sub_conj`, `measureGram_eq_scaled_integral`.
- `totalGram_mul_sub_eq_pick` — `totalGram · (w_l − conj w_m) = y² · (m(w_l) − conj m(w_m))`.

`GaloisForLFunctions.HTGeometry.ChamberLawPickKernel`
- `sub_conj_upperNode_ne_zero` — the Pick denominator has imaginary part `2y`.
- `chamberPickKernel`, `totalGram_eq_smul_chamberPickKernel` — the scaled Gram is the Pick kernel
  scaled by `y²`.
- `re_quadForm_smul_neg_iff` — a positive real scaling moves no negative directions.
- `chamberLaw_chamberPickKernel` — **(M3) as the card states it**: at all small heights the negative
  index of the Pick kernel of the chamber member's regularized Herglotz transform is exactly the
  Hamming distance of its coefficient sign pattern from the positive chamber.

All build; every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

Why the regularization is load-bearing, recorded because the wrong route is tempting. One cannot
write `∫ dν/((t−z)(t−conj w)) = (∫1/(t−z) − ∫1/(t−conj w))/(z−conj w)`: under (H0) neither Cauchy
integral need converge for an infinite measure. This is the same error as the retracted
constant-shift bridge earlier in this card. The proof never splits an integral — it uses
`integral_sub` on the *combined* integrand, whose decay is `t^(-2)`, and the regularizing term
cancels before any integration is done.

The `(H0)` input enters as `hreg`, integrability of the regularized kernel at the nodes — i.e. the
condition for the transform to be defined at all — rather than as an assumption about the matrix.

### HT half: the polynomial gauge, and its localisation

`MulPolynomialInvariance` already existed in the tree (untracked, built on this card's
`bindPointMap` / `exists_triangular_solution` / `eval_aeval_X` infrastructure). Verified here rather
than rewritten: it builds, and `hypertranscendental_polynomialGauge`,
`hypertranscendental_mul_polynomial`, `differentiallyAlgebraic_of_mul_polynomial` all depend only on
the three standard axioms. It subsumes `hypertranscendental_gauge_iff_mul`, which hard-codes the
multiplier `1 + z²`, by allowing any nonzero polynomial multiplier.

The obstruction that made it unusable, and why it had no callers anywhere in the tree: it requires
`ContDiff ℂ ⊤ C` **globally**. The object it is meant for is a Cauchy transform, which is analytic
only off the real axis (`analyticOnNhd_cauchyTransform`). So the global gauge cannot reach the
regularized Herglotz transform at all.

`GaloisForLFunctions.HTGeometry.LocalPolynomialGauge` — the gauge redone on a domain.
- `iteratedDeriv_mul_polynomial_at`, `iteratedDeriv_add_polynomial_at` — the two jet identities at a
  single point of smoothness, from mathlib's `iteratedDeriv_fun_mul` / `iteratedDeriv_add`, both of
  which already carry `ContDiffAt` hypotheses.
- `differentiallyAlgebraicOn_of_mul_polynomial`, `differentiallyAlgebraicOn_add_polynomial`.
- `not_differentiallyAlgebraicOn_polynomialGauge` — the affine gauge on an open `U`.

Nothing algebraic changed: the jet substitution, its point map, and the nonvanishing argument are
the same declarations, since nonvanishing is a statement about polynomials alone. Only the jet
identities moved from global smoothness to smoothness at the point, which is all they ever used.

One subtlety the localisation forces. A gauge identity holding only *on* `U` does not by itself
transfer to jets, because `iteratedDeriv m z` depends on `m` near `z`, not on its values on `U`.
Hence `U` must be open, and the transfer goes through `Filter.EventuallyEq.iteratedDeriv_eq`.

Next: instantiate at `U = {z | z.im ≠ 0}` (or either half-plane) with `a = 1 + X²` and
`b = C M * X`, taking smoothness of `cauchyTransform` from `analyticOnNhd_cauchyTransform`, to get
that the regularized Herglotz transform has no differential relation off the real axis whenever its
Cauchy transform has none. That is the HT half's reduction (M1)/(M2) in citable form.

### The HT reduction, instantiated at the actual transform

`GaloisForLFunctions.HTGeometry.RegularizedTransformGauge`
- `offRealAxis`, `isOpen_offRealAxis`, `one_add_X_sq_ne_zero`
- `contDiffAt_cauchyTransform` — the Cauchy transform of a finite measure is smooth off the real
  axis, from `analyticOnNhd_cauchyTransform` via `AnalyticAt.contDiffAt`.
- `not_differentiallyAlgebraicOn_regularizedHerglotzTransform` — **the HT half's reduction**: off
  the real axis, if the Cauchy transform of the Nevanlinna-weighted measure satisfies no algebraic
  differential equation, neither does the regularized Herglotz transform
  `∫ regularizedHerglotzKernel t z · exp (u t) dμ`.

This is the local gauge of the previous entry instantiated with `a = 1 + X²` and
`b = C M · X`, where `M` is the weighted mass, using `regularizedHerglotzTransform_eq` for the gauge
identity. Unconditional; depends only on `propext`, `Classical.choice`, `Quot.sound`.

The question for the transform is therefore now entirely a question about a *Cauchy transform of a
finite measure*, with the regularization and the mass term both discharged. That is the form the
existing genericity layer (`HerglotzGenericity`, `NevanlinnaNoncriticalProjectiveCompactPatch`) is
stated in.

Tree hygiene note: the umbrella build replays warnings from `ArithmeticFunctionDomain`,
`FinitePrimeCoefficientField`, `FiniteRangePrimeDirichletModuli`, `DifferentialPivotRelationIdeal`
and an info suggestion from `DigammaGammaFactorialBlowUp`. These are pre-existing and belong to
other cards; none of this card's modules emit any diagnostic. They matter only because the full
lint gate fails on warnings.

### Strengthening the carrier capstone to the half-plane form

A mismatch blocked composing the HT reduction with the corpus genericity layer, and it was not a
naming difference. The gauge consumes `¬ DifferentiallyAlgebraicOn C U`; the carrier capstone proved
global `Hypertranscendental C`. Since `DA → DA_On`, negating the *local* form is the **stronger**
statement, so the capstone was too weak to feed the gauge.

Inspection of the proof settled it. In
`AnalyticNevanlinnaCarrierRelationFree.lean`, the global relation hypothesis `hPzero` is used
exactly once, and inside a scope where `hupper : ∀ x, 0 < (combinedProjectiveRowShiftPacket packet
shift x).im` is available — the relation is only ever evaluated at packet nodes, which lie off the
real axis. The half-plane statement is therefore what the pattern argument actually gives; global
hypertranscendence was a weakening applied at the end.

Changed accordingly:
- `not_differentiallyAlgebraicOn_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree` —
  the strengthened form, concluding that no nonzero `P` annihilates the jets at every `z` with
  `0 < z.im`. The only proof change is `hPzero z` becoming `hPzero z ⟨from hupper (r, 0)⟩`, using
  `combinedProjectiveRowShiftPacket packet shift x = packet.1 x.1 + shift.1 x.2` at the zero shift,
  with `CarrierPatternShift p = Fin p.shiftCount = Fin 1` inhabited by `0`.
- `hypertranscendental_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree` — retained
  verbatim as a one-line corollary, so every downstream user is unaffected.
  `positiveSingularContinuousCarrier_hypertranscendental_dense_residual` still builds unchanged.

The conclusion is stated inline as an explicit `¬ ∃ n P, …` rather than via
`DifferentiallyAlgebraicOn`, because that predicate lives in `DigammaGammaLocalHypertranscendence`
and importing it into this core module would be a heavy and unnecessary dependency. (`autoImplicit`
silently turned the unknown identifier into an implicit binder first — the usual trap.)

All three declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

What still separates this from a composed HT theorem for the card:
1. Domain bookkeeping — `RegularizedTransformGauge` is stated on `offRealAxis`; restating it on
   `{z | 0 < z.im}` is mechanical, and the restriction `upper ⊆ offRealAxis` gives the implication
   in the needed direction anyway.
2. The measures differ and this is *not* mechanical: the capstone is about
   `weightedBoundaryCarrier F.base.toBoundaryFamily eta density`, the gauge about
   `nevanlinnaWeightedMeasure μ u`. Identifying the two, or restating one in terms of the other, is
   the real remaining connector.

### The gauge decoupled from the measure, and the last obligation

The gauge was tied to `nevanlinnaWeightedMeasure μ u` only because it consumed
`regularizedHerglotzTransform_eq`. Decoupled here, so it applies to any carrier:

`GaloisForLFunctions.HTGeometry.RegularizedTransformGauge` (extended)
- `differentiallyAlgebraicOn_mono` — a relation on a set restricts to any subset.
- `upperHalfPlane_subset_offRealAxis`.
- `not_differentiallyAlgebraicOn_herglotzPresentation` — for **any** finite measure `ν` and any mass
  constant `M`, the presentation `z * M + (1 + z ^ 2) * cauchyTransform ν z` satisfies no algebraic
  differential equation on an open set off the real axis whenever `cauchyTransform ν` satisfies none
  there. No reference to how the measure was produced.
- `not_differentiallyAlgebraicOn_herglotzPresentation_upperHalfPlane` — the same on
  `{z | 0 < z.im}`, which is exactly the domain the strengthened packet capstone now delivers.

Unconditional; only `propext`, `Classical.choice`, `Quot.sound`.

`upperHalfPlane` and `isOpen_upperHalfPlane` already existed in `PrimeLogHerglotz` under the same
namespace and are reused, not redeclared.

So the two halves now meet on the same domain and the same shape of hypothesis. The single
remaining obligation to compose them into one theorem is an instance:
`IsFiniteMeasure (weightedBoundaryCarrier F.base.toBoundaryFamily eta density)`.
The route is `boundaryBarycenter_isProbabilityMeasure` in `LabeledBoundarySimplex`, whose
hypotheses are `[IsProbabilityMeasure η]`, `Measurable ν`, and `∀ t, IsProbabilityMeasure (ν t)`;
`AtomlessProjectiveFrameFiber` already discharges the last two as `F.measurable_leaf` and
`fun t => (F.leaf t).prop`. What must be supplied is that `linftyDensityMeasure eta density` is a
probability measure for the capstone's density `linftyOne mu + w.1.1`, i.e. the normalisation
carried by the positive chart.

### The two halves composed

`GaloisForLFunctions.HTGeometry.CarrierHerglotzPresentationFree`
- `not_differentiallyAlgebraicOn_cauchyTransform_weightedBoundaryCarrier` — pattern
  relation-freeness restated for `cauchyTransform` in the form the gauge consumes. The restatement
  is definitional: `cauchyTransform ν z` unfolds to `∫ x, ((x : ℂ) - z)⁻¹ ∂ν`, and membership in
  `upperHalfPlane` to `0 < z.im`, so the two forms are the same proposition.
- `not_differentiallyAlgebraicOn_herglotzPresentation_weightedBoundaryCarrier` — **the composed
  statement**: for any mass constant, the normalized presentation `z * M + (1 + z ^ 2) * C` of a
  carrier avoiding every canonical finite pattern satisfies no algebraic differential equation on
  the upper half-plane.

Unconditional; only `propext`, `Classical.choice`, `Quot.sound`. Compiled first try.

The finiteness obligation flagged in the previous entry is not an obstruction: the singular-continuous
capstone already carries `IsProbabilityMeasure carrier` in its own conclusion, alongside
`LinftyStrictlyPositive`, `∫ density = 1`, `NoAtoms`, mutual singularity and the Hamburger moments.
So it is available wherever the capstone is applied, and the composed theorem takes it as an
instance argument.

This is the HT half of the card in citable form. The remaining step is packaging rather than
mathematics: the dense-residual capstone
`positiveSingularContinuousCarrier_hypertranscendental_dense_residual` still states its carrier set
with the global `Hypertranscendental`, because it was written against the pre-strengthening
corollary. Restating that set with the half-plane predicate and rerouting its one call site to
`not_differentiallyAlgebraicOn_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree`
would carry the dense/residual packaging over to the composed statement verbatim.

### Dense/residual packaging carried to the half-plane

`countablePatterns_actualNevanlinna_notDifferentiallyAlgebraicOn_dense_residual` (in
`CarrierHerglotzPresentationFree`) — the dense residual family of pattern-free carriers, recorded
with the half-plane predicate. Same hypotheses as
`allFinitePatterns_positiveActualCarrier_relationFree_dense_residual`, whose dense/residual
conclusion it reuses directly; the only new content is the subset map through the strengthened
packet lemma. Unconditional.

This was written as a new theorem rather than by editing
`positiveSingularContinuousCarrier_hypertranscendental_dense_residual`, because the dense/residual
property belongs to the *pattern-free* set and both predicates are supersets of it — so no existing
statement had to change, and the global capstone keeps working untouched.

Net state of the HT half, all unconditional:
- per carrier — `not_differentiallyAlgebraicOn_herglotzPresentation_weightedBoundaryCarrier`
- dense residual family — `countablePatterns_actualNevanlinna_notDifferentiallyAlgebraicOn_dense_residual`
- the gauge for an arbitrary finite measure — `not_differentiallyAlgebraicOn_herglotzPresentation`
- the regularized transform of a Nevanlinna-weighted measure —
  `not_differentiallyAlgebraicOn_regularizedHerglotzTransform`

A note on a Lean detail worth remembering: writing the subset as a standalone `have hsubset : {w | …}
⊆ {w | …}` fails, because the set-builder binder has no type annotation and `w.1.1` cannot be
resolved. Leaving both subset obligations as goals of `Dense.mono` / `Filter.mem_of_superset` lets
the expected type determine `w`, and the same term closes both.

### Correction: what "the HT half is complete" does and does not mean

The previous entry said the HT half was complete end-to-end. That overstates it, and reading the
card's headline claim against `BoundaryCarrierTranslationFreeness` shows where the line actually is.

The card's HT claim is about the **full complex translation family**: no nonzero differential
polynomial over `C(z)` in any finite tuple of *distinct translates* vanishes identically. That
predicate is already formalized, as `MaximalTranslationDifferentialFree` — "every
polynomial-coefficient relation among every finite family of distinct complex translates and finite
jet depths has zero coefficient vector" — and it is exactly the shape of the `hfree` hypothesis this
card's chain carries. Dense/residual families satisfying it are already proved
(`allFinitePatterns_positiveActualCarrier_relationFree_dense_residual`,
`maximalTranslationDifferentialFree_of_fullRankWitness`).

So the translation-family content was never the missing piece, and the pattern machinery — with
`InjectiveShiftConfiguration` and `CarrierPatternShift` — is what encodes the shifts.

What is genuinely established by the work logged above:
- that freeness holds for the **Cauchy transform of the carrier** (corpus, pre-existing), and
- a **single-function** gauge from that Cauchy transform to the regularized transform `m_u`
  (`not_differentiallyAlgebraicOn_herglotzPresentation…`, this card).

What remains is the **multi-shift gauge**: transporting `MaximalTranslationDifferentialFree` from
the carrier's Cauchy family to the translated family of `m_u`. Mathematically this should go
through, since each translate satisfies `m_u(z + h) = (z + h) · M + (1 + (z + h)²) · C(z + h)`, a
polynomial gauge with coefficients polynomial in `z`, so a joint relation among the `m_u`-translates
substitutes into a joint relation among the `C`-translates. But it is a pattern-level statement, not
an instance of the single-function gauge, and it is not formalized.

Stated precisely, the open item is: from `MaximalTranslationDifferentialFree` for the carrier,
derive the corresponding pattern-relation-freeness for the family `z ↦ z · M + (1 + z²) · C z` and
its translates. That is the last step between the corpus's freeness theorems and the card's claim as
written about `m_u`.

### The multi-shift gauge

`GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge` — the componentwise version of the
multiplicative gauge, which is the piece the translation-family claim needs.

- `FamilyJetIndex`, `familyJetVec`, `FamilyDifferentiallyAlgebraicOn` — jet coordinates of a finite
  family: one spectral variable plus one jet block per component.
- `familyJetVariable`, `familyMulJetImage` — the blockwise Leibniz substitution.
- `bindPointMap_familyMulJetImage` — on actual jets it returns the jets of the multiplied family.
- `exists_familyMulJetImage_preimage` — the point map covers every packet where no multiplier
  vanishes. The substitution is *block diagonal*, so each block is the same triangular system as the
  single-function case and `mulPolynomialJetLower` / `mulPolynomialJetLower_congr` are reused per
  block, with `choose` supplying one solution per component.
- `familyDifferentiallyAlgebraicOn_of_mul_polynomial` — **the componentwise gauge**: a differential
  relation among a family each multiplied by its own nonzero polynomial pulls back to a relation
  among the original family. Nonvanishing uses the product `∏ i, aeval (X (inl ())) (a i)`, nonzero
  because `MvPolynomial` over `ℂ` is a domain.

Stated for an arbitrary family rather than for translates; the translated family is the instance,
with `a i = 1 + (X + h i) ^ 2`. Unconditional; only `propext`, `Classical.choice`, `Quot.sound`.

What this does and does not close. The gauge now exists at multi-shift level, so the obstruction
named in the previous entry — that the gauge was single-function while the card's claim is about the
translation family — is removed *in the jet formalism*. What is still not bridged is the encoding
gap: the corpus states freeness in the packet/pattern formalism
(`probabilityCarrierExpandedPatternRelationHolds`, `MaximalTranslationDifferentialFree`), whereas
this gauge is stated for `FamilyDifferentiallyAlgebraicOn` in the `MvPolynomial` jet formalism. The
single-shift bridge between the two already exists inside the proof of
`hypertranscendental_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree`
(`reshapeJet`, `renameToSingleShiftJets`, `finitePatternOfPolynomial` at `shiftCode : Fin 1 → Unit`).
`finitePatternOfPolynomial` is already general in the number of shifts `m`, so the multi-shift bridge
is the same construction without the `m = 1` specialisation — that is the remaining connector.

### The componentwise affine gauge completed

The multiplicative family gauge only handled multipliers, so the affine case needed the additive
half. Added to `FamilyPolynomialGauge`:

- `familyShiftPoly`, `familyDifferentiallyAlgebraicOn_of_add_polynomial` — adding a polynomial
  componentwise preserves relation-freeness. This reuses `axisShiftSubst` at the distinguished
  coordinate `Sum.inl ()` together with `axisShiftSubst_ne_zero`, so nonvanishing is free: the
  substitution is invertible, unlike the multiplicative one. The jet identity is
  `iteratedDeriv_add_polynomial_at`, already proved for the single-function local gauge.
- `familyDifferentiallyAlgebraicOn_of_affine` — **the componentwise affine gauge**: for a family
  `g`, nonzero multipliers `a`, and shifts `b`, a relation among
  `fun i w => eval w (b i) + eval w (a i) * g i w` pulls back to a relation among `g`.

Unconditional; only `propext`, `Classical.choice`, `Quot.sound`.

This is the exact shape the translated transform needs, since
`m_u (z + h i) = (z + h i) · M + (1 + (z + h i)²) · C (z + h i)`
is `eval z (b i) + eval z (a i) * C (z + h i)` with `a i = 1 + (X + C (h i))²` and
`b i = (X + C (h i)) * C M`, and `a i ≠ 0`.

So the gauge side of the translation-family claim is now complete: multiplicative, additive, and
affine, at family level, for an arbitrary family with translates as the instance.

The remaining connector is unchanged and is purely one of encoding: bridging the corpus's
packet/pattern formalism (`MaximalTranslationDifferentialFree`,
`probabilityCarrierExpandedPatternRelationHolds`) to `FamilyDifferentiallyAlgebraicOn`. The
single-shift bridge exists inside
`hypertranscendental_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree` via
`reshapeJet`, `renameToSingleShiftJets` and `finitePatternOfPolynomial`; the latter is already
general in the shift count, and `Fin m × Fin (n+1) ≃ Σ i : Fin m, Fin (orders i)` at constant
`orders` is the index identification the multi-shift version needs.

### Encoding bridge, first half: reshaping family jets

`GaloisForLFunctions.HTGeometry.FamilyJetReshape` — the multi-component analogue of `reshapeJet`,
which handles one distinguished spectral variable in `Fin (n + 2)`. Here the spectral variable is
the `Sum.inl` coordinate and the jet variables are indexed by component and order.

- `familyReshapeJet`, `familyReshapeJetInv`, `familyReshapeJetInv_comp_familyReshapeJet`,
  `familyReshapeJet_injective` — absorbing the spectral variable into `ℂ[X]` coefficients is an
  injective ring map, by exhibiting the inverse.
- `eval_specialize_familyReshapeJet` — specializing the coefficients at `z` and evaluating at the
  jet values is evaluating the original at `Sum.elim (fun _ => z) v`, i.e. at the family jet vector.
  This is the compatibility the pattern argument runs on.
- `familySigmaEquiv`, `renameToFamilyShiftJets`, `renameToFamilyShiftJets_injective` — the identity
  `Σ _ : Fin m, Fin (n+1) ≃ Fin m × Fin (n+1)` carrying jet coordinates into the pattern's dependent
  shift/order form, at constant `orders`.

Unconditional; only `propext`, `Classical.choice`, `Quot.sound`. `specializePolynomialCoefficients`
needed no generalisation — it was already stated for an arbitrary index type.

What remains of the bridge is the second half: building the finite pattern from a reshaped relation
(`finitePatternOfPolynomial` at `shiftCode` the tuple of distinct translates, `orders ≡ n+1`),
showing `probabilityCarrierExpandedPatternRelationHolds` for it, and running
`polynomial_eq_zero_of_patternCoefficientVector_eq_zero` back through the two injectivity lemmas
above. That is the multi-shift analogue of the ~90-line argument inside
`hypertranscendental_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree`, and it is the
only step still separating the corpus's freeness theorems from the card's translation-family claim
about `m_u`.

### The gauge instantiated at the actual translates

`GaloisForLFunctions.HTGeometry.TranslatedFamilyGauge`
- `translatedNevanlinnaMultiplier c = 1 + (X + C c)²`, `translatedMassShift c M = (X + C c) * C M`,
  with their evaluation lemmas.
- `translatedNevanlinnaMultiplier_ne_zero` — nonzero, seen by evaluating at `-c`, where it is `1`.
- `contDiffAt_cauchyTransform_translate` — the translated Cauchy transform is smooth wherever its
  node is off the real axis.
- `familyDifferentiallyAlgebraicOn_translatedCauchy_of_presentation` — **a differential relation
  among the translates of the Herglotz presentation pulls back to one among the translates of the
  Cauchy transform.**

Unconditional; only `propext`, `Classical.choice`, `Quot.sound`.

This closes the analytic side of the translation-family claim: the gauge is no longer abstract, it
applies to `m_u (z + h i)` for an arbitrary finite tuple of shifts, on any set where every translated
node is off the real axis.

Remaining, unchanged: the pattern-encoding step. `FamilyJetReshape` supplies the reshape and rename
with their injectivity, and this module supplies the gauge; what is still missing is building the
finite pattern from a reshaped relation and deriving
`probabilityCarrierExpandedPatternRelationHolds`, i.e. the multi-shift analogue of the argument
inside `hypertranscendental_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree`. In
that argument the shift configuration is the zero one; for translates it is the tuple `h` itself,
which is exactly what `combinedProjectiveRowShiftPacket packet shift x = packet.1 x.1 + shift.1 x.2`
was built to express — so the machinery is already shaped for it.

### The translation family is capped at one translate by the shift palette `[VERIFIED]`

Attempting the pattern-encoding step surfaced a type-level constraint that changes the status of the
card's headline HT claim, and corrects an earlier entry of mine.

`FiniteDifferentialPattern Γ` carries `shiftCode : Fin shiftCount → Γ` together with
`shiftCode_injective`. Every carrier-freeness statement in the tree instantiates `Γ = Unit`
(`MaximalTranslationDifferentialFree`, `weightedBoundaryCarrierExpandedPatternRelationHolds`,
`probabilityCarrierExpandedPatternRelationHolds`, and the dense/residual theorems above them —
checked by enumeration, every occurrence of `FiniteDifferentialPattern` in `GaloisForLFunctions` is
at palette `Unit`). Injectivity into `Unit` forces `shiftCount ≤ 1`. Verified in Lean:

    example (p : FiniteDifferentialPattern Unit) : p.shiftCount ≤ 1 := by
      have h := p.shiftCode_injective
      have : Fintype.card (Fin p.shiftCount) ≤ Fintype.card Unit :=
        Fintype.card_le_of_injective _ h
      simpa using this

Since `CarrierPatternShift p = Fin p.shiftCount`, an `InjectiveShiftConfiguration
(CarrierPatternShift p)` supplies **at most one** complex shift. So a pattern relation can involve
the carrier's jets at nodes carrying at most one translate. Many packet rows give many *points*, not
many distinct *translates*.

Consequence for this card. `MaximalTranslationDifferentialFree` does not say what its docstring says
("every finite family of distinct complex translates"); as typed it is the single-translate
statement. The card's headline claim — no nonzero differential polynomial over `C(z)` in any finite
tuple of distinct translates — is therefore **not** established by the existing freeness theorems.

Correction to an earlier entry. I wrote that "the translation-family content was never the missing
piece" and that `MaximalTranslationDifferentialFree` "is exactly the card's HT claim". Both are
wrong, for this reason. What the corpus establishes, and what the gauge work above transports, is
the single-function statement.

What the fix would be: the structure is already generic in `Γ`, so the freeness layer would have to
be re-instantiated at a palette admitting `m` distinct codes (`Fin m`, or `ℂ` with the translates as
codes). That is a change to definitions with wide blast radius through the packet/pattern layer, not
a missing lemma. It is the honest open item for the HT half.

Unaffected by this: the chamber half (M3), and the gauge modules, which are stated for an arbitrary
finite family `Fin m → ℂ → ℂ` with no palette constraint and so already support `m` translates —
`familyDifferentiallyAlgebraicOn_of_affine` and
`familyDifferentiallyAlgebraicOn_translatedCauchy_of_presentation` are ready for the corrected
freeness input whenever it exists.

### How hard the palette fix actually is `[VERIFIED]`

The previous entry called the multi-translate fix "a change to definitions with wide blast radius".
That was an estimate, not a check. Checking it gives a much sharper picture.

**The rectangularization and evaluation core is already palette-generic.** Each of
`finitePatternOfPolynomial`, `polynomialPatternCoefficientVector`,
`polynomial_eq_zero_of_patternCoefficientVector_eq_zero`, `polynomialPatternCoefficientExpansion` is
stated `{Γ : Type*} {m : ℕ}`, and `expandedDifferentialEvaluationMatrix` is generic in its index
types. `PatternShape` and `PatternRow` are already `{Γ : Type*}`. None of these needs touching.

**Only the carrier-layer abbreviations pin `Unit`,** and they relax mechanically. Verified by
compiling palette-general copies of them verbatim — `CarrierPatternRow`, `CarrierPatternMonomial`,
`CarrierPatternShift`, `carrierPatternExponent`, `carrierPatternExponent_injective`, and crucially
the load-bearing dimension count `carrierPattern_rows_strictly_dominate_columns`, whose proof
(`simp` then `omega`) goes through unchanged at arbitrary `Γ`. Nothing in them uses a `Unit`-specific
fact; they only consume `p.jetExponent`, `p.orders` and cardinalities.

Also verified: patterns with two distinct shifts genuinely exist at a larger palette —

    example : ∃ p : FiniteDifferentialPattern (Fin 2), p.shiftCount = 2 :=
      ⟨finitePatternOfPolynomial (fun i : Fin 2 => i) Function.injective_id (fun _ => 1) 0, rfl⟩

so the cap really is the `Unit` instantiation and nothing deeper in the encoding.

**Where the real content sits.** What does *not* follow mechanically is the deep input: the
dense/residual freeness theorems (`allFinitePatterns_abstractCarrier_relationFree_dense_residual`
and the chain above it) must still hold when a pattern carries `m > 1` shifts, i.e. the full-rank /
controllability argument must survive the extra columns that distinct translates contribute. That is
genuine mathematics, not re-typing, and it is the actual open core of the HT half.

Nothing was installed for this entry: writing `Gen*` copies alongside the existing carrier
abbreviations would duplicate the corpus rather than improve it. The relaxation belongs in
`AnalyticNevanlinnaCarrierRelationFree` itself, as part of the same change that re-proves the
freeness layer at `m > 1`.

### Locating exactly what breaks at `m > 1` `[VERIFIED]`

Two entries ago I called the multi-translate fix "wide blast radius"; one entry ago I called the
remainder "genuine mathematics, not re-typing". Both were estimates. Checking further narrows it
again, and I want the record to reflect evidence rather than successive guesses.

Verified shift-generic (compiles verbatim at arbitrary palette `Γ`):
- the rectangularization/evaluation core, already stated `{Γ : Type*} {m : ℕ}`;
- the carrier-layer abbreviations and `carrierPatternExponent` with its injectivity;
- **both** dimension conditions — `carrierPattern_rows_strictly_dominate_columns` and
  `carrierPattern_shift_dimension_below_codimension`, the transversality codimension inequality,
  whose `finrank_pi_fintype` / `simp` / `omega` proof goes through unchanged;
- the control input `normalizedProjectiveCauchyJetLinftyContinuousControl`, which is generic in the
  node family `{ι : Type*} [Fintype ι]`.

Note also that `CarrierPatternRow` already budgets `Fintype.card (PatternShape p) +
coefficientDegree + p.shiftCount + 2` rows, with the docstring explaining that the extra
`shiftCount + 2` rows exist to make the transversality inequality automatic. The row budget was
designed for many shifts.

What actually depends on `Unit` being a subsingleton: exactly three sites, all in
`AnalyticNevanlinnaCarrierRelationFree.lean` and all inside the *bridge* from a differential
relation to a pattern, none in the freeness chain itself —
- line 78, inside `singleShiftJetEquiv` (the `Σ _ : Fin 1, Fin n ≃ Fin n` collapse). `FamilyJetReshape`'s
  `familySigmaEquiv` / `renameToFamilyShiftJets` already replace this for `m` shifts.
- line 609, `hshiftCode : Function.Injective shiftCode` for `shiftCode : Fin 1 → Unit`. At palette
  `Fin m` this is `Function.injective_id`.
- line 616, `shift0 := ⟨fun _ => 0, …⟩`, the *zero* shift configuration, injective only because the
  index is a subsingleton. At `m > 1` this must be the tuple of distinct translates itself, which is
  what `InjectiveShiftConfiguration` and `combinedProjectiveRowShiftPacket packet shift x =
  packet.1 x.1 + shift.1 x.2` exist to carry.

`BoundaryCarrierTranslationFreeness` and `NevanlinnaNoncriticalProjectiveCompactPatch` contain no
`Subsingleton` use at all.

Revised estimate, stated as such: the deep freeness content appears already shift-generic, and the
cap looks confined to the palette instantiation plus those three bridge sites. The step that remains
genuinely unverified is whether the dense/residual proofs, once re-typed at general `Γ`, still close
— they have no subsingleton dependence and their dimension and control inputs are shift-generic, so
there is reason to expect they do, but that has not been run.

### The multi-shift bridge, contradiction step

`GaloisForLFunctions.HTGeometry.FamilyPatternBridge`
- `familyShiftCode m = id : Fin m → Fin m`, `familyShiftCode_injective`, `familyOrders m n` — the
  `m`-translate pattern data, with the palette taken to be `Fin m` itself so that `m` distinct shift
  codes exist. This is the point where the `Unit` palette was the binding constraint.
- `familyPatternOfRelation` — the finite pattern attached to a family jet relation.
- `familyJetRelation_eq_zero_of_patternCoefficients_zero` — **if every pattern coefficient of the
  reshaped relation vanishes, the original family jet relation was zero.**

Unconditional; only `propext`, `Classical.choice`, `Quot.sound`.

This is the step that turns pattern-freeness back into a contradiction, and it composes the two
injectivity lemmas from `FamilyJetReshape` with the generic
`polynomial_eq_zero_of_patternCoefficientVector_eq_zero`. Notably it needs nothing about the palette
beyond injectivity of the shift codes, so — unlike the single-shift bridge, which uses
`Subsingleton.elim` at lines 78/609/616 — it does not rely on the shift index being a subsingleton.

Bridge status. Of the three `Unit`-dependent sites identified above, replacements now exist for two:
`singleShiftJetEquiv` is replaced by `familySigmaEquiv` / `renameToFamilyShiftJets`, and
`hshiftCode` by `familyShiftCode_injective`. The third, `shift0` — the zero shift configuration —
has no replacement yet because at `m > 1` it must be the tuple of distinct translates supplied by
the caller, not a constructed object.

What is still missing from the bridge is its *forward* step: showing that a family jet relation
actually makes `probabilityCarrierExpandedPatternRelationHolds` true for this pattern, which is the
`hrelation` calc chain of the single-shift argument (packet values, `carrierPatternExponent`,
`expandedDifferentialEvaluationMatrix`, `polynomialPatternCoefficientExpansion`). With the back step
now in place and both dimension conditions verified shift-generic, that calc chain is the remaining
piece of the encoding, alongside the still-unrun question of whether the dense/residual freeness
proofs close at `m > 1`.

### Identifying the two descriptions of a translated family

`GaloisForLFunctions.HTGeometry.IteratedDerivTranslate`
- `iteratedDeriv_comp_add_right` — `iteratedDeriv n (fun w => f (w + c)) z = iteratedDeriv n f (z + c)`.
  Absent from mathlib; `exact?` fails on it. Mathlib has only the single-derivative case
  `deriv_comp_add_const`, from which this follows by induction with the function generalised.
- `familyJetVec_translates` — the family jet vector of a translated family equals the jet vector of
  the single function read at the translated nodes.

Unconditional; only `propext`, `Classical.choice`, `Quot.sound`.

This is the identification the forward bridge step needs, and it is the conceptual join between the
two formalisms this card has been working across: the family gauge describes `m` separate functions
differentiated at one point, while the packet formalism describes one function differentiated at `m`
translated points. They are the same data, and now provably so.

With this, the forward step reduces to the calc chain proper — matching packet values against
`carrierPatternExponent` and `expandedDifferentialEvaluationMatrix`, then applying
`polynomialPatternCoefficientExpansion`. Every ingredient it consumes is now either generic or
supplied: the reshape and rename with injectivity (`FamilyJetReshape`), the contradiction step
(`FamilyPatternBridge`), the jet identification (here), and both dimension conditions verified
shift-generic.

### The multi-shift bridge closed on its algebraic side

`familyPatternExpansion_eq_eval` (added to `FamilyPatternBridge`) — **the forward step**: the pattern
coefficient expansion of a family jet relation, evaluated at jet values `x` and spectral value `z`,
is the original relation evaluated at the family jet vector `Sum.elim (fun _ => z) x`. It composes
`polynomialPatternCoefficientExpansion` with the rename compatibility (`MvPolynomial.eval₂_rename`)
and `eval_specialize_familyReshapeJet`.

With the back step already in place, the algebraic content of the multi-shift bridge is now complete
in both directions, at palette `Fin m` and with no subsingleton assumption anywhere:

- reshape and rename, with injectivity — `FamilyJetReshape`
- forward: expansion equals evaluation at the jet vector — `FamilyPatternBridge`
- back: vanishing pattern coefficients force the relation to vanish — `FamilyPatternBridge`
- the identification of the two descriptions of a translated family — `IteratedDerivTranslate`
- both dimension conditions, verified shift-generic
- the control input, generic in the node family

All unconditional; only `propext`, `Classical.choice`, `Quot.sound`.

What is left is no longer algebra. Two items, both outside the bridge:
1. The measure-side instantiation: matching `weightedBoundaryCarrierExpandedPacketValue` against the
   jet values `x`, which is where the carrier definitions (currently typed at palette `Unit`) enter,
   and which `familyJetVec_translates` is the identification for.
2. Whether the dense/residual freeness proofs close at `m > 1` — still unrun, and still the genuine
   open core of the HT half.

### The measure side identified, at any number of shifts

`GaloisForLFunctions.HTGeometry.PacketValueFamilyJet`
- `weightedBoundaryCarrierExpandedPacketValue_eq_familyJetVec` — **packet values are family jets of
  the translated Cauchy transforms.** The packet formalism evaluates one function at shifted nodes;
  the family gauge evaluates a jet vector of translated functions at one node. Same data.

Unconditional; only `propext`, `Classical.choice`, `Quot.sound`.

The key observation making this possible: `weightedBoundaryCarrierExpandedPacketValue` is already
generic in its shift index type, `{row ι : Type} [Fintype row] [Fintype ι]`, taking `orders : ι → ℕ`
and `shift : InjectiveShiftConfiguration ι`. It is *not* tied to `Unit` or to a pattern. The `m ≤ 1`
cap enters only when `CarrierPatternShift p` — which is `Fin p.shiftCount` for a `Unit`-palette
pattern — is supplied as that `ι`. Instantiated at `ι = Fin m` directly, the packet machinery
already describes `m` distinct translates, and the proof is `iteratedDeriv_comp_add_right` after
cancelling the `Fintype.equivFin` round trip.

So item 1 of the previous entry is discharged: the measure-side identification exists and is not
palette-restricted. Everything the multi-shift argument needs is now built except the deep input —
whether the dense/residual freeness proofs close at `m > 1`. That single question is the whole of
what separates this card's HT half from its stated claim.

### The abstract freeness layer is already multi-shift `[VERIFIED]`

The open core named in the previous entries — "do the dense/residual freeness proofs close at
`m > 1`" — is answered at the abstract level: they already do.

`NevanlinnaNoncriticalProjectiveCompactPatch.countablePatterns_global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual`
takes `(row κ ι : ℕ → Type)` with `[∀ n, Fintype (ι n)]` — the shift type is an arbitrary finite
type of **any** cardinality, one per pattern index. Its only dimension hypotheses are

    hrows : ∀ n, Fintype.card (κ n × Fin (degree n + 1)) + degree n < Fintype.card (row n)
    hdim  : ∀ n, Module.finrank ℝ (ι n → ℂ) <
              2 * (Fintype.card (row n) - Fintype.card (κ n × Fin (degree n + 1)) - degree n + 1)

which are exactly `carrierPattern_rows_strictly_dominate_columns` and
`carrierPattern_shift_dimension_below_codimension`, both verified above to generalise verbatim to an
arbitrary palette. Its conclusion is density and residuality of

    {w | ∀ n (shift : InjectiveShiftConfiguration (ι n)), actualNevanlinnaExpandedFullRankWitness … shift}

i.e. full-rank witnesses for *every* tuple of distinct complex shifts, as its docstring states.

So the `m ≤ 1` cap is not mathematical. It is entirely an artefact of the carrier layer
instantiating `ι` as `CarrierPatternShift p = Fin p.shiftCount` for a `FiniteDifferentialPattern
Unit`, where injectivity of `shiftCode : Fin shiftCount → Unit` forces `shiftCount ≤ 1`. The abstract
theorem underneath never had that restriction.

Status, stated carefully. What is verified: the abstract full-rank result is ι-generic and its
dimension hypotheses hold at arbitrary palette; the packet values, the control input, the
rectangularization core, and every bridge component built above are ι-generic or palette-general.
What is **not** done: performing the instantiation — re-typing the carrier layer at a palette with
`m` distinct codes and threading `hrows`/`hdim` through to recover multi-translate freeness. That is
plumbing across the carrier layer, not new mathematics, and it is the remaining work for the HT half.

This supersedes the earlier characterisation of that step as "genuine mathematics, not re-typing".

### The palette cap removed: freeness now holds at any number of translates `[DONE]`

The instantiation is performed. `AnalyticNevanlinnaCarrierRelationFree` no longer fixes the shift
palette at `Unit`.

Relaxed in place, so the `Unit` case remains available as a special case and no caller changes:
- `CarrierPatternRow`, `CarrierPatternMonomial`, `CarrierPatternShift`, `carrierPatternExponent`,
  `carrierPatternExponent_injective`, and both dimension theorems — now `{Γ : Type*}`.
- `allFinitePatterns_abstractCarrier_fullRankWitness_dense_residual`,
  `allFinitePatterns_positiveAbstractCarrier_fullRankWitness_dense_residual`,
  `allFinitePatterns_abstractCarrier_relationFree_dense_residual`,
  `allFinitePatterns_positiveActualCarrier_relationFree_dense_residual` — now `{Γ : Type}
  [Countable Γ]`, the countability being what the `⋂` over patterns needs.

Nothing else had to change: the abstract compact-patch theorem was already generic in the shift
type, the packet values were already generic in it, and both dimension hypotheses were verified to
generalise before the edit.

Verified after the change: the module builds, `BoundaryCarrierTranslationFreeness` builds, and both
relaxed freeness theorems still depend only on `propext`, `Classical.choice`, `Quot.sound`.

Verified consequence — at palette `Fin M` the patterns carry `M` distinct shifts:

    example (M n : ℕ) :
        (finitePatternOfPolynomial (fun i : Fin M => i) Function.injective_id
          (fun _ => n + 1) 0).shiftCount = M := rfl

and `CarrierPatternShift` of that pattern is `Fin M`, so an `InjectiveShiftConfiguration` on it
supplies `M` distinct complex translates. The `shiftCount ≤ 1` bound proved earlier applies only to
the `Unit` palette and no longer constrains the chain.

So the freeness layer now states and proves relation-freeness against patterns carrying arbitrarily
many distinct complex translates — the form the card's headline HT claim needs, and the form the
gauge and bridge modules above were built to consume.

Note on the tree state: `DirichletLSeriesUpperEnd.lean` is currently broken by another agent's
in-flight edit (first a type mismatch, then a `whnf` heartbeat timeout, and its olean is absent).
It contains no reference to any declaration changed here. It sits in the import closure of
`CarrierHerglotzPresentationFree`, so that module could not be rebuilt this turn; the relaxation
itself is verified independently.

### Fallout from the palette relaxation, found and fixed

Relaxing the freeness chain to `{Γ : Type} [Countable Γ]` made `Γ` un-inferable at one call site:
in `CarrierHerglotzPresentationFree`, the palette is determined only by the conclusion, which sits
under a `let`, so instance resolution got stuck ("typeclass instance problem is stuck"). Fixed by
pinning it explicitly, `(Γ := Unit)`, at that call.

Enumerated every caller of the four relaxed theorems across `GaloisForLFunctions`; there are exactly
two, and both now build:
- `NevanlinnaBoundaryFaceMaximalTranslation` — unaffected, its call site determines `Γ`.
- `CarrierHerglotzPresentationFree` — fixed as above.

Verified green after the change: `AnalyticNevanlinnaCarrierRelationFree`,
`BoundaryCarrierTranslationFreeness`, `NevanlinnaBoundaryFaceMaximalTranslation`,
`CarrierHerglotzPresentationFree`, `FamilyPatternBridge`, `PacketValueFamilyJet`.

The earlier `DirichletLSeriesUpperEnd` breakage was another agent's and has since been resolved by
them; its olean is present again.

State of the HT half. The freeness layer now admits arbitrarily many distinct translates, and the
gauge, the bridge in both directions, and both identifications are built and verified. The one piece
not yet written is the `hrelation` calc chain at `m > 1`: assembling
`weightedBoundaryCarrierExpandedPacketValue_eq_familyJetVec` and `familyPatternExpansion_eq_eval`
with the `carrierPatternExponent` / `expandedDifferentialEvaluationMatrix_apply` bookkeeping into
`weightedBoundaryCarrierExpandedPatternRelationHolds`, mirroring lines 618-686 of
`AnalyticNevanlinnaCarrierRelationFree` but with the shift configuration being the translates rather
than zero.

### The family pattern has exactly the shape the bridge expects

`GaloisForLFunctions.HTGeometry.FamilyPatternShape` — four compatibility facts, each `rfl`:
- `familyPatternOfRelation_shiftCount` — the pattern carries exactly `m` shift slots;
- `carrierPatternShift_familyPatternOfRelation` — its shift index is `Fin m`, so an
  `InjectiveShiftConfiguration` on it is a tuple of `m` distinct complex translates;
- `familyPatternOfRelation_orders` — its jet depths are uniformly `n + 1`;
- `familyPatternOfRelation_sigma` — hence its dependent jet type
  `Σ i, Fin (orders i)` is *definitionally* the bridge's `Σ _ : Fin m, Fin (n + 1)`.

That last one matters for the remaining assembly: the pattern side and the family side share a type
on the nose, so the `hrelation` calc chain needs no transport, no `Equiv` juggling and no `cast` —
`weightedBoundaryCarrierExpandedPacketValue_eq_familyJetVec` and `familyPatternExpansion_eq_eval`
can be composed directly against the pattern's own indices.

Remaining: that calc chain itself, mirroring lines 618-686 of `AnalyticNevanlinnaCarrierRelationFree`
with the shift configuration being the translates rather than zero. Its three steps are `hy` (packet
values are jets — supplied), `hprod`/`hsum` (the `carrierPatternExponent` and
`expandedDifferentialEvaluationMatrix_apply` bookkeeping, generic), and the expansion-to-evaluation
step (supplied). No further infrastructure is missing.

### 2026-08-02 — exact discrete-support meromorphic corollary formalized

Added and wired:

- `CountableWeightedDiracLinftyEquiv` — exact real-linear isometric equivalence
  `lp (fun _ : ℕ => ℝ) ∞ ≃ₗᵢ Lp ℝ ∞ (countableWeightedDirac ε atoms)` for injective atoms and
  strictly positive weights. Evaluation at every atom is literal, not merely almost everywhere.
- `HerglotzDiscreteSupportSeries` — exact `(H7)`, `(H7) → H0`, infinite-support certificate,
  locally uniform convergence on the full pole complement, holomorphy there, global meromorphy,
  absolute convergence of the real subtraction constant, and the identity
  `regularized integral = m_u - real constant`.
- `HerglotzDiscreteSupportFreeness` — homeomorphic transfer of the dense residual phase from
  `L∞(μ)` to literal `ℓ∞(ℝ)`, followed by the constant-gauge descent proving full finite-family
  complex-translation differential algebraic independence for the exact series `(1)`.

Direct foreground checks passed for all three modules. No `sorry`, `admit`, `axiom`, `opaque`, or
`unsafe` declaration occurs in them. `#print axioms` for the isometry, normal-convergence theorem,
global-meromorphy theorem, exact integral/series identity, and residual-freeness capstone reports
only `[propext, Classical.choice, Quot.sound]`.

This closes the entire **Discrete-support meromorphic corollary** section without replacing
`ell^infinity` by an `Lp` proxy. Remaining open sections on this card are the unit-residue
canonical-product and functional-equation-even strengthenings and their exact-index surgeries.

### 2026-08-02 — unit-residue canonical product and exact moving-location jet core formalized

Added and wired:

- `MovingCanonicalProduct` — exact bounded zero displacement
  `Λ_j(θ)=j+1+(1/4)tanh(θ_j)`, strict ordering and escape, reciprocal-square summability, exponent
  of convergence exactly one, an order-one growth envelope, the genus-one entire product, Schwarz
  reality, exact simple real divisor, normally convergent regularized logarithmic derivative,
  upper-half-plane Herglotz sign, and `-F'/F=M_θ` off the divisor.
- `MovingCanonicalJetControllability` — joint real controllability of the additional inverse-square
  coordinate and an arbitrary finite complex Cauchy packet; exact factorial-shift extraction of
  the location derivatives `(7)--(8)`; specialization to the moving canonical divisor; and the
  exact positive diagonal parameter speed `(1/4)cosh(θ_j)⁻²`. Both location and actual
  bounded-parameter jet maps are unconditionally surjective.

The controllability proof includes the real/conjugate rational-annihilator argument and the pole at
zero, rather than dropping the regularization coordinate. Direct foreground checks pass for both
modules. No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in them.

Remaining for this section: global compact-shift transversality/Baire completion for the nonlinear
moving-divisor chart, then exact canonical zero-replacement surgery. Functional-equation-even
product, its full-orbit freeness, and its even-index surgery remain open.
