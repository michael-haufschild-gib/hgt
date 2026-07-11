# Herglotz full-translation HT and Krein-index orthogonality

- **ID:** `herglotz-full-translation-ht-krein-index-orthogonality`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) — `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; exact Herglotz positivity; full complex translation orbit
- **Statement:** Maximal full-translation differential-algebraic freedom occurs generically inside an
  exact Herglotz cone.  Rational finite-rank carrier surgery then realizes every finite Krein
  negative index without changing that HT field or matroid.

## Herglotz full-orbit theorem `[PROVED HERE]`

Fix

`lambda_j=j+1`, `epsilon_j=2^(-j-1)`, `j>=0`.

For a bounded real sequence `u=(u_j) in ell^infinity(R)`, set

`m_u(z)=sum_j epsilon_j exp(u_j)/(lambda_j-z)`.                 (1)

The series converges normally away from the discrete pole set.  It defines a meromorphic function
on `C`, satisfies `m_u(conj z)=conj(m_u(z))`, and is Herglotz on the upper half-plane because

`Im(1/(lambda-z))>0` when `Im z>0`.

There is a comeager subset `U_free subset ell^infinity(R)` such that every `u in U_free` makes the
full family

`{m_u(z+h):h in C}`

differentially algebraically independent over `C(z)`.

### 1. Real Cauchy-jet spanning lemma

Let `x_1,...,x_L` be nonreal complex numbers such that all `x_p` and `conj(x_p)` are pairwise
distinct.  Fix `r>=0`.  For real `lambda` define the complex jet column

`v(lambda)_(p,ell)=ell!/(lambda-x_p)^(ell+1)`, `0<=ell<=r`.

Then the real span of

`{v(lambda_j):j>=0}`

is all of `C^(L(r+1))`, regarded as a real vector space.

Suppose a real-linear functional annihilates every column.  It has the form

`v |-> Re sum_(p,ell) c_(p,ell) v_(p,ell)`

for complex coefficients `c_(p,ell)`.  Thus the rational function of a real variable

`R(t)=sum_(p,ell) c_(p,ell) ell!/(t-x_p)^(ell+1)`

satisfies `Re R(lambda_j)=0` for infinitely many `lambda_j -> infinity`.  On the real line this is
equivalent to

`R(t)+conj(R(conj t))=0`.

The left side is a rational function and has infinitely many zeros, hence vanishes identically.
Its poles split into the disjoint packets `{x_p}` and `{conj(x_p)}`.  At `x_p`, only `R` contributes
to the principal part, so every `c_(p,ell)` is zero.  The annihilator is zero, proving the span
claim.  In particular, some finite set of mass coordinates gives a real-linear jet isomorphism onto
the packet.

### 2. One differential support and all nearby shifts

Fix `m,r` and a finite support of `R_0` distinct expanded differential monomials

`M_j(z,Y)=z^(k_j) prod_(i=1)^m prod_(ell=0)^r Y_(i,ell)^(alpha_(j,i,ell))`.

Put `q=max_j k_j`, and fix `h^0 in Conf_m(C)`.  Choose as many distinct evaluation points
`z_1,...,z_N` as needed so that every point `z_a+h_i^0` is nonreal, avoids the pole set, and the full
packet is disjoint from its complex conjugate.  The forbidden choices form countably many discrete
sets and finitely many real affine lines at each induction step, so such a packet exists.  Shrink to
a relatively compact real neighborhood `U` of `h^0` on which all separations persist.

For one row the jet space is

`X=C^(m(r+1))`.

Let `B subset X^N` be the algebraic locus where the `N by R_0` monomial-evaluation matrix has rank
less than `R_0`.  The same projective-incidence count as in the fixed-divisor theorem gives

`codim_C B >= N-q-R_0+1`.                                      (2)

Indeed, for a fixed projective coefficient vector, at most `q` distinct evaluation rows make its
polynomial in the jet variables identically zero; every other row imposes one nonzero polynomial
equation, while the coefficient vector costs dimension `R_0-1`.

Choose

`N>m+q+R_0-1`.                                                 (3)

Every Whitney stratum of `B` then has real codimension greater than `2m=dim_R U`.

Fix `u^0 in ell^infinity(R)`.  Apply the spanning lemma to the `Nm` evaluation nodes at `h^0` and
select finitely many mass coordinates `J` whose jet columns form a real basis.  By continuity the
same minor stays nonzero for every `h in U` after shrinking `U`.  Let `V=R^J` act by adding a
finitely supported vector `p` to `u^0`.  Define

`Psi:V times U -> X^N`

by the jets of `m_(u^0+p)` at the points `z_a+h_i`.  Differentiation with respect to `p_j` multiplies
the Cauchy jet column by the nonzero scalar `epsilon_j exp(u_j^0+p_j)`.  Therefore the derivative in
the `V` direction is onto at every `(p,h)`: `Psi` is a smooth real submersion.

Parametric transversality now gives a residual dense set of `p in V` for which `Psi_p` is transverse
to every stratum of `B`.  By (2)--(3), every transverse preimage is empty.  Thus the supported
monomials are linearly independent for every `h in U`.

### 3. Baire completion

Finite-coordinate perturbations can be chosen arbitrarily small in the `ell^infinity` norm, so the
preceding avoidance property is dense near every `u^0`.  On a compact subset of `U` it is open: the
jet map depends continuously on `u` in `ell^infinity`, its image is compact, and `B` is closed.

Exhaust each `Conf_m(C)` by countably many compacts and use finitely many patches on each compact.
Intersect over the countable collection of `m`, jet orders, and expanded monomial supports.
Because `ell^infinity(R)` is a Banach space and hence Baire, the intersection is comeager.

Clearing rational denominators and expanding polynomial coefficients in `z` shows that eliminating
every support is exactly differential algebraic independence over `C(z)`.  This proves the theorem.
`QED`

## Unit-residue canonical-product strengthening `[PROVED HERE]`

The positive masses in (1) can be replaced by simple zeros of multiplicity one.  Put

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

## Exact Krein-index orthogonality `[PROVED HERE]`

Fix `u in U_free` and write

`w_j=epsilon_j exp(u_j)>0`.

For a finite set `J subset N` with `|J|=k`, define the rational function

`R_J(z)=-2 sum_(j in J) w_j/(lambda_j-z)`

and

`m_(u,J)=m_u+R_J`.

Then:

1. the Pick kernel of `m_(u,J)` has exactly `k` negative squares;
2. the full complex translation orbit of `m_(u,J)` is differentially algebraically independent;
3. the complete differential-translation fields generated by `m_(u,J)` and `m_u` are equal.

Consequently one and the same maximal HT differential-translation field realizes every finite
Krein index `k=0,1,2,...` through real-symmetric meromorphic generators.

### Proof of exact index

For `z,w` in the upper half-plane, the Pick kernel is

`K_J(z,w)=(m_(u,J)(z)-conj(m_(u,J)(w)))/(z-conj(w))`

`          =sum_n c_n / ((lambda_n-z)(lambda_n-conj(w)))`,     (4)

where `c_n=-w_n` for `n in J` and `c_n=w_n` otherwise.

For any finite node packet, the Gram matrix in (4) is a positive semidefinite matrix minus `k`
rank-one positive semidefinite matrices.  Hence it has at most `k` negative eigenvalues.

Enumerate `J={j_1,...,j_k}` and choose nodes

`z_l=lambda_(j_l)+i y`, `1<=l<=k`.

As `y -> 0+`, multiplying their `k by k` Gram matrix by `y^2` gives

`y^2 (K_J(z_l,z_q))_(l,q) -> -diag(w_(j_1),...,w_(j_k))`.

The selected negative atom contributes `-w_(j_l)/y^2` on its diagonal.  All other diagonal
contributions are bounded, and every off-diagonal term is at worst `O(1/y)` because the selected
real poles are distinct.  The limiting matrix is negative definite, so the Gram matrix has `k`
negative eigenvalues for sufficiently small `y`.  Combined with the upper bound, the Pick kernel
has exactly `k` negative squares.

### Proof of HT and field invariance

For every complex shift `h`, `T_h R_J belongs C(z)`.  Translation by the known rational
differential tuple

`T_h m_u |-> T_h m_u+T_h R_J`

is an invertible substitution of the differential polynomial ring over `C(z)`.  It preserves
differential algebraic independence.  Moreover each translated generator on one side differs from
the corresponding generator on the other by a base-field element, proving equality of the generated
differential-translation fields. `QED`

## Attacks and boundaries

1. **Not a finite-probe fake.**  `k=0` is exact Herglotz positivity on the whole upper half-plane;
   `k>0` is the exact global negative-square index.
2. **Positivity does not make the function DA.**  The comeager positive-mass carriers have the
   strongest possible full translation differential independence.
3. **HT does not select positivity either.**  Every finite exact index occurs without changing the
   field or matroid.
4. **Unit residues are available.**  The canonical-product strengthening removes the arbitrary-mass
   objection and realizes the same law with simple zeros of an order-one entire function.
5. **The scalar functional equation is available.**  The even strengthening preserves reflection
   symmetry and realizes every even negative index in one free HT field.
6. **No Euler realization is preserved.**  The rational zero replacement changes the distinguished carrier.
   It proves field-level orthogonality, not that the actual zeta carrier can be modified while
   retaining its Euler product.
7. **Nyman--Beurling is not literally a Pick-kernel statement.**  The theorem excludes only attempts
   to derive its Hilbert norm canonically from the abstract HT field; the exact zeta-generated closure
   remains outside scope.

## Exact route consequence

The law puts exact all-order positivity and maximal HT on independent axes.  In one
differential-translation field, the exact negative-square index could be `0,1,2,...`.  Hence neither
Herglotz/Weil positivity nor its failure is forced by the strongest possible HT orbit law.  Any RH
route through Weil positivity, de Branges, Connes, or Hilbert--Polya must import a distinguished
Euler/spectral realization not contained in HT structure itself.

With the functional-equation involution imposed, the same statement holds with the exact allowed
index spectrum `2N`.  Thus FE plus maximal HT forces the known pairing parity and nothing stronger;
the RH condition `kappa_-=0` remains independent data.

For Nyman--Beurling, the corresponding conclusion is conditional and narrower: no Hilbert norm or
closure predicate invariant under the full field identification can distinguish the indices above.
The actual Nyman--Beurling space includes distinguished zeta/Euler data and is not refuted.

The theorem therefore does not say that the complete classical equivalences are false.  It proves
that hypertranscendence—even maximal uncountable translation hypertranscendence—cannot provide their
missing exact selector.

## Natural Hilbertization corollary `[PROVED] [BRIDGE]`

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

Thus the abstract maximal HT field has no nonzero automorphism-natural Hilbert norm.  A
Hilbert--Polya, de Branges, Connes, or Nyman--Beurling realization must break this scalar isotropy by
choosing a distinguished generator, source normalization, cyclic vector, measure, or Euler
embedding.  This corollary is elementary representation theory and is classified as a bridge, not
new scientific knowledge.

## Novelty gate

- **Proof gate:** passes by the real Cauchy-jet spanning lemma, rank-defect codimension, parametric
  transversality, and the exact signed-atomic kernel calculation.
- **Significance gate:** provisionally passes.  It is an exact, not finite, orthogonality theorem:
  the full Krein index ranges over every finite value inside one maximal HT field; this remains true
  for unit-residue logarithmic derivatives of order-one canonical products, and the FE-even subfamily
  realizes every even index.
- **Parent-theory gate:** open.  Herglotz representation, signed atomic kernels, and transversality
  are classical separately.  The residual full-complex translation differential-independence theorem
  inside a positive Herglotz cone is not yet reduced to a quoted parent theorem.
- **Literature gate:** preliminary exact searches completed across generalized Nevanlinna
  functions, hypertranscendence, generic meromorphic functions, and translate independence;
  specialist MathSciNet/zbMATH and citation-chain audit remains open.
- **Rediscovery gate:** open.

No candidate-new label is applied until those audits pass.

## Preliminary parent and literature comparison

1. **Jones--Kirby--Le Gal--Servi, strong transcendence.**  Proposition 3.2 proves that strongly
   transcendental holomorphic functions are residual in the unrestricted Frechet space `O(U)`.
   Their condition concerns arithmetic transcendence of finite point-jets and local definability.
   It does not work in a positive Herglotz cone, does not prove differential algebraic independence
   over `C(z)` of every uncountable translate tuple, and does not compare exact negative-square
   indices inside one field.  Source: `https://arxiv.org/abs/1712.07064`.
2. **Forstneric, holomorphic jet transversality.**  The general jet-transversality theorem supplies
   a parent mechanism for unrestricted holomorphic mapping spaces.  Here the parameter space is the
   nonlinear positive-mass Cauchy family; the real Cauchy-jet spanning lemma is what recovers the
   missing submersion.  The exact Herglotz and translation-field conclusions are not stated there.
   Source: `https://arxiv.org/abs/math/0401439`.
3. **Edwards, independent translates.**  This treats topological linear independence of translates
   in function spaces, not differential algebraic independence of every derivative/translate family
   and not a positive Pick kernel.  Source: `https://doi.org/10.5802/aif.35`.
4. **Krein--Langer generalized Nevanlinna theory.**  Integral representations and finite
   negative-square indices are classical.  The signed-atomic calculation above is a concrete special
   case, not a new parent mechanism.  The candidate-new content, if any, is the exact orthogonality
   with residual full-translation HT.  Adjacent source: Rovnyak--Sakhnovich,
   `https://doi.org/10.13001/1081-3810.1117`.
5. **Dijksma--Langer--Luger--Shondin factorization.**  The canonical factorization of a scalar
   generalized Nevanlinna function counts nonreal poles and generalized real poles of nonpositive
   type with multiplicity in the negative index.  This supplies the classical pole-count step used
   in the canonical-product and even-quartet strengthenings; it does not contain the Herglotz-cone
   genericity or fixed-HT-field plasticity theorem.  Source:
   `https://doi.org/10.1007/BF01236290`.

Exact searches for combinations of `Herglotz/Nevanlinna`, `Laguerre--Polya/canonical product`,
`differential algebraic independence`, `all translates`, `comeager/residual`, and `negative squares`
did not locate the combined theorem.
This is only preliminary negative evidence; MathSciNet/zbMATH and specialist citation-chain review
remain required.

## Lean status

The current Lean tree formalizes the finite pairability/index side (`OmegaComplexStructure`,
`SeamPolarizationWeld`, `SeamSpectralFlow`, `CarrierCauchy`), the measured-index blindness side, and
the forward infinite positive-measure Herglotz/Pick theorem in `MeasureCarrier.lean`.  It does not
contain infinite **signed** Cauchy-kernel index, Baire genericity in `ell^infinity`, algebraic
rank-defect codimension, or parametric transversality.  Those missing layers carry the complete
claim, so no partial theorem is promoted to stage 3.

## Gates

- [x] 0 -> 1: exact law and three proof cores isolated
- [x] 1 -> 2: complete unconditional paper proof
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready preprint and independent novelty audit

## Log

- 2026-07-11 -- Proved real jet-surjectivity for positive Cauchy masses by a rational-annihilator
  argument and used real parametric transversality to remove every uncountable shift configuration.
- 2026-07-11 -- Proved exact signed-atomic Krein index `k` by a rank upper bound and pole-localized
  negative-definite Gram matrices.  Rational surgery preserves the complete free HT field exactly.
