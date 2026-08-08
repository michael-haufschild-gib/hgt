# Rational-adelic constitutive rigidity and cofinal multiplicity one

- **ID:** `rational-adelic-constitutive-rigidity-and-cofinal-multiplicity-one`
- **Stage:** 1 — in progress
- **Type:** CENTRAL MCTG CONJECTURE / SOURCE-NATURALITY CLASSIFICATION
- **Status:** `[EXACT FINITE-SOURCE NONRIGIDITY] [VERTICAL GAUGE TORSOR PROVED]`
  `[TWO-ENDPOINT INFINITE MODULI PROVED] [FULL ADELIC FOURIER ARROW MISSING]`
  `[COFINAL MULTIPLICITY ONE CONJECTURAL] [SOURCE CHARGE OPEN] [NOT RH] [NO LEAN WRITTEN]`
- **Field role:** first concrete make-or-break theorem for Constraint Relativity/MCTG.
- **Paper anchors:**
  `../../2-fully-proven/constraint-relativity/prime-isotropy-vertical-shear-gauge-torsor-and-nonerasure-dichotomy.md`,
  `../../2-fully-proven/constraint-relativity/two-endpoint-prime-orbit-stokes-moduli-and-infinite-coinvariant-law.md`,
  `../../2-fully-proven/constraint-relativity/rational-adelic-h1-observer-coefficient-freedom-and-discriminant-law.md`.
- **Statement:** Finite-prime linear naturality cannot select Route-R observer. Exact ambiguity is
  representation on dilation coinvariants and target fixed-ideal ports. Proposed first genuine
  field theorem is singular cofinal multiplicity one: one pre-divisor all-prime arrow shrinks
  natural-transformation equalizer to a normalized line, while finite subcategory retains large
  moduli.

## 1. Exact problem after hostile closure

Literal source has retained functor value

\[
 H^1(C_p)\cong Q_p\oplus\mathbb C\eta_p,
 \qquad
 Q_p=\ker\varepsilon_0/\operatorname{im}(\alpha_p-1).
 \tag{CRM.1}
\]

Resolved comparison kills all `H1`, so observer quotient is full Hom-space. Two independent
ambiguities are exact:

1. **source splitting:** normalized Stokes readers form affine `Q_p^*` torsor;
2. **target coefficient:** for every `v in V`, map `P_v` satisfies `P_v(eta_p)=v`.

Vertical cochain shears act simply transitively on splittings. If all shears are gauge, invariant
observer erases `eta_p`; if splitting is marked, arbitrary `v` remains. This dichotomy is current
finite-source theorem, not conjecture.

## 2. Minimal finite source category

`[DEFINITION TARGET]` Let `mathsf S_fin` be category generated before divisor specialization by:

1. prime-isotropy complexes `C_p`;
2. rational dilation arrows and their relations;
3. zero and Haar endpoints;
4. literal anti-linear Real/reflection arrows;
5. strict resolved Xi comparison considered in homotopy category;
6. ordered finite Euler--Gamma port transports already constructed in corpus.

No Fourier arrow is admitted until full adelic cochain map is built. No cover is defined by desired
observer behavior.

Let

\[
 \mathcal R:\mathsf S_{\mathrm{fin}}\to\mathsf{Vect}_\mathbb C,
 \qquad
 \mathcal V=\mathcal V_+\oplus\mathcal V_-:
 \mathsf S_{\mathrm{fin}}\to\mathsf{Vect}_\mathbb C
 \tag{CRM.2}
\]

be retained `H1` and ordered fixed-ideal port functors. For explicit generator set `G_fin`, define
intertwiner equalizer

\[
 \mathcal N_{\mathrm{fin}}
 =\bigcap_{g\in G_{\mathrm{fin}}}
 \ker\left(
 \mathcal V(g)\circ(-)-(-)\circ\mathcal R(g)
 \right).
 \tag{CRM.3}
\]

### Finite-source nonrigidity theorem target

Existing Stage-2 results strongly imply, but a single typed category calculation must still record,

\[
 \dim\mathcal N_{\mathrm{fin}}>1
 \tag{CRM.4}
\]

and source-splitting ambiguity module contains nonzero Haar/orbit-phase subrepresentations. Until
`mathsf S_fin`, functors, and generator actions are written explicitly, `(CRM.4)` remains assembly
task, not promoted theorem.

## 3. Fourier level

Corpus contains:

- archimedean Schwartz Fourier/Poisson identities;
- endpoint exchange/zero-mode consequences on special pure tensors;
- periodic Poisson packet formulas;
- reflection identities in completed physical targets.

It does **not** contain full adelic Fourier cochain arrow

\[
 \mathcal F:C_p^\bullet\to C_{p'}^\bullet
 \tag{CRM.5}
\]

inducing action on `Q_p^*`. Thus “Poisson kills ambiguity” is not permitted conclusion.

Next finite theorem must construct `(CRM.5)` or prove obstruction. If constructed, compute fixed
space of ambiguity representation, especially orbit-phase distributions

\[
 \Lambda_{a,b}=S_a-S_b,
 \qquad a,b\in\mathbb R_{>0}/p^\mathbb Z.
 \tag{CRM.6}
\]

An endpoint-swapping involution may only conjugate shears and leave nonzero invariant subspace.

## 4. Singular cofinal source category

`[BOLD CONSTRUCTION PROGRAM]` Enlarge to `mathsf S_infinity` by adding:

1. fixed global additive character and self-dual Haar normalization;
2. full Fourier/Poisson unit and counit if `(CRM.5)` closes;
3. analytic dagger/reflection;
4. ordered all-prime Euler--Gamma port transport;
5. one genuine singular all-prime/cofinal boundary arrow that acts nontrivially on fixed
   `ell1` quotient.

Finite-prime corrections vanish/trivialize in physical fixed quotient. Therefore item 5 is
load-bearing: without it, arbitrary target coefficient survives.

Define

\[
 \mathcal N_\infty
 =\bigcap_{g\in G_\infty}
 \ker\left(
 \mathcal V(g)\circ(-)-(-)\circ\mathcal R(g)
 \right).
 \tag{CRM.7}
\]

## 5. Cofinal adelic constitutive multiplicity-one conjecture

`[COFINAL_ADELIC_CONSTITUTIVE_MULTIPLICITY_ONE]`

There exists explicitly constructed pre-divisor Euler--Gamma observer `sigma_EG` such that

\[
 \boxed{\mathcal N_\infty=\mathbb C\,\sigma_{\mathrm{EG}}.}
 \tag{CRM.8}
\]

Moreover:

1. no nonzero `epsilon_1` deformation of Stokes component extends across `mathsf S_infinity`;
2. orbit-phase ambiguity representation has no invariant vector;
3. `P_v` extends naturally iff `v in C sigma_EG(eta_p)`;
4. one source-side normalization independent of Xi zeros selects unique element of line;
5. restriction to `mathsf S_fin` recovers higher-dimensional observer space.

This theorem would produce first nontrivial constitutive natural transformation of MCTG. It would
select observer coefficient, not prove its two ports are both nonzero. RH still requires separate
port-support/nonerasure theorem.

## 6. Why linear naturality alone cannot finish

Intertwiner equalizer is vector space. If `sigma` is natural, so is `c sigma`. Central scalar target
automorphisms commute with all linear transports. Hence multiplicity one yields a line, not
distinguished nonzero point. Required normalization must be inhomogeneous source charge or period
condition defined before divisor. If normalization references Xi zero or target nonvanishing, it is
circular.

## 7. Literature collision map

1. Voronoi--Hankel/Fourier uniqueness for fixed representation, additive character, and self-dual
   measure (Shen--Wu, arXiv:2606.04336) rigidifies transform after inputs; it does not choose marked
   `H1->V_+ direct-sum V_-` coefficient.
2. Meyer adelic crossed-product cyclic homology (math/0312305) supplies carrier, not canonical
   coefficient.
3. Hopf-cyclic coefficient theories classify admissible coefficients; coefficient/module remains
   input.
4. Natural transformations of Ext functors form cohomological moduli (arXiv:2607.23495), supporting
   equalizer/torsor viewpoint rather than uniqueness.
5. Whittaker multiplicity-one theorems show plausible mechanism, but Whittaker datum/model is marked
   input; normalization dependence remains explicit (arXiv:2508.08523, 2412.06824).
6. Cartier/Poitou--Tate dualities provide perfect pairing, not distinguished vector
   (arXiv:2512.13856, 2504.14153).

No exact collision with `(CRM.8)` found. Ingredients occupied; literal source-cofinal equality is
unoccupied under current audit.

## 8. Conjecture / proof / fail loops

1. **One endpoint + Stokes period gives uniqueness.** `FALSE`: affine `Q_p^*` torsor.
2. **Two endpoints give uniqueness.** `FALSE`: Haar line collapses, infinite orbit-phase quotient
   survives.
3. **Treat all vertical shears as gauge.** `FALSE AS NONERASING THEORY`: forces `P(eta)=0`.
4. **Mark one Stokes splitting.** `INSUFFICIENT`: leaves arbitrary `P_v`.
5. **Rational scalings kill Haar.** `FALSE`: Haar shear commutes with all.
6. **Real/reflection kills Haar.** `FALSE`: leaves real line.
7. **Resolved comparison kills shear.** `FALSE`: shear preserved up to explicit cochain homotopy.
8. **Fourier/Poisson kills shear.** `OPEN/NOT YET TYPED`.
9. **Finite Gamma transport selects `v`.** `FALSE`: homogeneous target transport preserves scalar
   freedom and finite corrections are fixed-quotient trivial.
10. **Singular cofinal multiplicity one.** `OPEN`: next genuine theorem.

## 9. Hostile falsifiers

1. `epsilon_1` intertwines every declared generator;
2. orbit-phase shear transports conjugately through Fourier and cofinal arrows;
3. cofinal arrow acts trivially on fixed quotient;
4. two independent normalized intertwiners survive equalizer;
5. normalization uses Xi divisor or target nonvanishing;
6. selected line meets port discriminant at off-line grade—this does not falsify multiplicity one,
   but proves it insufficient for RH.

## 10. Immediate research order

1. define `mathsf S_fin`, functors, and generator matrices literally;
2. prove finite equalizer contains vertical ambiguity subrepresentation;
3. construct or obstruct full adelic Fourier cochain arrow;
4. compute Fourier action on orbit-phase quotient;
5. identify actual singular cofinal arrow from existing tail/Roos/completion corpus;
6. compute `N_infinity`;
7. only then return to total transgression/index.

## Lean-return note

- No Lean code was written or built.
- Lean corpus was read for exact source operations only.
- Do not formalize category before finite generator list and arrow laws close on paper.
- Likely later reuse `CCMRationalAdelicPrimeIsotropyRelativeXiChainMap`, endpoint, scaling,
  regulator, and fixed-ideal comparison files.

## Gates

- [x] exact splitting/gauge/target ambiguity mapped
- [x] two-endpoint infinite residual moduli
- [x] current Fourier-arrow absence audited
- [x] current literature collision audit
- [ ] literal finite category and equalizer theorem
- [ ] full adelic Fourier cochain arrow or obstruction
- [ ] orbit-phase Fourier representation
- [ ] singular cofinal arrow
- [ ] cofinal multiplicity one
- [ ] source normalization/nonzero charge
- [ ] marked-port support theorem

## Log

- 2026-08-08 — constitutive problem reduced from vague source naturality to explicit intertwiner
  equalizer; finite nonrigidity exact, cofinal multiplicity one isolated as first genuine field law.

