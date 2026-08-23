# Multiplicative power-quotient logarithmic residue

- **ID:** `multiplicative-power-quotient-logarithmic-residue`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; multiplicative quotients; invariant differential fields
- **Statement:** An infinite tower of algebraic power quotients of a generic multiplicative HT
  carrier has a nontrivial intersection: exactly the logarithmic-derivative field, which remains
  maximally translation-HT.

## Goal

Classify the information that survives every algebraic power normalization.  Ordinary rational
function fields lose the generator in the intersection of increasingly deep power subfields.  The
differential field may retain a constraint residue because differentiation sees infinitesimal
multiplicative motion.  The exact question is whether that residue is precisely `DY/Y`.

## Setup

Let `(K,D)` be a differential field of characteristic zero whose constant field contains all roots
of unity.  Let `A` be a nonempty index set and

`F=K<Y_a : a in A>`

the differential rational field on a differentially algebraically independent family.  Let

`1<N_0 | N_1 | N_2 | ...`, `N_n -> infinity`,

and set

`F_n=K<Y_a^(N_n) : a in A>`,

`u_a=DY_a/Y_a`, `L=K<u_a : a in A>`.

## Power-quotient residue theorem `[PROVED HERE]`

1. `F_n=L(Y_a^(N_n) : a in A)` as an ordinary rational extension of `L`.
2. `intersection_n F_n=L`.
3. Every strict divisibility step gives a strict field inclusion.
4. The family `{u_a}` is differentially algebraically independent over `K`.
5. If `A` is the full translation orbit of a maximally translation-HT meromorphic
   function `f`, then

   `intersection_n C(z)<T_h(f^(N_n)) : h in C>`

   is exactly

   `C(z)<T_h(f'/f) : h in C>`,

   and the residual translate family is still differentially algebraically independent.

### 1. Logarithmic coordinates and ordinary rationality

For each `a`, define differential polynomials `B_(a,r)` recursively by

`B_(a,0)=1`, `B_(a,r+1)=D B_(a,r)+u_a B_(a,r)`.

Induction gives

`D^r Y_a=Y_a B_(a,r)`.                                      (1)

Consequently

`F=L(Y_a:a in A)`                                           (2)

as an ordinary field.  Likewise, for every positive integer `N`,

`D(Y_a^N)/Y_a^N=N u_a`,                                    (3)

and the same recursion with `N u_a` gives

`K<Y_a^N:a in A>=L(Y_a^N:a in A)`.                          (4)

The elements `{Y_a}` are algebraically independent over `L`.  Indeed, independently scaling any
finite set of generators by nonzero constants,

`Y_a |-> c_a Y_a`,

extends to a differential automorphism of `F` and fixes every `u_a`.  If a nonzero polynomial over
`L` vanished at a finite tuple of the `Y_a`, applying all independent scalings and separating the
distinct character monomials would force every coefficient to vanish.  This proves the claimed
ordinary rationality in (2), and (4) follows in the same way.

### 2. Exact intersection

Let `R` belong to every `F_n`.  It involves only finitely many original coordinates.  For each `n`
and each independent choice of `N_n`-th roots of unity `zeta_a`, the automorphism

`Y_a |-> zeta_a Y_a`                                       (5)

fixes `F_n`, hence fixes `R`.  Fix one active coordinate and vary only its root of unity.  The union
of the groups `mu_(N_n)` is infinite because `N_n -> infinity`.  The equality obtained from (5) is
an identity between rational functions of the scaling parameter, so infinitely many constant zeros
force it to hold for every nonzero constant.

Thus `R` is fixed by the full coordinatewise algebraic torus on its finite support.  The fixed field
of

`(G_m)^S` acting on `L(Y_a:a in S)` by independent coordinate scaling is `L`: a rational function
with a nonzero character weight is moved, and independent weights leave no nonconstant monomial
ratio.  Therefore `R in L`.  Conversely, (3) puts every `u_a`, hence all of `L`, in every `F_n`.
This proves

`intersection_n F_n=L`.                                    (6)

The finite-support argument also kills the possible objection that an alternative expression for
`R` might use coordinates outside its original support: independent scaling of any such coordinate
would move that expression unless the coordinate cancels from the rational function.

### 3. Strictness

Write `N_(n+1)=q N_n` with `q>1`.  Then `F_(n+1) subset F_n`.  Choose an index `a` and an
`N_(n+1)`-th root of unity `zeta` for which `zeta^(N_n) != 1`.  Scaling only `Y_a` by `zeta` fixes
`F_(n+1)` but moves `Y_a^(N_n)`.  Hence `Y_a^(N_n) notin F_(n+1)` and the inclusion is strict.

### 4. The residue is still maximally HT

For a finite `S subset A`, every `Y_a`, `a in S`, satisfies

`D Y_a-u_a Y_a=0`                                          (7)

over `K<u_a:a in S>`.  Hence `K<Y_a:a in S>` is differentially algebraic over
`K<u_a:a in S>`.  The former field has differential transcendence degree `|S|`, so the latter does
as well.  Thus every finite subfamily of `{u_a}` is differentially algebraically independent, and
so is the whole family.

### 5. Translation realization

Let `f` be a nonzero meromorphic function for which

`{T_h f:h in C}`

is differentially algebraically independent over `C(z)`.  Substitute `Y_h=T_h f` in the abstract
theorem.  Differential independence makes the substitution injective.  Since powers and logarithmic
derivatives commute with translation,

`T_h(f^N)=(T_h f)^N`,

`D(T_h f)/(T_h f)=T_h(f'/f)`,

(6) becomes

`intersection_n C(z)<T_h(f^(N_n)):h in C>`

`  =C(z)<T_h(f'/f):h in C>`.                               (8)

The translate family on the right is differentially algebraically independent by Section 4. `QED`

## Attacks and boundaries

1. **Not merely a finite-level statement.**  Equation (8) computes the infinite intersection
   exactly.
2. **Not ordinary-field intuition.**  In an ordinary rational field, increasingly deep power
   subfields lose the generator.  The derivation leaves the nontrivial Maurer--Cartan residue
   `DY/Y` at every level.
3. **No cancellation loophole.**  Every field element has finite coordinate support; independent
   torus weights force all outside coordinates and all nonzero weights to cancel.
4. **Roots of unity are load-bearing.**  They are available over `C(z)`.  Over smaller constant
   fields the statement must be made after constant extension or with the Zariski closure of the
   available deck group.
5. **Generic/maximal HT is load-bearing for the independence conclusion.**  The intersection formula
   is an abstract differential-rational theorem; its maximal-HT realization requires an injective
   specialization.
6. **The tower does not remember a distinguished generator.**  Euler normalization or another
   arithmetic marking can distinguish representatives even when the unpointed pro-fields agree.

## RH-route pressure test

For analytic `f`, the stable residue is `f'/f`, so it retains the complete divisor as its pole set
with multiplicities.  Thus no infinite tower of algebraic power normalizations can erase either
maximal translation HT or zero geometry.  Combined with fixed-field Krein-index plasticity, this
excludes multiplicative-normalization implementations that expect repeated algebraic quotienting
to produce an RH-selecting finite core.  It would not exclude routes using additional Euler,
positivity, measure, or spectral data.

The separate theorem `power-normalization-profield-krein-blindness.md` proves that the complete
power tower and this exact residue are simultaneously identical across every finite Krein index.

## Parent-theory and novelty verdict

- `[SEARCH]` Rosenlicht's exponential-extension theory gives the Kummer analogy and the structure of
  differential fields generated by elements whose logarithmic derivatives lie in the base.  It does
  not state the decreasing power-subfield intersection or its translation-orbit consequence.
  Source: `https://msp.org/pjm/1975/57-1/pjm-v57-n1-p31-p.pdf`.
- `[SEARCH]` The logarithmic derivative as the differential-algebraic quotient of `G_m` by its
  constant points is classical generalized-Schwarzian theory.  Source: Scanlon,
  `https://doi.org/10.1016/j.aim.2018.03.008`.
- `[SEARCH]` Differential rational invariant fields of affine algebraic-group actions are a parent
  framework.  Source: Bekbaev, `https://arxiv.org/abs/math/0608479`.
- `[SEARCH]` A nonconstant differential rational function of a differential indeterminate remains
  differentially transcendental (ADH, Lemma 4.1.5).
- `[SEARCH]` Viewed over `L=K<u_a>`, the extension `L(Y_a)/L` is the generic exponential/
  Picard--Vessiot extension with differential Galois group the coordinate torus.  The field
  `L(Y_a^N)` is the fixed field of the finite Kummer subgroup `mu_N`, and the union of the
  `mu_(N_n)` is Zariski dense in the torus.  The Picard--Vessiot Galois correspondence therefore
  gives the intersection formula directly.

The arbitrary-family and translation-HT formulations are useful project bridges, but their proof
introduces no mechanism beyond standard Kummer and Picard--Vessiot fixed-field theory.  This card is
not new scientific knowledge.  The nontrivial candidate application is separated into
`power-normalization-profield-krein-blindness.md`.

## Lean status

On 2026-08-23, the complete theorem was formalized in
`formal/GaloisForLFunctions/HTGeometry/ArbitraryFamilyPowerQuotientResidue.lean` and
`formal/GaloisForLFunctions/HTGeometry/TranslationPowerQuotientResidue.lean`.

`arbitraryFamily_powerQuotientResidue` proves in one unconditional theorem that every level is the
ordinary rational extension of the common logarithmic-residue field, the powered coordinates are
algebraically independent over that field, the infinite intersection is exactly the residue,
every strict divisibility step is a strict field descent, and logarithmic residues retain full
differential independence. The translation module specializes this result to both arbitrary
meromorphic translation families and the existing entire-function `translationPowerProfield`
interface, including exact intersection and residual differential-independence theorems.

Both modules are wired into `GaloisForLFunctions.HTGeometry`. Exact source checks and targeted
build of the translation capstone pass. Axiom audits of generic intersection, strictness,
differential-independence, meromorphic specialization, and entire specialization report only
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1: exact intersection candidate, proof mechanism, and RH boundary isolated
- [x] 1 -> 2: complete unconditional paper proof
- [x] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: optional formal bridge documentation

## Log

- 2026-07-11 -- Discovered as the order-zero boundary left after positive-order differential-rational
  erosion reduced to the known differential-Luroth order lemma.  The surviving object is an
  infinitesimal multiplicative constraint, not a finite DA shadow.
- 2026-07-11 -- Proved the exact arbitrary-family intersection by independent Kummer deck actions
  and torus fixed fields; proved that the logarithmic residue retains full translation differential
  independence.  The Krein-index application is recorded as its own one-claim card.
- 2026-07-11 -- Downgraded after the parent-theory attack: the intersection is the fixed field of the
  Zariski closure of the accumulated Kummer deck groups, hence a routine Picard--Vessiot consequence.
