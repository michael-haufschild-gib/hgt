# Hypertranscendental source effectivity is enriched incidence over a fracture hypercube

- **ID:** `hypertranscendental-source-fracture-hypercube`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CONJECTURE / MULTI-RELATIVE EFFECTIVITY / ENRICHED INCIDENCE OBJECT
- **Scientific status:** `[CONJECTURE] [TWO-CHANNEL EXACT SEED LEAN-FORMALIZED]`
  `[ABELIAN THREE-CHANNEL OBSTRUCTION LEAN-FORMALIZED]`
  `[COORDINATE-FACET EFFECTIVITY LEAN-FORMALIZED]`
  `[NORMALIZED GAUGE GATE + PHYSICAL OSCULATION/ANOMALY SEEDS LEAN-FORMALIZED]`
  `[FIELDS-SCALE OPEN CORE]`
  `[NOT AN RH RESULT]`
- **Parents:**
  - `hypertranscendental-capacity-descent-postnikov-tower.md`
  - `hypertranscendental-constraint-hodge-duality.md`
  - `../3-formalized/source-producer-integral-realization-minimality.md`
  - `../2-fully-proven/new_scientific_knowledge/irrational-elliptic-gamma-hypertranscendence-matroid.md`
  - `../2-fully-proven/new_scientific_knowledge/multiple-gamma-effective-fracture-descent-orthogonality.md`
  - `../3-formalized/not_new_scientific_knowledge/birelative-fracture-square-and-three-channel-interaction.md`
  - `../3-formalized/not_new_scientific_knowledge/calibrated-fracture-incidence-kernel-cokernel.md`
  - `../3-formalized/not_new_scientific_knowledge/polarized-fracture-incidence-trichotomy.md`
- **Statement:** The source-canonical fracture hypercube is the kinematic coordinate system of a
  constrained hypertranscendental source, not the unified obstruction by itself.  Its faces record
  incomparable partial realizations and its Postnikov directions record coherence.  The unified
  object is conjecturally an anomaly-twisted, osculation/effectivity-bifiltered derived stack of
  reporter-normalized incidence lifts.  Its automorphisms are residual joint-fixed gauges; its
  existence, closure, positivity, monodromy, and higher interaction classes are different
  obstruction shadows.  It is defined only on a source-effectively normalized stratum, not
  canonically from bare source syntax, and it is not hypertranscendence itself.

## The displacement

The obstruction report isolates seven terminal failures: sign, critical scale, spectral
production, integral multiplicity, source purity, typed comparison, and arithmetic rigidity.  A
first synthesis placed these at successive stages of one Postnikov tower.  That picture confuses
two independent coordinates:

```text
cube direction       = which kind of information was forgotten;
Postnikov degree     = how high the compatibility/coherence failure occurs.       (1)
```

The directions are not naturally ordered.  Differential-algebraic descent, holomorphic/divisor
descent, polarization, critical bornology, integral realization, and source pointing are different
coefficient or realization categories.  In particular, the elliptic-gamma model supplies both a
nontrivial differential-algebraic anomaly and a nontrivial holomorphic gamma-gerbe class, but the
two live in quotient theories with incomparable gauge sectors.  There is no canonical map making
one a refinement of the other.

Therefore a linear tower can record coherence height only after the realization direction has
been fixed.  The full object must retain both coordinates in `(1)`.

## Exact two-channel fracture square `[PROVED + LEAN]`

Let `M` be a module and let `I,J` be two gauge submodules.  The two observations are `M/I` and
`M/J`.  There is a canonical sequence

```text
0 -> M/(I intersection J)
  -> M/I direct_sum M/J
  -> M/(I+J)
  -> 0,                                                        (2)
```

where the last map sends `(x mod I,y mod J)` to `x-y mod (I+J)`.

The sequence is exact.  Hence:

1. two observations have a common ambient representative exactly when their compatibility defect
   in `M/(I+J)` vanishes;
2. their common representative is determined modulo `I intersection J`;
3. every compatibility-defect class occurs.

This is parent Mayer--Vietoris algebra.  Its role is not novelty.  It proves that the correct
two-channel object is a fracture square and identifies both its ambiguity and its obstruction.

## Pairwise compatibility is not global effectivity `[PROVED + LEAN]`

The two-channel exactness does not iterate formally.  Let `I,J,K <= M` satisfy

```text
I+J=M,   I+K=M,   J+K=M.                                    (3)
```

Then every triple of quotient observations is pairwise compatible, because all three pairwise
defect quotients vanish.  Nevertheless, for any

```text
v notin (I intersection J)+K,                               (4)
```

the triple

```text
(0 mod I, 0 mod J, v mod K)                                 (5)
```

has no common representative.  More strongly, without assuming `(3)`, `(5)` has a common
representative if and only if

```text
v in (I intersection J)+K.                                 (6)
```

Thus the quotient

```text
M / ((I intersection J)+K)                                 (7)
```

is an exact positive receiver for this three-channel interaction obstruction.

This changes the earlier theory materially:

> **[NO-GO -- NONABELIANITY IS NOT THE SOURCE OF ALL HIGHER STAGES.]** Higher obstruction layers
> can occur for completely abelian linear quotient channels.  Noncommutative gauge associators are
> one source of higher coherence, not the first or only source.

> **Positive successor.** The universal receiver must include the augmented Cech interaction
> complex of the channel arrangement before any nonabelian enhancement is added.

## The abelian fracture complex

For a finite family of gauge subobjects `(I_i)`, define the augmented complex

```text
C^(-1) = M / intersection_i I_i,
C^p    = direct_sum_(|S|=p+1) M / sum_(i in S) I_i,          (8)
```

with the alternating quotient maps.  The augmentation sends one ambient class to all of its
partial observations.

- The two-channel theorem says the augmented complex is exact in degree zero for two channels.
- The three-channel theorem proves that its first interaction group can be nonzero even when all
  pairwise overlap targets vanish.
- The earlier finite-quotient interaction-cohomology theorem is a source-specific realization of
  the same phenomenon: marginal quotient fields miss a canonical relative HT interaction layer.
- The pair-face sewing theorem identifies a special HT class for which triple compatibility is
  complete.  It is a source-specific vanishing theorem, not a universal descent fact.

This resolves an apparent contradiction in the existing corpus.  Some constrained HT classes are
two-local; other abelian channel arrangements have genuine higher interaction.  The correct
question is not whether HT descent is universally pairwise or universally higher.  It is:

```text
Which source law forces which interaction groups to vanish?                   (9)
```

Equation `(9)` is a new research axis.  A source-specific vanishing or nonvanishing theorem is
mathematical content; the bare Cech complex is parent machinery.

## Nonlinear source fracture hypercube `[CONJECTURE]`

Let `(F,R)` be a regular source-minimal **source-effectively normalized** constrained HT germ with
reporter/normalization family `R`.  The bare source law may canonically supply its kinematic
partial realizations, but the Gamma periodic-gauge collision proves that it cannot canonically
supply the distinguished effective section.  The pair `(F,R)` should supply partial realization
functors indexed by retained channel subsets.  Write

```text
Fr_F(S) = realization retaining exactly the channels in S.                  (10)
```

The six presently forced directions are:

```text
source action;
polarization;
critical product bornology;
controlled continuation/transport;
distinguished source-effective section;
integral or ramified realization.                                           (11)
```

The maps of the cube are forgetful or localization functors, not arbitrary projections.  Each
vertex carries its own source-specific Postnikov tower of descent and coherence.

> **[CONJECTURE -- NORMALIZED HT FRACTURE-HYPERCUBE EFFECTIVITY.]** There is a
> differential-birationally and Morita invariant construction `Fr_(F,R)` on the maximal
> source-effectively normalized essential image such that:
>
> 1. the full source-effective realization is the homotopy limit of the compatible punctured
>    fracture cube on the essential image of regular source-minimal HT germs;
> 2. the total homotopy fibre is the interaction spectrum of partial realizations invisible on
>    every proper face;
> 3. its Postnikov groups are the successive joint-effectivity obstructions;
> 4. maximal vertical Kolchin growth and thin source-relative amplitude characterize the
>    source-effective essential image;
> 5. a distinguished effective point reconstructs the pointed analytic germ, rather than storing
>    the germ or its divisor as input;
> 6. analytic, monodromy, spectral, polarized, and integral realization functors are jointly
>    conservative on that essential image.

This is the precise higher-level meaning of

```text
hypertranscendence = infinite algebraic capacity concentrated on a thin constraint boundary.
```

The capacity is the maximal vertical observable growth.  The thin boundary is the source-relative
fracture diagram.  The constraint on hypertranscendental functions is the requirement that their
partial realizations glue to an effective point of this diagram.

## Elliptic gamma is the first pointed analytic fracture object `[PROVED ON PAPER]`

The irrational elliptic gamma function already has two independently constructed anomaly faces.

1. Its translation multipliers are differential-algebraic, but their compatible primitive is
   hypertranscendental.  This gives a nonzero DA-filtered class killed by meromorphic realization.
2. The gamma-function family is a meromorphic section of a nontrivial Hermitian holomorphic gerbe,
   whose Dixmier--Douady class generates the fibre class of the triptic curve.

Felder--Henriques--Rossi--Zhu already place the gamma family in a group--Cech double complex.  Their
degree-one meromorphic cochain `s_Gamma` has coboundary `phi` whose components are exponentials of
rational functions.  Therefore `phi` lies not only in the holomorphic-unit coefficient complex but
in its intersection with the differential-algebraic coefficient complex.

The resulting relative class

```text
[s_Gamma] in H^1(C_M/C_(DA intersection O))
```

is nonzero: its connecting class maps to the gamma-gerbe class, whose Dixmier--Douady image is the
generator on a generic triptic fibre.  The source pointing selects the standard wedge component,
which is the actual irrational elliptic gamma function and carries the independently nonzero DA
translation anomaly.  Both anomalies become coboundaries in the same ambient meromorphic theory.

Thus one pointed cochain produces two nonzero anomaly faces in different coefficient directions
and different cohomological degrees.  They are not asserted equal; common origin and simultaneous
ambient effectivity are the comparison.  See
`../2-fully-proven/new_scientific_knowledge/irrational-elliptic-gamma-pointed-bi-anomaly-fracture.md`.

## What constrains a hypertranscendental function `[CONJECTURE]`

The elliptic-gamma theorem suggests a more precise founding law than “constraint, not flow.”  The
function is an ambient primitive whose source coboundary lands in a much thinner coefficient
category, while the primitive itself cannot descend to that category.

> **[CONJECTURE -- THIN-BOUNDARY RELATIVE-COHOMOLOGY PRINCIPLE.]** Every regular source-minimal
> constrained HT germ `F` has a minimal pointed ambient cochain `s_F` and a source-canonical thin
> coefficient object `A_F` such that
>
> ```text
> D s_F lies in A_F,
> [s_F] is nonzero in H^q(C_ambient/C_A_F),                 (17)
> ```
>
> maximal vertical Kolchin growth is concentrated in the choice of ambient primitive, while the
> source boundary `D s_F` has finite/perfect source-relative amplitude.  Conversely, effective
> maximal-growth pointed classes of the form `(17)` reconstruct the source-minimal analytic germ.

For Euler gamma, `s_F` is a degree-zero function and its shift boundary is algebraic.  For the
irrational elliptic gamma object, `s_F` is the pointed degree-one group--Cech cochain and its
boundary is simultaneously holomorphic and DA.  In both cases hypertranscendence is not absence of
a law.  It is the nontriviality of the relative primitive class under a very thin source boundary.

This gives an exact interpretation of “infinite algebraic capacity concentrated on a thin
constraint boundary”: infinite capacity belongs to the non-descending primitive; thinness belongs
to its source coboundary.

The source-minimality clause is essential.  Without it one can manufacture an artificial complex
whose differential sends any chosen function to a prescribed boundary.

> **[NO-GO -- UNPOINTED RELATIVE COHOMOLOGY.]** A bare relative class does not identify the source
> component that carries the observable anomaly.  The elliptic-gamma construction needs its
> framing and standard-wedge pointing to recover the DA edge.

> **Positive successor.** The unified object is a pointed relative cochain in a source-canonical
> fracture hypercube, not an unpointed cohomology class.

## Natural all-depth model: transverse multiple-gamma constraint height `[PROVED]`

The multiple elliptic gamma hierarchy supplies a much stronger natural cubical model than the
abstract three-submodule example.  Let `Psi_r` be the logarithmic derivative of the generic
order-`r` multiple elliptic gamma function with `r+1` structural parameter translations, and put

```text
R_tau=C[t_0^(+-1),...,t_r^(+-1)],
x_j=t_j-1.
```

The exact theorem already proved in the corpus is

```text
Ann_DA(Psi_r)
 = I_r
 = < product_(j in J) x_j : |J|=r >.                       (18)
```

Equivalently, for an iterated structural difference

```text
D_m=product_j Delta_(tau_j)^(m_j),
```

one has

```text
D_m Psi_r is DA  iff  #{j:m_j>0} >= r.                     (19)
```

The total number of iterations is irrelevant.  Repeating one direction arbitrarily often remains
HT.  What matters is transverse support: the number of distinct source directions coupled by the
observable.

This gives a decisive no-go and positive law.

> **[NO-GO -- LINEAR OR TEMPORAL DEPTH.]** Hypertranscendental constraint depth is not the number
> of repeated evolution steps.  No amount of iteration in fewer than `r` directions reaches the DA
> sector.

> **Positive theorem.** The complete constant-coefficient constraint object is the squarefree
> cubical ideal `(18)`.  The cyclic structural module is
>
> ```text
> R_tau.[Psi_r] ~= R_tau/I_r,                               (20)
> ```
>
> the localized Stanley--Reisner ring of the `(r-2)`-skeleton on `r+1` vertices.

Thus the slogan “infinite capacity on a thin boundary” is literal in a natural analytic hierarchy:
all faces using fewer than `r` independent directions remain hypertranscendental, while every
`r`-direction transverse face lands in DA.  The source constraint is a skeleton, not a clock
trajectory.

Equation `(18)` also gives the first exact source-specific fracture-collapse law.  The abstract
fracture complex need not be exact universally, but the multiple-gamma source specifies exactly
which cubical faces vanish modulo DA and which carry irreducible HT information.  See
`../2-fully-proven/new_scientific_knowledge/multiple-elliptic-gamma-transverse-constraint-depth.md`.

## Exact correction: HT is not a descent obstruction `[PROVED]`

The coordinate-facet ideals of the squarefree module satisfy the finite distributivity law

```text
J_F + intersection_G J_G = intersection_G (J_F+J_G).      (21)
```

Lean now proves that every pairwise-compatible finite facet packet has one global polynomial
representative, unique modulo the Stanley--Reisner ideal.  The full augmented facet complex is
exact by a monomialwise simplex contraction, and localization preserves this exactness.

Combining this with `(18)`--`(20)` gives a natural analytic separation theorem:

> **HT--DESCENT ORTHOGONALITY.** The generic multiple-gamma structural HT module has complete
> effective facet descent, while arbitrary iteration in fewer than `r` source directions remains
> hypertranscendental.  Hypertranscendence can live in global sections of an exact constraint
> sheaf; it is not intrinsically a failure of gluing or a nonzero higher Cech class.

This falsifies the strongest reading of the fracture proposal.

```text
[NO-GO] the fracture cube or its unpolarized cohomology is itself the unified HT obstruction;
[POSITIVE] the cube reconstructs the ambient primitive class, and the remaining obstruction is
           incidence with the enriched source-effective locus.                              (22)
```

Let `V_F` be the ambient primitive object, `Prim_F` the affine torsor fixed by the source boundary,
and `A_F` the source-built pointed, polarized, controlled, integral admissible object.  The refined
common obstruction object is

```text
Inc_F=A_F times^h_(V_F) Prim_F.                            (23)
```

The fracture hypercube presents the inputs and computes kinematic descent.  Empty incidence,
multiple components, stabilizers, and higher homotopy of `(23)` distinguish failure of existence,
noncanonicity, monodromy, and higher coherence.  This is the same primitive-incidence object
independently forced by the pointed polarized critical-Tate coupling program; the present result
localizes where it must enter and prevents a second competing foundational object.

## First exact incidence computation `[PROVED + LEAN]`

The finite linearized theory now computes `(23)`, rather than merely naming it.  Let `J_i<=M` be
the finite channels, put

```text
K_s=intersection_(i in s) J_i,                             (24)
```

and let `c:M->N` be a source calibration.  Suppose `a` is one common representative of the local
packet and `n in N` is the prescribed pointing.  Define

```text
omega_c(x,n)=[n-c(a)] in N/c(K_s).                         (25)
```

Lean proves that `(25)` is independent of `a` and that

```text
Inc_c(x,n) is nonempty  iff  omega_c(x,n)=0,
if nonempty, Inc_c(x,n) is a torsor under K_s intersection ker(c).   (26)
```

Thus existence failure and boundary noncanonicity are literally the cokernel and kernel of the
same restricted calibration map

```text
K_s --c--> N.                                              (27)
```

If `(27)` is surjective and injective, every compatible packet and every pointing have one unique
effective lift.  This is the first exact resolution theorem for the unified incidence object.

> **[CONJECTURE -- NORMALIZED HT INCIDENCE-INDEX PRINCIPLE.]** Every regular source-minimal
> source-effectively normalized constrained HT pair `(F,R)` canonically determines, after
> kinematic fracture descent, a derived calibration morphism
> `kappa_(F,R):K_F->N_(F,R)` from its residual gauge object to its reporter-pointed polarized controlled integral
> target.  The unified obstruction is the derived fibre of `kappa_F` over the source pointing.
> Its degree-zero obstruction is the nonlinear replacement of `coker(kappa_F)`, its automorphisms
> are the replacement of `ker(kappa_F)`, and its higher homotopy records interaction and descent
> coherence.  Natural analytic, Hermitian, spectral, bornological, and integral obstruction
> theories are conservative realizations of this one derived calibration cone.

The statement is falsifiable.  It fails if a natural normalized HT obstruction survives while
every reporter-compatible realization of the calibration cone is contractible, or if two
inequivalent normalized HT germs have equivalent pointed cones.  Standard kernel--cokernel algebra
and derived fibres are parent theory; the candidate-new claim is the normalized HT construction,
reconstruction, and joint conservativity.  No canonical reconstruction from bare source syntax is
claimed.

## Polarized incidence has three phases `[PROVED + LEAN]`

The kernel--cokernel calculation is still linear and unpolarized.  Let `C` now be the closed proper
cone of admissible positive source corrections in a Hilbert realization, let `f` be the continuous
calibration map, and let `b` be the target defect.  Positivity asks whether

```text
b belongs to f(C).                                         (28)
```

Lean proves the exact trichotomy:

```text
I.   b in f(C):                  an effective positive lift exists;
II.  b in closure(f(C))\f(C):    positive lifts exist cofinally but are not attained;
III. b notin closure(f(C)):      a strict dual-cone certificate detects failure.    (29)
```

Phase II is load-bearing.  Farkas duality gives

```text
b in closure(f(C))
  iff every continuous dual-cone reporter is nonnegative on b.             (30)
```

Therefore every continuous positivity test can pass while no positive source-effective lift
exists.  A cofinal sequence of actual positive finite lifts proves only phase I or II; closedness
of `f(C)`, compactness, coercivity, or another attainment theorem is required to exclude II.

```text
[NO-GO] all finite or continuous dual positivity tests imply positive effectivity;
[POSITIVE] they imply weak incidence, and closed-image attainment promotes weak to exact.
```

> **[CONJECTURE -- CRITICAL CLOSURE-DEFECT PRINCIPLE.]** In a regular constrained HT source, the
> source-sign obstruction and the critical all-scale obstruction are different phases of the same
> polarized incidence map.  A negative Weil/Hankel/Herglotz/spectral reporter is a phase-III dual
> certificate.  Cofinal finite positivity without a critical source state is phase-II nonattainment.
> Spectral incompleteness is the same closure defect seen as nonclosed operator range.  A genuine
> source producer proves phase I by constructing a lift or proving the relevant image closed.

This is stronger than saying that several criteria are equivalent to positivity.  It predicts a
single source-built cone map, locates each obstruction relative to its image and closure, and
identifies the additional theorem that resolves the middle phase.  It is falsified if the natural
RH-chain realizations cannot be compared to one source cone map or if their critical obstruction
persists after that map is proved closed and exact.

## Physical-character comparison and the completion interaction `[PROVED BRIDGE + OPEN FACE]`

The multiple-Gamma chart now supplies a genuine two-realization comparison.  The exponential mode
`E_lambda(z)=exp(lambda z)` has been constructed inside the global meromorphic fraction field, and
Lean proves for every source-labelled coface

```text
product_(j!=i)(T_(tau_j)-1)E_lambda
  =product_(j!=i)(exp(lambda tau_j)-1)E_lambda.             (30a)
```

Consequently the DA physical characteristic boundary is exactly the locus on which all genuine
meromorphic source cofaces kill `E_lambda`.  Under rational independence their common degeneracy
spectrum is the single central character.  This closes a real comparison edge of the fracture
chart; see
`../3-formalized/not_new_scientific_knowledge/multiple-gamma-da-meromorphic-physical-character-comparison.md`.

The same source exhibits the next interaction obstruction.  Every finite nonzero period-mode
restriction is invertible, while the complete rank-three period-incidence operator has nonclosed
range.  More precisely, Lean now proves that the complete period-incidence representation admits
a continuous left inverse exactly when the embedded integral period group is discrete.  Thus
exactness of every physical character fibre does not imply exactness after the source-forced
critical completion.

```text
[NO-GO] fibrewise comparison exactness implies uniform source effectivity;
[POSITIVE] the remaining class is the defect of commuting physical-character base change with
           critical completion.                            (30b)
```

For a source constraint complex `C_F`, physical character germ `chi_F`, and source-forced
completion `Comp_F`, the proposed interaction object is

```text
BCDef_F=cofib(
  L chi_F^*(Comp_F C_F)
    -> Comp_F(L chi_F^* C_F)).                              (30c)
```

Derived completion and base-change defects are parent mathematics.  The candidate-new obligation
is to construct `Comp_F` from the embedded HT source, prove `(30c)` presentation invariant, and
show that one natural analytic nonattainment obstruction is exactly a realization of `BCDef_F`.
Without those steps `(30c)` is only a typed open face of `(23)`, not a discovery claim.

## Osculation/effectivity fracture `[PROVED; LEAN-FORMALIZED]`

The physical-character comparison has a second independent filtration which completion alone does
not see.  For a quadratic binomial source constraint

```text
F(lambda)
 =(exp(a lambda)-1)(exp(b lambda)-1)
  -(exp(c lambda)-1)(exp(d lambda)-1),                    (30d)
```

Lean proves the exact phase law

```text
ab!=cd                                      -> ord_0 F=2,
ab=cd, ab!=0, a+b!=c+d                     -> ord_0 F=3.  (30e)
```

Thus matching tangent products cancels the quadratic jet, while the first unmatched symmetric
moment produces tangency excess one.  The Hankel conic on the source
`(1,alpha,alpha^2)` realizes the second phase: its cubic jet is
`-3 alpha^2(alpha-1)^2`.

More importantly, one rationally independent rank-three source supports both an exact order-two
quadratic constraint and this exact order-three Hankel constraint, while its complete
period-incidence representation has no continuous left inverse.  Therefore the global effectivity
phase does not determine local physical osculation.

```text
[NO-GO] the common obstruction is one scalar defect or one unfiltered derived class;
[POSITIVE] the conservative source object is at least bifiltered by
           global effectivity x local physical osculation.             (30f)
```

The source fracture object `(23)` must therefore retain the physical arc-contact Rees filtration
as part of its constraint incidence, alongside the critical bornological filtration.  The new open
interaction is not merely whether base change commutes with completion, but whether the
source-natural comparison between these two filtrations is strict.  See
`../3-formalized/new_scientific_knowledge/quadratic-physical-osculation-effectivity-fracture.md`.

## Physical reversal anomaly `[PROVED; LEAN-FORMALIZED]`

The osculation filtration still does not recover source orientation.  For the complete finite
physical defect product

```text
G_tau(z)=product_i(exp(tau_i z)-1),                         (30g)
```

Lean proves

```text
G_(-tau)(z)=(-1)^r exp(-(sum_i tau_i)z) G_tau(z).           (30h)
```

The multiplier in `(30h)` is an involutive reversal cocycle.  Moreover,

```text
G_tau(z)=exp((sum_i tau_i)z/2) product_i 2sinh(tau_i z/2),  (30i)
```

which separates the oriented first-moment character from the centered self-dual factor.  If `r`
is even and `sum_i tau_i=0`, the two opposite source orientations have identical complete analytic
physical germs.  Consequently support, multiplicity, contact filtration, and every functorial
derived topology built from that germ are simultaneously blind.

This has now been extended to every componentwise sign-surgery mask.  Lean constructs the exact
multiplier and proves its XOR composition law, so the anomaly is a genuine cocycle for the source
orientation groupoid.  The remaining object is the torsor classified by that cocycle together with
a reporter-compatible trivialization on the source-effectively normalized stratum.  The bare source
cannot choose this point: `Gamma` and `exp(2 pi i z)Gamma` have the same unit-shift constraint and
regular pointing.

```text
[NO-GO] orientation is recoverable by enriching the unlabelled physical germ;
[POSITIVE] orientation is a normalized source-equivariant lift carrying the explicit reversal
           anomaly, with conservativity gated by
           K^S intersect intersection_r ker(R_r)={0}.                      (30j)
```

Thus polarization is not another invariant extracted from the derived characteristic carrier.  It
is candidate reporter-normalized equivariance/trivialization data over the source groupoid.  See
`../3-formalized/new_scientific_knowledge/physical-defect-orientation-anomaly.md`.

## Normalized gauge fibre `[PROVED LINEAR GATE + TYPED OPEN LIFT]`

The Gamma periodic-gauge collision forces a correction to the whole reconstruction program.  A
bare source constraint determines a solution torsor, not a canonical analytic germ.  Even one
regular value and every fixed finite jet can leave a nontrivial source-fixed gauge.

For an additive reporter family `R=(R_r)`, Lean proves the exact gate

```text
Obs_R injective
  iff G_(F,R):=K^(S_F) intersect intersection_r ker(R_r)={0}.       (30k)
```

A nonzero member of `G_(F,R)` is an explicit joint-nonconservativity witness.  Multiplicatively,
the normalized solution fibre is a torsor under the gauges preserving the normalization and is a
singleton exactly when that stabilizer is trivial.

```text
[NO-GO] a bare source canonically generates its effective section or polarization;
[POSITIVE] reconstruction is exact on the maximal source-effectively normalized stratum cut out
           by the joint-fixed common-kernel condition.                     (30l)
```

This changes the candidate unified object from a single source-assigned point to a **stack of
normalized effective lifts** over the kinematic fracture cube.  Its automorphism group at `(F,R)`
is the typed nonlinear replacement of `G_(F,R)`; its existence obstruction is the corresponding
cokernel/higher interaction class.  The open Fields-scale theorem is to construct this stack for
natural HT sources and prove that the analytic, Hermitian, spectral, bornological, monodromy, and
integral reporters are jointly conservative on its normalized essential image.  See
`../5-failed/universal-bare-source-effectivity-reconstruction.md` and
`../3-formalized/not_new_scientific_knowledge/joint-source-realization-common-kernel-criterion.md`.

## Gauge-attainment complementarity `[PROVED; LEAN-FORMALIZED]`

The normalization and bornological faces are not merely independent.  They are driven in opposite
directions by the same period-closure phase.  For every integral submodule `L<=C`, Lean proves

```text
period-incidence for L has no continuous left inverse
  -> every global meromorphic L-fixed gauge is constant,                  (30m)

there exists a nonconstant global meromorphic L-fixed gauge
  -> period-incidence for L has a continuous left inverse.                (30n)
```

Together with continuous left invertibility iff `L` is discrete, this gives

```text
nondiscrete source: automatic meromorphic gauge rigidity + global incidence nonattainment;
discrete gauge ambiguity: uniform incidence attainment.                    (30o)
```

The Gamma and irrational-triptic sources occupy opposite endpoints.  Densifying a source removes
periodic boundary noncanonicity by producing arbitrarily small periods, and those same periods
destroy the uniform inverse.  Therefore source enrichment cannot monotonically solve both
obstructions.

```text
[NO-GO] densification simultaneously removes gauge ambiguity and preserves uniform attainment;
[POSITIVE] gauge rigidity and global attainment are complementary phases of one period-closure
           object, requiring phase-specific normalization or completion producers.            (30p)
```

See
`../3-formalized/new_scientific_knowledge/period-gauge-attainment-complementarity.md`.

## Candidate unified object: normalized anomaly-fracture stack `[CONJECTURE]`

The exact results now force a more precise object than the original phrase “derived incidence
space.”  For a source-effectively normalized pair `(F,R)`, let

```text
G_(F,R)  = residual joint-fixed gauge invisible to all reporters,
L_(a_F)  = line/torsor classified by the physical orientation-anomaly cocycle,
kappa_(F,R)^(p,q) = calibration map in
                     osculation degree p and effectivity degree q.          (30q)
```

The candidate obstruction object is the anomaly-twisted bifiltered derived fibre

```text
U_(F,R)^(p,q)
  =hofib_(b_(F,R)^(p,q))(kappa_(F,R)^(p,q); L_(a_F)).       (30r)
```

This notation is a typed research target, not an existing construction.

> **[CONJECTURE -- NORMALIZED ANOMALY-FRACTURE PRINCIPLE.]**  On the maximal
> source-effectively normalized HT essential image, the different obstruction classes are
> conservative realizations of `(30r)`:
>
> - its automorphism object is the typed nonlinear joint-fixed common kernel;
> - failure of nonemptiness is the calibration/descent obstruction;
> - closure without a point is critical bornological nonattainment or spectral incompleteness;
> - failure of positive real points is the positivity/orientation obstruction;
> - twisting of local fibres is monodromy or noncanonical boundary data;
> - osculation degree records physical contact multiplicity independently of effectivity degree;
> - higher homotopy records genuine multi-face interaction classes.

A source producer theorem does not merely show that one obstruction scalar vanishes.  It proves
that the critical self-dual bidegree of `(30r)` has a reporter-compatible positive point with
trivial automorphism group and the required integral/ramified lift.

The Gamma collision prevents deleting `R`; gauge-attainment complementarity forces normalization
and critical completion to vary oppositely with period closure; the osculation/effectivity fracture prevents collapsing
`(p,q)` to one filtration; the reversal-blind locus prevents deleting `L_(a_F)`; and the
three-channel interaction example prevents replacing the derived fibre by pairwise compatibility.
Each constituent is therefore forced by a separate exact no-go.

Derived fibres, quotient stacks, anomaly lines, Rees filtrations, and kernel/cokernel sequences are
parent mathematics.  Candidate novelty can begin only with a presentation-invariant HT
construction of `(30r)`, a natural nontrivial analytic realization, and a transferred theorem that
is unavailable in the parent realizations separately.

## Unified explanation of the RH-chain obstructions `[CONJECTURE; PRESSURE TEST ONLY]`

The 26 proof chains in the obstruction report typically construct one face or one edge of a
putative source object and then ask that face to determine the global lift.  The exact no-gos show
why this repeatedly fails:

| Report obstruction | Fracture interpretation |
|---|---|
| source sign/orientation | phase-III separation from the positive image, detected by a dual reporter |
| critical all-scale estimate | phase-II closure-only nonattainment at the critical bornology |
| spectral/determinant realization | missing realization map or nonclosed-range phase II |
| arithmetic multiplicity | missing integral/ramified lift |
| non-circular comparison | face data do not descend from one source-pure common lift |
| missing typed bridge | a required edge or higher comparison map of the cube is absent |
| algebraicity/rigidity | the integral lift misses its arithmetic essential image |

The multiple-gamma collapse shows that “missing common lift” is still too narrow: an ambient common
lift may exist uniquely while no enriched source-effective realization exists.  The conjectural
common obstruction is therefore not one scalar or merely one Cech class.  It is the derived
incidence space `(23)` between the reconstructed primitive and the simultaneously positive,
integral, critical, controlled, source-pointed locus.  Different chains see different realization
shadows of the same incidence problem.

> **[CONJECTURE -- COMMON SELF-DUAL DEGENERACY SPECTRUM; NOT RH.]** If a completed-zeta fracture
> object is constructed entirely from prime and archimedean source data, its critical zeros are the
> common self-dual degeneracy support of the distinguished effective section under the jointly
> conservative realizations.  Spectral incompleteness, continuation failure, positivity failure,
> monodromy, and noncanonical boundary conditions are then different face obstructions to the same
> lift.

This statement neither constructs the zeta object nor proves positivity, effectivity, or RH.  Its
value is a falsifiable architecture: a genuine zeta construction must type all relevant faces and
their comparisons before it may use the zero divisor.

## Strong predictions

1. **Descent before selection.** Exact reconstruction of the ambient primitive does not imply
   enriched source effectivity.  Natural HT sources can be Cech-acyclic and still have nontrivial
   polarization, bornology, integral, or pointing incidence.
2. **Interaction-before-orientation.** A source sign theorem can fail even after every pairwise
   analytic comparison is closed, because the remaining class may live in a higher interaction
   group rather than on the polarization edge itself.
3. **Source-specific descent height.** No universal finite truncation exists, but particular
   source laws can force a sharp transverse face threshold.  The multiple elliptic gamma hierarchy
   proves that this threshold is squarefree support width, not iteration order.
4. **Producer theorems are incidence theorems.** A useful source producer will simultaneously
   improve more than one obstruction face because it places one reconstructed primitive in the
   coupled admissible locus, not because several RH criteria were restated as equivalent.
5. **Critical failure is often nonattainment, not negativity.** Cofinal positive finite states and
   nonnegative dual reporters need not produce a critical state.  A closed-image or compactness
   theorem is an independent source law.
6. **Anomaly coupling precedes positivity.** Positivity cannot be added at the end.  It is a
   reduction of a globally effective fracture point and can be obstructed by non-polarization
   interaction classes.
7. **Zeros are outputs of a normalized section.** A carrier, topology, determinant line, or
   spectral category can be complete while the bare source leaves a gauge torsor of possible
   sections.  Degeneracy belongs to the reporter-normalized distinguished section in the full
   stack.
8. **No scalar master obstruction.** The same nondiscrete source can carry different physical
   contact orders.  Obstruction classes must be bidegree-sensitive: effectivity and osculation are
   independent axes whose interaction, rather than either marginal invariant, is the candidate
   common object.
9. **Orientation is equivariant lift data.** Even the complete physical analytic germ can be
   reversal-blind.  A sign-sensitive producer must carry and trivialize the source reversal
   anomaly; no derived refinement of the unlabelled germ can substitute for that lift.

## Parent theory and external novelty boundary

The following are parent mathematics and are not novelty claims:

- the Chinese remainder and Mayer--Vietoris exact sequence `(2)`;
- Cech complexes of subobjects and non-distributive subobject lattices;
- homotopy limits, total fibres, Bousfield localizations, and chromatic fracture cubes;
- Postnikov towers, obstruction theory, gerbes, and descent;
- systems of realizations, comparison torsors, and Tannakian reconstruction.
- Farkas duality, weak infeasibility, facial reduction, and nonclosed linear images of proper
  cones.

Primary parent checks include the gamma-gerbe construction of
Felder--Henriques--Rossi--Zhu, the general chromatic fracture cube of
Antolin-Camarena--Barthel, and symmetric monoidal fracture-square reconstruction of
Naumann--Pol--Ramzi.  Morain's 2025--2026 geometric multiple-elliptic-gamma theory already extends
the Bernoulli-rational coboundary architecture to higher-rank lattices; that extension is parent
mathematics, not evidence for novelty here.  Exact searches did not locate a source-canonical
fracture cube for hypertranscendental functions, a DA-filtered/holomorphic elliptic-gamma
bi-anomaly, a source-calibration incidence cone for HT functions, or an essential-image
reconstruction theorem coupling the six channels in `(11)`.  A new exact search for
hypertranscendental derived incidence, reconstruction, polarization, and kernel--cokernel
calibration found ordinary HT closure results such as Huang--Ng
(`https://arxiv.org/abs/2007.10037`) and unrelated derived obstruction theories, but no equivalent
of the incidence-index principle.  Liu--Pataki (`https://arxiv.org/abs/1507.00290`) and
Pataki--Touzov (`https://arxiv.org/abs/2110.11437`) already develop the closure-only phase for
general conic programs; that phase is parent mathematics, not HT novelty.  This is negative search
evidence, not priority certification.

The candidate-new content begins only when the following are proved:

1. the kinematic channels and cube maps are canonically generated by a source-minimal HT
   constraint, while the effective section is selected only on a classified normalized stratum;
2. the total interaction spectrum is presentation invariant;
3. effectivity reconstructs the analytic germ exactly when the normalized joint-fixed reporter
   kernel is trivial;
4. two genuinely different analytic realizations recover their known obstructions from one class;
5. the unified object yields a new analytic theorem not available in either realization alone.

The current algebraic seeds are architecture, not a novelty claim.

## Anti-theatre gate

Retire or enlarge the conjecture if:

1. the six cube directions are manually copied from the RH report rather than constructed from an
   independent HT source law;
2. the cube is a Cartesian product with no compatibility restriction;
3. the total fibre merely renames a list of known anomalies;
4. the source germ, target divisor, or desired sign is stored in a vertex;
5. different source presentations give inequivalent cubes;
6. no natural analytic source realizes a nonzero interaction class;
7. no pair of genuinely different realization functors is proved jointly conservative;
8. an existing fracture, motivic-realization, or twistor category already supplies the claimed
   essential-image theorem unchanged.
9. unpolarized fracture cohomology is called the HT obstruction despite the exact multiple-gamma
   descent theorem.
10. the calibration morphism is chosen to kill the desired obstruction rather than constructed
    functorially from the source;
11. the nonlinear theory merely renames the kernel and cokernel of an arbitrary map without
    proving reconstruction or joint conservativity.
12. closure-only incidence merely renames weak conic infeasibility without constructing a natural
    HT source cone and realization map;
13. finite positivity is called phase II without proving convergence to the critical target and
    failure of exact incidence.
14. a distinguished section, polarization, or anomaly trivialization is claimed to be canonical
    from the bare source despite a surviving normalized joint-fixed gauge.

Every no-go has a positive successor: identify the missing cube direction, compute the residual
interaction quotient, prove the maximal source class on which descent is effective, or exhibit the
additional comparison morphism required for a common lift.

## Fields-scale theorem target

The exact module sequence and three-channel counterexample are not Fields-scale.  A Fields-scale
result would prove the enriched fracture-incidence correspondence for a nontrivial analytic class,
including:

1. a source-canonical and presentation-invariant construction of the kinematic cube plus a
   classification of admissible reporter/normalization families;
2. an intrinsic maximal-growth/thin-amplitude source-effectively normalized essential image;
3. reconstruction of the pointed analytic HT germ from one normalized effective fracture point,
   with the joint-fixed common kernel calculated exactly;
4. calculation of its total interaction spectrum, a source-specific collapse law, and the
   residual enriched incidence object after kinematic descent collapses;
5. construction of the reporter-normalized derived calibration morphism and identification of its
   kernel, cokernel, stabilizer torsor, and higher incidence groups in natural analytic realizations;
6. construction of its polarized source cone and a theorem deciding exact incidence versus the
   closure-only phase at the critical bornology;
7. the elliptic-gamma anomaly bicomplex as a fully typed two-axis analytic model;
8. a nonlinear or nonabelian model with a genuinely higher interaction class;
9. two independently constructed realization functors proved jointly conservative;
10. a new transferred analytic theorem that neither parent realization proves alone.

That theorem would found a genuine field.  The present result identifies the shape of the object
and proves that both a single tower and pairwise compatibility are structurally insufficient.

## Gates

- [x] seven RH obstruction classes treated only as pressure-test faces
- [x] six independent information channels inherited from exact deletion tests
- [x] two-channel common-lift sequence Lean-formalized
- [x] exact ambiguity and compatibility quotient Lean-formalized
- [x] pairwise compatibility proved insufficient for three abelian channels
- [x] exact residual three-channel quotient Lean-formalized
- [x] linear tower corrected to cube directions plus Postnikov height
- [x] nonabelian-only explanation of higher stages falsified
- [x] fracture-cube parent theory identified
- [x] natural all-depth HT fracture module identified in the multiple elliptic gamma hierarchy
- [x] exact squarefree transverse collapse law linked to the fracture architecture
- [x] linear/temporal depth falsified with a nontrivial positive support theorem
- [x] pairwise-to-global coordinate-facet effectivity Lean-formalized
- [x] uniqueness modulo the Stanley--Reisner ideal Lean-formalized
- [x] full coordinate-facet augmented complex proved exact on paper
- [x] failure-of-descent definition of HT falsified by a strong natural positive theorem
- [x] fracture cube corrected from unified object to chart for the derived incidence fibre
- [x] linear calibrated incidence cokernel and kernel Lean-formalized
- [x] unique pointed reconstruction criterion Lean-formalized
- [x] incidence-index principle stated with explicit falsifiers
- [x] exact/closure-only/dual-certificate polarized trichotomy Lean-formalized
- [x] cofinal positive approximation and dual blindness Lean-formalized
- [x] closed-image promotion theorem Lean-formalized
- [x] critical closure-defect principle stated with explicit falsifiers
- [x] genuine DA/meromorphic physical-character comparison Lean-formalized
- [x] fibrewise exact/global nonclosed interaction isolated
- [x] uniform character-effectivity iff period discreteness Lean-formalized
- [ ] construct the source-forced completion and base-change comparison morphism
- [ ] compute the physical base-change/completion defect in one analytic HT source
- [ ] define the full finite-channel augmented fracture complex in Lean
- [ ] formalize its monomialwise chain contraction
- [x] type the elliptic-gamma DA/holomorphic filtered group--Cech complex on paper
- [x] prove the two nonzero anomaly faces have one pointed cochain origin
- [ ] formalize the elliptic-gamma filtered group--Cech theorem in Lean
- [ ] prove presentation invariance in one analytic source class
- [ ] prove two realization functors jointly conservative
- [ ] prove a new analytic theorem by transfer through the common object
- [ ] complete independent specialist novelty and significance audit
