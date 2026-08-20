# The irrational triptic source-effectivity character reconstructs its HT germ

- **ID:** `irrational-triptic-source-effectivity-character`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Type:** ANALYTIC HT RECONSTRUCTION / SYSTEM OF REALIZATIONS / POSITIVE EFFECTIVITY MODEL
- **Scientific status:** `[PAPER PROOF COMPLETE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[LEAN-FORMALIZED ANALYTIC AND CRITICAL CORE] [NOT AN RH RESULT]`
- **Parents:**
  - `irrational-elliptic-gamma-hypertranscendence-matroid.md`
  - `irrational-elliptic-gamma-pointed-bi-anomaly-fracture.md`
  - `multiple-gamma-period-excess-closure-phase-transition.md`
  - `../../3-formalized/not_new_scientific_knowledge/rank-three-meromorphic-source-effectivity-reconstruction.md`
  - `../../3-formalized/source-producer-integral-realization-minimality.md`

## Scope and theorem

Fix `sigma,tau` in the upper half-plane with `1,sigma,tau` linearly independent over `Q`.  Put

```text
H=Z+Z sigma+Z tau,                 E=[C/H].                 (1)
```

This card proves the source-effectivity reconstruction theorem on the regular source-minimal
irrational triptic class.  It does not claim the universal equivalence for every constrained HT
function.

Let `b=(1,Theta_tau,Theta_(sigma|tau))` be the explicit multiplicative boundary constructed from
the source periods by the one-dimensional products in
`EllipticGammaProductSourceEquation.lean`.  Choose a source point `z_*` off the numerator and
denominator divisors and a nonzero value `a_*`.  Define the pointed solution fibre

```text
Sol_*(b,a_*)={x in M(C)^x:
  x(z+v_i)/x(z)=b_i(z), i=0,1,2, and x(z_*)=a_*}.           (2)
```

The **triptic source-effectivity character** is the compatible system

```text
TSEC(b,a_*) =
  ( Sol_*(b,a_*),
    beta_Gamma in H^1(C_M/C_A),
    (G_Gamma,nabla_Gamma,h_Gamma),
    Tr_crit(H\{0}),
    (H -> C, DD_Gamma, D_Gamma in Z[C/H]),
    comparison maps ).                                     (3)
```

Here `C_A=C_O intersection C_DA` is the degreewise intersection coefficient complex on the FHRZ
invariant wedge cover; `(G,nabla,h)` is its Hermitian holomorphic gamma gerbe with connective
structure; `Tr_crit` is the complete divided-difference trace; `DD_Gamma` is the integral
Dixmier--Douady class; and `D_Gamma` is the integral orbit divisor.  The analytic germ is not a
field of `(3)`: it is the unique point observed from the solution fibre `(2)`.

> **[THEOREM -- IRRATIONAL TRIPTIC SOURCE-EFFECTIVITY RECONSTRUCTION.]**
> For the standard elliptic-gamma boundary and standard regular pointing:
>
> 1. `TSEC(b,a_*)` is canonically constructed from the pointed source constraint;
> 2. `Sol_*(b,a_*)` is a singleton whose element is the genuine elliptic-gamma meromorphic germ;
> 3. before pointing, the solution fibre is a `C^x`-torsor, and its morphisms are reconstructed as
>    the unique constant quotients of source solutions;
> 4. the analytic, group--Cech monodromy, critical spectral, Hermitian, and integral realization
>    functors are jointly conservative on this triptic effective stratum;
> 5. the spectral closed-range phase is the image of integral period-rank excess, while the
>    integral Kummer content is not recoverable after complexification.

This is the first complete positive source-effectivity model in the program.  It is an exact
height-one analytic theorem, not the universal all-HT classification conjecture.

## Construction without storing the answer

### Analytic pointing and effectivity

The double products satisfy on their common regular locus

```text
Gamma(z+1)=Gamma(z),
Gamma(z+sigma)=Theta_tau(z) Gamma(z),
Gamma(z+tau)=Theta_(sigma|tau)(z) Gamma(z).                 (4)
```

The boundary products in `(4)` are defined before `Gamma`.  They are obtained by splitting the
double index into its zero face and shifted positive face.  Thus `(2)` is constructed from source
data.

The product gives existence.  If `x,y` solve the same unpointed constraint, `x/y` is fixed by
`1,sigma,tau`.  Its fixed-period subgroup contains `H`; the nondiscrete rank-three period theorem
makes `x/y` constant.  Equality at `z_*` makes that constant one.  Therefore `(2)` is a singleton.
The same argument without the last step classifies every source-preserving morphism by one element
of `C^x`.

### Monodromy and Hermitian transport

Felder--Henriques--Rossi--Zhu construct from the same source periods a degree-one meromorphic
group--Cech cochain `s_Gamma` whose coboundary is exponential-rational, hence lies in both the
holomorphic-unit and DA-meromorphic coefficient complexes.  Its relative class

```text
beta_Gamma=[s_Gamma mod C_A]                                (5)
```

has nonzero connecting class.  The holomorphic image is the gamma gerbe with nonzero
Dixmier--Douady generator; the standard pointed wedge is the analytic solution of `(4)`.  FHRZ
also construct the compatible Hermitian structure and connective data.  Consequently the
monodromy and Hermitian outputs in `(3)` are produced from the same pointed cochain, not attached
after analytic reconstruction.

The differential-character statement used here is parent mathematics: integral characteristic
class, curvature/connective data, and holonomy determine the differential cohomology class through
the standard character diagram.  The source pointing fixes the remaining standard-wedge gauge.

### Critical, spectral, integral, and unbounded structure

For `lambda in H\{0}`, the source collar supplies

```text
nabla_lambda f=(f(z+lambda)-f(z))/lambda
               =integral_0^1 f'(z+t lambda)dt.             (6)
```

The critical trace is the complete `ell^infinity` space of decoded coordinates, realized with

```text
w(lambda)=lambda/(1+|lambda|).                              (7)
```

Every nonzero coordinate is recovered by multiplication by `w(lambda)^(-1)`; its Hermitian phase
has norm one.  The unscaled period embedding `H -> C` remains as a separate integral comparison.

Because `H` has rank three in real dimension two, it is nondiscrete and contains nonzero periods
tending to zero.  Hence the inverse of the raw unweighted incidence is unbounded and its range is
not closed.  The critical norm in `(7)` is therefore load-bearing.  The separate finite facet
descent has Hodge Laplacian `Box_S=n_S id` and uniform gap at least one, so the nonclosed phase is
located precisely in the physical period comparison rather than in kinematic descent.

The multiple-gamma period-excess theorem proves the cross-realization transfer

```text
integral period rank excess r>=1
  iff the physical period subgroup is nondiscrete
  iff the incidence range is nonclosed.                    (8)
```

Thus the spectral closure phase is not a renamed integral invariant: it is an analytic operator
property proved equivalent to integral rank excess.  Conversely the orbit divisor
`D_Gamma in Z[C/H]` retains coefficient divisibility and Kummer content, which disappear after
complexification.

## Joint conservativity proof

Let `u:L->L'` be a morphism between triptic effective characters whose five realization images are
equivalences and whose comparison maps commute.

1. The integral realization identifies the oriented period embedding, the DD class, and the orbit
   divisor, including coefficient multiplicities.
2. The monodromy and Hermitian realizations identify the differential gamma-gerbe class: the
   integral class and curvature determine it up to a flat character, and holonomy removes that
   ambiguity.  The pointed standard wedge identifies the same source component on both sides.
3. The spectral equivalence, together with `(8)`, identifies the completed physical-period
   comparison and prevents replacement by a complexified lattice with the same algebraic span.
4. The analytic realization identifies the explicit boundary `b` and pointed value `a_*`.
   Singleton reconstruction of `(2)` then identifies the meromorphic germ.  The unpointed theorem
   reconstructs its source-preserving scalar morphism, and pointing makes that scalar one.
5. Since `L` is the compatible lift of these faces and every comparison map agrees, the underlying
   cochain, differential character, critical trace, integral lift, and distinguished effective
   section agree.  Hence `u` is an equivalence.

The converse is functorial.  Therefore the five realizations are jointly conservative.

Step 5 uses the universal property of the compatible limit, which is parent category theory.  The
nonformal content is Steps 1--4: the actual source-produced comparison diagram, exact analytic
solution-fibre reconstruction, DA-filtered nonzero cochain, and the integral-to-spectral transfer
`(8)`.

## Why the realizations are genuinely different

The following deletion tests prevent `(3)` from collapsing to five names for one invariant.

1. **Delete analytic pointing:** the same boundary has the full `C^x` solution torsor.
2. **Delete monodromy:** the standard wedge does not determine the higher nonzero gamma-gerbe
   class; the DA and DD anomalies occur in different degrees and target groups.
3. **Delete spectral completion:** every finite period restriction is invertible although the
   full nondiscrete incidence has nonclosed range.
4. **Delete Hermitian transport:** the same unpolarized analytic completion admits distinct signed
   Krein chambers; curvature/holonomy data are not determined by the carrier alone.
5. **Delete the integral lift:** complexification erases coefficient divisibility and the exact
   Kummer root spectrum of `Z[C/H]`.

These witnesses are not all internal deformations of one fixed gamma germ; they establish
necessity on the minimal source class for which `(3)` is intended.  Joint conservativity on the
triptic effective stratum is the positive successor.

## Parent theory and novelty gate

The following are explicitly parent mathematics and are not novelty claims:

- the elliptic-gamma functional equations and `SL_3(Z) semidirect Z^3` automorphy;
- the FHRZ Hermitian holomorphic gamma gerbe and its DD generator;
- differential cohomology character diagrams, curvature, integral class, and holonomy;
- homotopy limits and the fact that their projections are jointly conservative;
- weighted `ell^infinity` spaces and polar decomposition;
- fixed-field uniqueness of functional equations up to constants.

Primary parents include:

- Felder--Varchenko, *The elliptic gamma function and SL(3,Z) x Z^3*,
  https://arxiv.org/abs/math/9907061;
- Felder--Henriques--Rossi--Zhu, *A gerbe for the elliptic gamma function*,
  https://arxiv.org/abs/math/0601337;
- Simons--Sullivan, *Axiomatic Characterization of Ordinary Differential Cohomology*,
  https://arxiv.org/abs/math/0701077;
- Amabel--Debray--Haine, *Differential Cohomology*,
  https://arxiv.org/abs/2109.12250.

The candidate-new result is the HT-specific conjunction: the DA-filtered pointed gamma cochain,
the exact irrational triptic solution-torsor reconstruction, the critical physical-period
completion, the integral orbit-divisor/Kummer lift, and transfer `(8)` assembled into one
source-produced conservative character without storing the germ.

- `[ANTI-THEATRE -- PASS PROVISIONAL]` Joint conservativity is not claimed from the limit alone;
  the source-produced inhabitant, analytic observation theorem, and integral--spectral transfer
  are proved separately.
- `[NOVELTY -- PROVISIONAL PASS]` Searches found the parent components but no DA-filtered,
  critically completed, integral source-effectivity character with the reconstruction theorem
  above.  This needs specialist review.
- `[SIGNIFICANCE -- PASS FOR A MAJOR THEOREM]` The theorem gives the first positive analytic model
  of the six-channel HT architecture and reconstructs an actual HT germ and its morphisms.
- `[FIELDS VERDICT]` This is not yet the universal Fields-scale classification.  That requires
  extension beyond the triptic stratum and an intrinsic essential-image theorem for general
  regular source-minimal HT germs.
- `[RH BOUNDARY]` No zeta source object, zero divisor, positivity theorem, or RH conclusion is
  used or obtained.

## Lean boundary

Lean formalizes unconditionally:

- the complete period-one elliptic-gamma source equation and the zero/successor factor identities
  underlying the two structural product reindexings;
- the rank-three commuting difference-differential field and its constant joint-fixed field;
- classification of equal multiplicative boundaries by one nonzero constant;
- regular-point analytic reconstruction and the subsingleton pointed solution fibre;
- specialization to the actual elliptic-gamma meromorphic product;
- the complete critical period trace, its injective realization, explicit inverse, and unit phase;
- the finite facet Clifford square and uniform Hodge seed;
- the integral algebraic Kummer core and period-incidence closure phase.

Lean does not yet formalize the FHRZ group--Cech complex, differential gamma gerbe, or the typed
five-face homotopy limit.  No such result is inserted as an axiom.

## Gates

- [x] boundary constructed without the elliptic-gamma germ
- [x] effectivity realized by the actual convergent product
- [x] unpointed solution torsor and source morphisms reconstructed
- [x] pointing proved to select one analytic germ
- [x] DA and monodromy faces produced from one pointed gamma cochain
- [x] Hermitian connective data identified from the same parent cochain
- [x] critical complete trace constructed with explicit inverse
- [x] raw unbounded/nonclosed period phase retained
- [x] integral orbit divisor and DD class retained
- [x] integral period excess transferred to spectral closed-range failure
- [x] joint conservativity proved on the compatible triptic effective stratum
- [x] five deletion tests recorded
- [x] differential-cohomology and limit-theory parent collision explicit
- [ ] global analytic-subring packaging of the source boundary in Lean
- [x] whole-product `sigma` and `tau` source equations packaged in Lean
- [ ] FHRZ/differential-character comparison formalized in Lean
- [ ] independent specialist proof and novelty audit

## Scope clarification: fibrewise effectivity versus source-frame reconstruction

The source-effectivity theorem is a theorem for the **standard oriented triptic boundary and
pointing**.  It does not say that the common orbit divisor or the DA-relative conormal module alone
reconstructs that source frame.

The finite-marker stabilizer theorem now proves why the larger TSEC package is load-bearing.  A
common divisor on `C/H` can recover `H` only up to its finite stabilizer and forgets a decomposition
of `H` into the two labelled elliptic faces.  The typed pre-pushforward boundary divisors recover the
faces on their aperiodic stratum; the oriented period embedding and gerbe data supply information
that no subgroup-level marker can recover because `Zq=Z(-q)`.

Thus this card remains a positive fibrewise effectivity model.  The new open problem is horizontal:
prove that such models assemble functorially over changes and degenerations of source frame, rather
than assuming the standard frame as part of the input.  See
`../../1-in-progress/hypertranscendental-stabilizer-enriched-realization-stack.md`.

## Lean progress — the whole-product source equations are closed

The gate "whole-product `sigma` and `tau` source equations packaged in Lean" is met.
`GaloisForLFunctions.HTGeometry.EllipticGammaProductSourceEquation` proves both, unconditionally
and axiom-clean (`[propext, Classical.choice, Quot.sound]`), for the genuine convergent double
product and not for a formal surrogate:

```text
ellipticGammaProduct_add_sigma :
  0 < im sigma, 0 < im tau, and the backward product nonzero at z
    ==>  Gamma(z + sigma) = Theta_tau(z) * Gamma(z)
ellipticGammaProduct_add_tau :
  same hypotheses
    ==>  Gamma(z + tau) = Theta_sigma(z) * Gamma(z)
ellipticGammaForwardProduct_add_one, ellipticGammaBackwardProduct_add_one :
  exact period one
```

The nonvanishing hypothesis is the regular locus: the identity is an identity of meromorphic
functions and the two sides are compared where the backward product does not vanish.  The
supporting reindexings `ellipticGammaForwardProduct_add_sigma`,
`ellipticGammaBackwardProduct_eq_boundary_mul_add_sigma` and their `tau` counterparts are proved in
the same module.

The remaining Lean gates of this card are the global analytic-subring packaging of the source
boundary and the FHRZ/differential-character comparison.

## Lean progress 2026-08-20 — the global analytic-subring packaging of the source boundary is closed

The gate "global analytic-subring packaging of the source boundary in Lean" is met.
`GaloisForLFunctions.HTGeometry.EllipticGammaThetaBoundaryAnalytic` (wired, `lake build` green,
`#print axioms = [propext, Classical.choice, Quot.sound]`) proves that both structural boundaries

```text
Theta_tau(z)      = ∏_k (1 − q^(k+1)/x(z)) · ∏_k (1 − q^k x(z)),
Theta_(sigma|tau)(z) = ∏_j (1 − p^(j+1)/x(z)) · ∏_j (1 − p^j x(z))
```

converge locally uniformly on the whole plane, hence are **entire**, packages them in the global
analytic germ ring, and restates the three source equations as unconditional identities in the
meromorphic germ field:

```text
hasProdLocallyUniformlyOn_ellipticGammaForwardBoundaryFactor
hasProdLocallyUniformlyOn_ellipticGammaBackwardBoundaryFactor
    normal convergence of each single q-Pochhammer boundary product on every compact set
differentiable_ellipticGammaMultiplicativeThetaBoundary
differentiable_ellipticGammaMultiplicativeThetaBoundaryTau
    both boundaries are entire
entireAnalyticElem, ellipticGammaThetaBoundaryAnalytic(Tau), ellipticGammaThetaBoundaryMero(Tau)
    the boundaries as elements of `analyticSubring ℂ` and of `meroField ℂ`
ellipticGammaMero_add_sigma :  T_sigma Gamma = Theta_tau · Gamma
ellipticGammaMero_add_tau   :  T_tau   Gamma = Theta_(sigma|tau) · Gamma
ellipticGammaMero_add_one   :  T_1     Gamma = Gamma
```

The last three are exactly `(4)` **with no regular-locus hypothesis**: the nonvanishing clause of
`ellipticGammaProduct_add_sigma`/`_add_tau` disappears because the identity is now an identity of
germs in a field, the denominator germ being nonzero as a germ
(`ellipticGammaBackwardAnalytic_ne_zero`).  The boundary is still constructed *before* the gamma
product — from the source periods alone — so the card's "construction without storing the answer"
discipline is preserved.

### Corpus audit: the FHRZ layer is not absent

The Lean-boundary paragraph above is out of date on its second point.  The tree already owns

```text
GroupCechBicomplex                     the group–Čech total complex of φ : G →* H,
                                       totalD2_totalD1, totalD3_totalD2, sector restrictions
GammaGerbeDixmierDouadyGenerator       coboundary₁/₂/₃ on the triptic lattice, the DD cocycle
                                       gammaGerbeDD, coboundary₃_gammaGerbeDD = 0, and the
                                       alternation obstruction killing every coboundary
GammaGerbeThetaCocycle                 FHRZ's thetaProd_cocycle,
                                       thetaProd_defect_eq_gammaGerbeExponent, and
                                       coboundary_gammaGerbeExponent_not_coboundary —
                                       the gamma gerbe has no holomorphic trivialisation
CechLowDegreeComplex, CechFineAcyclicModule
```

so the remaining Lean gate of this card is the *differential-character comparison* itself, not the
group–Čech complex or the gerbe class.
