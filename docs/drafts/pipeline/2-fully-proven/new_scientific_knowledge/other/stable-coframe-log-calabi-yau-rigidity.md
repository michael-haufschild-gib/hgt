# A full stable velocity coframe forces a logarithmic Calabi--Yau horizon

- **ID:** stable-coframe-log-calabi-yau-rigidity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) + Lean-formalized local core
- **Source:** differential-tail converse via rational eigenvolume
- **Statement:** If a finite int-amplified endomorphism of a smooth projective variety has a
  full-rank finite-dimensional stable sector of rational first-order velocity observables, then
  their eigenvolume has only simple poles.  Those poles form a totally invariant reduced boundary
  `D` with `K_X+D~0`, and the map is etale off `D`.  In the polarized case, existing structure
  theorems then force a finite quotient of a toric log-Calabi--Yau fibration over an abelian
  variety after the prescribed modification.

## Goal

Prove a nontrivial converse: extract the logarithmic boundary geometry from the stable
differential tail instead of assuming a torus, abelian variety, or orbifold in advance.

## Gates

- [x] 0 -> 1 in-progress: tail-to-eigenvolume mechanism isolated and literature boundary checked
- [x] 1 -> 2 fully-proven: divisor dynamics and ramification fixed-point proof complete
- [ ] 2 -> 3 formalized: full algebraic-geometric theorem encoded in Lean
- [ ] 3 -> 4 publication-ready: expert novelty review and extension from coframes to arbitrary tails

## Setup

Let `X/C` be a smooth projective variety of dimension `r` and let

`f:X->X`

be a finite int-amplified endomorphism.  Let `L=C<X>` be the differential rational function
field of a differential-generic point.  For a rational one-form `omega` on `X`, write

`J_omega(x)=omega_x(delta x)`

for its first-order velocity observable.

Assume there is an `r`-dimensional `C`-vector space `W` of rational one-forms such that:

1. a basis `omega_1,...,omega_r` is generically a coframe;
2. `f*W=W`.

The second condition makes `f*|W` an automorphism.  Hence for every `n` and every `omega in W`
there is `eta_n in W` with `omega=f^(n*)eta_n`, so

`J_omega in intersection_n f^(n*)L=Tail(f)`.                      (1)

Thus `W` is a full-rank first-order sector of the differential tail, not extra propagated data.

## Theorem A: the eigenvolume horizon theorem

**[PROVED HERE]**

Let

`Omega=omega_1 wedge ... wedge omega_r`.

After replacing `f` by an iterate, there is a reduced divisor `D` such that

`div(Omega)=-D`,                                                   (2)

`f^(-1)(D)=D`,                                                     (3)

`f:X\D -> X\D` is etale,                                          (4)

`K_X+D~0`,                                                        (5)

and

`f*(K_X+D)=K_X+D` as divisors.                                    (6)

In particular, the stable coframe cannot have a zero, a regular degeneracy divisor, or a pole of
order greater than one.  Every divisorial singularity is forced to be logarithmic.

### Step 1: tail coframe gives an eigenvolume

Write the constant matrix of `f*|W` as `A in GL_r(C)`.  Taking the top exterior power gives

`f*Omega=det(A) Omega`.                                            (7)

Therefore `div(f*Omega)=div(Omega)`.

### Step 2: the ramification order law

Let `E` be a prime divisor, let `F=f(E)`, let `e_E` be the ramification index at `E`, and put

`c_E=ord_E(Omega)`.

Pullback of a rational top form includes the ramification divisor, so (7) gives

`c_E=e_E c_F+(e_E-1)`,                                            (8)

or equivalently

`c_E+1=e_E(c_F+1)`.                                               (9)

Equation (9) is the exact local law.  The shift by one is not a convention: it is the Jacobian
contribution of ramification.

### Step 3: the support is periodic

Let `S=Supp(div(Omega))`.  If `F in S`, then `c_F+1` is an integer different from `1`.  Equation
(9) implies `c_E+1` is also different from `1` for every `E` over `F`; hence

`f^(-1)(S) subset S`.                                              (10)

Starting from any component of `S`, choose successive inverse-image components.  They remain in
the finite set `S`, so a component repeats.  Its forward cycle contains the starting component.
Every component of `S` is therefore periodic.  After a common iterate, every component is fixed
and is its own complete divisorial inverse image.

### Step 4: expansion quantizes every pole order to `-1`

For a fixed component `E`, write `f*E=e_E E`.  Its numerical divisor class is nonzero because it
has positive intersection with an ample `(r-1)`-fold product.  It is therefore an eigenvector of
`f*` on `N^1(X)`.  Every eigenvalue of an int-amplified endomorphism has modulus greater than one,
so the positive integer `e_E` satisfies `e_E>1`.

Equation (9) is now

`c_E+1=e_E(c_E+1)`.

Since `e_E>1`, its unique integral solution is

`c_E=-1`.                                                         (11)

This local fixed-point argument is Lean-formalized as
`ramificationPoleOrder_fixed_eq_neg_one` in
`formal/GaloisForLFunctions/HTGeometry/RamificationPoleFixedPoint.lean`.

Thus `div(Omega)=-D` for the reduced divisor supported on `S`, proving (2) and (5).

### Step 5: no ramification remains off the horizon

If a ramification prime `E` lay outside `D`, then `c_E=0`.  Its image also lies outside `D` by
the periodicity proved above, so (8) would read `0=e_E-1`, contradicting ramification.  Hence the
ramification divisor is supported on `D`, proving (4).  On each component of `D`, (8) gives the
coefficient identity

`R_f=f*D-D`.

Together with `K_X=f*K_X+R_f`, this proves (6).

## Corollary B: structural classification of the full-coframe case

The pair `(X,D)` is log canonical by the standard invariant-boundary theorem for int-amplified
endomorphisms.  It is a log Calabi--Yau pair by (5).  If `f` is polarized, the theorem of
Moraga--Yanez--Yeong implies that a pdlt modification of `(X,D)` is a finite quotient of a toric
log-Calabi--Yau fibration over an abelian variety:
<https://arxiv.org/abs/2406.18092>.

If `X` is of Fano type, the earlier toric characterization of Meng--Zhang applies to the reduced
totally invariant boundary and yields a quasi-etale toric cover under its stated regularity
hypotheses: <https://arxiv.org/abs/1702.07883>.

The literature supplies the classification after a log Calabi--Yau boundary is known.  The new
bridge proved here is that a full stable velocity coframe manufactures that boundary and forces
its coefficient to be exactly one.

## Related weighted theorem

The finite-holonomy generalization from eigenvolumes to eigen-`k`-canonical densities is separated
into `eigenplurivolume-log-crepant-orbifold.md`.  It produces a rational log-crepant boundary and
forces normalized pole order `-1` on recurrent expanding components, but does not imply that the
boundary is reduced, effective, or log canonical.  Those distinctions are unnecessary here
because a genuine coframe supplies an ordinary eigenvolume (`k=1`).

## Physical/topological reading

This paragraph is interpretation, not an additional theorem.

The eigenvolume is the orientation density of the persistent velocity sector.  Ramification
rescales the shifted pole order `c+1` by an integer expansion factor.  On a recurrent horizon the
only possible fixed point is `c=-1`: a simple logarithmic pole.  Thus the boundary is not chosen
as a compactification device after the fact.  It is selected by the coarse-graining law itself.

In physical language, the stable tail has an exact no-bulk-volume property.  Ordinary volume
degeneracies are erased; only a logarithmic horizon density survives.  This is a static constraint
topology and does not posit quantum evolution, time, or a black-hole model.

## Novelty and significance gate

### Parent results deliberately separated

- canonical-divisor pullback and ramification: classical;
- eigenvalues of an int-amplified pullback on `N^1` have modulus greater than one: standard
  amplified-endomorphism theory;
- log canonicity of the reduced invariant boundary and bounds on totally invariant divisors:
  Zhong, <https://arxiv.org/abs/1905.05362>;
- classification of polarized log-Calabi--Yau pairs: Moraga--Yanez--Yeong 2024.

### New theorem surface

The audited literature did not state the chain

`full first-order stable tail
 -> rational eigenvolume
 -> shifted ramification fixed point
 -> reduced log-Calabi--Yau boundary
 -> toric/abelian fibration after modification`.

The local law (9) and its fixed point are elementary once exposed, but they close a genuine
converse for the full-coframe sector.  Novelty remains provisional pending expert review.

This advances the classification program substantially but does **not** clear the Fields-Medal
gate.  The remaining medal-level step is to extract a coframe, foliation, or lower-rank log factor
from an arbitrary nonconstant differential tail, whose minimal observable may have higher order
and need not be linear in velocity.

## Lean status

The arithmetic ramification fixed point is formalized in
`formal/GaloisForLFunctions/HTGeometry/RamificationPoleFixedPoint.lean`:

- `ramificationShift_fixed_eq_neg_one`;
- `ramificationPoleOrder_fixed_eq_neg_one`.

`formal/GaloisForLFunctions/HTGeometry/EigenvolumeRamificationSystem.lean` formalizes the whole
combinatorial and arithmetic core of Theorem A downstream of the local law (9).  The system is a
type of primes `alpha`, an image map `F`, a ramification index `e` and an eigenvolume order `c`
subject to `c x + 1 = e x * (c (F x) + 1)`.

| Theorem A step | Lean declaration |
|---|---|
| (10), preimage stability of the support | `order_ne_zero_of_image_ne_zero`, `order_ne_zero_of_iterate_ne_zero` |
| iterated order law along a forward orbit | `shift_eq_prod_iterate`, `one_lt_prod_iterate_of_expanding` |
| step 3, backward orbits return | `exists_pos_iterate_eq_self_of_backwardStable` |
| step 4 on a cycle, with no iterate taken | `eigenvolumeOrder_eq_neg_one_of_periodic` |
| (2) and (5), the horizon is reduced | `eigenvolumeOrder_eq_neg_one` |
| (3), total invariance `f^(-1)(D) = D` | `order_ne_zero_iff_image_ne_zero` |
| (4), etale off the horizon | `ramificationIndex_eq_one_of_order_eq_zero` |
| (6), `R_f = f^*D - D` at coefficients | `ramificationCoefficient_eq_pullback_sub` |
| expansion is necessary | `exists_nonexpanding_order_ne_neg_one` |
| finiteness of the support is necessary | `exists_infiniteSupport_order_ne_neg_one` |
| **sharp step 4: one ramified place on the cycle suffices** | `one_lt_prod_iterate_of_exists_ramified`, `eigenvolumeOrder_eq_neg_one_of_ramifiedCycle` |
| sharp horizon theorem | `eigenvolumeOrder_eq_neg_one_of_someRamified` |

Three improvements over the paper argument are now proved.  First, the passage to an iterate in
step 3 is unnecessary: the cycle equation `c + 1 = (product of e along the cycle) * (c + 1)`
already forces `c = -1` on every periodic component, so `f` itself has reduced horizon.  Second,
both standing hypotheses are sharp.  Dropping expansion admits `c = 5` on a one-point support;
dropping finiteness of the support admits `c(n) = 2^n - 1` on `N` with `F(n) = n - 1` and
expanding indices throughout.  Third, step 4 needs far less than the card assumes: a periodic
prime whose cycle carries ramification at even **one** place already has order exactly `-1`
(`eigenvolumeOrder_eq_neg_one_of_ramifiedCycle`), with no expansion at every component, no
finiteness of the support and no surjectivity.  Since the product of the indices along the cycle
is what enters, one index above one is enough to break the fixed point.

All ten declarations were audited with `#print axioms`; they use only `propext`,
`Classical.choice`, and `Quot.sound`.

`formal/GaloisForLFunctions/HTGeometry/TameEisensteinDifferentExponent.lean` supplies the
arithmetic source of the `e - 1` in the local law (8), in the local model where that law lives.
For a discrete valuation ring, a uniformizer `x`, and a monic degree-`e` polynomial whose lower
coefficients all have valuation at least `e` -- the Eisenstein presentation of a totally ramified
extension -- with `e` a unit at the place:

| statement | Lean declaration |
|---|---|
| valuation of a sum is bounded by its summands | `le_addVal_sum` |
| valuation of a power of a uniformizer | `addVal_pow_uniformizer` |
| derivative of the Eisenstein presentation | `derivative_eisensteinPoly`, `eval_derivative_eisensteinPoly` |
| **the ramification exponent is exactly `e - 1`** | `addVal_eval_derivative_eisensteinPoly` |
| the shift by one is the ramification index | `addVal_eval_derivative_eisensteinPoly_succ` |
| the local different is exactly `m^(e-1)` | `span_eval_derivative_eisensteinPoly` |

The mechanism is an ultrametric strict minimum: the leading term `e x^(e-1)` has valuation
`e - 1` because `e` is a unit in the tame case, while every other term carries a coefficient of
valuation at least `e`.  This is the precise sense in which the `+1` of (9) is the Jacobian
contribution of ramification rather than a normalisation convention.  mathlib supplies only the
divisibility `P^(e-1) | different` (`pow_sub_one_dvd_differentIdeal`); the matching upper bound,
which is what makes the exponent exact, is proved here.  All seven declarations are axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/TopExteriorPowerDeterminant.lean` supplies the eigenvolume
identity (7) as linear algebra.  For a free module with a finite linearly ordered basis, the
functorial action of an endomorphism on the **top** exterior power is multiplication by its
determinant:

| statement | Lean declaration |
|---|---|
| the full index set is the unique top combination | `uniqueTopCombination` |
| its increasing enumeration is a bijection | `topEnumEquiv` |
| the coordinate matrix along that enumeration has determinant `det f` | `det_coord_matrix` |
| **top exterior power of `f` is `det f` times the identity** | `exteriorPower_map_card_eq_det_smul`, `exteriorPower_map_card_apply` |
| an automorphism has unit determinant | `isUnit_det_linearEquiv` |
| **pullback scales the top wedge by a unit** | `exteriorPower_map_card_eq_unit_smul` |

Applied to `W` with the automorphism `f^*|W` of matrix `A`, this is exactly
`f^*Omega = det(A) Omega` with `det(A)` a unit, hence `div(f^*Omega) = div(Omega)`.  mathlib has
the exterior-power basis and `LinearMap.det` separately but not their top-degree identification;
that identification is proved here.  All seven declarations are axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/LocalRamificationOrderLaw.lean` assembles the local law (8)
itself.  For a ring homomorphism of discrete valuation rings sending a uniformizer to an element
of valuation `e`:

| statement | Lean declaration |
|---|---|
| units have valuation zero | `addVal_of_isUnit` |
| powers scale by `e` | `addVal_map_pow_of_addVal_eq` |
| **the ramification index scales every valuation** | `addVal_map_eq_mul_ramification` |
| **`ord (pullback form) = e * ord (form) + (e - 1)`** | `addVal_pullback_form` |
| the Jacobian shift `(8)` iff `(9)` | `orderLaw_iff_shiftLaw` |
| integer order of a rational form | `natOrd`, `natOrd_spec`, `natOrd_mul` |
| ramification scales the integer order | `natOrd_map_eq_mul_ramification`, `ramificationOrder_frac` |
| **`(8)` for a form with poles** | `ramificationOrderLaw_frac` |
| **`(9)` for a form with poles** | `ramificationShiftLaw_frac` |

mathlib defines the ramification index combinatorially and has no theorem computing the effect of
an extension on adic valuations; the scaling identity is proved here from the discrete valuation
structure alone, with no finiteness, separability or Dedekind hypothesis.  Together with the exact
tame exponent this closes the whole of the local law: both the `e` and the `e - 1` of (8) are now
theorems rather than inputs, and `orderLaw_iff_shiftLaw` is the exact bridge to the shifted form
(9) consumed by `EigenvolumeRamificationSystem.lean`.

The law is also proved for **rational** forms, which is the case the card actually needs: an
eigenvolume has poles, so its order is an arbitrary integer rather than a valuation of a ring
element.  Writing the form as a quotient `a / b`, its order is `natOrd a - natOrd b` in `Z`, and
`ramificationOrderLaw_frac` is exactly `c_E = e c_F + (e - 1)` with `c` of either sign;
`ramificationShiftLaw_frac` is its shifted form `c_E + 1 = e (c_F + 1)`, which is the hypothesis
`hlaw` of the abstract system.  All declarations are axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/RingOrdRamification.lean` restates the law in mathlib's
own order-of-vanishing vocabulary.  `Ring.ord` is the module-length order of vanishing in a
Noetherian local ring and is the primitive on which the scheme-level `AlgebraicGeometry.ord` at a
codimension-one point is built, so this is the interface the globalisation must speak:

| statement | Lean declaration |
|---|---|
| ramification scales `Ring.ord` | `ord_map_eq_mul_ramification` |
| the local law in `Ring.ord` vocabulary | `ord_pullback_form` |
| a uniformizer has order one | `ord_uniformizer` |
| order zero characterises units | `isUnit_of_addVal_eq_zero` |
| **a local homomorphism has ramification index at least one** | `one_le_ord_map_uniformizer` |

The last item discharges the hypothesis `1 <= e` of the abstract system.  Note that injectivity is
*not* enough for it: an injective map of discrete valuation rings can send a uniformizer to a
unit, so locality is the right hypothesis and is exactly what a dominant morphism supplies.

`formal/GaloisForLFunctions/HTGeometry/DivisorSupportFinite.lean` discharges the finiteness
hypothesis of the abstract system.  By Krull's height theorem a height-one prime containing a
nonzero element is minimal over the principal ideal that element generates, and a Noetherian ring
has only finitely many minimal primes over a fixed ideal:

| statement | Lean declaration |
|---|---|
| a height-one prime containing `a` is minimal over `(a)` | `mem_minimalPrimes_span_of_height_eq_one` |
| **a nonzero element vanishes along finitely many prime divisors** | `finite_heightOneSupport` |
| **the divisorial support of a rational form is finite** | `finite_heightOneSupport_frac` |
| complement of the support | `notMem_of_notMem_heightOneSupport` |

This is exactly the `hfin` hypothesis of `EigenvolumeRamificationSystem.lean`, so the finiteness
that step 3 of Theorem A relies on -- and which the sharpness counterexample
`exists_infiniteSupport_order_ne_neg_one` shows cannot be dropped -- is now a theorem in the
Noetherian model rather than an assumption.

`formal/GaloisForLFunctions/HTGeometry/PrimeDivisorLyingOver.lean` discharges the last remaining
hypothesis, surjectivity of the divisor map.  For an integral extension of domains,
incomparability forces a prime strictly below a prime lying over a prime divisor to contract to
zero, hence to be zero:

| statement | Lean declaration |
|---|---|
| the zero ideal contracts to zero | `comap_bot_eq_bot` |
| **a prime lying over a prime divisor is a prime divisor** | `height_eq_one_of_comap_height_eq_one` |
| **every prime divisor downstairs is dominated** | `exists_heightOne_comap_eq` |
| **the prime below a prime divisor is a prime divisor** | `under_height_eq_one_of_height_eq_one` |

The last item makes the card's map `F` -- send a prime divisor to the prime divisor below it --
well defined: going down (available for flat, in particular for the geometric situation) lifts a
prime strictly below the contraction to a prime strictly below, which must then be zero.

Every hypothesis of `EigenvolumeRamificationSystem.lean` is now a theorem in the local Noetherian
model: `hlaw` from `ramificationShiftLaw_frac`, `1 <= e` from `one_le_ord_map_uniformizer`, `hfin`
from `finite_heightOneSupport_frac`, and surjectivity from `exists_heightOne_comap_eq`.

`formal/GaloisForLFunctions/HTGeometry/LocalizationAtPrimeDivisorDVR.lean` supplies the local
rings themselves.  On a normal variety the local ring along a prime divisor is a discrete
valuation ring; in commutative algebra this is the statement for a Noetherian integrally closed
domain localised at a height-one prime:

| statement | Lean declaration |
|---|---|
| the local ring has Krull dimension one | `ringKrullDim_localizationAtPrime` |
| it is not a field | `not_isField_localizationAtPrime` |
| every nonzero prime of it is maximal | `dimensionLEOne_localizationAtPrime` |
| **the local ring at a prime divisor is a discrete valuation ring** | `isDiscreteValuationRing_localizationAtPrime` |

mathlib provides this only for Dedekind domains, where every nonzero prime already has height one;
the height-one statement over a base of arbitrary dimension, which is what a variety needs, is
proved here.  This is what makes the valuation-theoretic layer of the card apply at every prime
divisor rather than only in dimension one.

`formal/GaloisForLFunctions/HTGeometry/PrimeDivisorOrder.lean` attaches the order function to
actual prime divisors and identifies its support:

| statement | Lean declaration |
|---|---|
| prime divisors of a normal Noetherian domain | `PrimeDivisor` |
| each carries a discrete valuation | `isDiscreteValuationRing_primeDivisor` |
| order of an element along a prime divisor | `orderAt` |
| **the order is nonzero exactly on the prime divisors containing the element** | `orderAt_ne_zero_iff` |
| **a nonzero element has finite divisorial support** | `finite_orderAt_support` |

This closes the loop between the valuation layer and the finiteness layer: the `hfin` hypothesis
of the abstract system is now proved for the order function actually attached to a ring element,
not merely for an abstract order assignment.

`formal/GaloisForLFunctions/HTGeometry/PrimeDivisorPullbackOrder.lean` proves the pullback law at
the level of actual prime divisors.  A ring homomorphism carrying a prime divisor `P` back to a
prime divisor `Q` induces a homomorphism of the local rings there, both discrete valuation rings,
and its ramification index scales every order:

| statement | Lean declaration |
|---|---|
| the complement condition making the local map exist | `primeCompl_le_comap` |
| the induced map of local rings | `localMapAt`, `localMapAt_algebraMap` |
| nonzero elements stay nonzero locally | `algebraMap_localization_ne_zero` |
| **`ord (pullback of a) at P = e * ord a at Q`** | `orderAt_map_eq_mul_ramification` |

This is the ring-level form of the divisor pullback formula, the half of (8) carrying the factor
`e`, now stated for genuine prime divisors of a normal Noetherian domain rather than for a single
abstract pair of discrete valuation rings.  mathlib provides no pullback law for orders of
vanishing in any form.

`formal/GaloisForLFunctions/HTGeometry/EigenvolumeHorizonCapstone.lean` assembles the whole local
model.  For a normal Noetherian domain with a self-map, the order of a rational form `a / b` along
a prime divisor is the difference of the orders of numerator and denominator, and:

| Theorem A item | Lean declaration |
|---|---|
| the prime divisor below a prime divisor | `divisorBelow` |
| integer order of a rational form | `formOrder` |
| **finiteness of the divisorial support** | `finite_formOrder_support` |
| **(2), (5) the horizon is a reduced divisor** | `formOrder_eq_neg_one` |
| **(3) total invariance of the horizon** | `formOrder_ne_zero_iff` |
| **(4) unramified off the horizon** | `ramificationIndex_eq_one_off_horizon` |

Conclusions (2)-(5) of Theorem A therefore hold as Lean theorems about genuine prime divisors,
with finiteness of the support discharged internally for the concrete order function.  What is
supplied as data is exactly the local order law at each prime divisor and the ramification of
recurrent cycles; the `e` half of that law is itself proved in
`PrimeDivisorPullbackOrder.lean`.

`formal/GaloisForLFunctions/HTGeometry/EigenvolumePullbackLaw.lean` removes the local order law
from that list of data.  The pullback of the rational form `a / b` along the self-map is
`(phi a * J) / (phi b)`, where `J` is the Jacobian factor, so the order of the pullback is
governed by the pullback law together with the order of `J`:

| statement | Lean declaration |
|---|---|
| the order is additive and finite on nonzero elements | `orderAt_mul`, `orderAt_ne_top` |
| **shifted law from the pullback law and the Jacobian** | `formOrder_pullback_shiftLaw` |
| **the local order law for an eigenvolume** | `eigenvolume_shiftLaw` |
| **(2), (5) the horizon of an eigenvolume is reduced** | `eigenvolume_formOrder_eq_neg_one` |
| **(3) total invariance** | `eigenvolume_formOrder_ne_zero_iff` |
| **(4) unramified off the horizon** | `eigenvolume_ramificationIndex_eq_one_off_horizon` |

The hypothesis `hlaw` is thereby replaced by the two statements it is made of, both of which are
the geometry of the situation rather than an assumption about orders: that the form is an
eigenvolume, meaning its pullback has the same divisor as the form itself, and that the Jacobian
factor has order `e - 1` at every prime divisor.  The second is exactly the different exponent,
proved in the Eisenstein presentation in `TameEisensteinDifferentExponent.lean`.

`formal/GaloisForLFunctions/HTGeometry/SchemeEigenvolumeHorizon.lean` carries the same conclusions
over from the ring model to an actual scheme.  The order function is mathlib's order of vanishing
at a codimension-one point, and the abstract ramification system is instantiated on the
codimension-one points of an integral Noetherian scheme with a self-morphism:

| Theorem A item | Lean declaration |
|---|---|
| codimension-one points and the point below | `CodimOnePoint`, `pointBelow` |
| order of a rational function there | `ordAt` |
| **finiteness of the divisorial support** | `finite_ordAt_support` |
| **(8), (9) the shifted local order law** | `schemeEigenvolume_shiftLaw` |
| **(2), (5) the horizon is a reduced divisor** | `schemeEigenvolume_ordAt_eq_neg_one` |
| **(3) total invariance of the horizon** | `schemeEigenvolume_ordAt_ne_zero_iff` |
| **(4) unramified off the horizon** | `schemeEigenvolume_ramificationIndex_eq_one_off_horizon` |
| the pullback law at every codimension-one point | `ord_functionFieldMap_pointwise` |

The shifted law is no longer a hypothesis at this level either: it is assembled from the pullback
law, the order of the Jacobian factor, and the eigenvolume condition.  What is supplied as data is
the geometry of the situation -- that the form is an eigenvolume, that the Jacobian has order
`e - 1`, and that recurrent components carry ramification -- together with the ramification indices
themselves.

What remains paper-level is the geometric input that is neither linear algebra nor valuation
theory: the identification of a rational top form on a variety with the top wedge of a coframe
space, the globalisation of the local law over all prime divisors of a smooth projective variety,
and the int-amplified eigenvalue bound giving `e_E > 1` on recurrent components.  These need Weil divisors, the canonical divisor of a finite
morphism, and `N^1` with amplified pullback eigenvalues, none of which exist in mathlib or in this
project.  Corollary B needs log-canonical MMP results and is further out.  No axiom is introduced
for any of them.

## RH impact audit

There is no direct RH implication.  The theorem gives a falsifiable structural test: if an
algebraic model of the completed-zeta source claims a full-rank first-order persistent sector, its
eigenvolume must determine a reduced logarithmic boundary and, after the known modifications, a
toric/abelian fibration.  No such coframe or boundary has been proved for the zeta source.  A
single logarithmic derivative by itself does not meet the full-rank hypothesis, so this result
cannot be used to infer RH, a critical-line constraint, or positivity.

## Log

- 2026-07-15 -- [PROVED HERE] full stable coframe converted to an eigenvolume; support periodicity,
  simple-pole quantization, log-Calabi--Yau boundary, and polarized structural corollary proved.
- 2026-08-05 -- Lean closed the whole combinatorial-arithmetic core of Theorem A in
  `EigenvolumeRamificationSystem.lean`: preimage stability of the support, return of backward
  orbits under a surjective image map on a finite support, the cycle fixed point (which removes
  the passage to an iterate), total invariance, etale-off-the-horizon, and the coefficient form of
  `R_f = f^*D - D`.  Expansion and finiteness of the support were both shown necessary by explicit
  counterexamples.  Only the algebraic-geometric inputs (7), (8) and the int-amplified eigenvalue
  bound remain paper-level; they need divisor and `N^1` infrastructure absent from mathlib.
- 2026-08-06 -- Lean proved the exact tame ramification exponent in
  `TameEisensteinDifferentExponent.lean`: for an Eisenstein presentation of degree `e` over a
  discrete valuation ring with `e` a unit at the place, the derivative evaluated at a uniformizer
  has valuation exactly `e - 1`, and the local different is exactly the `(e-1)`-st power of the
  maximal ideal.  mathlib had only the divisibility `P^(e-1) | different`; the matching upper
  bound is new here and it is what makes the `e - 1` of the local law (8) exact rather than a
  lower bound.  The proof is an ultrametric strict minimum: tameness makes the leading term
  `e x^(e-1)` strictly smaller in valuation than every other term.
- 2026-08-06 -- Lean proved the eigenvolume identity (7) as linear algebra in
  `TopExteriorPowerDeterminant.lean`: for a free module with a finite linearly ordered basis, the
  top exterior power of an endomorphism is multiplication by its determinant, and an automorphism
  therefore scales the top wedge by a unit.  mathlib had the exterior-power basis and
  `LinearMap.det` but no identification between them in top degree.  Step 1 of Theorem A is now
  formal; only the geometric identification of a rational top form with a coframe top wedge, the
  global form of (8), and the int-amplified eigenvalue bound remain.
- 2026-08-06 -- Lean closed the local law (8) in `LocalRamificationOrderLaw.lean`.  The missing
  half was that a homomorphism of discrete valuation rings multiplies valuations by the
  ramification index; mathlib defines that index combinatorially and never computes its effect on
  valuations.  Proved from the discrete valuation structure alone.  With the tame exponent from
  the previous entry, both the `e` and the `e - 1` of (8) are now theorems, and the equivalence
  of (8) with the shifted form (9) is explicit.  Steps 1, 2, 3, 4 and 5 of Theorem A are now
  formal apart from their geometric globalisation.
- 2026-08-06 -- Step 4 sharpened in Lean.  The paper argument asks for `e_E > 1` at every
  component, obtained from int-amplification.  Only the *product* of the indices along a cycle
  enters, so one ramified place on the cycle already forces `c = -1`:
  `eigenvolumeOrder_eq_neg_one_of_ramifiedCycle` needs no expansion at every component, no
  finiteness of the support, and no surjectivity.  The horizon theorem was restated under the
  weakened hypothesis as `eigenvolumeOrder_eq_neg_one_of_someRamified`.
- 2026-08-06 -- Globalisation reconnaissance.  mathlib **does** have the order of a rational
  function along a codimension-one point of a scheme, `AlgebraicGeometry.ord` with `ord_mul`,
  `ord_add`, `ord_of_isUnit`, `ord_eq_iff`, plus `Ring.ord`/`ordFrac` and `ord_eq_addVal` for
  Noetherian local rings.  It does **not** have the divisor of a rational function as a cycle
  with finite support (`AlgebraicGeometry.AlgebraicCycle` is a stub), nor any pullback law for
  `ord` along a morphism.  Those two are the next concrete targets for globalising the local law.
- 2026-08-06 -- The local law extended to rational forms, which is the case the card needs: an
  eigenvolume has poles, so `c` must range over all of `Z` and not just over valuations of ring
  elements.  `natOrd` gives the integer order of a quotient `a / b`, and
  `ramificationOrderLaw_frac` / `ramificationShiftLaw_frac` prove (8) and (9) for it.  The shifted
  form is now literally the `hlaw` hypothesis consumed by `EigenvolumeRamificationSystem.lean`,
  so the whole chain from the local law to the reduced horizon is formal in the local model.
- 2026-08-06 -- The local law restated in mathlib's `Ring.ord` vocabulary
  (`RingOrdRamification.lean`), which is the primitive underlying the scheme-level
  `AlgebraicGeometry.ord` at a codimension-one point.  Also proved that a *local* homomorphism has
  ramification index at least one, discharging the `1 <= e` hypothesis of the abstract system;
  injectivity alone does not suffice, since an injective map of discrete valuation rings can send
  a uniformizer to a unit.
- 2026-08-06 -- Finiteness of the divisorial support proved in `DivisorSupportFinite.lean`, from
  Krull's height theorem plus finiteness of minimal primes in a Noetherian ring.  This discharges
  the `hfin` hypothesis of the abstract system, which the earlier counterexample
  `exists_infiniteSupport_order_ne_neg_one` had shown to be indispensable.  Every hypothesis of
  `EigenvolumeRamificationSystem.lean` except surjectivity of the divisor map is now a theorem in
  the local/Noetherian model.
- 2026-08-06 -- Surjectivity of the divisor map proved in `PrimeDivisorLyingOver.lean` from lying
  over plus incomparability for integral extensions of domains.  With it, every hypothesis of the
  abstract ramification system is now a theorem in the local Noetherian model, so the only thing
  separating the card from a fully formal Theorem A is the passage from that model to a smooth
  projective variety: identifying a rational top form with a coframe top wedge, and transporting
  the local law along a morphism of schemes.
- 2026-08-06 -- Well-definedness of the divisor map proved: under going down, the prime below a
  prime divisor is again a prime divisor (`under_height_eq_one_of_height_eq_one`).  With the
  converse already in hand, height one is preserved in both directions, so the card's map `F` on
  prime divisors is well defined and onto.
- 2026-08-06 -- The local rings supplied: a Noetherian integrally closed domain localised at a
  height-one prime is a discrete valuation ring (`LocalizationAtPrimeDivisorDVR.lean`).  mathlib
  had this only for Dedekind domains, where height one is automatic; the version over a base of
  arbitrary dimension is what a variety of dimension `r` needs, and it is what lets the whole
  valuation layer of this card apply at every prime divisor.
- 2026-08-06 -- The order function attached to actual prime divisors (`PrimeDivisorOrder.lean`):
  every prime divisor of a normal Noetherian domain carries a discrete valuation, the order of an
  element is nonzero exactly at the prime divisors containing it, and a nonzero element therefore
  has finite divisorial support.  The `hfin` hypothesis is now proved for the concrete order
  function rather than assumed for an abstract one.
- 2026-08-06 -- The pullback law proved at the level of prime divisors
  (`PrimeDivisorPullbackOrder.lean`): a homomorphism carrying a prime divisor back to a prime
  divisor induces a map of the local discrete valuation rings, and its ramification index scales
  the order of every element.  This is the `e` half of (8) for genuine prime divisors of a normal
  Noetherian domain; mathlib has no pullback law for orders of vanishing at all.
- 2026-08-06 -- Capstone assembled (`EigenvolumeHorizonCapstone.lean`).  Conclusions (2)-(5) of
  Theorem A now hold as Lean theorems about the genuine prime divisors of a normal Noetherian
  domain with a self-map: the horizon is a reduced divisor, it is totally invariant, and the map
  is unramified off it.  Finiteness of the divisorial support is discharged internally for the
  concrete order function of a rational form `a / b`.  The remaining data is the local order law
  at each prime divisor, whose `e` half is proved in `PrimeDivisorPullbackOrder.lean`.
- 2026-08-06 -- The local order law itself discharged (`EigenvolumePullbackLaw.lean`).  The order
  of a pullback is additive over the Jacobian factor, so the shifted law (9) follows from the
  pullback law and the single statement that the Jacobian has order `e - 1`.  Combined with the
  eigenvolume condition -- the pullback of the form has the same divisor as the form -- this
  yields the horizon theorem with `hlaw` no longer assumed:
  `eigenvolume_formOrder_eq_neg_one`, `eigenvolume_formOrder_ne_zero_iff`,
  `eigenvolume_ramificationIndex_eq_one_off_horizon`.  The remaining data is geometric rather than
  valuation-theoretic: the eigenvolume condition, and the different exponent `e - 1` for a general
  normal domain (proved here only in the Eisenstein presentation).
- 2026-08-06 -- The eigenvolume condition derived rather than assumed
  (`EigenvolumeUnitInvariance.lean`).  The order of a rational form depends only on the form, not
  on the chosen numerator and denominator (`formOrder_eq_of_cross`), and is unchanged by a unit
  factor.  Since the top wedge of an invariant coframe pulls back to the determinant of the
  transition matrix times itself, and that determinant is a unit, the eigenvolume condition is a
  consequence of Step 1 rather than a hypothesis: `unitEigenvolume_formOrder_eq_neg_one`,
  `unitEigenvolume_formOrder_ne_zero_iff`,
  `unitEigenvolume_ramificationIndex_eq_one_off_horizon` take the unit identity in place of it.
- 2026-08-06 -- The scheme layer opened (`SchemeOrderSupportFinite.lean`).  A rational function is
  a unit in the local ring away from its zero and polar loci, so its order of vanishing is zero
  there (`ord_algebraMap_stalk_eq_zero`, `ord_germToFunctionField_eq_zero_of_isUnit_germ`), and on
  an affine open of an integral locally Noetherian scheme its divisorial support is finite
  (`finite_ord_support_of_isAffineOpen`), by Krull's height theorem applied to the numerator and
  the denominator.  The dictionary between codimension-one points of an affine open and
  height-one primes is proved on the way: `coheight_eq_height_primeIdealOf`,
  `isUnit_germ_iff_notMem_primeIdealOf`, `primeIdealOf_injective`.  mathlib defines the order of
  vanishing but has no divisor of a rational function and no finiteness statement for its support.
- 2026-08-06 -- The scheme-level finiteness globalised and the pullback law proved there.
  `finite_ord_support` (`SchemeOrderSupportFinite.lean`): on a quasi-compact integral locally
  Noetherian scheme the divisorial support of any rational function is finite, obtained from the
  affine case by a finite affine cover.  `ord_pullback_eq_mul_ramification`
  (`SchemeOrderPullbackLaw.lean`): at codimension-one points whose local rings are discrete
  valuation rings, a homomorphism of those local rings compatible with a homomorphism of the
  function field scales the order of every rational function by its ramification index.  The
  bridge is `ord_algebraMap_stalk_eq_addVal`: mathlib's order of vanishing, defined by module
  length, agrees with the additive valuation at such a point, which is what lets the ring-level
  ramification law apply on a scheme.  Both hypotheses of the scheme-level pullback law are
  exactly what a morphism of schemes carrying one codimension-one point to another supplies.
- 2026-08-06 -- The pullback law attached to an actual morphism of schemes
  (`SchemeMorphismOrderPullback.lean`).  A morphism carrying the generic point to the generic
  point induces `functionFieldMap` on function fields, and that homomorphism extends the
  homomorphisms of local rings it induces at every point
  (`functionFieldMap_algebraMap`), by naturality of specialisation with respect to `stalkMap`.
  Hence `ord_functionFieldMap_eq_mul_ramification`: for a morphism of integral locally Noetherian
  schemes and a codimension-one point whose local ring and image local ring are discrete
  valuation rings, the order of the pullback of a rational function is the ramification index of
  the induced map of local rings times the order downstairs.  The abstract law
  `ord_pullback_eq_mul_ramification` was generalised to two schemes for this, so it covers a
  morphism `X -> Y` and not only a self-map.
- 2026-08-06 -- The discrete valuation rings supplied at scheme level.  The local criterion was
  isolated as pure commutative algebra in `LocalNoetherianNormalDVR.lean`
  (`isDiscreteValuationRing_of_ringKrullDim_eq_one`: a Noetherian integrally closed local domain
  of Krull dimension one is a discrete valuation ring), which mathlib has only through the
  Dedekind interface.  `SchemeNormalStalkDVR.lean` applies it on a scheme: since the Krull
  dimension of a stalk is the codimension of the point, a scheme whose affine charts have
  integrally closed sections has discrete valuation rings as its local rings at every
  codimension-one point (`isDiscreteValuationRing_stalk`,
  `isIntegrallyClosed_stalk_of_isAffineOpen`, `isDiscreteValuationRing_stalk_of_isAffineOpen`).
  This is the instance the scheme-level pullback law requires.  The earlier
  `LocalizationAtPrimeDivisorDVR.lean` now delegates to the same local criterion instead of
  repeating its proof.
- 2026-08-06 -- Theorem A assembled on a scheme (`SchemeEigenvolumeHorizon.lean`).  The abstract
  ramification system is instantiated on the codimension-one points of an integral Noetherian
  scheme with `Scheme.ord` as the order function, its support finite by `finite_ordAt_support`,
  and the shifted law assembled from the pullback law, the Jacobian order and the eigenvolume
  condition.  Conclusions (2)-(5) therefore hold as Lean theorems about an actual scheme and an
  actual self-morphism, not only in the ring model: `schemeEigenvolume_ordAt_eq_neg_one`,
  `schemeEigenvolume_ordAt_ne_zero_iff`,
  `schemeEigenvolume_ramificationIndex_eq_one_off_horizon`.  `ord_functionFieldMap_pointwise`
  discharges the pullback hypothesis from the induced maps of local rings, so the only data left
  is geometric: the eigenvolume condition, the different exponent, and ramification on recurrent
  components.
- 2026-08-06 -- Step 1 discharged at scheme level (`SchemeEigenvolumeUnit.lean`).  A rational
  function whose order of vanishing is zero everywhere does not move the divisor of another
  (`ord_mul_of_ord_eq_zero`), and an invertible section over an open set containing every point is
  such a function (`ord_eq_zero_of_isUnit_section`).  Since the top exterior power of an invariant
  coframe pulls back to the determinant of the transition matrix times itself, and that
  determinant is an invertible constant, the eigenvolume condition follows from invariance of the
  coframe rather than being assumed: `unitSchemeEigenvolume_ordAt_eq_neg_one`,
  `unitSchemeEigenvolume_ordAt_ne_zero_iff`,
  `unitSchemeEigenvolume_ramificationIndex_eq_one_off_horizon` take the identity
  `f^*Omega = c Omega` in place of the eigenvolume condition.
- 2026-08-06 -- Equation (6) proved, and at every place rather than only on the horizon
  (`EigenvolumeBoundaryDivisor.lean`, `SchemeEigenvolumeBoundary.lean`).  The horizon theorem
  pins the order of the eigenvolume to `0` or `-1` (`order_eq_zero_or_neg_one`), so the boundary
  coefficient is `0` or `1` (`boundaryCoeff_eq_zero_or_one`): the boundary is reduced.  With total
  invariance and unramifiedness off the horizon, the identity
  `e - 1 = e * boundary(F x) - boundary(x)` then holds at every place
  (`ramification_eq_pullback_sub`), which is the coefficient form of `R = f^* D - D`.  The earlier
  `ramificationCoefficient_eq_pullback_sub` only covered places already known to lie on the
  horizon; the off-horizon case is exactly where `e = 1` is needed, and it now follows.  Scheme
  versions: `schemeEigenvolume_ordAt_eq_zero_or_neg_one`,
  `schemeEigenvolume_boundaryCoeff_eq_zero_or_one`,
  `schemeEigenvolume_ramification_eq_pullback_sub`.
- 2026-08-06 -- The Jacobian defined and its action on top forms proved
  (`KaehlerJacobianTopForm.lean`).  The pullback of differentials along a polynomial endomorphism
  is the linear map sending `d x_i` to `d (phi x_i)`; expanding the latter in the basis of
  differentials produces the Jacobian matrix of partial derivatives
  (`pullbackDifferential_D_X_eq_sum`, `D_eq_sum_pderiv_smul`), its matrix in that basis is the
  transposed Jacobian (`toMatrix_pullbackDifferential`), and hence its determinant is the Jacobian
  determinant (`det_pullbackDifferential`).  On the top exterior power the induced map is
  multiplication by that determinant (`exteriorPower_pullbackDifferential_apply`).  This is the
  algebraic content of "pullback of a rational top form includes the ramification divisor": the
  Jacobian factor `J` of the order law is now a defined object rather than a posited one.  mathlib
  has the Kaehler differentials of a polynomial ring and their basis, but no Jacobian and no
  statement about the top exterior power.
- 2026-08-06 -- The `e - 1` verified in the fundamental local model
  (`TamePowerMapRamification.lean`).  The coordinatewise power map is the local model of a totally
  ramified cover of index `e`; its Jacobian matrix is diagonal with entries `e x^(e-1)`
  (`jacobian_powMap`), so its determinant is `prod_i e x_i^(e-1)` (`det_jacobian_powMap`), and when
  `e` is invertible this is a unit times the `(e-1)`-st power of the product of the coordinates
  (`det_jacobian_powMap_eq_unit_mul`).  The order of the Jacobian determinant along each coordinate
  divisor is therefore exactly `e - 1`, which is the shift of the ramification order law (8).
  Tameness is not a convenience here: in the wild case the factor `e` is not a unit and the order
  is strictly larger, so the shift is exactly one less than the ramification index precisely when
  `e` is invertible.  `exteriorPower_pullbackDifferential_powMap` states the same fact on top
  differential forms.
- 2026-08-06 -- The toric model of the whole theorem (`TameMonomialEigenvolume.lean`).  A monomial
  map raises each coordinate to its own power, so its ramification index varies from one coordinate
  divisor to the next exactly as `e_E` varies from one prime divisor to the next.  Its Jacobian
  determinant is a unit times the product of the coordinates with the shifted exponents
  (`det_jacobian_monomialMap_eq_unit_mul`), which is the ramification divisor `R_f = sum (e_i - 1)
  E_i`.  Multiplying by the product of the coordinates turns that into the pullback of the same
  product up to a unit (`exists_unit_det_jacobian_mul_prod`): the logarithmic volume form
  `prod x_i^(-1) dx` is an eigenvolume, its horizon is the union of the coordinate hyperplanes, and
  its order there is `-1`.  This is Theorem A realised in the toric case, and it shows the
  hypotheses of the general theorem are consistent and sharp.
- 2026-08-06 -- The toric model's divisor data made explicit (`CoordinateDivisorOrder.lean`).  Each
  coordinate of a polynomial ring over a field generates a height-one prime (`isPrime_span_X`,
  `height_span_X`), so it is a prime divisor `coordDivisor i`, and the coordinate is a uniformizer
  of the local ring there (`irreducible_algebraMap_X`).  Hence the order of a monomial along that
  divisor is its exponent: `orderAt_coordDivisor_X_self`, `orderAt_coordDivisor_X_of_ne`, and with
  the additivity lemmas `orderAt_prod`, `orderAt_pow`.  Applied to the toric model this discharges
  the two divisor hypotheses of Theorem A in that model: the logarithmic volume form has a simple
  pole along each coordinate divisor (`orderAt_coordDivisor_prod_X`, so `c = -1`), and the Jacobian
  determinant of a tame monomial map has order exactly `e i - 1` there
  (`orderAt_coordDivisor_det_jacobian`), which is the hypothesis `hjac` of the horizon theorem.
- 2026-08-06 -- The toric model expressed in the vocabulary of the ramification system.  The
  ramification index of a monomial map along the `i`-th coordinate divisor is exactly `e i`
  (`orderAt_coordDivisor_monomialMap_X`), and the order of the logarithmic volume form there is
  `-1` (`formOrder_coordDivisor_log`), stated with the same `formOrder` used by the abstract
  capstone.  Together with `orderAt_coordDivisor_det_jacobian` this gives, in one concrete model,
  every divisor-level quantity the horizon theorem speaks about: `c = -1`, `e = e i`, and the
  Jacobian order `e i - 1`.
- 2026-08-06 -- Total invariance of the coordinate divisors proved (`MonomialMapInjective.lean`).
  Composing two monomial maps multiplies their exponents (`monomialMap_comp`), so composing with a
  second map turns a monomial map into the uniform expansion by the product of the exponents, which
  is injective; hence every monomial map with positive exponents is injective
  (`monomialMap_injective`).  Killing a coordinate commutes with a monomial map
  (`killCoord_comp_monomialMap`), and the kernel of the coordinate-killing map is the ideal
  generated by that coordinate (`comap_bot_killCoord`, via `sub_killCoord_mem_span`).  Together
  these give `comap_monomialMap_span_X`: a monomial map pulls each coordinate divisor back to
  itself.  That is condition (3) of Theorem A -- total invariance of the horizon -- proved outright
  in the toric model rather than assumed, and it supplies the divisor map `F` of the abstract
  ramification system there.
- 2026-08-06 -- The toric certificate (`ToricEigenvolumeCertificate.lean`).  A single unconditional
  theorem `toric_eigenvolume_certificate` collects, for a tame monomial map acting on the
  logarithmic volume form, every quantity and every conclusion of Theorem A: the coordinate divisors
  are totally invariant (3), the order of the form there is `-1` (2) and (5), the ramification index
  is the exponent, the Jacobian determinant has order one less than the exponent, the shifted order
  law (8)-(9) holds, and ramification is the pullback difference of the boundary (6).  Its only
  hypotheses are `1 <= e i` and tameness; nothing about orders is assumed.  This certifies that the
  hypotheses of the general theorem are simultaneously satisfiable and that its conclusions are
  correct where they can be checked by hand.
- 2026-08-06 -- The local law made usable at a single divisor, and the toric horizon derived through
  it.  The packaged laws quantify over all prime divisors at once, because they are stated through
  the divisor map, so no concrete instance could invoke them; `EigenvolumePointwiseLaw.lean`
  restates them with the two divisors and the identification between them as explicit arguments
  (`formOrder_shiftLaw_at`, `formOrder_eigen_shiftLaw_at`), assuming nothing about any other prime
  divisor.  `ToricHorizonDerivation.lean` then runs the general machinery on the toric model:
  `toric_shiftLaw` obtains the local order law at a coordinate divisor from the general law, with
  the ramification index, the Jacobian order and the eigenvolume condition supplied by the monomial
  map, and `toric_formOrder_eq_neg_one` concludes `c = -1` from it by the expansion fixed-point
  argument of Step 4.  Since the same value is computable directly, this is a test of the general
  proof rather than a new computation.
- 2026-08-06 -- Step 3's passage to an iterate formalised (`CommonPeriodIterate.lean`,
  `SchemeHorizonIterate.lean`).  The proof of Step 3 gives each component of the support its own
  period; the sentence "after a common iterate, every component is fixed" needs a common period,
  which is the product of the individual ones (`exists_common_period`, from `iterate_mul_eq_self`).
  Combined with backward stability and finiteness of the support this gives
  `exists_iterate_fixing_support`, and at scheme level `exists_iterate_fixing_horizon`: there is a
  single positive iterate fixing every component of the horizon.  This was the one sentence of
  Step 3 that the abstract ramification system did not cover, since it only produced periodicity
  one component at a time.
- 2026-08-06 -- Step 1 completed with the nonvanishing (`CoframeEigenvolumeNonzero.lean`).  The
  wedge of a whole basis is a basis vector of the top exterior power, hence nonzero
  (`topWedge_ne_zero`), so an invariant coframe determines a *nonzero* eigenvolume on which the
  induced map acts by the determinant, a unit (`exists_ne_zero_eigenvolume`).  The nonvanishing is
  not decoration: the order of the zero form is undefined, so every later step of the theorem
  presupposes it, and until now it was implicit.
- 2026-08-06 -- The bridge from forms to functions.  The top exterior power of a module with a
  finite basis is free of rank one, so every top form is a scalar multiple of the wedge of the basis
  (`eq_smul_topWedge`), and over a field a nonzero top form is a *nonzero* scalar times it
  (`exists_ne_zero_smul_eq_of_ne_zero`).  Applied to rational top forms this is what lets
  `div(Omega)` be treated as the divisor of a rational function, which is the form in which the
  horizon theorem is stated here: the eigenvolume is encoded as the ratio of the form to a fixed
  reference form.
- 2026-08-06 -- The side conditions shown indispensable (`EigenvolumeHypothesisSharpness.lean`).
  Finiteness of the support was already known to be necessary
  (`exists_infiniteSupport_order_ne_neg_one`); the other two side conditions of the horizon theorem
  are necessary as well.  Without ramification the local order law is satisfied by a constant order
  of any value (`exists_unramified_order_ne_neg_one`: identity divisor map, all indices one), and
  without surjectivity of the divisor map the backward orbit can escape so that no component is
  recurrent, making the ramification condition vacuous while the order is still not `-1`
  (`exists_nonsurjective_order_ne_neg_one`: the successor map).  All three hypotheses of
  `eigenvolumeOrder_eq_neg_one_of_someRamified` are therefore sharp, so Step 4's appeal to
  expansion is not an artefact of the proof.
- 2026-08-06 -- The tame different exponent freed from the presented shape
  (`TameMonicDifferentExponent.lean`).  Every monic polynomial is its leading power plus its lower
  monomials (`eq_eisensteinPoly_of_monic`), so the exact computation applies to an arbitrary monic
  polynomial whose coefficients below the leading one have valuation at least its degree:
  `addVal_eval_derivative_monic`, `addVal_eval_derivative_monic_succ`,
  `span_eval_derivative_monic`.  That coefficient hypothesis says exactly that the coefficients lie
  in the maximal ideal of the base, expressed in the valuation upstairs, so this is the form the
  result takes when the polynomial arises as the minimal polynomial of a uniformizer instead of
  being written down.  What still separates this from the general tame statement is only the
  monogenicity of the extension, not the shape of the polynomial.
- 2026-08-06 -- The tame different exponent for a monogenic extension
  (`TameMonogenicDifferentExponent.lean`).  Because the ramification index multiplies valuations, a
  coefficient in the maximal ideal downstairs has valuation at least the index upstairs
  (`le_addVal_map_of_addVal_ne_zero`) -- which is exactly the bound the exact computation needs.
  Hence for an extension of discrete valuation rings presented by an Eisenstein polynomial of degree
  equal to the ramification index, with that index a unit at the place, the derivative at a
  uniformizer has valuation exactly `e - 1` (`addVal_eval_derivative_map_eisenstein`).  The
  hypotheses are now the extension and its Eisenstein presentation, with no condition on the shape
  of the polynomial and no explicit coefficient bound: the `e - 1` of the order law (8) is proved
  for every monogenic tame totally ramified extension.
- 2026-08-06 -- An Eisenstein presentation presents a uniformizer
  (`EisensteinRootUniformizer.lean`).  In an extension of discrete valuation rings whose
  ramification index equals the degree of an Eisenstein polynomial, every root of that polynomial
  has valuation exactly one (`addVal_eq_one_of_eisenstein_root`): the constant coefficient
  contributes exactly the index, every other term at least that and, once the root has positive
  valuation, strictly more, so the ultrametric strict minimum pins the valuation.  This makes the
  presentation coherent -- the element it presents is automatically a uniformizer, so the different
  computation applies to it without assuming irreducibility separately.  Supporting lemmas
  `addVal_pow`, `eval_eisensteinPoly`, `eval_map_monic`.
- 2026-08-06 -- The different exponent consolidated.  An element of valuation one is a uniformizer
  (`irreducible_of_addVal_eq_one`), so combining with the previous entry gives
  `addVal_eval_derivative_of_eisenstein_root`: for an extension of discrete valuation rings and an
  Eisenstein presentation of degree the ramification index, with that index a unit at the place,
  the derivative at any root has valuation exactly `e - 1`.  Neither irreducibility of the presented
  element nor any bound on the coefficients upstairs is assumed -- the presentation supplies both.
  This is the `e - 1` of the order law (8) with the hypotheses reduced to the extension and its
  presentation.
- 2026-08-06 -- The strict minimum principle (`AddValuationStrictMin.lean`).  The corpus had only
  the inequality direction, that a uniform lower bound on the summands bounds the sum
  (`le_addVal_sum`).  `addVal_sum_eq_of_strict_min` is the matching exact statement: a finite sum in
  which one term has valuation strictly below every other has exactly that valuation.  This is what
  turns a valuation estimate into a valuation computation, and it is the tool the Eisenstein
  criterion needs: in the relation satisfied by a uniformizer the terms have valuations `e * v(c_i)
  + i`, pairwise distinct modulo `e`, so the minimum is attained once and the sum's valuation is
  pinned.
- 2026-08-06 -- The Eisenstein criterion proved, without completeness
  (`EisensteinCriterion.lean`).  `eisenstein_of_monic_uniformizer_root`: if a uniformizer of the
  upper ring satisfies a monic relation of degree the ramification index, that relation is
  automatically Eisenstein.  The argument is arithmetic, not topological: the term of index `i` has
  valuation `e * v(c_i) + i`, and these are pairwise distinct because their residues modulo `e` are
  the distinct indices, so the minimum is attained once and the strict minimum principle pins the
  valuation of the sum.  Since that valuation is `e`, the minimising index is the only one congruent
  to zero, giving `v(c_0) = 1` and pushing every other coefficient into the maximal ideal.
  Completeness was expected to be needed here and is not: it enters only in producing the monic
  relation, that is in `B = A[x]` itself.
- 2026-08-06 -- The tame different reduced to a monogenic presentation
  (`TameDifferentMonogenic.lean`).  For a monic relation of degree the ramification index, being
  Eisenstein and presenting a uniformizer are the *same* condition
  (`eisenstein_iff_addVal_eq_one`) -- each direction is one of the two valuation computations
  proved above.  Hence `addVal_eval_derivative_of_monic_uniformizer_root` and
  `span_eval_derivative_of_monic_uniformizer_root`: given the extension, a uniformizer satisfying a
  monic relation of degree `e`, and tameness, the derivative there has valuation exactly `e - 1` and
  the local different is the `(e-1)`-st power of the maximal ideal.  No hypothesis on the
  coefficients survives.  The `e - 1` of the order law (8) now rests on monogenicity alone.
- 2026-08-06 -- The monic relation produced rather than assumed
  (`TameDifferentFreeExtension.lean`).  An element of a finite free algebra satisfies the
  characteristic polynomial of multiplication by it, monic of degree the rank
  (`exists_monic_relation_of_free`, from Cayley-Hamilton).  So for a finite free extension of
  discrete valuation rings whose rank is the ramification index, a uniformizer automatically
  satisfies a monic relation of exactly that degree, and no monogenicity need be assumed:
  `exists_eisenstein_relation_of_free` shows the relation is Eisenstein, and
  `exists_monic_relation_addVal_eval_derivative` computes the valuation of its derivative as
  `e - 1`.  Freeness is not a restriction here, since a finite torsion-free module over a discrete
  valuation ring is free.  The quantity computed is the derivative of the characteristic
  polynomial; it is the different exactly when the uniformizer generates the extension.
- 2026-08-06 -- Digit expansion in a uniformizer (`UniformizerDigitExpansion.lean`).  If the residue
  extension is trivial, every element of the upper ring is a polynomial in a uniformizer with
  coefficients from the base, up to a remainder divisible by the chosen power
  (`exists_digit_expansion`, by induction on the exponent using `dvd_of_addVal_ne_zero`).  Carried
  out to the ramification index this says the powers below that index generate the upper ring modulo
  the maximal ideal of the base, which is the generation statement a monogenic presentation needs;
  what remains to conclude `B = A[x]` from it is Nakayama.
- 2026-08-06 -- Monogenicity proved, with no completeness (`MonogenicOfDigitExpansion.lean`).  The
  digit expansion says the powers of a uniformizer below the ramification index generate the
  extension modulo the maximal ideal of the base; Nakayama upgrades that to generation outright
  (`span_pow_eq_top`), using mathlib's `Submodule.le_of_le_smul_of_le_jacobson_bot` with the
  Jacobson radical identified as the maximal ideal.  So a finite extension of discrete valuation
  rings with trivial residue extension is generated by a single uniformizer.  Completeness was the
  expected obstacle throughout this arc and is needed nowhere: what the classical argument uses it
  for is infinite expansions, and the finite expansion plus Nakayama suffices.
- 2026-08-06 -- Monogenicity in algebra form (`adjoin_singleton_eq_top`).  The span of the powers
  being everything gives `A[x] = B` as an algebra, so a finite extension of discrete valuation rings
  with trivial residue extension is generated by any uniformizer.  This is the hypothesis mathlib's
  `conductor_mul_differentIdeal` needs in order to identify the different with the ideal generated
  by the derivative of the minimal polynomial; supplying it would turn the computation of the
  characteristic polynomial's derivative into a computation of the different itself.
- 2026-08-06 -- The conductor removed (`ConductorAdjoinTop.lean`).  The conductor of an element is
  the set of scalars carrying the ring into the subalgebra it generates, so when that subalgebra is
  everything the condition is vacuous and the conductor is the unit ideal
  (`conductor_eq_top_of_adjoin_eq_top`).  Combined with monogenicity this gives
  `conductor_eq_top_of_uniformizer` for a finite extension of discrete valuation rings with trivial
  residue extension.  The conductor is the factor standing between the derivative of a minimal
  polynomial and the different in mathlib's `conductor_mul_differentIdeal`; with it trivial, that
  identity reads `differentIdeal = span {f'(x)}` once the generation hypothesis is transported to
  the fraction field.
- 2026-08-06 -- Half the fraction-field transport (`AdjoinFractionTransport.lean`).  The image of
  the lower ring lands in the subalgebra generated over the lower fraction field
  (`map_mem_adjoin_of_mem_adjoin`, by induction on membership in the ring-level adjoin), so if the
  generator generates the ring then the image of the whole ring is contained in it
  (`range_le_adjoin_of_adjoin_eq_top`).  What remains for the full transport is that this subalgebra
  is a field -- true because the generator is integral over the lower fraction field -- from which
  it contains the fraction field of the upper ring and is therefore everything.
- 2026-08-06 -- The fraction-field transport completed (`adjoin_fraction_eq_top`).  The subalgebra
  generated over the lower fraction field is a field, because the generator is algebraic there, and
  it contains the image of the upper ring; so it contains the fraction field of that ring and is
  everything.  Together with `conductor_eq_top_of_uniformizer` this supplies both inputs of
  mathlib's `conductor_mul_differentIdeal`, whose conclusion then reads
  `differentIdeal A B = span {f'(x)}` for the minimal polynomial of a uniformizer -- and with the
  tame computation of that derivative, the different is the `(e-1)`-st power of the maximal ideal.
- 2026-08-06 -- The different of a monogenic extension (`DifferentIdealMonogenic.lean`).  With the
  conductor trivial, mathlib's identity collapses to
  `differentIdeal A B = span {aeval x (derivative (minpoly A x))}`
  (`differentIdeal_eq_span_aeval_derivative`).  Both of its hypotheses are now supplied by the
  preceding modules: the conductor is trivial because the uniformizer generates the extension, and
  the generation hypothesis holds over the fraction field by the transport.  What remains to reach
  `differentIdeal A B = (maximalIdeal B)^(e-1)` is the identification of the degree of the minimal
  polynomial with the ramification index, so that the tame computation of the derivative applies
  to it.
- 2026-08-06 -- The powers of a uniformizer are a basis (`UniformizerPowerBasis.lean`).  Distinct
  powers below the ramification index carry valuations in distinct residue classes modulo that
  index, so no two terms of a relation can have equal valuation and the strict minimum principle
  gives any relation a finite valuation, which a vanishing sum cannot have
  (`linearIndependent_pow`).  With the generation statement this makes them a basis
  (`uniformizerPowBasis`), so the rank of the extension equals the ramification index
  (`finrank_eq_ramificationIndex`) rather than being assumed equal to it.  This is the degree
  identification the different statement was waiting for.
