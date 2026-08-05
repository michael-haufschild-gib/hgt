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

Two improvements over the paper argument are now proved.  First, the passage to an iterate in
step 3 is unnecessary: the cycle equation `c + 1 = (product of e along the cycle) * (c + 1)`
already forces `c = -1` on every periodic component, so `f` itself has reduced horizon.  Second,
both standing hypotheses are sharp.  Dropping expansion admits `c = 5` on a one-point support;
dropping finiteness of the support admits `c(n) = 2^n - 1` on `N` with `F(n) = n - 1` and
expanding indices throughout.

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

What remains paper-level is the rest of the algebraic-geometric input to the abstract system: the
eigenvolume identity (7) from `f^*|W`, the passage from the local different to the global divisor
pullback formula (8) on a smooth projective variety, and the int-amplified eigenvalue bound giving
`e_E > 1` on recurrent components.  These need Weil divisors, the canonical divisor of a finite
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
