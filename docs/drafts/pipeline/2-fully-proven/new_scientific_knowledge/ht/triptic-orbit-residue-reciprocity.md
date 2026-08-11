# Triptic Orbit-Residue Reciprocity

- **ID:** `triptic-orbit-residue-reciprocity`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / RECIPROCITY LAW / COMPLETE INVARIANT
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` — the reciprocity law has an unconditional paper proof; completeness as a DA/HT invariant additionally depends on independent audit of the elliptic-gamma atomic theorem
- **Statement:** A meromorphic `1`-periodic function with constant mixed difference determines labelled orbital principal-part divisors on two noncommensurable elliptic curves. After the natural identification of their orbit sets with one rank-three quotient group, those divisors are exactly equal. Their common value is a complete invariant modulo differentially algebraic functions.

## Setup

Let `tau,sigma in H`, with

`1,tau,sigma`

linearly independent over `Q`. Put

`Lambda_tau=Z+Z tau`, `Lambda_sigma=Z+Z sigma`,

`H_3=Z+Z tau+Z sigma`, `G=C/H_3`,

and let `delta=d/dz`.

Let

`Q={F in Mer(C):Delta_1 F=0 and Delta_tau Delta_sigma F in C}`.

For `F in Q`, define the two quasi-elliptic boundary functions

`U_tau=Delta_sigma F`, `U_sigma=Delta_tau F`.

Then

`Delta_tau U_tau in C`, `Delta_sigma U_sigma in C`.

Thus `U_tau` has finitely many pole classes on the elliptic curve

`E_tau=C/Lambda_tau`,

while `U_sigma` has finitely many pole classes on

`E_sigma=C/Lambda_sigma`.

Translation by `sigma` is non-torsion on `E_tau`, and translation by `tau` is non-torsion on `E_sigma`. Their abstract orbit sets are canonically the same group:

`E_tau/<sigma> = C/(Lambda_tau+Z sigma)=G`,

`E_sigma/<tau> = C/(Lambda_sigma+Z tau)=G`.

## Labelled orbital principal parts

For a pole class `p` of `U_tau`, write

`PP_p(U_tau)=sum_(k>=1) a_(p,k)(z-p)^(-k)`

and encode its orders by

`L_p(X)=sum_(k>=1) a_(p,k)X^(k-1)/((-1)^(k-1)(k-1)!) in C[X]`.

Define the `tau`-side differential orbit-residue divisor

`R_tau(F)=sum_p L_p(delta)[-p+H_3] in C[delta][G]`.

Likewise, for a pole class `q` of `U_sigma`, write

`PP_q(U_sigma)=sum_(k>=1) b_(q,k)(z-q)^(-k)`,

`M_q(X)=sum_(k>=1) b_(q,k)X^(k-1)/((-1)^(k-1)(k-1)!)`,

and define

`R_sigma(F)=sum_q M_q(delta)[-q+H_3] in C[delta][G]`.

Changing fundamental parallelograms does not change either divisor. Terms from pole classes in the same non-torsion translation orbit add in the same `G`-coordinate.

These are ordinary orbital principal-part sums, with every pole order retained as a coefficient of `delta`. No gamma function enters their definition.

## Reciprocity theorem `[PROVED HERE]`

For every `F in Q`,

`R_tau(F)=R_sigma(F)`.

Equivalently, for every `g in G` and every `k>=1`,

`sum_(-p+H_3=g) a_(p,k)=sum_(-q+H_3=g) b_(q,k)`.

Thus the normalized order-`k` principal-part mass on each `sigma`-orbit of `E_tau` equals the normalized order-`k` principal-part mass on the corresponding `tau`-orbit of `E_sigma`.

The two curves have noncommensurable period lattices. The equality is not a residue theorem internal to either elliptic curve; it is a rank-three compatibility law imposed by the existence of the common primitive `F`.

### Direct proof from meromorphic local finiteness

This proof uses neither elliptic gamma nor differential Galois theory.

Fix `g in G`, choose `p in C` with `-p+H_3=g`, and fix a pole order `k>=1`. For `n,m in Z`, let

`c_(n,m)`

be the coefficient of `(z-(p+n tau+m sigma))^(-k)` in the principal part of `F`; set it to zero when there is no order-`k` pole. Period `1` makes this well defined, and `Q`-independence makes the points distinct modulo `Z`.

The order-`k` coefficient of `U_tau=Delta_sigma F` at the same point is

`B_(n,m)=c_(n,m+1)-c_(n,m)`.

Since `Delta_tau U_tau` is constant, the principal parts of `U_tau` are `tau`-periodic. Hence

`B_(n,m)=B_m`

is independent of `n`. Similarly, the coefficient of `U_sigma=Delta_tau F` is

`A_(n,m)=c_(n+1,m)-c_(n,m)=A_n`,

independent of `m`.

It follows that the array is additively separable. Explicitly, put

`a_n=c_(n,0)-c_(0,0)`, `b_m=c_(0,m)`.

Then

`c_(n,m)=a_n+b_m`

for all `n,m`.

Only finitely many `B_m` are nonzero. Indeed, the points `p+m sigma` are distinct on the compact elliptic curve `E_tau`, while `U_tau` has only finitely many pole classes there. Thus `b_m` is eventually constant at both ends; write its limits as `b_+` and `b_-`. Likewise, only finitely many `A_n` are nonzero, so `a_n` has limits `a_+` and `a_-`.

The two orbital principal-part sums in the coordinate `(g,k)` are the boundary jumps

`R_tau(g,k)=sum_m B_m=b_+-b_-`,

`R_sigma(g,k)=sum_n A_n=a_+-a_-`.

Now use meromorphic local finiteness. In the mixed quadrant `n -> +infinity`, `m -> -infinity`, the coefficient `c_(n,m)` is eventually the constant

`a_+ + b_-`.

There are infinitely many pairs in this quadrant for which

`Im(n tau+m sigma)`

stays bounded: take, for example, `m` to be the nearest negative integer to `-n Im(tau)/Im(sigma)`. After subtracting an integer from the real part, the corresponding points have an infinite subsequence in a compact rectangle. They are distinct by the `Q`-independence of `1,tau,sigma`.

If `a_+ + b_-` were nonzero, `F` would therefore have infinitely many order-`k` poles accumulating in a compact set, impossible for a meromorphic function. Hence

`a_+ + b_-=0`.

The opposite mixed quadrant gives

`a_- + b_+=0`.

Subtracting these identities yields

`a_+-a_-=b_+-b_-`.

Therefore `R_sigma(g,k)=R_tau(g,k)`. Since `g` and `k` were arbitrary, the two labelled divisors are equal.

## Mixed-value augmentation law `[PROVED HERE] [BRIDGE]`

The common divisor also remembers the constant mixed-difference value.  For

```text
D=sum_g L_g(delta)[g] in C[delta][G],
```

define its simple-residue augmentation by

```text
aug_0(D)=sum_g L_g(0).                                      (A1)
```

If `C=Delta_tau Delta_sigma F`, then

```text
aug_0(R_trip(F))=-C/(2 pi i).                               (A2)
```

Indeed, `U_tau=Delta_sigma F` is `1`-periodic and obeys

```text
U_tau(z+tau)-U_tau(z)=C.
```

Integrate `U_tau(z)dz` counterclockwise around a fundamental parallelogram with edges `1` and
`tau`.  The two `tau`-parallel edge integrals cancel by `1`-periodicity.  The translated
unit-edge integral differs from the original by `C`, so the full boundary integral is `-C`.
The residue theorem gives total residue `-C/(2 pi i)`, which is exactly the left side of (A2).
The same calculation for `U_sigma=Delta_tau F` gives the identical value on the other elliptic
boundary, consistently with reciprocity.

For the multiplicative object below, suppose

```text
C_Y(z)=c exp(2 pi i n z),    c in C*, n in Z.               (A3)
```

Then the common integer orbit divisor satisfies the exact charge law

```text
deg(D_Y)=-n.                                                 (A4)
```

To see this, apply (A2) to `F=delta Y/Y`.  Its mixed difference is
`delta C_Y/C_Y=2 pi i n`, while the simple residues of the two boundary logarithmic derivatives
are exactly the zero and pole orders defining `D_Y`.

Thus a global mixed-cocycle value and the total local orbit charge determine one another.  A
nonzero Fourier degree `n` forces nonzero common boundary charge `-n`; conversely, degree zero of
the common divisor forces the exponential character in (A3) to have `n=0`.  The one-curve
factor-of-automorphy/degree calculation is classical theta-function theory.  Its simultaneous
realization by the same labelled divisor on both noncommensurable elliptic boundaries is the
triptic reciprocity content.

### Second proof through the hypertranscendental normal form

Let `Psi=delta log Gamma(z;tau,sigma)`. The two one-orientation principal-part normal forms give

`F-R_tau(F)Psi in Mer_DA`,

`F-R_sigma(F)Psi in Mer_DA`.

Atomic defect independence makes the differential translation map

`C[delta][G] -> Mer/Mer_DA`, `D mapsto [D Psi]`,

injective. Subtraction therefore gives the same equality. This second proof is not needed for reciprocity, but it connects the unconditional residue law to the complete DA/HT invariant below.

## Completeness theorem `[PROVED HERE]`

Write the common divisor as

`R_trip(F)=R_tau(F)=R_sigma(F)`.

Then

`R_trip:Q -> C[delta][G]`

is a surjective homomorphism of differential translation modules, and

`ker R_trip=Q intersect Mer_DA`.

Consequently

`Q/(Q intersect Mer_DA) isomorphic to C[delta][G]`.

### Proof

The normal-form proof gives

`F-R_trip(F)Psi in Mer_DA`.

Freeness of the differential translation orbit of `Psi` shows that `F` is DA exactly when `R_trip(F)=0`. This identifies the kernel.

For any `D in C[delta][G]`, the function `F=D Psi` belongs to `Q` and has

`R_trip(F)=D`.

This proves surjectivity.

The completeness statement is therefore stronger than reciprocity alone: the common cross-curve residue divisor distinguishes every two mixed-constraint functions up to a DA summand.

## Exact DA and hypertranscendence criterion `[PROVED HERE]`

For every `F in Q`,

`F is DA iff R_trip(F)=0`.

If any labelled orbit coefficient survives, then `F` is hypertranscendental.

This turns local pole data on either elliptic boundary into a complete global differential-algebraic obstruction for the common primitive.

## Exact annihilator and spectrum `[PROVED HERE]`

Let `A=C[delta][G]`. For every `P in A`,

`P F is DA iff P R_trip(F)=0 in A`.

Hence

`Ann_DA^A(F)=Ann_A(R_trip(F))`.

For nonzero `R_trip(F)`, the exact DA translation spectrum is

`Spec_DA(F)=pi^(-1)(Stab_G(R_trip(F)))`.

The stabilizer is finite. Therefore every hypertranscendental member of `Q` has a DA spectrum that is a finite extension of `H_3`, and every such finite extension is realized.

## Differential boundary matroid `[PROVED HERE]`

For shifts `h_1,...,h_m`, with `q_i=h_i+H_3`,

`dtrdeg_(C(z)) C(z)<Delta_(h_1)F,...,Delta_(h_m)F>_delta`

is

`rank_(C(delta)){(t_(q_i)-1)R_trip(F):1<=i<=m}`.

Thus one cross-curve residue divisor controls the complete finite differential-dependence geometry of every translation defect.

## Multiplicative triptic reciprocity `[PROVED HERE]`

Let `Y` be a nonzero meromorphic function satisfying

`Y(z+1)=Y(z)`

and suppose its mixed multiplicative coboundary has constant logarithmic derivative:

`C_Y(z)=Y(z+tau+sigma)Y(z)/(Y(z+tau)Y(z+sigma))`,

`delta C_Y/C_Y in C`.

Equivalently, `C_Y` is a nowhere-vanishing exponential character. Since it is `1`-periodic, it has the form `c exp(2 pi i n z)` for some `c in C*` and `n in Z`.

Define the two shift quotients

`A_tau(z)=Y(z+sigma)/Y(z)`,

`A_sigma(z)=Y(z+tau)/Y(z)`.

Then

`A_tau(z+tau)=C_Y(z) A_tau(z)`,

`A_sigma(z+sigma)=C_Y(z) A_sigma(z)`.

Their divisors therefore descend respectively to finite divisors on `E_tau` and `E_sigma`. Sum the orders in the first divisor along `sigma`-orbits, and those in the second along `tau`-orbits. After identifying both orbit sets with `G`, the resulting integer divisors are equal:

`D_tau(Y)=D_sigma(Y)=:D_Y in Z[G]`.

### Direct proof

Apply the direct array proof of reciprocity to

`F=delta Y/Y`.

The exponential-character condition on the mixed multiplicative coboundary gives

`Delta_tau Delta_sigma F=delta C_Y/C_Y in C`.

Moreover,

`Delta_sigma F=delta A_tau/A_tau`,

`Delta_tau F=delta A_sigma/A_sigma`.

The residue of a logarithmic derivative is the zero or pole order. Hence the two order-one orbit-residue divisors of `F` are exactly `D_tau(Y)` and `D_sigma(Y)`, while all higher-order labels vanish. Additive reciprocity proves their equality.

### Exact DA/HT classification

Assuming the elliptic-gamma atomic theorem,

`Y is DA over C(z) iff D_Y=0`.

Indeed, the common divisor is `R_trip(delta Y/Y)`. If it vanishes, the completeness theorem makes `delta Y/Y` DA, and the first-order equation

`Y'=(delta Y/Y)Y`

plus differential-algebraic transitivity makes `Y` DA. The converse follows by logarithmic differentiation. Thus every nonzero divisor gives a hypertranscendental `Y`.

### Every shift quotient and finite translate product

For `h in C`,

`Y(z+h)/Y(z) is DA iff h+H_3 in Stab_G(D_Y)`.

For a finite integer divisor

`P=sum_g n_g[g] in Z[G]`,

choose lifts `a_g` and put

`Y_P(z)=product_g Y(z+a_g)^(n_g)`.

Then

`Y_P is DA iff P D_Y=0 in Z[G]`.

Finally, for shifts `h_1,...,h_m`, the differential transcendence degree of the quotient family

`Y(z+h_i)/Y(z)`

is

`dim_C span{(t_(h_i+H_3)-1)D_Y:1<=i<=m}`.

The rank may be taken over `C` rather than `C(delta)` because `D_Y` has integer, derivative-free coefficients.

This class contains the elliptic gamma function but is defined solely by an exponential-character mixed multiplicative constraint. The theorem classifies the entire class, including all finite translate products, by one finite integer divisor.

## Why this is not one-curve orbital-residue theory

The orbital residues of Dreyfus--Hardouin--Roques--Singer and the complete orbital/panorbital obstruction of Arreche--Babbitt solve

`f=T_s(g)-g`

inside the function field of one elliptic curve. They do not compare residue data from two noncommensurable elliptic curves, do not classify a common meromorphic primitive modulo the full DA field, and do not produce a rank-three differential group-algebra invariant.

The new feature here is reciprocity across the two boundary curves:

`(E_tau, translation by sigma) <-> (E_sigma, translation by tau)`.

Neither side alone determines why its orbit divisor must equal the other. The equality is the constraint-side shadow of the common triptic primitive.

## Attack by established triptic cohomology

Felder--Henriques--Rossi--Zhu interpret elliptic gamma functions as meromorphic sections of a gamma gerbe over the universal triptic curve and compute its multiplicative analytic cohomology. Their construction is the strongest parent-theory threat because it already relates different two-dimensional faces of a rank-three lattice.

The located theorems concern multiplicative cocycles, gerbe classes, pseudodivisors, and modular identities. They do not state:

- equality of the two labelled orbital principal-part divisors above for arbitrary `F in Q`;
- completeness modulo differentially algebraic functions;
- the free `C[delta][G]` module;
- the exact DA annihilator and spectrum;
- the `C(delta)` boundary-matroid formula.

The reciprocity theorem may ultimately admit a gerbe-cohomological reformulation, but no equivalent result has been located.

## Other parent and rediscovery attacks

1. **Classical theta/Mittag--Leffler theory.** It proves each one-sided principal-part expansion, but not equality of the two expansions modulo orbit identification. This is why the normal-form card is a bridge while reciprocity remains live.
2. **Panorbital residues.** These complete elliptic summability and characterize differential integrability for one translation. They do not provide cross-curve reciprocity.
3. **Parameterized difference Galois theory.** It supplies atomic independence and telescoping criteria, but does not define or compare the two residue divisors.
4. **Ruijsenaars minimal solutions.** These classify selected first-order analytic difference solutions up to periodic ambiguity, not the mixed-constraint class modulo DA functions.
5. **Kato's rational-period theorem.** It proves DA in the commensurable case and explicitly leaves non-rational periods unknown.
6. **Nishizawa, Narukawa, Winding, and recent geometric families.** These supply higher elliptic gamma functions, modular identities, cone variants, and arithmetic cocycles, but no differential orbit-residue reciprocity.

Preliminary exact, equivalent, stronger, mechanism, citation-neighborhood, and older-parent searches through 2026 found no such theorem.

## Significance gate

The theorem supplies a new kind of residue law:

- it compares local meromorphic data on two different elliptic curves;
- it is complete for DA versus HT behavior of an infinite natural function class;
- it determines exact annihilators, spectra, and differential matroids;
- its multiplicative form classifies DA versus HT behavior of every meromorphic solution whose triptic multiplicative cocycle is an exponential character, together with all finite translate products and shift quotients;
- every algebraic value of the invariant is realized;
- it converts a rank-three compatibility constraint into a directly readable finite invariant.

This is qualitatively stronger than proving one more named special function hypertranscendental.

## Boundaries

1. Rational dependence of `1,tau,sigma` destroys the non-torsion orbit geometry and may introduce nonconstant joint constants.
2. The theorem is meromorphic; essential singularities are excluded.
3. Coefficients of the differential translation algebra are constant. DA-function coefficients are not classified.
4. Reciprocity itself is unconditional. Only completeness, the exact DA/HT criterion, and the annihilator/matroid consequences depend on the independently unaudited paired telescoping theorem behind elliptic-gamma atomicity.
5. Scientific priority remains provisional until experts in elliptic difference Galois theory and gamma gerbes inspect both proof and literature.

## Lean formalization boundary

Formalizing the finite group-algebra equality would certify only the last formal step. The analytic content requires elliptic principal parts, non-torsion translation orbits, two elliptic function fields, and the atomic theorem, none of which exist in the local Lean tree. Formalization now would be theatre.

## Gates

- [x] Two intrinsic one-curve residue divisors defined without gamma.
- [x] Natural identification of their orbit index sets with `C/H_3` proved.
- [x] Cross-curve reciprocity proved directly from meromorphic local finiteness, without gamma or Galois theory.
- [x] Completeness modulo DA functions proved.
- [x] Exact DA/HT criterion proved.
- [x] Exact differential-translation annihilator and spectrum proved.
- [x] Differential boundary-matroid formula proved.
- [x] Multiplicative divisor reciprocity and complete finite-product classification proved.
- [x] Every invariant and every finite spectrum extension realized.
- [x] Routine one-orientation normal form separated and demoted.
- [x] Panorbital-residue and gamma-gerbe parent attacks completed preliminarily.
- [ ] Independent audit of elliptic-gamma atomicity and paired telescoping.
- [ ] Independent expert literature audit across gerbes and elliptic summability.
- [ ] Final scientific-priority verdict.

## Primary sources checked

- C. Hardouin and M. F. Singer, *Differential Galois Theory of Linear Difference Equations*, Mathematische Annalen 342 (2008), 333--377.
- G. Felder, A. Henriques, C. A. Rossi, and C. Zhu, *A gerbe for the elliptic gamma function*, Duke Mathematical Journal 141 (2008), 1--74.
- C. E. Arreche and M. W. Babbitt, *Panorbital residues and elliptic summability*, arXiv:2508.18247 (2025).
- T. Dreyfus, C. Hardouin, J. Roques, and M. F. Singer, elliptic difference Galois and orbital-residue results.
- S. N. M. Ruijsenaars, *First order analytic difference equations and integrable quantum systems*, Journal of Mathematical Physics 38 (1997), 1069--1146.
- M. Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational Period*, Funkcialaj Ekvacioj 64 (2021), 225--235.

## Log

- 2026-07-10 — Isolated after the one-orientation normal form failed the routine-parent novelty gate.
- 2026-07-10 — Defined both labelled orbital principal-part divisors intrinsically on the two elliptic boundary curves.
- 2026-07-10 — Proved their equality through two independent normal forms and differential-translation freeness.
- 2026-07-10 — Proved completeness, exact annihilators, spectra, realization, and the boundary matroid.
- 2026-07-10 — Distinguished the theorem from one-curve orbital/panorbital summability and from multiplicative gamma-gerbe cohomology.

## Lean status — the reciprocity theorem is formalized unconditionally

The "Lean formalization boundary" section above is retired: it claimed that the analytic content
requires elliptic principal parts and two elliptic function fields, none of which exist in the local
Lean tree.  In fact the direct proof needs only the Laurent coefficients of a meromorphic germ, and
the corpus already owned those (`MeromorphicLaurentCoefficient.lean`).  What was missing were three
properties of that transform and the two geometric reduction arguments; all are now built.

`GaloisForLFunctions/HTGeometry/MeromorphicLaurentTranslation.lean` (wired, axiom-clean):

    laurentCoeff_comp_add         translation equivariance of the Laurent transform
    laurentCoeff_congr            the coefficients depend only on the punctured germ
    laurentCoeff_eq_zero_of_analyticAt
    laurentCoeff_eq_zero_of_meromorphicOrderAt_nonneg
    meromorphicOrderAt_neg_of_laurentCoeff_ne_zero
                                  a nonzero negative coefficient forces a pole
    finite_setOf_laurentCoeff_ne_zero_of_bounded
                                  **local finiteness**: only finitely many points of a bounded set
                                  carry a nonzero principal-part coefficient
    laurentCoeff_add, laurentCoeff_sub, laurentCoeff_add_const
    laurentCoeff_shiftDiff        the coefficients of `z ↦ f(z+h) - f(z)` are the differences
    laurentCoeff_add_zsmul_of_period

`GaloisForLFunctions/HTGeometry/TripticCornerAccumulation.lean` (wired, axiom-clean):

    cornerIndex                   `m = -⌈n·Im τ / Im σ⌉`, the compensating index
    cornerIndex_im_bound          it keeps `n·Im τ + m·Im σ` inside `(-Im σ, 0]`
    cornerIndex_tendsto_atBot     and drives `m → -∞`
    laurentCoeff_add_intCast      integer translation invariance from `1`-periodicity
    laurentCoeff_const_eq_zero_of_mixedQuadrant
                                  **the mixed-quadrant accumulation law**: a `1`-periodic
                                  coefficient constant on a mixed quadrant has that constant zero
    finite_setOf_laurentCoeff_ne_zero_orbit
                                  **finitely many nonzero coefficients along a lattice orbit**

`GaloisForLFunctions/HTGeometry/TripticOrbitResidueReciprocity.lean` (wired, axiom-clean):

    eq_of_forall_ge_increment_zero, eq_of_forall_le_increment_zero
    sum_Ico_increment_telescope, exists_symmetric_bound_of_finite_support
    triptic_orbit_residue_reciprocity :
      for `F` meromorphic on `ℂ`, `1`-periodic, with constant mixed difference, and for `τ, σ` in
      the upper half plane with `1, τ, σ` independent over `ℤ`,

        ∑ᶠ m : ℤ, laurentCoeff (Δ_σ F) (p + m·σ) ℓ = ∑ᶠ n : ℤ, laurentCoeff (Δ_τ F) (p + n·τ) ℓ

      for every base point `p` and every negative index `ℓ`.

That is the card's reciprocity theorem verbatim, one `(g, ℓ)` coordinate at a time, and the
coordinatewise form is exactly what the card states as the equivalent formulation.  The proof is the
card's own: the discrete separability core (`DiscreteOrbitReciprocity.lean`) is now fed by proved
analytic inputs instead of hypotheses.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every declaration above, and
`lake build GaloisForLFunctions.HTGeometry` succeeds.

Still to formalize on this card: the augmentation law `(A2)`, which needs a residue theorem on a
parallelogram; and the completeness, DA/HT, annihilator, matroid and multiplicative-classification
consequences, which the card already flags as resting on the independently unaudited elliptic-gamma
atomic theorem.

## Lean status — the local argument principle

`GaloisForLFunctions/HTGeometry/MeromorphicLogDerivResidue.lean` (wired, axiom-clean):

    laurentCoeff_const_div_sub          the residue of `c/(z-a)` is `c`
    logDeriv_eventuallyEq_of_nhdsNE     the logarithmic derivative is a punctured-germ invariant
    logDeriv_sub_zpow                   `logDeriv (w ↦ (w-a)^n) z = n/(z-a)`
    laurentCoeff_logDeriv_eq_order :
      for `f` meromorphic at `a` of finite order `n`,
        laurentCoeff (logDeriv f) a (-1) = n

This is the local form of the argument principle — mathlib has no complex residue at all — and it
is what converts the additive reciprocity theorem at index `ℓ = -1` into the card's multiplicative
divisor statement: the order-one orbit-residue divisors of `δ Y / Y` are the zero/pole order
divisors of the two shift quotients.

## Lean status — multiplicative triptic reciprocity

Added to `TripticOrbitResidueReciprocity.lean` (wired, axiom-clean):

    laurentCoeff_logDeriv_eq_untop            the residue of `δY/Y` at a point is the order of `Y`
    triptic_multiplicative_divisor_reciprocity :
      for `Y` meromorphic on `ℂ`, nowhere locally zero, `1`-periodic, whose triptic multiplicative
      cocycle has constant logarithmic derivative,

        ∑ᶠ m : ℤ, ord(Y, p + mσ + σ) - ord(Y, p + mσ)
          = ∑ᶠ n : ℤ, ord(Y, p + nτ + τ) - ord(Y, p + nτ)

The summands are exactly the zero/pole orders of the two shift quotients `A_τ = Y(·+σ)/Y` and
`A_σ = Y(·+τ)/Y`, so this is the card's `D_τ(Y) = D_σ(Y)`.  The meromorphy of `δY/Y` and its
`1`-periodicity are derived from those of `Y`, not assumed.

Both unconditional theorems of the card — additive and multiplicative reciprocity — are therefore
formalized.  The remaining statements (completeness, exact DA/HT criterion, annihilator and
spectrum, boundary matroid, and the DA/HT half of the multiplicative classification) rest, as the
card's own boundary note 4 records, on the independently unaudited elliptic-gamma atomic theorem,
and are not unconditional on paper either.

## Correction — the elliptic-gamma atomic theorem is corpus-owned, not an external parent

Every boundary note on this card that defers to "the independently unaudited elliptic-gamma atomic
theorem" is stale.  The order-one atomic input is formalized in this tree:

    GaloisForLFunctions/HTGeometry/EllipticGammaAtomicOverDAExtension.lean
      ellipticGammaExternalDefectFamily_differentialIndependent_daExtension

Its hypotheses are the data of the class only — both periods in the upper half plane, `ℚ`-linear
independence of the source periods, and the theta-translation nonresonance and separation
conditions on the shift family.  There is no assumed theorem.  `#print axioms` reports
`[propext, Classical.choice, Quot.sound]`.

So the consequences on this card that were labelled conditional on that parent are conditional on
nothing external: what remains for them is Lean derivation work inside this corpus, not an
unformalized classical input.

## Lean progress — the integral channel of the common divisor

Added to `GaloisForLFunctions/HTGeometry/TripticSourceDivisor.lean` (wired, axiom-clean):

    intCast_finsum                                     casting an integer unrestricted sum
    triptic_multiplicative_divisor_reciprocity_int     **reciprocity in ℤ, not only after
                                                       complexification**
    laurentCoeff_shiftDiff_logDeriv                    the order-one coefficient is the shift order
    finite_support_shiftOrder                          the orbital divisor is finitely supported
    tripticOrbitCharge                                 the integral orbital charge `∑ᶠ` of a source
    tripticOrbitCharge_mul                             **additive under multiplication of sources**
    tripticOrbitCharge_shift                           invariant along the orbit direction

The integral channel is exactly what the Kummer-content card argues is load-bearing: after
tensoring with `ℂ` every divisor becomes infinitely divisible and the root spectrum disappears.
`tripticOrbitCharge_mul` is the homomorphism hypothesis of the abstract Kummer classification
(`hasSourceRootModuloKernel_iff_content_dvd`); what still separates the two is surjectivity of the
divisor map, i.e. realization of an arbitrary finite integral divisor by a translated gamma product.

## Lean status — the augmentation law `(A2)` and the charge law `(A4)`

The residue theorem needed for `(A2)` is now in the tree, for poles of **arbitrary order** — mathlib
has no complex residue at all, and the vendored `PNTPlus` rectangle residue theorem is restricted to
simple poles by an explicit `HasSimplePolesOn` hypothesis.

`GaloisForLFunctions/HTGeometry/MeromorphicPrincipalPart.lean` (wired, axiom-clean):

    exists_taylor_remainder        finite Taylor expansion with analytic remainder, in the
                                   `taylorCoeffZero` normalization
    principalPart                  the truncated principal part of a meromorphic germ, written with
                                   inverse natural powers, so it is analytic off the pole and
                                   vanishes at it
    analyticAt_principalPart
    eq_add_principalPart           **the principal-part splitting**: off `a`, a function whose
                                   clearing shift `t ↦ tᵏ f(a+t)` is analytic at `0` is an analytic
                                   germ at `a` plus its principal part truncated at `k`

`GaloisForLFunctions/HTGeometry/RectangleResidueTheorem.lean` (wired, axiom-clean):

    hIntegral_of_primitive, vIntegral_of_primitive
    rectangleIntegral_eq_zero_of_primitive
                                   the four-edge fundamental theorem of calculus
    invPowPrimitive, hasDerivAt_invPowPrimitive
    rectangleIntegral_inv_pow_eq_zero
                                   `∮ (s-p)^{-m} = 0` for `m ≥ 2`, from the single-valued primitive
                                   `(s-p)^{1-m}/(1-m)`
    principalTail, analyticAt_principalTail, rectangleIntegral_principalTail_eq_zero
    principalPart_eq_tail_add_residue
    rectangleIntegral'_principalPart
                                   the boundary integral of a principal part is its order-one
                                   Laurent coefficient
    rectangleBorderIntegrable_finset_sum, rectangleIntegral_finset_sum
    rectangleIntegral'_eq_sum_laurentCoeff
                                   **the residue theorem on a rectangle, poles of arbitrary order**

`GaloisForLFunctions/HTGeometry/TripticAugmentationLaw.lean` (wired, axiom-clean):

    vIntegral_period_eq            the two vertical edges cancel by `1`-periodicity
    hIntegral_top_eq               the top edge exceeds the bottom by exactly `C`
    triptic_augmentation_law :
      for `U` `1`-periodic with `U(s+τ) = U s + C` and `Im τ > 0`, meromorphic on the closed
      rectangle of width `1` and height `Im τ` with finitely many interior poles,

        ∑ p ∈ P, laurentCoeff U p (-1) = -C / (2πi)

    triptic_charge_law :
      if `logDeriv Y` gains `2πin` under `τ`, then `∑ p ∈ P, ord(Y, p) = -n`

That is `(A2)` and `(A4)` verbatim.  No oblique contour was needed: because `1` lies in the lattice,
the axis-parallel rectangle of width `1` and height `Im τ` is already a fundamental domain of
`ℤ + ℤτ`, so the card's parallelogram argument runs on a rectangle, where mathlib's Cauchy theorem
applies directly.  Interval integrability along the shifted bottom edge is *derived* from
`1`-periodicity plus analyticity on the border, not assumed.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every declaration above.

## Lean progress — the realizing source belongs to the class

`GaloisForLFunctions/HTGeometry/EllipticGammaConeCocycle.lean` (wired, axiom-clean):

    expChar_add, expChar_one, expChar_add_one, expChar_neg_mul_self, one_sub_expChar_neg
    coneProduct_periodic            every factor is `1`-periodic, hence so is the product
    ellipticGammaCone_periodic      **`Γ(z+1) = Γ(z)`**
    coneProduct_cocycle_identity    the four-fold shift identity
                                      `(1 - e(z))·N = (1 - e(-z))·D`
    coneProduct_mixed_cocycle       `N = -e(-z)·D`
    ellipticGammaCone_mixed_cocycle **`C_Γ(z) = Γ(z+a+b)Γ(z)/(Γ(z+a)Γ(z+b)) = -e(-z)`**

Together with the two shift relations added to `ExpConeProduct.lean`,

    singleFactor, singleProduct     `P(w) = ∏_{k ≥ 0}(1 - e(k b + w))`
    singleProduct_shift             `P(w) = (1 - e(w))·P(w + b)`
    hasProd_singleProduct_shifted   Fubini for the double product
    coneProduct_shift               `Φ(w) = P(w)·Φ(w + a)`
    coneProduct_comm                `Φ` is symmetric in its two periods

this establishes both defining properties of the multiplicative triptic source class for `Γ`:
`1`-periodicity, and a mixed multiplicative coboundary that is an exponential character (so its
logarithmic derivative is the constant `-2πi`).  Combined with the divisor computation, the
realizing source is now a proved member of the class with proved divisor `[0]`, and its translates
realize every class `[g]`.

The cancellation is exact and needs no analysis beyond the shift relations: in

    N = Φ(-z)Φ(a+b-z)Φ(z+a)Φ(z+b),   D = Φ(z+a+b)Φ(z)Φ(b-z)Φ(a-z),

every cone product cancels against a partner, leaving `P(-z)P(z+b)` against `P(z)P(b-z)`, whose
ratio is `(1 - e(-z))/(1 - e(z)) = -e(-z)`.

## Lean progress — the orbital charge is a class function on `G`

`GaloisForLFunctions/HTGeometry/TripticChargeClassFunction.lean` (wired, axiom-clean):

    meromorphicOrderAt_of_period       a period of a function is a period of its order
    shiftOrder_of_period               hence of every shift order
    tripticOrbitCharge_of_period       **`1`-invariance**, from `1`-periodicity of the source
    tripticOrbitCharge_of_shiftOrder_invariant
                                       **`τ`-invariance**, from `τ`-invariance of the shift-quotient
                                       divisor — the exact content of the mixed-cocycle condition,
                                       since an exponential character has no zeros or poles
    eq_of_add_zsmul                    one period upgrades to all its integer multiples
    tripticOrbitCharge_of_periodGroup  **the charge is constant on classes of `H₃ = ℤ + ℤτ + ℤσ`**

This is the well-definedness of `D_Y` as an element of `ℤ[G]`, `G = ℂ/H₃`: the three directions have
three different reasons, and only the `τ` one uses the defining cocycle condition of the source
class.  Together with `tripticOrbitCharge_mul` (additivity) and the elliptic-gamma realization it
completes every input of the abstract Kummer classification except finiteness of the class support
and the identification of the kernel with the differentially algebraic members.

Added to the same module (wired, axiom-clean):

    meromorphicOrderAt_eq_zero_of_untop₀
    finite_setOf_meromorphicOrderAt_ne_zero  the divisor of a meromorphic function meets every
                                             compact set finitely
    finite_setOf_shiftOrder_ne_zero          hence so does the shift-order support: a base point
                                             carries charge only if the source has a zero or pole at
                                             it or at its `σ`-translate

With `H₃`-invariance and compact local finiteness together, the charge is a well-defined finitely
supported function on `G` once a bounded fundamental domain is chosen, which is the last structural
input of `D : M → ℤ[G]`.

## Lean progress — finite order everywhere, and the half-line law at every period point

`GaloisForLFunctions/HTGeometry/EllipticGammaConeOrder.lean` (wired, axiom-clean):

    exists_notMem_of_countable                    a countable set is not the plane
    analyticOrderAt_ne_top_of_countable_zeroSet   an entire function with countable zero set is
                                                  nowhere locally zero
    withTop_sub_ne_top                            a difference of finite orders is finite
    countable_coneProduct_zeroSet                 the zero set is indexed by `ℕ × ℕ × ℤ`
    countable_ellipticGammaConeNum_zeroSet
    meromorphicOn_ellipticGammaCone
    meromorphicOrderAt_ellipticGammaCone_ne_top   **the order of `Γ` is finite everywhere**

Finiteness of the order is precisely the hypothesis `tripticOrbitCharge_mul` needs, so the divisor
map is now known to be additive on the realizing sources.

Added to `EllipticGammaConeDivisor.lean` (wired, axiom-clean):

    coneProduct_periodPoint_orbit_eq_zero_iff      **the general pole half line**: along the
                                                   `b`-orbit of `c + d·a + e·b`, the denominator
                                                   vanishes exactly for `d ≤ 0` and `m ≤ -e`
    coneProduct_num_periodPoint_orbit_eq_zero_iff  and the numerator exactly for `1 ≤ d`,
                                                   `1 - e ≤ m`
    meromorphicOrderAt_ellipticGammaCone_periodPoint
                                                   the order along that orbit, as the difference of
                                                   the two indicator conditions

The two half lines are disjoint (`d ≥ 1` against `d ≤ 0`), and in both regimes the shift difference
is supported at the single index `m = -e`.  So the charge is `1` on the orbit of *every* period
point, not only the origin — which is the statement that `D_Γ` is the class `[0]` in `ℤ[G]` rather
than a base-point-dependent number.

## Lean progress — products of gamma translates add their divisors

Added to `EllipticGammaConeDivisor.lean` and `EllipticGammaConeOrder.lean` (wired, axiom-clean):

    untop₀_ite_sub_ite
    shiftOrder_ellipticGammaCone_periodPoint       **the shift order along the orbit of any period
                                                   point is supported at the single index `m = -e`**,
                                                   uniformly in the two regimes `1 ≤ d` and `d ≤ 0`
    tripticOrbitCharge_ellipticGammaCone_periodPoint
                                                   hence the charge is `1` at *every* period point
    finite_shiftOrder_support_ellipticGammaCone_periodPoint
    ellipticGammaConeTranslate_eq_comp
    meromorphicOn_ellipticGammaConeTranslate
    meromorphicOrderAt_ellipticGammaConeTranslate_ne_top
    finite_shiftOrder_support_ellipticGammaConeTranslate
                                                   the support is a single index inside the class and
                                                   empty outside it
    tripticOrbitCharge_ellipticGammaConeTranslate_mul
                                                   **`D_{Y₁Y₂} = D_{Y₁} + D_{Y₂}` for translates**

The uniformity is the point: in the zero regime the shift difference is
`[1-e ≤ m+1] - [1-e ≤ m]` and in the pole regime it is `[m ≤ -e] - [m+1 ≤ -e]`, and both equal
`[m = -e]`.  So the charge does not depend on which representative of the class is taken as base
point, which is what makes `D` a function on `ℤ[G]` rather than on `ℂ`.

With additivity now available *on the realizing sources* — the finiteness and finite-order
hypotheses of `tripticOrbitCharge_mul` are discharged, not assumed — the card's "products add
divisors, integer powers give signed multiplicities" is formal for the gamma translates.

## Lean progress — the elliptic gamma source as a convergent atom series

`GaloisForLFunctions/HTGeometry/EllipticGammaConeSource.lean` (wired, axiom-clean):

    logDeriv_coneFactor            `(log(1 - e(w)))′ = -2πi·e(w)/(1 - e(w))`
    norm_logDeriv_coneFactor_le    where the factor is within `1/2` of one, its logarithmic
                                   derivative is at most `4π` times the deviation
    summable_logDeriv_coneFactor   hence the atom series converges, by the same geometric
                                   domination as the product
    logDeriv_coneProduct_eq_tsum   **`(log Φ)′(z) = ∑_{j,k ≥ 0} -2πi e(ja + kb + z)/(1 - e(ja + kb + z))`**

`Ψ = δ log Γ` is the difference of two such series, one at `z` and one at `a + b - z`.  This is the
object the principal-part normal form `F − R_trip(F)Ψ ∈ Mer_DA` is written in, now available as an
explicit convergent series rather than as a name.

Added to the same module (wired, axiom-clean):

    ellipticGammaSource            `Ψ = δ log Γ`, as a definition rather than a name
    logDeriv_of_periodic           a period of a function is a period of its logarithmic derivative
    ellipticGammaSource_periodic   **`Ψ(z+1) = Ψ(z)`**
    ellipticGammaSource_eq_sub     **`Ψ(z) = -(log Φ)′(a+b-z) - (log Φ)′(z)`**, the splitting into
                                   two convergent atom series

So `Ψ` is now a constructed object with its `1`-periodicity proved and its two-series expansion
available.  Its mixed difference is the logarithmic derivative of the cocycle `-e(-z)`, i.e. the
constant `-2πi`, which is the statement that `Ψ` itself lies in the mixed-constraint class `Q`.

## Lean progress — the two shift laws for the source, and the atom cancellation

Added to `ExpConeProduct.lean` and `EllipticGammaConeSource.lean` (wired, axiom-clean):

    differentiable_singleFactor, hasProdLocallyUniformlyOn_singleFactor
    differentiable_singleProduct       **the single-index product `P` is entire**
    singleProduct_eq_zero_iff
    logDeriv_comp_add_const
    logDeriv_singleProduct_shift       `(log P)′(w) = (log(1 - e(w)))′ + (log P)′(w + b)`
    logDeriv_coneProduct_shift         `(log Φ)′(w) = (log P)′(w) + (log Φ)′(w + a)`
    logDeriv_one_sub_expChar           `(log(1 - e(w)))′ = -2πi·e(w)/(1 - e(w))`
    expChar_atom_sum                   **`e(z)/(1 - e(z)) + e(-z)/(1 - e(-z)) = -1`**

These are the four ingredients of the mixed-difference computation.  Writing `S = (log Φ)′` and
`T = (log P)′`, the eight terms of `Ψ(z+a+b) + Ψ(z) - Ψ(z+a) - Ψ(z+b)` pair off under the first
shift law into `-T(z) + T(z+b) - T(-z) + T(b-z)`; the second shift law turns that into
`-L(z) - L(-z)` with `L(w) = -2πi·e(w)/(1 - e(w))`; and the atom identity evaluates it to `-2πi`.

So the mixed difference of `Ψ` is the constant `-2πi`, which is exactly the membership
`Ψ ∈ Q` that the normal form is stated against — now reduced to assembling four proved identities
rather than to any analytic input.

## Lean progress — `Ψ ∈ Q` is proved

`ellipticGammaSource_mixed_difference` (wired, axiom-clean):

    Ψ(z+a+b) + Ψ(z) - Ψ(z+a) - Ψ(z+b) = -2πi

off the zeros of the eight cone products and four single-index products involved, and off the two
points where `e(±z) = 1`.  Together with `ellipticGammaSource_periodic` this is exactly the
membership of the source in the mixed-constraint class:

    Δ_1 Ψ = 0,   Δ_a Δ_b Ψ = -2πi ∈ ℂ.

The proof is the three-stage collapse the card describes, now carried out mechanically: the eight
cone-source terms pair off under `logDeriv_coneProduct_shift` into four single-index terms; those
pair off under `logDeriv_singleProduct_shift` into two atoms; and `expChar_atom_sum` evaluates the
two atoms to `-1`, giving the constant `-2πi`.  No analytic input beyond the two product shift
relations is used.

## Lean progress — the residue normal form on one orbit

The kernel identification is now formal down to a single remaining step.  Five new modules, all
wired into `GaloisForLFunctions.HTGeometry`, all `#print axioms`-clean:

```text
TripticEntireRigidity          const_of_entire_of_periodic_of_mixed_const — an ENTIRE member of `Q`
                                is constant AND its mixed constant `C` is forced to `0`.  Two
                                Liouvilles: `Δ_σ f` is entire, `1`-periodic and changes by `C` under
                                `τ`, so its derivative is lattice-periodic hence constant, so it is
                                affine, and a genuine period kills both the slope and `C`
MeromorphicLogDerivLocalForm   laurentCoeff_logDeriv_eq_zero_of_le — a logarithmic derivative has NO
                                Laurent coefficient below the residue.  The corpus previously
                                computed only the residue itself
JacobiThetaSourcePrincipalPart analyticOrderAt_jacobiTheta₂_eq_one (every theta zero is simple) and
                                the COMPLETE principal part of `Ψ_θ = δ log θ`: residue `1` on the
                                odd half-period orbit, nothing anywhere else
TripticSeparatedPrincipalPart  exists_finiteSupport_separation_of_orbit_sum_eq_zero — a vanishing
                                orbital divisor makes both separated families of the coefficient
                                array FINITELY SUPPORTED, i.e. confines the poles to finitely many
                                full `σ`-lines and finitely many full `τ`-lines
TripticLineAtom /              rowAtom, colAtom and the incidence law: a `σ`-line atom has residue
TripticAtomIncidence /          `1` at every orbit point of its own row and `0` on every other row,
TripticResidueNormalForm        by `ℚ`-independence alone; hence
                                exists_atomCombination_residue_normalForm — every source of
                                vanishing orbital divisor has the residues of an explicit finite
                                combination of theta-source translates at every orbit point
```

Also built and reusable well beyond this card:
`DifferentialAlgebraicAntiderivative.differentialAlgebraicOver_of_deriv` — differential algebraicity
is stable under **integration**, not only differentiation (`k⟨y′⟩` has finite transcendence degree,
`y` satisfies `y′ = c` over it, then finite-transcendence descent), together with its analytic form
`differentiallyAlgebraic_of_deriv`, a pure jet reindexing.

What is left is the extension from order `-1` to all orders (the jets of the theta source, with pole
order `j+1`), the passage from one orbit to the finitely many that occur, and the application of
`const_of_entire_of_periodic_of_mixed_const` to the pole-free remainder.

## Correction — the "what is left" list above is stale

The closing sentence of the previous section ("the extension from order `-1` to all orders, the
passage from one orbit to the finitely many that occur, and the application of
`const_of_entire_of_periodic_of_mixed_const` to the pole-free remainder") names work that is
**already in the tree**.  An audit of the modules resolves every item:

    TripticJetAtom.lean            jetAtom, rowJetAtom, colJetAtom and the incidence laws at
                                   order j+1; a jet is invisible at every other negative order
    TripticJetAtomShift.lean       atomPoleSet, its countability and open complement, the σ-shift
                                   law for positive-order jets, the mixed second difference
    TripticGlobalCoefficient.lean  the base-point-free formula for every Laurent coefficient
    TripticTransverseCoefficient.lean   the row and column fields
    TripticIndexBound.lean         only finitely many shift indices connect two pole classes
    TripticLineFiniteness.lean     poles with invariant principal part lie on finitely many cosets
    TripticLineSupportFinite.lean  only finitely many lines carry a nonzero transverse coefficient
    TripticOrderBound.lean         the column field is a row field, and the orders are bounded
    TripticAtomSum.lean            the weighted atom sum of one order in one direction
    TripticTotalAtomSum.lean       the total atom sum, 1-periodic with vanishing mixed difference
    TripticRemainderRigidity.lean  the pole-free remainder is entire, and constant off a countable
                                   set
    TripticKernelNormalForm.lean   exists_totalAtomSum_no_principal_part
    TripticKernelIdentification.lean
      exists_const_sub_totalAtomSum_of_vanishing_divisor :
        **a source with vanishing orbital divisor is, off a countable set, an explicit finite
        combination of theta-source jets plus a constant, and its mixed constant is zero**

So the whole principal-part half of the kernel identification is formal, at every order and over all
orbits.  Do not rebuild any of it.

## Lean progress — the atoms are differentially algebraic

The remaining half of `ker R_trip = Q ∩ Mer_DA` is that the atom family itself is differentially
algebraic.  That is now proved.

`GaloisForLFunctions/HTGeometry/ThetaLogDerivDifferentialAlgebraic.lean` (wired, axiom-clean):

    differentialAlgebraicOver_ratFunc_thetaLogDerivMero :
      **the theta logarithmic derivative is differentially algebraic over `ℂ(z)`**
    differentialAlgebraicOver_ratFunc_differentialJet          DA passes to every jet
    differentialAlgebraicOver_ratFunc_differentialJet_thetaLogDerivMero
    differentialAlgebraicOver_ratFunc_addTranslationMeroEquiv_thetaLogDerivMero :
      and to every translate
    differentialAlgebraicOver_ratFunc_differentialJet_addTranslationMeroEquiv_thetaLogDerivMero :
      hence to the whole atom family of the normal form

The mechanism is that the source is *not* elliptic — a quasiperiod step changes it by `-2πi` — but
its derivative is, and differential algebraicity is stable under integration.  Both inputs were
already corpus-owned: `thetaLogDerivMero_deriv_mem_ellipticMeroField` (the quasiperiod constant
disappears under differentiation), `differentialAlgebraicOver_of_mem_ellipticMeroField` (a doubly
periodic germ is DA, with no elliptic generation theorem), and `differentialAlgebraicOver_of_deriv'`
(the antiderivative law).  The translate statement additionally uses the compositum-to-`ℂ(z)` base
change.

### The one remaining step of the kernel theorem

`exists_const_sub_totalAtomSum_of_vanishing_divisor` produces a *function* identity off a countable
set; the differential algebraicity above is a statement about *germs* in `meroField ℂ`.  What is
left is exactly the realization bridge in the germ-to-function direction: a jet relation over
`ℂ(z)` satisfied by a germ is satisfied by its meromorphic normal form.  The opposite direction
(`differentialAlgebraicOver_of_differentiallyAlgebraic_toMeromorphicNFOn`) is already in the tree, so
this is one lemma, not a layer.  With it, `ker R_trip = Q ∩ Mer_DA` closes, and with the surjectivity
of `R_trip` — realized by the already-built gamma-translate sources — so does the completeness
theorem.

## Lean progress — the germ-to-function jet bridge is proved

The step the previous section isolated is closed.

`GaloisForLFunctions/HTGeometry/MeromorphicNormalFormJetBridge.lean` (wired, axiom-clean):

    analyticAt_mvPolynomialJetEval :
      a polynomial in the point and the jets of a function analytic at a point is analytic there
    differentiallyAlgebraic_toMeromorphicNFOn_of_differentialAlgebraicOver :
      **a differentially algebraic germ has a globally differentially algebraic normal form**

The tree already contained the opposite direction
(`differentialAlgebraicOver_of_differentiallyAlgebraic_toMeromorphicNFOn`), so the jet bridge of the
meromorphic field is now an equivalence for fractions of entire representatives.

Three steps carry it.  A relation in the field restricts along `restrictMeroAlgHomRatFunc` to a disc
on which the denominator does not vanish; there the fraction is analytic and
`exists_relation_of_differentialAlgebraicOver_analyticMeroElement` turns the field relation into a
pointwise one.  The evaluated relation is analytic on the whole analytic locus of the normal form,
which is the complement of a countable set (`Meromorphic.countable_compl_analyticAt`) and therefore
connected, so the identity theorem spreads the vanishing from the disc to the entire locus.  At a
pole every jet of the normal form is the junk value `0`, so multiplying the relation by the value
slot — the same device that makes the Weierstrass equation global — absorbs those points and gives
an equation valid at every point of the plane.

### What the kernel theorem still needs

Only the realization dictionary: that the germ of the atom sum is the corresponding finite
combination of jets of translates of `thetaLogDerivMero`, i.e. that passing from germs to functions
commutes with the field operations off the poles.  With it, the chain closes:

    atoms are DA germs      (ThetaLogDerivDifferentialAlgebraic)
    → the atom sum is a DA germ            (field closure)
    → its normal form is DA as a function  (MeromorphicNormalFormJetBridge)
    → F is DA                              (F agrees with the atom sum plus a constant off a
                                            countable set)

and `ker R_trip = Q ∩ Mer_DA` follows from `exists_const_sub_totalAtomSum_of_vanishing_divisor`.

## Lean progress — the positive-order atoms are differentially algebraic as functions

`GaloisForLFunctions/HTGeometry/JetAtomDifferentiallyAlgebraic.lean` (wired, axiom-clean):

    norm_lattice_ge                 a nonzero point of `ℤ + ℤσ` has norm at least `min 1 (Im σ)`
    dist_atomPoleSet_ge             so two distinct poles of a line atom are separated
    eventually_nhdsNE_notMem_atomPoleSet
                                    hence the poles are isolated: on every punctured neighbourhood
                                    the atom is eventually regular
    meromorphicOn_jetAtom
    periodic_toMeromorphicNFOn_jetAtom_one, ..._sigma
                                    the normal form of a positive-order jet is periodic for both
                                    generators
    differentiallyAlgebraic_toMeromorphicNFOn_jetAtom_succ :
      **every positive-order jet of a line atom satisfies a global algebraic differential
      equation**

This route needs no germ theory: the jet is lattice-periodic because the quasiperiod constant
disappears under one differentiation, and a lattice-periodic meromorphic normal form is
differentially algebraic by the corpus's own elliptic theorem — the elliptic generation theorem is
never used.  The isolation of the poles is elementary lattice separation, not the identity theorem.

Remaining for the kernel: the order-zero atom (its normal form's derivative is the order-one jet's
normal form, so `differentiallyAlgebraic_of_deriv` applies once the pole-value bookkeeping is
recorded), and the passage from the individual atoms to their finite combination, which runs through
the two jet bridges and the field closure of `daOverRatFuncField`.

## Lean progress — the kernel of the orbit-residue divisor is proved

The chain the previous section laid out is complete.  Four new modules, all wired, all
`[propext, Classical.choice, Quot.sound]`:

    MeromorphicFractionRealization.lean
      toMeromorphicNFOn_congr             the normal form depends only on the punctured germs
      eventually_nhdsNE_ne_zero_of_germ_ne_zero
                                          the zeros of an entire function with a nonzero germ are
                                          isolated
      RealizesMero x f                    `f` agrees with a fraction of entire representatives of
                                          the germ `x` off the zeros of the denominator
      meromorphicOn_of_fraction, toMeromorphicNFOn_eq_of_fraction
      differentialAlgebraicOver_of_realizesMero,
      differentiallyAlgebraic_of_realizesMero
                                          realization transports differential algebraicity both ways
      realizesMero_zero, realizesMero_add, realizesMero_const_mul, realizesMero_sum
      differentiallyAlgebraic_toMeromorphicNFOn_sum

    JetAtomDifferentiallyAlgebraic.lean   (extended)
      not_differentiableAt_of_not_analyticAt, meromorphicOrderAt_deriv_neg
      eventuallyEq_deriv_of_eventuallyEq_nhdsNE
      deriv_toMeromorphicNFOn             **differentiation commutes with the normal form**
      deriv_jetAtom
      differentiallyAlgebraic_toMeromorphicNFOn_jetAtom
                                          every jet of a line atom, the atom itself included

    TripticAtomSumDifferentiallyAlgebraic.lean
      exists_fraction_jetAtom             every jet of a line atom is a quotient of two entire
                                          functions: the base case is `θ′/θ`, the step is the
                                          quotient rule
      RealizedDA and its closure under constant multiples, sums and finite sums
      realizedDA_jetAtom, realizedDA_rowAtomSum, realizedDA_totalAtomSum
      differentiallyAlgebraic_toMeromorphicNFOn_totalAtomSum

    TripticKernelDifferentialAlgebraicity.lean
      frequently_nhdsNE_notMem_of_countable
      toMeromorphicNFOn_eq_of_eq_off_countable :
        two meromorphic functions agreeing off a countable set have the same normal form
      realizedDA_const
      differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor :
        **`Cst = 0` and the source is differentially algebraic**

That last theorem is the kernel half of the completeness statement:

    F ∈ Q  with vanishing orbital divisor  ⟹  F ∈ Mer_DA,

with no hypothesis beyond the card's own setting — `F` meromorphic on `ℂ`, `1`-periodic, constant
mixed second difference, `1, τ, σ` independent over `ℤ` and each of `τ, σ` in the upper half plane.

Three mechanisms carry it, and each is worth keeping:

* the *quotient-rule induction*: a jet of a line atom is `A_j / B_j` with `A_{j+1} = A_j′B_j -
  A_jB_j′` and `B_{j+1} = B_j²`, so every atom has an entire fraction presentation and therefore a
  germ, without any theory of meromorphic functions as quotients;
* the *realization dictionary*: sums and constant multiples of realized functions are realized by
  the corresponding germs, so the field-theoretic closure of `daOverRatFuncField` becomes a closure
  statement about functions — this is what makes a finite combination of atoms differentially
  algebraic;
* *agreement off a countable set does not move the normal form*: the complement of a countable set
  is dense, so the difference of the two normal forms vanishes frequently near a point of its
  analytic locus, the identity theorem spreads that over the locus, and the locus contains a
  punctured neighbourhood of every point.

### What the completeness theorem still needs

Only the other half: surjectivity of `R_trip` and the converse `R_trip(F) ≠ 0 ⟹ F` is
hypertranscendental.  The first is the realization of an arbitrary finite divisor by a product of
gamma translates, for which the corpus already owns `SourceDivisorSurjectivity`,
`EllipticGammaConeDivisor` and `EllipticGammaConeOrder`; the second is freeness of the differential
translation orbit of the source.

## Lean progress — the kernel of the multiplicative orbital charge

`GaloisForLFunctions/HTGeometry/TripticMultiplicativeKernel.lean` (wired, axiom-clean):

    differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge :
      **a multiplicative triptic source whose orbital charge vanishes on every orbit has a
      differentially algebraic logarithmic derivative, and its mixed constant is zero**

This is the multiplicative kernel, and it is a two-line consequence of the additive one once the
order bookkeeping is done: a logarithmic derivative has no Laurent coefficient below its residue
(`laurentCoeff_logDeriv_eq_zero_of_le`), so the orbital divisor of `δ log Y` is concentrated in
order `-1`, where `laurentCoeff_shiftDiff_logDeriv` identifies it with the shift order; vanishing
orbital charge therefore means a vanishing orbital divisor at *every* order, which is exactly the
hypothesis of `differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor`.

Together with `tripticOrbitCharge_mul` (the charge is additive) and
`tripticOrbitCharge_ellipticGammaConeTranslate` (every class is realized) this supplies two of the
three inputs of the abstract Kummer classification: the divisor map is a homomorphism, every class
is in its image, and its kernel contains the differentially algebraic sources.  What is still
missing for the third is the reverse inclusion — a source with nonzero charge is
hypertranscendental — which is the freeness of the differential translation orbit of the elliptic
gamma source, and the group-theoretic packaging of the class `M` itself as an `AddCommGroup` on
which the divisor map is an `AddMonoidHom`.

## Lean progress — the additive orbital divisor of the elliptic gamma source

`GaloisForLFunctions/HTGeometry/EllipticGammaSourceOrbitalDivisor.lean` (wired, axiom-clean):

    additiveOrbitalDivisor F σ p          the order `-1` orbital divisor of an additive source
    additiveOrbitalDivisor_logDeriv :
      the additive divisor of a logarithmic derivative is the multiplicative orbital charge
    additiveOrbitalDivisor_ellipticGammaSourceTranslate :
      **the translated elliptic gamma source realizes the unit class**
    additiveOrbitalDivisor_ellipticGammaSource_of_notMem :
      and carries no charge on any orbit outside the period group
    additiveOrbitalDivisor_ellipticGammaSource

This is the source side of the normal form: with the kernel theorem already proved, what a general
mixed-constraint source needs is a *subtractable* object carrying a prescribed divisor, and the
gamma translates are exactly that.  The remaining structural step is the finiteness of the divisor
support of a general source in `Q` — finitely many orbit classes, by the coset finiteness of the
pole set of `Δ_σ F`, and finitely many orders, by the boundedness of its pole orders — after which
`F` minus the corresponding finite gamma combination has vanishing divisor and the kernel theorem
applies, giving the normal form `F - R_trip(F)Ψ ∈ Mer_DA` for arbitrary `F`.

## Lean progress — the divisor support of a general source is finite

`GaloisForLFunctions/HTGeometry/TripticBoundaryPoleClasses.lean` (wired, axiom-clean):

    pole_invariant_zsmul          a translation invariance of the negative Laurent coefficients
                                  invariates the pole set under the whole cyclic group it generates
    laurentCoeff_invariant_zsmul  and the coefficients themselves
    exists_finset_boundaryPoleClasses :
      **the poles of `Δ_σ F` lie on finitely many cosets of `ℤ + ℤτ`**
    exists_orderBound_boundary :
      **and their orders are bounded below by a single integer**

Neither needs the vanishing hypothesis; both hold for every source of the mixed-constraint class.
The mechanism is that `Δ_σ F` is exactly `1`-periodic and changes by the mixed constant under a
`τ`-step, and a constant moves no Laurent coefficient of negative index — so the whole negative
principal-part data is invariant under `ℤ + ℤτ`, the pole set is lattice invariant, and the corpus's
`exists_finset_pole_classes` (finitely many poles in a compact fundamental parallelogram) applies.
The order bound is then one minimum over a finite set of coset representatives, transported back by
the same invariance.

This is the finiteness the general normal form needs: the orbital divisor of an arbitrary `F ∈ Q`
is carried by finitely many orbit classes and finitely many orders, so a finite combination of
gamma translates — whose divisors are computed in `EllipticGammaSourceOrbitalDivisor` — can be
subtracted to leave a source of vanishing divisor, which the kernel theorem sends to `Mer_DA`.

## Lean progress — the gamma jets are an exact divisor basis

`GaloisForLFunctions/HTGeometry/EllipticGammaJetSourceDivisor.lean` (wired, axiom-clean):

    additiveOrbitalDivisorAt F σ p ℓ           the orbital divisor at an arbitrary order
    additiveOrbitalDivisorAt_iteratedDeriv :
      **the jet law for orbital divisors** — differentiating a source multiplies its orbital
      divisor by the falling product and shifts the order
    additiveOrbitalDivisorAt_logDeriv_of_le    a logarithmic derivative has no divisor below `-1`
    gammaJetSource a b g j                     the `j`-th jet of the translated gamma source
    additiveOrbitalDivisorAt_gammaJetSource_self :
      **`(-1)ʲ j!` at order `-(j+1)` on its own class**
    additiveOrbitalDivisorAt_gammaJetSource_of_ne_order :
      **and `0` at every other order**
    additiveOrbitalDivisorAt_gammaJetSource_of_notMem :
      and `0` on every orbit outside the period group

The jet law needs no commutation of `Δ_σ` with differentiation — which would be false at the poles,
where the junk values of the two constructions differ.  It goes through `laurentCoeff_shiftDiff`
first, so only the *coefficients* are differentiated, and there the corpus's jet law applies
verbatim.

With this the divisor basis is complete: one gamma jet per class and per order, each carrying its
own slot and invisible in every other, and the finiteness theorems of
`TripticBoundaryPoleClasses` say that a general source occupies only finitely many slots.  What
remains for the general normal form is the finite bookkeeping that assembles the correcting
combination — after which `F` minus it has vanishing divisor and the kernel theorem applies.

## Lean progress — the orbital divisor is linear

`GaloisForLFunctions/HTGeometry/TripticOrbitalDivisorLinearity.lean` (wired, axiom-clean):

    laurentCoeff_const_mul
    laurentCoeff_boundary_periodic_one, laurentCoeff_boundary_periodic_tau
                                        the two invariances of the boundary coefficients, extracted
    finite_support_orbitalDivisorTerm :
      **only finitely many points of a `σ`-orbit carry a nonzero boundary coefficient**
    additiveOrbitalDivisorAt_add, additiveOrbitalDivisorAt_sub,
    additiveOrbitalDivisorAt_const_mul :
      **the orbital divisor is linear on sources of finite orbit support**

Linearity is not formal: the orbital divisor is an unrestricted sum, and `finsum` splits over a sum
only when both families are finitely supported.  The finite-support theorem is what licenses it, and
it holds for every mixed-constraint source — `Δ_σ F` has `1`- and `τ`-invariant negative
coefficients, and the corpus's orbit accumulation theorem turns that invariance into finiteness on
each orbit.

With linearity, the correction can be assembled slot by slot: subtracting a scaled gamma jet changes
the divisor in exactly one `(class, order)` slot and leaves every other slot untouched, so a finite
induction over the occupied slots — finite by `TripticBoundaryPoleClasses` — reduces an arbitrary
source to one of vanishing divisor.

## Lean progress — the divisor is a class function, and the basis is translation covariant

Two more modules, wired and axiom-clean.

`GaloisForLFunctions/HTGeometry/TripticOrbitalDivisorClassFunction.lean`:

    additiveOrbitalDivisorAt_shift_sigma   moving the base point along its own orbit reindexes the
                                           unrestricted sum
    additiveOrbitalDivisorAt_shift_one, ..._shift_tau
    additiveOrbitalDivisorAt_classFunction :
      **the orbital divisor depends only on the class of the base point in `ℂ/(ℤ+ℤτ+ℤσ)`**

`EllipticGammaJetSourceDivisor.lean` (extended):

    additiveOrbitalDivisorAt_gammaJetSource_translate :
      the divisor of a translated gamma jet is that of the untranslated one at the translated base
      point
    additiveOrbitalDivisorAt_gammaJetSource_of_notMem_translate :
      hence a gamma jet carries no divisor off the class of its translation point

The class-function property is what makes a correction well posed: the number to be cancelled is
attached to the class, not to a chosen representative, so a coefficient computed at one
representative kills the divisor at every other point of the same class simultaneously.

### The assembly, and the one device it needs

With the divisor a class function, the correction can be written down in closed form rather than
built by induction:

    A = Σ_{j<J} Σ_{q∈P} ( d(q, -(j+1)) / ((-1)ʲ j! · #{q' ∈ P : q' ≡ q}) ) · gammaJetSource τ σ q j

where `P` is the finite pole-class set of `TripticBoundaryPoleClasses` and `J` its order bound.  The
multiplicity divisor is the corpus's own `lineCount` device from `TripticAtomSum`, and it removes
the need to deduplicate `P` modulo the full period group: every representative of a class
contributes its share, and because `d` is a class function the shares sum to `d` exactly.  Its
divisor is then computed by `additiveOrbitalDivisorAt_add`/`_const_mul` over the two finite sums,
with `additiveOrbitalDivisorAt_gammaJetSource_self`, `..._of_ne_order` and
`..._of_notMem_translate` evaluating each term.

## Lean progress — the basis is a class function too

Added to `EllipticGammaJetSourceDivisor.lean` (wired, axiom-clean):

    additiveOrbitalDivisor_ellipticGammaSource_periodPoint :
      the additive orbital divisor of the gamma source is `1` at **every** period point
    additiveOrbitalDivisorAt_gammaJetSource_periodPoint :
      **a gamma jet realizes `(-1)ʲ j!` at every point of its own class**

No new analytic input was needed: the corpus already proved the multiplicative statement
`tripticOrbitCharge_ellipticGammaCone_periodPoint` — the charge of the elliptic gamma at an
arbitrary period point `c + d·τ + e·σ` is `1`, by the half-line laws
`coneProduct_periodPoint_orbit_eq_zero_iff` and `coneProduct_num_periodPoint_orbit_eq_zero_iff` —
and `additiveOrbitalDivisor_logDeriv` converts it, after which the jet law lifts it to order
`-(j+1)`.

This was the last evaluation lemma the closed-form correction needed.  Every term of

    A = Σ_{j<J} Σ_{q∈P} ( d(q, -(j+1)) / ((-1)ʲ j! · #{q' ∈ P : q' ≡ q}) ) · gammaJetSource τ σ q j

is now computable at every base point and order:

* `additiveOrbitalDivisorAt_gammaJetSource_periodPoint` — on its own class, at its own order;
* `additiveOrbitalDivisorAt_gammaJetSource_of_ne_order` — zero at every other order;
* `additiveOrbitalDivisorAt_gammaJetSource_of_notMem_translate` — zero off its class;

and the divisor of the sum is assembled by `additiveOrbitalDivisorAt_add` and
`additiveOrbitalDivisorAt_const_mul`, whose finite-support hypotheses come from
`finite_support_orbitalDivisorTerm`.

## Lean progress — the divisor of a finite sum

`GaloisForLFunctions/HTGeometry/TripticOrbitalDivisorFinsetSum.lean` (wired, axiom-clean):

    FiniteOrbitSupport F σ p ℓ            the boundary coefficients are nonzero at only finitely
                                          many points of the orbit
    meromorphicOn_finsetSum
    finiteOrbitSupport_add, finiteOrbitSupport_finsetSum
    additiveOrbitalDivisorAt_finsetSum :
      **the orbital divisor of a finite sum of sources is the sum of their orbital divisors**

The two statements have to be proved by the same induction and cannot be separated: additivity of
the divisor is conditional on finite orbit support, so the induction step needs the support of the
partial sum, which is itself only available inductively.  The support of a sum sits inside the union
of the supports because the boundary coefficient of a sum is the sum of the boundary coefficients —
that is where meromorphy at each orbit point is used.

This is the last general-purpose lemma the correction needs.  Its divisor is now a finite double sum
of evaluated terms, each computed by the three gamma-jet lemmas, and the remaining work is the
counting identity: over the representatives of one class the multiplicity-divided coefficients sum
back to the class value, because the divisor is a class function.

## Lean progress — the class relation and the support of a gamma jet

`GaloisForLFunctions/HTGeometry/TripticGammaCorrectionBasis.lean` (wired, axiom-clean):

    SameClass τ σ q p                     `q - p` lies in the period group
    sameClass_iff, sameClass_refl, sameClass_symm, sameClass_trans, periodGroupMem_neg
    classCount P τ σ p                    the number of representatives of the class of `p` in `P`
    classCount_congr                      it depends only on the class
    laurentCoeff_shiftDiff_gammaJetSource the boundary coefficients of a gamma jet, in terms of the
                                          source it differentiates
    finiteOrbitSupport_gammaJetSource :
      **every gamma jet has finite orbit support at every negative order**

The support statement is a three-way case split and each branch closes for a different reason:
above the jet's own order the falling product of the jet law vanishes; below it the underlying
logarithmic derivative has no coefficient at all; and at its own order the support is exactly the
shift-order support, which the corpus already knows is a single index
(`finite_shiftOrder_support_ellipticGammaConeTranslate`).

That was the last side condition the finite-sum divisor law needs, so every summand of the
correction now satisfies the hypotheses of `additiveOrbitalDivisorAt_finsetSum`, and `classCount`
supplies the multiplicity divisor that makes the class sum collapse.

## Lean progress — the triptic normal form, and the class `Q` restated as it is defined

An audit of the Lean class `Q` found the formalisation too narrow.  The card defines

    Q = {F ∈ Mer(ℂ) : Δ₁F = 0 and Δ_τΔ_σF ∈ ℂ},

an identity in `Mer(ℂ)`; the Lean statements demanded it pointwise, `∀ z`.  For a function with
poles the pointwise form is *unsatisfiable*: at a pole one side of the mixed identity has a finite
artefact value where the identity requires the cancellation of an infinity.  In particular the
elliptic gamma source `Ψ` — the very element the completeness theorem needs in `Q` — does not
satisfy it, so the old hypotheses admitted only pole-free sources.

`GaloisForLFunctions/HTGeometry/TripticGermConstraint.lean` restates the class as it is defined:

    PeriodicOneGerm F        ∀ z, ∀ᶠ w in 𝓝[≠] z, F (w+1) = F w
    MixedConstGerm F τ σ C   ∀ z, ∀ᶠ w in 𝓝[≠] z, F(w+τ+σ) - F(w+τ) - F(w+σ) + F w = C

with the transport toolkit (`tendsto_nhdsNE_add_const`, `eventuallyEq_boundary_shift_one/_tau/
_sigma`), the pointwise recovery at points of analyticity (`mixedConst_eq_of_analyticAt`), and the
differentiation law `mixedConstGerm_deriv` / `mixedConstGerm_iteratedDeriv_succ`.  Laurent
coefficients depend only on the punctured germ, so every coefficient-level consequence survives:
the whole chain from `laurentCoeff_boundary_periodic_one` up through the reciprocity theorem, the
separation of the principal-part array, the kernel normal form, the kernel identification and the
kernel differential algebraicity now runs on the germ hypotheses, unchanged in conclusion.

`GaloisForLFunctions/HTGeometry/EllipticGammaSourceGermConstraint.lean` then proves the membership
the card asserts:

    mixedConstGerm_ellipticGammaSource : MixedConstGerm (ellipticGammaSource a b) a b (-2πi)
    periodicOneGerm_gammaJetSource     : every jet is exactly `1`-periodic
    mixedConstGerm_gammaJetSource_zero : the source jet carries the constant `-2πi`
    mixedConstGerm_gammaJetSource_succ : every higher jet carries the constant `0`

The twelve cone- and single-product nonvanishing side conditions of the pointwise cocycle are
discharged by `eventually_nhdsNE_ne_zero_of_countable_zeroSet`: each product is entire with a
countable zero set, hence nonzero on a punctured neighbourhood of every point.

`GaloisForLFunctions/HTGeometry/TripticNormalForm.lean` assembles the correction and closes the
normal form:

    exists_gammaCorrection_vanishing_divisor :
      ∃ P J, ∀ p ℓ < 0, additiveOrbitalDivisorAt (F - gammaCorrection τ σ F P J) σ p ℓ = 0

    exists_gammaCorrection_differentiallyAlgebraic :
      ∃ P J, Cst = gammaCorrectionConst τ σ F P J ∧
        DifferentiallyAlgebraic (toMeromorphicNFOn (F - gammaCorrection τ σ F P J))

The first is a three-way case split: on a class represented in `P` the correction reproduces the
divisor exactly; off every represented class the source has no divisor either, because a nonzero
boundary coefficient forces a pole and every pole class is represented; and above the order bound of
the boundary function both sides vanish.  The second feeds that to the kernel theorem, which applies
because `F - A` is again a member of the class: `A` is a finite combination of gamma jets, each
exactly `1`-periodic with a constant mixed difference.

The second conjunct is the normal form `F - R_trip(F)Ψ ∈ Mer_DA`.  The first is the mixed-value
augmentation law (A2): the mixed constant of a source is exactly the constant carried by the
zeroth-order slice of its own correction, which is `-2πi` times the total simple-residue mass.

## Lean progress — surjectivity of the orbit-residue divisor

`GaloisForLFunctions/HTGeometry/TripticGammaCorrection.lean` now carries the general object rather
than only the correcting one:

    jetCombination τ σ c P J   = Σ_{j<J} Σ_{q∈P} c q j · gammaJetSource τ σ q j
    gammaCorrection τ σ F P J  = jetCombination τ σ (gammaCorrectionCoeff τ σ F P) P J

with the divisor laws proved once, for arbitrary weights: `..._jetCombination_eq_sum`,
`..._eq_single`, `..._of_notMem`, `..._of_le`.  The counting theorem for the correction is the
instantiation with the correcting weights.

`TripticNormalForm.lean` adds

    exists_mem_class_with_prescribed_divisor :
      ∀ P J d, ∃ Y C, MeromorphicOn Y ℂ ∧ PeriodicOneGerm Y ∧ MixedConstGerm Y τ σ C ∧
        (divisor of Y at order i < J on the class of q ∈ P is d q i) ∧
        (divisor of Y vanishes off every class of P, and above the order bound)

which is the **surjectivity half of the completeness theorem**: every prescribed divisor datum on
finitely many classes and finitely many orders is realized inside the class `Q`, by the jet
combination with weights `d q j / ((-1)ʲ j!)`.

### What the kernel half still needs, and where it comes from

`ker R_trip ⊇ Q ∩ Mer_DA` is the kernel theorem, already closed.  The reverse inclusion is the
freeness of the differential translation orbit of `Ψ`.  The corpus owns that input already, and
unconditionally:

    EllipticGammaDefectFieldEscape.ellipticGammaTranslatePacket_diffIndepOn_of_separated
      — the order-one translation packet `{Ψ} ∪ {Ψ(·+a) : a ∈ A}` is differentially independent
        over `ℂ`, for `A` nonresonant and pairwise separated;
    DifferentialOperatorRowHypertranscendence.hypertranscendentalOver_differentialOperatorRow_of_ne_zero
      — a nonzero constant-coefficient differential-operator row applied to a differentially
        independent family is hypertranscendental over the constants.

Composing them: a nonzero jet combination is hypertranscendental over `ℂ`, hence — by transitivity
of differential algebraicity over the differentially algebraic extension `ℂ(z)/ℂ` — not
differentially algebraic over `ℂ(z)` either.  Since the correction's weights are recovered from its
divisor, a differentially algebraic member of `Q` has vanishing divisor.  What remains is the
bridge between the two presentations: the germ of `iteratedDeriv j (logDeriv (ellipticGammaConeTranslate τ σ q))`
is the `j`-th differential jet of the translated `ellipticGammaLogDerivMero` germ.

## Lean progress — freeness of the differential translation orbit

`GaloisForLFunctions/HTGeometry/TripticJetRowFreeness.lean` (wired, axiom-clean):

    differentialIndependent_ellipticGammaTranslateFamily :
      a finite family of translates of the elliptic gamma logarithmic derivative, at nonresonant
      and pairwise separated shifts, is differentially independent over the constants

    hypertranscendentalOver_ellipticGammaTranslateRow :
      hence any nonzero constant-coefficient differential-operator row applied to it is
      hypertranscendental over `ℂ`

The first is the packet theorem of `EllipticGammaDefectFieldEscape` transported from the set form
`DiffIndepOn` to the family form: the translates are pairwise distinct because the defects are, and
a family whose members lie in a differentially independent set and are pairwise distinct is
differentially independent.  The second is the operator-row criterion of
`DifferentialOperatorRowHypertranscendence` — the two were built for the all-order multiple
elliptic-gamma argument and apply verbatim here.

Neither carries an added hypothesis: the inputs are the card's own standing assumptions on the
periods, plus the statement that the base points are distinct classes lying off the period lattice —
which is what "distinct orbits in `G`" means.

That is the freeness the kernel half needs, in the germ presentation.  The remaining step is
presentational: identify the germ of `jetCombination τ σ c P J` with the operator row
`Σ_q (Σ_j c q j ∂ʲ) Ψ_q`, so that the hypertranscendence transfers to the function and contradicts
differential algebraicity of a member of `Q` with nonzero divisor.
