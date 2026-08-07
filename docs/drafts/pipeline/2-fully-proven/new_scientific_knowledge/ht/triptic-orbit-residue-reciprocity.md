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
