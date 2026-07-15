# Differential-algebraic gauges make HT orbit laws divisor-blind

- **ID:** `da-gauge-ht-divisor-blindness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / foundational route boundary — `[PROVED HERE] [BRIDGE]`
- **Statement:** The complete differential-algebraic matroid of all translates of a meromorphic
  function, the corresponding logarithmic-derivative matroid, and every source class taken modulo
  differentially algebraic functions are invariant under multiplication by a nonzero
  differential-algebraic gauge. Rational gauges also preserve minimal differential aperture
  exactly and already realize arbitrary finite
  functional-equation/conjugation-symmetric off-critical zero packets.  Consequently no theorem
  expressed only in these HT invariants can determine an RH-type zero-location property.

## Medalist lens

Hypertranscendence is a statement in a differential field.  RH is a statement about the location
of a divisor.  The first question is therefore not whether HT is strong, but whether the divisor
descends through the equivalence relation under which HT is invariant.

It does not.  The gauge group of nonzero DA meromorphic functions changes divisors while preserving
the differential transcendence data.  The smallest counteraction is multiplication by a
polynomial.

## Differential-field gauge invariance `[PROVED HERE]`

Let `K` be a differential field of meromorphic functions stable under translations, and let `f` be
a nonzero meromorphic function.  Fix a finite set of shifts `H={h_1,...,h_m}`.  Let `A` be a
nonzero element of `K`, with every translate `T_hA` still in `K`.

Put

`f_A=A f`.

For every `h in H`,

`T_h f_A=(T_hA)(T_hf)`.

Since `T_hA` is an invertible element of the meromorphic field `K`,

`K<(T_hf_A)_(h in H)>_D = K<(T_hf)_(h in H)>_D`.          (1)

Thus every differential transcendence degree and every differential-algebraic dependence relation
of the finite translate family is identical before and after the gauge.  In particular, full
translation-orbit differential independence is gauge invariant.

For logarithmic derivatives,

`D log f_A=D log f+D log A`,

and `D log A in K`.  Hence the corresponding finite logarithmic-derivative families also generate
the same differential fields:

`K<(T_h Dlog f_A)_(h in H)>_D = K<(T_h Dlog f)_(h in H)>_D`. (2)

If a source extractor is a finite constant-coefficient differential-translation operator `L`, then

`L(Dlog f_A)-L(Dlog f)=L(Dlog A) in K`.                    (3)

Therefore the extracted source class in `Mer/K` is unchanged.

### DA gauges outside the chosen base

More generally, suppose `A` is DA over `K` rather than an element of `K`.  Adjoin the finitely many
translated jets of `A` needed for a given finite test.  This is a differential-algebraic base
extension.  Differential transcendence degree is unchanged by such a base extension, and (1)--(3)
hold after extension.  Eliminating the differential-algebraic coefficients returns the same
differential transcendence ranks over `K`.

The rational-gauge specialization below avoids this extra base-change step entirely.

## Exact aperture strengthening `[PROVED HERE]`

For a differential field `K`, write

`J_m(f)=K(f,Df,...,D^m f)`

and let `ap_K(f)` be the least `m` for which the displayed jet tuple is algebraically dependent,
with value `infinity` for an HT element. If `A in K^x`, Leibniz gives a lower-triangular linear
transformation

`(f,Df,...,D^m f) -> (Af,D(Af),...,D^m(Af))`

whose diagonal is the nonzero element `A`. Applying the same formula to `f=A^(-1)(Af)` gives the
inverse. Therefore

`J_m(Af)=J_m(f)` for every `m`,

`ap_K(Af)=ap_K(f)`.                                       (3a)

This permits an exact quantitative realization. Over `K=C(s)`, the zero-free entire exponential
cascade

`U_0=1`, `U_1=exp(s)`, `U_(n+1)=exp(U_n)`

has `ap_K(U_n)=n` by the exact entire-cascade order theorem. A zero-free entire HT unit is

`U_infinity=exp(1/Gamma)`.

Indeed, Hölder makes `1/Gamma` HT. If `U_infinity` were DA, its logarithmic derivative
`(1/Gamma)'` would be DA, and an ADE for that derivative is an ADE for `1/Gamma` after shifting
derivative indices, a contradiction.

For any finite effective divisor `D`, let `Q_D` be its polynomial. Then

`F_(D,n)=Q_D U_n`

is entire and satisfies

`Div(F_(D,n))=D`, `ap_(C(s))(F_(D,n))=n`                  (3b)

for every `n in N union {infinity}`. Thus finite divisor data and differential aperture are
independent coordinates, not merely distinct examples at the HT endpoint.

## Arbitrary finite off-line packet implantation `[PROVED HERE]`

Choose a finite list of pairs

`0<a_j<1/2`, `b_j>0`, `j=1,...,r`,

whose functional-equation/conjugation quartets are pairwise disjoint.  In centered coordinates
`z=s-1/2`, define

`Q_j(z)=((z-a_j)^2+b_j^2)((z+a_j)^2+b_j^2)`

and

`A(s)=prod_j Q_j(s-1/2)`.                                  (4)

The polynomial `A` has real coefficients in centered coordinates and is even there.  Consequently

`A(1-s)=A(s)`, `A(conj s)=conj(A(s))`.                     (5)

Its zeros are exactly the prescribed off-critical quartets

`1/2 +/- a_j +/- i b_j`.                                   (6)

For real `s`, every factor in (4) is strictly positive:

`((z-a_j)^2+b_j^2)((z+a_j)^2+b_j^2)>0`, `z in R`.          (7)

Hence the gauge adds no real zero.

Now let `X` be any nonzero entire function satisfying the functional-equation and Schwarz
symmetries, and put

`X_A=A X`.

Then `X_A` has the same symmetries, contains every quartet (6), and differs from `X` only by a
rational gauge.  If `X` has exact entire order one, so does `X_A`: polynomial multiplication
preserves finite positive order.  If `X` is zero-free on the real axis, so is `X_A` by (7).

Equations (1)--(3) show that `X` and `X_A` have identical differential translate matroids,
identical logarithmic-derivative translate matroids, and identical finite extracted source classes
modulo `K`.

## Completed-xi countermodel family `[PROVED HERE]`

Take `X=xi` and `K=F_s`, Nagoshi's small-growth meromorphic differential field.  Every rational
function and every complex translate of the polynomial gauge lies in `F_s`.  The proved
prime-feature theorem and primitive transfer give full complex translation-orbit differential
independence for `xi` and `xi'/xi` over `F_s`.

For every finite packet (6), define

`xi_A=A xi`.                                                (8)

Then:

1. `xi_A` is entire of exact order one;
2. `xi_A(1-s)=xi_A(s)` and `xi_A(conj s)=conj(xi_A(s))`;
3. `xi_A` is zero-free on the real segment `0<s<1`, by the unconditional positivity of `xi`
   there and (7);
4. `xi_A` has every prescribed off-critical quartet (6), so its RH analogue is false;
5. every finite family of distinct complex translates of `xi_A` is differentially algebraically
   independent over `F_s`;
6. the same is true for the logarithmic derivatives of those translates;
7. the even-shift prime-source exposure of `Dlog xi_A` differs from that of `Dlog xi` by a rational
   function only.

Thus the strongest HT law obtained in this lane, all elementary completed-function symmetries,
exact order one, and real-axis nonvanishing are simultaneously compatible with arbitrary finite
off-line zero packets.

## Divisor-blindness theorem `[PROVED HERE]`

Let `I` be any invariant of nonzero meromorphic functions which factors through any combination of:

1. differential-algebraic dependence relations among finitely many translates and jets;
2. the same data for logarithmic derivatives;
3. finite constant-coefficient differential-translation source extractors modulo a
   translation-stable DA field.

Then `I(X_A)=I(X)` for every rational gauge `A` above.  Since `X_A` may contain an arbitrary finite
off-critical quartet packet while `I` is unchanged, no such invariant determines whether all zeros
lie on the critical line.

The quantitative equations `(3a)`--`(3b)` show that adding minimal differential order to `I` does
not repair the blindness: every finite effective divisor occurs at every finite aperture and at
infinite aperture.

Equivalently:

> The divisor-location predicate does not descend to the DA-gauge quotient on which these HT
> invariants live.

This is a theorem about the information content of HT laws, not a probabilistic heuristic.

## Operator-algebra correction for finite residue packets `[PROVED HERE] [BRIDGE]`

There is a second, independent reason not to identify a finite off-line residue packet with
torsion in the HT source-boundary module.  For a Laplace pair

`F(s)=integral_0^infinity exp(-s t)f(t)dt`,

the two basic actions are transmuted as

`partial_s F = Laplace(-t f)`,

`sF = Laplace(partial_t f)`

up to the standard endpoint distribution.  A finite packet

`ell(t)=sum_j p_j(t)exp(-lambda_j t)`

is killed by the constant-coefficient time operator

`prod_j(partial_t+lambda_j)^(deg(p_j)+1)`.

It is therefore torsion for the spectral-coordinate algebra `C[s]`, not for the
differential-algebra character algebra `C[partial_s]`.  Under the latter action, a polynomial acts
as multiplication by a polynomial in `t`; no nonzero such polynomial annihilates a nonzero
exponential polynomial on an interval.  After transform, the same packet is a rational principal
part and is already zero in the quotient modulo a DA base.

Thus finite spectral torsion and differential non-torsion are transverse notions.  Localizing the
HT boundary module cannot convert one into the other.  Any proposed RH saturation theorem must
first state which operator algebra acts; using the same symbol `D` for both actions creates a false
bridge.

This correction is consistent with the already formalized stronger warning in
`HTGeometry/FiniteGibbsDifferentialBoundary.lean`: even the rational function `1/s` has no nonzero
constant-coefficient annihilator under spectral differentiation, because successive derivatives
raise its pole order.  The present paragraph records the transform-level reason, not a new
independence theorem.

## Consequences for the named RH routes

The theorem reverses an overbroad research hope.  A law merely asserting HT, nonholonomicity, full
translation-orbit differential independence, or prime-source exposure modulo DA cannot prove or
disprove the full Li, Weil, Nyman--Beurling, Hilbert--Polya, Connes, or de Branges route.  Those
routes use extra data which breaks the gauge:

1. **Li/Keiper:** the canonical divisor-normalized Li coefficients change when zeros are implanted;
2. **Weil positivity:** the explicit-formula distribution acquires the added quartet atoms;
3. **Hilbert--Polya and Connes:** the spectral divisor changes;
4. **de Branges:** Hermite--Biehler/kernel positivity is divisor sensitive;
5. **Nyman--Beurling:** the exact reciprocal/Euler carrier, not its DA coset, controls the closure
   problem.

The full routes therefore remain logically available.  What is excluded is any implementation
which claims that the DA-gauge-invariant HT data alone already supplies their missing positivity or
spectral selector.

This also identifies a necessary condition on any genuinely RH-bearing HT law:

> It must be gauge-breaking and divisor-sensitive.  If it is invariant under rational symmetric
> gauges, it cannot select RH.

## Candidate competition and attack

1. **Finite-state obstruction.** Correct but already proved and too narrow.
2. **Categorical exclusion of the named routes.** False: several are RH-equivalent and all use
   divisor-sensitive infinite data.
3. **DA-gauge divisor blindness.** Correct and gives the exact reason HT-only categorical exclusion
   fails.

The theorem survives degenerate cases:

- one quartet is obtained with one degree-four gauge;
- repeated quartet multiplicities are obtained by powers of `Q_j`;
- arbitrary finite packets are obtained by products;
- the gauge is strictly positive on the real axis;
- taking `A=1` recovers the original function;
- no assertion is made for exact Euler coefficients rather than their class modulo DA.

## Scientific status and novelty gate

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The scientific mechanism is classical.
Multiplication by a base-field unit preserves generated differential fields; polynomials realize
arbitrary finite divisors; centered real-even polynomials preserve the two xi symmetries.  The
exact information-theoretic packaging was not located in the searched corpus, but a capable
specialist can derive it immediately.  The theorem therefore fails the novelty half of the dual
gate despite being complete and useful.

The surviving research residue is not another invariant on the DA quotient.  It is the search for
a canonical gauge-breaking constraint that is weaker than an RH-equivalent positivity criterion
but still excludes symmetric off-line DA implants.

## Formalization status

The concrete one-quartet rational-gauge countermodel is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/XiRationalQuartetGauge.lean`; its exact claim has a separate
stage-3 card.  The present theorem remains at stage 2 because the generated differential-field
equalities, logarithmic-derivative matroid invariance, arbitrary finite packet theorem, and exact
order-one statement have not all been formalized in Lean as this complete claim.

## Gates

- [x] Gauge invariance of translate-generated differential fields proved.
- [x] Exact minimal differential-aperture invariance proved.
- [x] Every finite effective divisor realized at every finite and infinite aperture.
- [x] Logarithmic-derivative and source-coset invariance proved.
- [x] Arbitrary finite symmetric off-line packet polynomial constructed.
- [x] Completed-xi specialization and route boundary proved.
- [x] Overbroad categorical route exclusion attacked and rejected.
- [x] Audit the differential-algebraic base-extension paragraph; the rational-gauge theorem does
  not depend on it, and differential transcendence rank is unchanged under a differential-
  algebraic base extension.
- [x] Formalize the concrete rational-quartet `xi` countermodel as a separate exact stage-3 claim.
- [x] Apply the final parent-theory novelty verdict and move this complete paper theorem to stage 2.

## Log

- 2026-07-11 -- Opened after the arbitrary-complex HT orbit theorem failed the novelty gate.  The
  off-line rational gauge family proves that the entire HT orbit matroid is orthogonal to finite
  divisor location and that HT-only data cannot categorically settle any full RH route.
- 2026-07-11 -- Completed the paper proof, classified the mechanism as a bridge, and separated the
  fully formalized concrete quartet countermodel from the still-paper-level differential-field
  invariance theorem.
- 2026-07-11 -- Consolidated the exact rational-gauge aperture theorem and the every-divisor at
  every-aperture realization from a duplicate bridge card. This strengthens the quantitative
  blindness statement without creating a second wrapper claim.
