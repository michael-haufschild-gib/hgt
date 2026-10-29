# Finite-field zeta zeros in the shifted quotient

- **ID:** `finite-field-zeta-pole-transfer`
- **Stage:** 1-in-progress
- **Type:** CLASSICAL BRIDGE
- **Source:** [finite-field-positive-genus-base](../3-formalized/finite-field-positive-genus-base.md).
- **Target:** Prove actual meromorphic pole orders, including multiplicities, for the
  reciprocal and shifted quotient of the constructed elliptic curve's point-count zeta function.

## Scope and frontier

Write `Z(T)=P(T)/((1−T)(1−3T))` for the already formalized curve over `F₃`.
The source polynomial `P` comes from the actual extension point counts; `deg P=2`
and every root has modulus `1/√3`. The previous module proves noncancellation
algebraically, but not meromorphic pole orders.

The natural Eisenstein constant-term factor is `ζ_F(s)/ζ_F(s+1)`, hence
`Z(T)/Z(T/3)` with `T=3^(−s)`. Lee–Lombardo, *Eisenstein series on affine
Kac–Moody groups over function fields*, Sections 4 and 7,
<https://arxiv.org/pdf/1208.4006>, is the primary reference. This is classical
mathematics: verdict **BRIDGE**, no novelty claim.

The corpus's loop-Eisenstein programme currently concerns `Q` and still lacks its
arithmetic-series unfolding. No finite-field arithmetic Eisenstein series or unfolding
was found. A theorem about the quotient below must not be represented as a theorem
about that unconstructed series. The exact remaining input is an identification of its
constant term with the coefficient expansion and a proof that summation does not cancel
the relevant coefficient poles.

The supplied continuation does not name or define the series. The Eisenstein ratio is
the concrete application selected from the corpus and literature, not a proved
identification of an otherwise unspecified series.

## Exact statement and dependency-closed paper proof `[PROVED HERE]`

Let `ρ` be any root of `P`, of algebraic multiplicity `m>0`.
The polynomial germ has analytic order `m`: factor
`P(T)=(T−ρ)^m U(T)` with `U(ρ)≠0`.
The denominator of `Z` is nonzero at `ρ`, so
`ord_ρ Z=m` and `ord_ρ(1/Z)=−m`.

Let `C(T)=Z(T)/Z(T/3)`. At `T=3ρ`, the numerator `Z(T)` is an analytic
unit: `|3ρ|²=3`, whereas the zeros of `P` have norm squared `1/3` and the
two denominator roots have norm squared `1` and `1/9`.
The germ `Z(T/3)` has order `m`, since the linear substitution has nonzero
derivative `1/3`. Consequently `ord_(3ρ) C=−m`. This proves pole inheritance
with the exact original root multiplicity, without an assumed noncancellation input.

Algebraic cancellation gives the reduced rational expression
`C(T)=(1−T/3)P(T)/((1−3T)P(T/3))` away from finitely many exceptional values.
It represents the same meromorphic germ everywhere; division-by-zero conventions
at individual points are irrelevant. The quotient's finite poles are exactly `T=1/3`
(simple) and `T=3ρ` for roots `ρ` of `P`, with their multiplicities. Its nontrivial
pole multiset therefore has cardinality `2g=2`.

The series version is defined directly as `Z(T) * Z(T/3)⁻¹` in `C[[T]]`;
both denominators have constant coefficient one. Multiplication and the existing
point-count rationality identity give its rational equation coefficient by coefficient.
This ties the meromorphic quotient back to the formal arithmetic series.

For an analytic continuation certificate, take Taylor series at zero. The polynomial
denominator `D(T)=(1−T)(1−3T)` is nonzero at zero. The identity `DZ=P` therefore
holds on a neighborhood of zero, and multiplicativity of the Taylor map gives
`D·Taylor(Z)=P`. Cancelling the nonzero formal series `D` in the existing identity
`D·zeta=P` proves `Taylor(Z)=zeta`. A linear change of variable rescales Taylor
coefficients by `3^(−n)`. The local identity `C(T)Z(T/3)=Z(T)` then gives
`Taylor(C)=zeta·rescale(1/3,zeta)⁻¹`. Analyticity of `C` at zero supplies a positive
convergence radius and a `HasFPowerSeriesAt` certificate for precisely these coefficients.
Thus the rational meromorphic function is an actual continuation of the series.

For the additive parameter set `t(s)=exp(−log(3)s)` and
`c(s)=ζ_F(s)/ζ_F(s+1)=C(t(s))`. Since
`t'(s)=−log(3)t(s)≠0`, substitution preserves every meromorphic order.
Each root `ρ` gives the explicit pole representative
`s_ρ=−log(3ρ)/log(3)`, because `3ρ≠0` and `exp(log(3ρ))=3ρ`.
Moreover `|t(s_ρ)|²=3`, so injectivity of the real exponential gives
`−2log(3) Re(s_ρ)=log(3)` and `Re(s_ρ)=−1/2`.
The second coordinate repeats vertically; the finite count `2g` refers to the
multiplicative coordinate and multiplicities, not all points of the `s`-plane.

For the existing affine `A₁` inversion sets define the finite-field coefficient by
the finite product of `c(λ(β∨))`. The genus-dependent prefactor in Lee–Lombardo is
`3^(length(w)(1−g))=1`, since this curve has `g=1`. The finite simple reflection has
the singleton inversion set `{α}`, and the affine simple reflection has `{δ−α}`.
Their coefficients are exactly `c(λ₁)` and `c(λ₀)`. Hence the explicit pole parameters
above give genuine coefficient poles in either simple-coroot coordinate, independently
of the other coordinate. This uses the actual infinite affine root datum but supplies
no unproved group-level unfolding.

Attack: roots need not be distinct, and a denominator zero alone is not a pole.
The multiplicity formulation handles the first issue; disjoint modulus circles prove
the required unit conditions for the second. No functional equation or point-count
enumeration is needed. Summation of Weyl terms may still cancel these poles, so no
claim about the full Eisenstein series follows at this stage.

## Gates

- [x] Corpus and primary-literature audit; exact normalization fixed.
- [x] Exact paper proof; all analytic inputs are polynomial factorization and local order laws.
- [x] Lean formalization of reciprocal and shifted-quotient pole orders.
- [x] Exact pole locus and nontrivial pole count.
- [x] Explicit additive pole parameters and exact orders on the shifted Weil line.
- [ ] Analytic continuation of the actual point-count quotient series.
- [ ] Both simple affine Weyl coefficients and their poles.
- [ ] Foreground source check and transitive axiom audit; umbrella import.

## Continuation

Next analytic target: identify the Taylor series of `Z(T)/Z(T/3)` with the
actual point-count quotient series; apply its poles to both simple affine coefficients.
Keep the finite-field series/unfolding gap explicit; do not replace an arithmetic coset
sum by a definition equal to its proposed constant term.

## Working state

- `/tmp/hgt_zeta_poles.lean`: quotient power-series identities, reciprocal pole locus,
  shifted quotient exact multiplicities and complete pole locus, arithmetic pole multiset
  with cardinality and exact order. Complete foreground check passed, exit 0, no diagnostics.
- `/tmp/hgt_zeta_additive.lean`: standalone exponential/logarithmic coordinate lemmas;
  complete foreground check passed, exit 0, no diagnostics.
  `/tmp/hgt_zeta_additive_bridge.txt` contains the additive
  zeta ratio, explicit Frobenius-indexed pole parameters, and combined specification.
- `/tmp/hgt_zeta_coefficients.lean`: both simple affine coefficients and pole transfer;
  depends on the final `ArithmeticEffectivityTheory/FiniteFieldEllipticZetaPoles.lean`.
- `/tmp/hgt_zeta_continuation.lean`: Taylor identities and actual `HasFPowerSeriesAt`
  certificates for both zeta and its shifted quotient; awaiting the pole module's olean.
  It reuses `HardyTaylorCoefficient` and `AffineFluxTaylorCoeff`, whose oleans exist.
- Reuse `HTGeometry.analyticOrderAt_eval_eq_rootMultiplicity` from
  `HTGeometry/PolynomialHeatNonrealCount.lean` (existing olean). Do not rebuild it.
- Mathlib API scratch files `/tmp/hgt_zeta_poles_names.lean`,
  `/tmp/hgt_zeta_poles_api.lean`, `/tmp/hgt_zeta_order_api.lean` are owned and disposable.
  `meromorphicOrderAt_div` has no generated function-form alias in the installed olean;
  `convert!` resolves the pointwise-function and instance presentation mismatch. No limit
  changes or trusted computations.
- Production source `ArithmeticEffectivityTheory/FiniteFieldEllipticZetaPoles.lean`
  combines the passed multiplicative and coordinate proofs with the additive pole bridge.
  Its foreground source compilation passed with exit 0 and no diagnostics; its olean
  is required by the continuation module. Never rebuild that olean.
- `/tmp/hgt_zeta_continuation.lean` is being checked in foreground session `67055`.
  Do not start another compiler until it exits.
- Next: check `/tmp/hgt_zeta_continuation.lean`, preserve its final production source;
  update the coefficient draft to import the continuation module, check it; audit all
  transitive axioms, wire both owning umbrellas, preserve audit, clean only owned scratch.
