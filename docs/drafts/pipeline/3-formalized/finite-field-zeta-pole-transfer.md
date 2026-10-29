# Finite-field zeta zeros in the shifted quotient

- **ID:** `finite-field-zeta-pole-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CLASSICAL BRIDGE
- **Source:** [finite-field-positive-genus-base](finite-field-positive-genus-base.md).
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
The finite count `2g` refers to the multiplicative coordinate and multiplicities,
not all lifts in the `s`-plane.

For the existing affine `A₁` inversion sets define the finite-field coefficient by
the finite product of `c(λ(β∨))`. The genus-dependent prefactor in Lee–Lombardo is
`3^(length(w)(1−g))=1`, since this curve has `g=1`. The finite simple reflection has
the singleton inversion set `{α}`, and the affine simple reflection has `{δ−α}`.
Their coefficients are exactly `c(λ₁)` and `c(λ₀)`. Hence the explicit pole parameters
above give genuine coefficient poles in either simple-coroot coordinate, independently
of the other coordinate. The proved cardinality two of the Frobenius index makes this
an existence theorem for either coordinate, not only a conditional statement indexed
by a potentially empty type. This uses the actual infinite affine root datum but supplies
no unproved group-level unfolding.

Attack: roots need not be distinct, and a denominator zero alone is not a pole.
The multiplicity formulation handles the first issue; disjoint modulus circles prove
the required unit conditions for the second. No functional equation or point-count
enumeration is needed. Summation of Weyl terms may still cancel these poles, so no
claim about the full Eisenstein series follows at this stage.

## Gates

- [x] Corpus and primary-literature audit; exact normalization fixed.
- [x] Dependency-closed paper proof followed by Lean formalization.
- [x] Reciprocal and shifted-quotient pole orders, complete finite pole locus, and multiplicities.
- [x] Arithmetic pole multiset has cardinality `2 * geometricGenus = 2`.
- [x] Explicit additive pole parameters and exact orders on `Re s = -1/2`.
- [x] Taylor identities and `HasFPowerSeriesAt` for the actual point-count quotient series.
- [x] Both simple affine coefficient formulas and unconditional pole existence.
- [x] Transitive axiom audit and owning umbrella imports.
- [x] Final non-output check of the installed coefficient source.

## Lean certificates and validation

All curve-level declarations below are in namespace
`GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase`.

- `ArithmeticEffectivityTheory/FiniteFieldEllipticZetaPoles.lean`:
  `shiftedZetaQuotientSeries_rational`, `reciprocalZeta_pole_iff`,
  `shiftedZetaQuotient_order_at_root`, `shiftedZetaQuotient_pole_iff`,
  `arithmeticPoleMultiset_card`, `arithmeticPoleMultiset_order`,
  `arithmeticZetaRatio_order_at_zero`, `arithmeticZetaRatio_pole_iff`,
  `arithmeticPoleParameter_spec`, and `finiteFieldZetaPoleTransfer_spec`.
  The combined specification has no parameters or mathematical assumptions.
- `ArithmeticEffectivityTheory/FiniteFieldEllipticZetaContinuation.lean`:
  `zetaFunction_taylor`, `shiftedZetaQuotient_taylor`,
  `zetaFunction_hasFPowerSeriesAt`, and `shiftedZetaQuotient_hasFPowerSeriesAt`.
  These identify the actual arithmetic series and certify its local convergence.
- `HTGeometry/LoopEisenstein/AffineA1FiniteFieldCoefficients.lean`, namespace
  `GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1`:
  `finiteFieldCoefficient_finiteReflection`, `finiteFieldCoefficient_affineReflection`,
  `simpleCoefficient_orders`, `simpleCoefficient_poles`, and `simpleCoefficient_has_poles`.
  The last theorem proves pole existence for every fixed other coordinate, with no
  assumed zero, pole, or noncancellation input.

The two curve-level modules passed foreground source compilation with exit 0 and no
diagnostics. Their oleans were created only for their dependent new modules. The coefficient
source passed verbatim in the independent non-output audit harness, which checked 29
selected declarations and their transitive dependencies with `#print axioms`. All report
exactly `[propext, Classical.choice, Quot.sound]`; the audit exited 0. Its complete output
is preserved in
[finite-field-zeta-pole-transfer-audit.txt](finite-field-zeta-pole-transfer-audit.txt).

The installed coefficient source passed its final foreground, non-output check with exit 0
and no diagnostics:

```sh
lake --old env lean GaloisForLFunctions/HTGeometry/LoopEisenstein/AffineA1FiniteFieldCoefficients.lean
```

Both owning umbrellas import the new leaves. A transitive source-import audit found no
dependency on either owning umbrella, so these imports introduce no cycle. No full or
umbrella build, existing-olean rebuild, numerical experiment, finite point enumeration,
proof placeholder, new mathematical axiom, kernel bypass, or raised Lean limit was used.

## Remaining full-series frontier

The actual quotient of point-count series and both simple affine zeta-product formulas
now have certified arithmetic poles. This does not construct an arithmetic Eisenstein
coset sum or identify its constant term with these formulas. Such an identification
requires finite-field arithmetic-series definitions and an unfolding proof. A pole theorem
for the full summed constant term or Eisenstein series additionally requires proof that
summation does not cancel the coefficient poles. These inputs remain open, not hidden
hypotheses of the completed theorems.

Do not replace the missing arithmetic coset sum by a definition equal to its proposed
constant term. The series in the user's earlier correction was not explicitly specified;
no identification with an unspecified series is claimed.
