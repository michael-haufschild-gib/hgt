# Irrational elliptic-gamma hypertranscendence and the exact translation-defect matroid

- **ID:** `irrational-elliptic-gamma-hypertranscendence-matroid`
- **Stage:** 3-formalized
- **Type:** SPECIAL-FUNCTION HYPERTRANSCENDENCE / EXACT DIFFERENTIAL MATROID
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE — PAPER PROOF]`
  `[SIGNIFICANCE PASS] [EXTERNAL NOVELTY PRELIMINARY] [NOT AN RH RESULT]`
- **Parent proof:**
  `../not_new_scientific_knowledge/paired-quasi-elliptic-constraint-rigidity.md`
- **Formal bridge:**
  `../../3-formalized/not_new_scientific_knowledge/relative-boundary-effectivity-conservativity.md`

## Theorem

Let `tau,sigma` lie in the complex upper half-plane and suppose that

```text
1,tau,sigma are linearly independent over Q.
```

Let `Gamma(z;tau,sigma)` be the standard additive elliptic gamma function and put

```text
F=partial_z log Gamma(z;tau,sigma),
H=Z+Z tau+Z sigma.
```

Then:

1. `F` and `Gamma` are hypertranscendental over `C(z)`.
2. The exact differential-algebraic shift spectrum is

   ```text
   {h in C : Delta_h F is DA over C(z)}=H.                 (1)
   ```

3. If `h_1,...,h_n` represent `m` distinct nonzero cosets of `H`, then

   ```text
   dtrdeg_(C(z)) C(z)<Delta_(h_1)F,...,Delta_(h_n)F>_delta=m.  (2)
   ```

   Repeated cosets contribute no new differential-transcendence degree and the zero coset is
   differential-algebraic.  Thus the complete finite shift-defect matroid is the partition
   matroid of `C/H`, with the zero class deleted from the free part.
4. For `h notin H`, the elliptic-gamma quotient

   ```text
   Gamma(z+h;tau,sigma)/Gamma(z;tau,sigma)
   ```

   is hypertranscendental.

This is a theorem about the actual elliptic gamma function.  The fact that a broader one-pole
constraint class collapses to elliptic gamma does not demote the theorem; it only prevents the
class itself from being advertised as a new family.

## Proof

Write

```text
lambda_tau=partial_z log theta_tau,
lambda_sigma=partial_z log theta_sigma.
```

The elliptic-gamma equations give the compatible paired boundary system

```text
Delta_sigma F=lambda_tau,
Delta_tau F=lambda_sigma.                                  (3)
```

The two right-hand sides are differential-algebraic: their derivatives are elliptic functions.
Let `E_tau,E_sigma` be the elliptic function fields for the lattices `Z+Z tau` and
`Z+Z sigma`, and put `K=E_tau E_sigma`.  Rational independence implies:

- `E_tau` and `E_sigma` are algebraically independent over `C`;
- the common fixed field of the two translations on every field generated below is `C`, because
  a meromorphic function with periods `1,tau,sigma` has a nondiscrete period group and is
  constant.

For any finite family of shifts, each `d_h=Delta_h F` satisfies a compatible unipotent system over
`K`.  The several-automorphism parameterized Picard--Vessiot theory of Hardouin--Singer applies to
this integrable two-translation system.  If the `d_h` were differentially dependent, the proper
differential algebraic subgroup of the additive Galois group would, by Cassidy's classification,
give operators `L_h in C[delta]`, not all zero, and one simultaneous primitive `g in K` such that

```text
Delta_sigma g=sum_h L_h(Delta_h lambda_tau),
Delta_tau   g=sum_h L_h(Delta_h lambda_sigma).              (4)
```

The usual temporary extension of the common constants to a differential closure does not enlarge
the final coefficient field.  Every invariant fraction and every telescoper uses finitely many
coefficients; specialization over the algebraically closed field `C`, followed by normalization
of one nonzero operator coefficient, descends `(4)` to `C`.

View `K` as the function field of the product of the two elliptic curves; what is used here is the
proved algebraic independence of their function fields in the common argument, not abstract
nonisogeny of the curves.  In the first equation of `(4)`, translation by `sigma` acts on the
`E_tau` factor and fixes the `E_sigma` factor.  Specializing the second factor away from the finite
denominator locus produces the same equation with `g_tau in E_tau`.

The function `lambda_tau(z+h)-lambda_tau(z)` has two simple pole classes on the first elliptic
curve.  Their translation-by-`sigma` orbits coincide exactly when `h in H`.  For `h notin H`, the
highest principal-part coefficient of every nonzero `L_h` has nonzero sum on one isolated orbit.
Every coboundary `Delta_sigma g_tau` has zero principal-part sum on each orbit by finite-support
telescoping.  This contradicts `(4)` and proves `(1)`.

For representatives of distinct nonzero cosets, their isolated pole orbits are disjoint.  Choosing
an operator of maximal differential order in `(4)` gives the same contradiction on one private
orbit, proving differential independence and `(2)`.  Hypertranscendence of `F` follows from any
`h notin H`: if `F` were DA, so would be `Delta_h F`.  If `Gamma` were DA, its logarithmic
derivative would be DA.  The quotient statement follows by logarithmically differentiating the
quotient.

## Differential-algebraic anomaly corollary

Let `B` be the multiplicative group of nonzero meromorphic functions DA over `C(z)` and let
`M` be all nonzero meromorphic functions.  For `u in H`, put

```text
a_u(z)=Gamma(z+u)/Gamma(z).
```

Then `a` is a cocycle in `Z^1(H,B)`, its class is nonzero in `H^1(H,B)`, and its image in
`H^1(H,M)` is zero.  Indeed, `Gamma` trivializes it in `M`; any trivialization in `B` would differ
from `Gamma` by a meromorphic function fixed by `1,tau,sigma`, hence by a constant, contradicting
the theorem.  Equivalently, the fixed coset of `Gamma` in `M/B` has nonzero connecting class.

This is the first natural analytic realization of the source-effectivity object: locally DA
boundary multipliers possess a meromorphic primitive but no DA primitive.

## Pointed DA--holomorphic bi-anomaly corollary

The gamma-gerbe construction supplies a second, independent anomaly face from the same source
cochain.  On the fixed irrational triptic fibre, the Felder--Henriques--Rossi--Zhu group--Cech
cochain `s_Gamma` has coboundary components that are exponentials of rational functions.  Hence
its coboundary lies in the intersection of the holomorphic-unit and DA-meromorphic coefficient
complexes.

It follows that `s_Gamma` defines a nonzero relative class modulo this intersection.  Its
connecting class maps to the nontrivial gamma-gerbe class and hence to the Dixmier--Douady
generator.  The source pointing selects the standard wedge component `Gamma(z;tau,sigma)`, whose
independently nonzero edge is the DA translation anomaly above.  Both edge anomalies become
effective in the ambient meromorphic coefficient theory.

This is proved in
`irrational-elliptic-gamma-pointed-bi-anomaly-fracture.md`.  It is the first natural analytic
two-axis model of the source-fracture architecture.  The DA and DD classes are not identified;
their exact relation is common pointed origin and simultaneous ambient effectivity.

## Significance and novelty gate

Masaki Kato proved differential algebraicity of the multiple elliptic gamma function for rational
period vectors and stated explicitly that the non-rational-period case was unknown:
https://doi.org/10.1619/fesi.64.225.  The present theorem settles the generic rank-three
non-rational regime for `G_1` in the opposite direction and strengthens it to the exact spectrum
and complete finite defect matroid.

The principal parent theories are:

- Hardouin--Singer's parameterized difference Galois theory, including the general
  `Sigma-Delta-Pi` theory for several commuting automorphisms,
  https://arxiv.org/abs/0801.1493;
- Cassidy's classification of differential algebraic subgroups of the additive group;
- elliptic orbital-residue and telescoping theory;
- Felder--Varchenko's elliptic-gamma automorphy class,
  https://arxiv.org/abs/math/9907061;
- the gamma gerbe of Felder--Henriques--Rossi--Zhu,
  https://arxiv.org/abs/math/0601337.

Morain's 2025--2026 geometric multiple-elliptic-gamma papers extend the Bernoulli-rational
coboundary and higher-cocycle theory to higher-rank lattices.  They do not address differential
algebraicity, the irrational shift spectrum, or the DA-filtered anomaly.

Targeted searches through 2026 found results on differential transcendence of elliptic
hypergeometric solutions and `q`-difference equations over elliptic fields, but no theorem for the
irrational elliptic gamma function, no spectrum `(1)`, no matroid `(2)`, and no DA-filtered
cohomology class above.  This is a preliminary novelty conclusion, not a substitute for specialist
review.

- **Paper verdict:** yes.  The hypertranscendence theorem, exact spectrum, matroid, and DA anomaly
  form a coherent standalone paper.  The pointed DA--holomorphic bi-anomaly materially strengthens
  it by connecting the new DA theorem to the established gamma-gerbe geometry through a new
  intersection-coefficient relative class.
- **Fields verdict:** no.  This is significant new special-function knowledge, not the general HT
  reconstruction/effectivity equivalence.
- **RH boundary:** the theorem supplies a natural analytic HT effectivity model but no zeta source
  object, critical-zero statement, positivity theorem, or RH implication.

## Formalization status

Lean now proves the actual meromorphic elliptic-gamma theorem surface, not only an abstract
boundary skeleton.  The paper-facing capstone is
`GaloisForLFunctions.HTGeometry.EllipticGammaTranslationCosetRankLaw`; it reuses the analytic
modules `EllipticGammaPeriodCosetMatroid`, `EllipticGammaQuotientPeriodCosetMatroid`, and
`EllipticGammaRationalBaseMatroid`.

Unconditional declarations package:

- the complete pointed period-coset matroid for additive defects over the paired elliptic
  compositum;
- the same complete pointed matroid for multiplicative shift quotients;
- exact extended rank of every indexed subpacket as number of occupied nonzero period classes;
- equality of quotient and logarithmic-defect matroids over the embedded rational-coordinate
  field;
- freeness over that rational base for every separated nonzero period-class family;
- simultaneous hypertranscendence of the elliptic gamma source and logarithmic derivative over
  the paired elliptic compositum.

The paper's complete upper structure over `C(z)` additionally invokes the classical theorem that
the full elliptic function field is generated by a Weierstrass function and its derivative, hence
is differentially algebraic over the constants.  Mathlib contains the Weierstrass differential
equation but not the required global generation theorem for this repository's meromorphic elliptic
subfield.  That classical bridge is proved on paper and is not represented by a Lean axiom.  Lean
therefore certifies the full natural-base matroid and the rational-base independence/lower-rank
half exactly; it does not overstate the missing classical base-change interface.

## Gates

- [x] actual elliptic-gamma theorem isolated from the collapsed abstract class
- [x] complete paper proof written
- [x] Hardouin--Singer several-automorphism parent checked
- [x] exact shift spectrum and finite differential matroid proved
- [x] complete natural-base defect and quotient matroids Lean-formalized
- [x] exact arbitrary-subpacket rank law Lean-formalized
- [x] rational-base quotient/defect transport and separated-family freeness Lean-formalized
- [x] nonzero DA-filtered cohomology class deduced
- [x] pointed DA--holomorphic bi-anomaly class deduced
- [x] DD and DA anomaly faces recovered from one pointed gamma cochain
- [x] external search found Kato's explicit open non-rational regime
- [x] preliminary exact/equivalent/stronger novelty search
- [x] significance: resolves an open special-function regime and gives strictly stronger structure
- [x] algebraic conservativity/effectivity core Lean-formalized
- [x] classical elliptic-field generation bridge formalized for the full rational-base upper matroid
      (obtained without the generation theorem: `ellipticMeroField_le_daOverRatFuncField`,
      `meromorphicEllipticCompositum_le_daOverRatFuncField`,
      `differentialAlgebraicOver_ratFunc_of_differentialAlgebraicOver_compositum`, and the two
      resonant-class corollaries — see the progress entry at the end of this card)
- [ ] independent expert audit of simultaneous telescoping descent and novelty

## Lean progress — the elliptic-field bridge, obtained without the generation theorem

`formal/GaloisForLFunctions/HTGeometry/EllipticCompositumRationalBase.lean` (axiom-clean, umbrella
registered).  The gate below asked for "the classical elliptic-field generation bridge", i.e. the
theorem that the field of `Lambda`-elliptic functions is `C(P, P')` and therefore differentially
algebraic over the constants.  That theorem is still absent from mathlib for this repository's
meromorphic elliptic subfield — and it is no longer needed, because its *consequence* is now proved
directly:

- **`ellipticMeroField_le_daOverRatFuncField`** — for `Im tau > 0`, every element of the concrete
  elliptic meromorphic field `ellipticMeroField tau` is differentially algebraic over `C(z)`.  This
  is `differentialAlgebraicOver_of_mem_ellipticMeroField` (proved in
  `EllipticMeroFieldDifferentialAlgebraicity` from the unconditional elliptic
  differential-algebraicity theorem: a doubly periodic meromorphic germ is DA, with no theta
  functions, no Weierstrass structure theorem and no contour integration), combined with
  `linearIndependent_one_of_im_pos`.
- **`meromorphicEllipticCompositum_le_daOverRatFuncField`** — hence every element of the paired
  elliptic compositum `E_sigma E_tau` is differentially algebraic over `C(z)`; the differentially
  algebraic germs form an intermediate field `daOverRatFuncField`, and the compositum is a join of
  two elliptic fields.
- **`differentialAlgebraicOver_of_base_differentialAlgebraic`** — a general differential-field tower
  law: if every element of a base field `B` (inside the ambient differential field) is
  differentially algebraic over `F`, then differential algebraicity over `B` descends to `F`.  A
  witnessing jet relation has finitely many coefficients, each DA over `F`, so
  `differentialAlgebraicOver_trans_finite_nonempty` applies after descending the relation to the
  differential adjunction of those coefficients.
- **`differentialAlgebraicOver_ratFunc_of_differentialAlgebraicOver_compositum`** — therefore every
  statement of differential algebraicity over the *natural* elliptic base upgrades verbatim to the
  *rational* base `C(z)`.  This is exactly the base-change interface the card described as missing.
- **`differentialAlgebraicOver_ratFunc_thetaLogDerivDefectMero`** — the concrete instance: the theta
  logarithmic-derivative defect, the carrier of the zero shift class, is differentially algebraic
  over `C(z)`.

What is *not* claimed: the generation theorem itself (`C(P, P')`) is still not formalized, and the
transcendence-degree-one presentation of the elliptic field is not asserted anywhere.  The upper
matroid needs only differential algebraicity, and that is now unconditional.

The rational-base upper half is now formalized as well:

- **`differentialAlgebraicOver_ratFunc_ellipticGammaExternalLogDerivDefectMero_of_resonant`** and
  **`differentialAlgebraicOver_ratFunc_ellipticGammaExternalQuotientMero_of_resonant`** — for
  `h in H = Z + Z tau + Z sigma`, both the additive defect and the multiplicative shift quotient are
  differentially algebraic over `C(z)`, not merely over the paired elliptic compositum.  Together
  with the already formalized rational-base independence half
  (`ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase`,
  `..._differentialMatroid_eq_freeOn_rationalBase`) this is the complete rational-base statement:
  the zero coset carries no differential transcendence and distinct nonzero cosets are free.

## Stage-3 Lean certificate

```text
ellipticMeroField_le_daOverRatFuncField
meromorphicEllipticCompositum_le_daOverRatFuncField
differentialAlgebraicOver_ratFunc_of_differentialAlgebraicOver_compositum
ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase
```

The classical elliptic-field generation theorem is not used: its consequence, differential
algebraicity of the elliptic meromorphic field over `C(z)`, is proved directly.

Every declaration named above was resolved against the built Lean tree and `#print axioms`
reported only `propext`, `Classical.choice`, `Quot.sound`.  `scripts/formal_tools.py lint`
reports no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in the tree.
