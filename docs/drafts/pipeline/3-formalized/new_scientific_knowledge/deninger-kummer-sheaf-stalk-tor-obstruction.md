# Kummer sheaf stalk Tor obstruction

- **ID:** `deninger-kummer-sheaf-stalk-tor-obstruction`
- **Stage:** 2-fully-proven
- **Type:** NO-GO THEOREM WITH POSITIVE SURVIVOR
- **Label:** `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`
- **Parent:** `deninger-leafwise-sheafified-unit-amalgamation`

## Statement

Let \(k\) be a field and let \(V\) be a \(k\)-vector space with
\(\Lambda^2V\ne0\).  Put
\[
 E=\Lambda_k(V),\qquad
 \mathfrak m=E^{>0},\qquad
 I=\mathfrak m^2=\Lambda_k^{\ge2}(V),\qquad
 K=E/I=k\oplus V.                                                     \tag{1}
\]
Give \(k\) the augmentation \(E\)-module structure.  Then
\[
 \operatorname{Tor}_1^E(k,K)
 \cong I/\mathfrak m I
 \cong\Lambda^2_kV\ne0.                                               \tag{2}
\]
Consequently
\[
 k\mathop{\otimes}^{\mathbb L}_E K
\]
is not equivalent to the underived augmentation base change.  In
particular, if a sheaf-level Kummer morphism is null after taking a stalk,
the stalk of the derived unit-amalgamated pushout has an additional Tor
class even when its chartwise derived global sections are conjecturally
two-term.

## Proof

The quotient in `(1)` gives a short exact sequence of \(E\)-modules
\[
 0\longrightarrow I\longrightarrow E\longrightarrow K\longrightarrow0.
                                                                            \tag{3}
\]
Apply \(k\otimes_E^{\mathbb L}-\).  Since \(E\) is free over itself,
\(\operatorname{Tor}_1^E(k,E)=0\).  The relevant part of the long exact
Tor sequence is
\[
 0\longrightarrow\operatorname{Tor}_1^E(k,K)
 \longrightarrow k\otimes_E I
 \longrightarrow k\otimes_E E.                                      \tag{4}
\]
The last arrow is induced by \(I\hookrightarrow E\) followed by the
augmentation.  It is zero because \(I\subset\mathfrak m\).  Therefore
\[
 \operatorname{Tor}_1^E(k,K)\cong k\otimes_E I
 \cong I/\mathfrak m I.                                               \tag{5}
\]
By `(1)`,
\[
 I=\bigoplus_{n\ge2}\Lambda^nV,\qquad
 \mathfrak mI=\bigoplus_{n\ge3}\Lambda^nV.
\]
Taking the quotient in `(5)` proves `(2)`.

A sheaf-cohomology Kummer class is represented by a derived morphism
\(HV[-1]\to\mathcal R_X\).  Its derived stalk is null: over a field, the
target stalk concentrated in degree zero has no corresponding degree-one
extension.  Hence the stalk of the sheaf pushout is the augmentation base
change above, and `(2)` applies.

## Consequences for Deninger's coefficient

1. The chartwise equivalence
   \[
   R\Gamma(X_F,\mathscr A_F)\simeq k\oplus V[-1]
   \]
   would not imply that \(\mathscr A_F\) has two-term homotopy sheaves.
2. A length-one Rost--Schmid resolution of only the degree-zero and
   degree-one homotopy sheaves cannot be justified from chartwise Milnor
   amplitude.
3. The sheafified pushout may still be a candidate for
   \(R\alpha_*\mathscr G\): a derived pushforward is allowed to have
   complicated stalks while its global cohomology is small.
4. The three-term arithmetic complex must be obtained from a proven
   two-level derived descent/localization model for chartwise derived
   sections, or from an additional source-natural localization that removes
   `(2)`.  It cannot be obtained by silently discarding stalk Tor.

## Positive survivor

The global chartwise algebra and its proved real Milnor amplitude survive.
The correct next conjecture is:

- construct the sheaf-level candidate;
- prove its chartwise derived-section comparison;
- prove arithmetic generic/closed-point localization gives a two-column
  derived-section diagram;
- totalize that diagram with the real orientation boundary.

`DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE` then applies to the resulting
acyclic descent model, not to the naïve homotopy sheaves of the pushout.

## Novelty audit

The Tor calculation is elementary.  Its new role is to rule out a tempting
but false shortcut in the Deninger program: transferring a global
two-term Milnor computation to stalkwise amplitude of
\(R\alpha_*\mathscr G\).

**Verdict:** `FULLY PROVEN ON PAPER`.

## Lean status

### The Tor computation landed

`formal/GaloisForLFunctions/RHTower/DeningerKummerStalkTor.lean`, together with
`formal/GaloisForLFunctions/RHTower/DeningerMilnorSquareZeroQuotient.lean` for `K = E/I`.
Axiom audit: `propext, Classical.choice, Quot.sound`.

- `deningerExtGe j` — the part of `E = Λ(V)` of degree at least `j`: `m = Λ^{≥1}`,
  `I = Λ^{≥2}`, `mI = Λ^{≥3}`.
- `deningerExtGe_mul_le`, `deningerIota_mem_one`, `deningerIotaMulti_mem`,
  `deningerExtGe_one_mul` — **`(1)`**: `m · Λ^{≥j} = Λ^{≥j+1}` for `j ≥ 1`.  With `j = 1` this is
  `I = m²`; with `j = 2` it is `mI = Λ^{≥3}`.  The hard inclusion is the splitting
  `v₁ ∧ ⋯ ∧ vₙ = v₁ · (v₂ ∧ ⋯ ∧ vₙ)` on the spanning wedge monomials.
- `deningerProj_two_of_ge_three`, `deningerExtSquare_inf_ge_three` — the graded projection kills
  `Λ^{≥3}`, so `Λ²V ∩ mI = 0`.
- `deningerExtGe_two_eq_sup` — `I = Λ²V ⊕ mI`.
- `deningerTor_map_eq`, `deningerTor_injective` — **`(2)`, `(5)`**: the quotient `I/mI` is exactly
  the image of `Λ²V`, and `Λ²V` injects into it: `I/mI ≅ Λ²V`.
- `deningerStalkTor_ne` — **the obstruction**: if `Λ²V ≠ 0` then `I ≠ mI`, so `I/mI ≠ 0` and the
  augmentation base change of `K` is not derived-trivial.
- `deningerExtSquareQuotEquiv` (companion module) — `K = E/I ≅ k ⊕ V` with `V² = 0`, the `(1)` of
  this card, proved as `RingQuot` of the square-zero relation.

### Exact scope

Formalized: the whole computation, i.e. `m² = I`, `mI = Λ^{≥3}`, `I/mI ≅ Λ²V` and its
nonvanishing — the content that makes the obstruction real.

Not formalized: the identification `Tor₁^E(k,K) ≅ I/mI` itself, which is the long exact sequence of
`(3)`–`(5)` together with `Tor₁^E(k,E) = 0`.  `E = Λ(V)` is noncommutative and mathlib has neither
tensor products nor Tor over a noncommutative ring, so that step cannot be stated there; it is
standard homological algebra and the card's own proof treats it as such.  The consequences listed
for Deninger's coefficient are statements about objects the corpus does not construct.
