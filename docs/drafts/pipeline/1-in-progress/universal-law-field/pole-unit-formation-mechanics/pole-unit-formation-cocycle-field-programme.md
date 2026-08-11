# Pole-unit formation-cocycle mechanics

- **ID:** ULF-PUFM-1
- **Stage:** 1-in-progress
- **Type:** FIELD PROGRAMME / COMPLETED FORMATION MECHANISM
- **Statement:** Near a normalization pole, source formation should split canonically into a
  universal polar law and a scale-cocycle whose full correction tower reconstructs the regular
  constitutive germ.
- **Status:** `[MECHANISM, NOT OBJECT] [PRE-RH] [PAPER CORE SEPARATE]`

## 1. Why this programme exists

The full-frontier grammar

\[
 \textsf{mark}\to\textsf{form}\to\textsf{ghost}\to\textsf{dualize}
 \to\textsf{admit}\to\textsf{saturate}\to\textsf{conserve}
\]

has a finite exact realization in Witt-formation mechanics.  Its first genuinely cofinal source
problem is not another finite symmetric-function identity.  It is what happens when an infinite
positive formation reaches its normalization wall.

The existing critical-clock theorem proves that a simple pole produces the universal
unit-exponential clock.  The existing critical-clock blindness theorem proves that this leading
law cannot determine the divisor.  Therefore the universal limit is not the missing field.  The
load-bearing datum must be the entire deformation away from the limit.

## 2. Frozen mechanism

Write a meromorphic source near a pole as

\[
 Z(z)=z^{-r}U(z),\qquad U(0)\ne0.
\]

For scale `epsilon` and relative displacement `w`, define the normalized formation response

\[
 B_\epsilon(w)=\frac{Z(\epsilon w)}{Z(\epsilon)}
 =w^{-r}\frac{U(\epsilon w)}{U(\epsilon)}.
\]

The proposed field mechanism is the four-level decomposition

\[
 \boxed{
 \text{pole order}
 \;\oplus\;
 \text{scale cocycle}
 \;\oplus\;
 \text{correction jets}
 \;\oplus\;
 \text{analytic continuation memory}.}
\]

It is operational:

1. **form:** `Z` is the completed source response;
2. **conserve:** ratios compose under successive scale changes;
3. **ghost:** logarithmic correction jets linearize the cocycle;
4. **reconstruct:** one nontrivial scale ray recovers the regular unit germ;
5. **admit:** the positive Gibbs source exists only on one side of the pole;
6. **remember:** analytic continuation of the reconstructed germ carries the divisor.

## 3. Conjecture attacks

1. **The universal Gamma clock determines the source.**  False by the corpus's explicit
   critical-clock divisor-blind witness.
2. **A fixed finite correction depth determines the divisor.**  Attack by multiplying the regular
   unit by a factor beginning in degree `N+1` and carrying new zeros.
3. **Positive Mellin coefficients orient the continued divisor.**  False without an additional
   reflected order law; the blind witness is a positive source with an off-axis zero.
4. **The scale cocycle is merely a ratio identity.**  Test whether one ray reconstructs every
   logarithmic unit coefficient and whether the same coefficients control probability moments,
   Hankel sections, and analytic continuation.
5. **Analytic continuation is automatic from the local germ.**  Uniqueness is automatic only after
   a common connected continuation domain is supplied; existence and source admission are not.

## 4. RH gate

For the high-exponent Euler shell,

\[
 S_m(1+z)=z^{-1}U_m(z),\qquad
 U_m(z)=((1+z)-1)\zeta(1+z)H_m(1+z).
\]

For `m>=12`, `H_m` is zero-free on the strict-right half-plane.  Thus the full correction germ,
once continued there, remembers exactly the nonpolar zeta divisor.  This changes the RH question
from “find another carrier” to the following mechanism-level problem:

> construct a source-generated reflected complete-order law on the full scale cocycle, and prove
> that it remains admitted under the continuation which the correction tower reconstructs.

No critical-line conclusion may be claimed from the leading exponential clock, a finite jet, or
positivity on the convergent real axis.  The downstream selection theorem is now exact: finite
formation and exterior responses obey an inverse conservation law, and any joint Hausdorff
multiplicative completion preserves that inverse.  For the Euler-shell pole unit this would exclude
every strict-right zero.  The missing construction is therefore a source-generated joint
formation/exterior completion, not an unspecified “complete-order” condition.

## Gates

- [x] leading universal clock separated from constitutive corrections
- [x] exact cocycle and correction-jet reconstruction conjecture frozen
- [x] known critical-clock blindness installed as falsifier
- [x] dependency-closed analytic theorem promoted
- [x] Lean certification of exact algebraic/reconstruction core
- [x] abstract conservative-inverse completion and RH selection consequence
- [ ] source-generated joint formation/exterior completion on the strict-right half-plane
- [ ] RH selection consequence

## Log

- 2026-08-11 — opened after the full-frontier fusion experiment showed that finite Witt formation
  and safe-fibre complete test closure still stop at the normalization wall.
- 2026-08-11 — pole/unit scale cocycle, correction reconstruction, and finite-depth divisor
  blindness proved on paper and certified in Lean.  The remaining gate is a source-generated
  reflected complete-order continuation, not another local response identity.
